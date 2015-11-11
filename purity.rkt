#lang racket

(require "general.rkt")
(require "ast.rkt")
(require "lattice.rkt")
(require "cesk.rkt")
(require "test.rkt")

(provide (all-defined-out))

;;
(define (outer-scope-declaration? decl e parent)
  (let up ((e e))
    (let ((p (parent e)))
      (match p
        (#f #f)
        ((«lam» _ x _)
         (let right ((x x))
           (if (null? x)
               (up p)
               (if (equal? decl (car x))
                   #t
                   (right (cdr x))))))
        ((«let» _ x e0 e1)
         (if (eq? e0 e)
             (up p)
             (if (equal? decl x)
                 #t
                 (up p)))) 
        ((«letrec» _ x _ _)
         (if (equal? decl x)
             #t
             (up p)))
        (_ (up p))))))

(define (inner-scope-declaration? decl e)
  (or (eq? decl e)
      (for/or ((e* (children e)))
        (inner-scope-declaration? decl e*))))

(define (free-variable? decl e)
  (set-member? (free e) decl))

(define (ctx-local-decl? decl κ)
  (and κ
       (let ((λ (ctx-λ κ)))
         (inner-scope-declaration? decl λ))))

(define (get-declaration name e parent)
  (let up ((e e))
    (let ((p (parent e)))
      (match p
        (#f #f)
        ((«lam» _ x _)
         (let right ((x x))
           (if (null? x)
               (up p)
               (if (equal? name («id»-x (car x)))
                   (car x)
                   (right (cdr x))))))
        ((«let» _ x e0 e1)
         (if (eq? e0 e)
             (up p)
             (if (equal? name («id»-x x))
                 x
                 (up p)))) 
        ((«letrec» _ x _ _)
         (if (equal? name («id»-x x))
             x
             (up p)))
        (_ (up p))))))

(define (escape-analysis sys)
  (let* ((graph (system-graph sys))
         (initial (system-initial sys))
         (ast (ev-e initial))
         (α (lattice-α (system-lattice sys)))
         (γ (lattice-γ (system-lattice sys)))
         (σ (system-σ sys)))

    (define (eval-atom ae ρ σ) ; copied from cesk, but in principle can/should be provided in system
      (match ae
        ((«lit» _ v)
         (α v))
        ((«id» _ x)
         (let ((a (env-lookup ρ x)))
           (store-lookup σ a)))
        ((«lam» _ x e)
         (let ((cl (clo ae ρ)))
           (α cl)))
        ((«quo» _ atom)
         (α atom))
        (_ (error "cannot handle ae" ae))))

    (define (check-values ae ρ σ M)
      (let ((d (eval-atom ae ρ σ)))
        (for/fold ((M M)) ((w (γ d)))
          (match w
            ((clo λ _) (set-add M λ))
            (_ M)))))
    
    (define (handle-state s M)
        (match s
          ((ev («app» _ _ aes) ρ σi _ _ _)
           (let ((σ (vector-ref σ σi)))
             (for/fold ((M M)) ((ae aes))
               (check-values ae ρ σ M))))
          ((ev («set!» _ _ ae) ρ σi _ _ _)
           (let ((σ (vector-ref σ σi)))
             (check-values ae ρ σ M)))
          ;((ev («let» _ _ (? ae? ae) _) ρ σi _ _ _)
          ;((ev (? ae? ae) _ _ (cons (letk x e ρ*) ι) κ Ξi)
          ((ev (? ae? ae) ρ σi '() _ _)
           (let ((σ (vector-ref σ σi)))
             (check-values ae ρ σ M)))
          (_ M)))

    (define (traverse-graph graph)
      (for/fold ((M (set))) (((s t) graph))
          (handle-state s M)))

    (traverse-graph graph)))


(define (print-escape-info M)
  (for ((λ M))
    (printf "~a\n" λ)))


(define FRESH "fresh")
(define UNFRESH "unfresh")

(define (fresh-analysis sys ⊥ ⊔ escapes?)
  (let* ((graph (system-graph sys))
         (Ξ (system-Ξ sys))
         (initial (system-initial sys))
         (ast (ev-e initial))
         (parent (make-parent ast)))

    (define (freshness ae Fκ)
      (match ae
        ((«id» _ x)
         (let* ((decl (get-declaration x ae parent)))
                (hash-ref Fκ decl ⊥)))
        (_ (set UNFRESH))))

    (define (handle-state q E s Fs)
      (let ((Fs (if (and (ev? s)
                         («lam»? (parent (ev-e s))))
                    (let* ((κ (state-κ s))
                           (κq (match q ; with a match just to be sure we're transitioning from an app (`(ev-κ q)` would suffice)
                                 ((ev («app» _ _ _) _ _ _ κq _) κq)))
                           (ρ* (ev-ρ s))
                           (Ξ (vector-ref Ξ (ev-Ξ s)))
                           (Fκ (hash-ref Fs κ (hash)))
                           (Fκ* (for/fold ((Fκ Fκ)) ((name (hash-keys ρ*)))
                                  (let ((decl (get-declaration name (ev-e s) parent)))
                                    (hash-set Fκ decl (⊔ (hash-ref Fκ decl ⊥) (set UNFRESH)))))))
                      (hash-set Fs κ Fκ*))
                     Fs)))
        (match s
          ((ev («set!» _ x ae) ρ _ ι κ Ξi)
           (let ((declx (get-declaration («id»-x x) x parent))
                 (Ξ (vector-ref Ξ Ξi)))
             
             (define (walk-stack-set S W Fs)
               (if (set-empty? W)
                   Fs
                   (let ((κdyn (set-first W)))
                     (if (set-member? S κdyn)
                         (walk-stack-set S (set-rest W) Fs)
                         (let* ((κ (car κdyn))
                                (dyn (cdr κdyn))
                                (Fκ (hash-ref Fs κ (hash)))
                                (ψ (if dyn
                                       (freshness ae Fκ)
                                       (set UNFRESH)))
                                (Fκ* (hash-set Fκ declx (⊔ (hash-ref Fκ declx ⊥) ψ)))
                                (Fs* (hash-set Fs κ Fκ*)))
                           (if κ
                               (let* ((λ (ctx-λ κ))
                                      (ικs (stack-lookup Ξ κ))
                                      (dyn* (and dyn (not (escapes? λ)))))
                                 (let* ((W* (set-union (set-rest W) (for/set ((ικ ικs)) (cons (cdr ικ) dyn*)))))
                                   (walk-stack-set (set-add S κdyn) W* Fs*)))
                               (walk-stack-set (set-add S κdyn) (set-rest W) Fs*)))))))

             (walk-stack-set (set) (set (cons κ #t)) Fs)))
          ((ev («let» _ x (? ae? ae) e1) _ _ ι κ Ξi) ; only on ae; only for this impl
           (let* ((declx x)
                  (Fκ (hash-ref Fs κ (hash)))
                  (ψ (freshness ae Fκ))
                  (Ξ (vector-ref Ξ Ξi))
                  (Fκ* (hash-set Fκ declx (⊔ (hash-ref Fκ declx ⊥) ψ))))
             (hash-set Fs κ Fκ*)))
          ((ev (? ae? ae) _ _ (cons (letk x e ρ*) ι) κ Ξi)
           (let* ((declx x)
                  (Fκ (hash-ref Fs κ (hash)))
                  (ψ (freshness ae Fκ))
                  (Ξ (vector-ref Ξ Ξi))
                  (Fκ* (hash-set Fκ declx (⊔ (hash-ref Fκ declx ⊥) ψ))))
            (hash-set Fs κ Fκ*)))
          ((ev (? ae? ae) _ _ '() κ Ξi)
           (let* ((Fκ (hash-ref Fs κ (hash)))
                  (ψ (freshness ae Fκ))
                  (Ξ (vector-ref Ξ Ξi))
                  (ικGs (stack-pop '() κ Ξ (set))))
             (for/fold ((Fs Fs)) ((ικG ικGs))
               (let* ((ι (car ικG))
                      (κ* (cadr ικG))
                      (Fκ (hash-ref Fs κ* (hash)))
                      (Fκ* (match ι
                             ((cons (letk x e ρ*) ι*)
                              (let ((declx x))
                                (hash-set Fκ declx (⊔ (hash-ref Fκ x ⊥) ψ))))
                             (_ Fκ))))
                 (hash-set Fs κ* Fκ*)))))
          ((ko v _ (cons (letk x e ρ) ι) κ Ξi) ; when e0 in let is not ae, letk is used; only for this impl
           (let* ((declx x)
                  (Ξ (vector-ref Ξ Ξi))
                  (Fκ (hash-ref Fs κ (hash)))
                  (Fκ* (if (set-member? E (fr))
                           (hash-set Fκ declx (⊔ (hash-ref Fκ declx ⊥) (set FRESH)))
                           Fκ))) ;TODO argh! ; only in impl
             (hash-set Fs κ Fκ*)))
          (_ Fs))))

    (define (traverse-graph* S W Fs F)
      (if (set-empty? W)
          F
          (let ((qt (set-first W)))
            (if (set-member? S qt)
                (traverse-graph* S (set-rest W) Fs F)
                (let* ((q (car qt))
                       (t (cdr qt))
                       (s (transition-s t))
                       (E (transition-E t))
                       (Fs* (handle-state q E s Fs))
                       (F* (hash-set F s Fs*)))
                    (let* ((W* (set-union (set-rest W) (for/set ((t* (hash-ref graph s (set))))
                                                         (cons s t*))))
                           (unchanged (equal? Fs Fs*))
                           (S* (if unchanged (set-add S qt) (set))))
                    (traverse-graph* S* W* Fs* F*)))))))

    (traverse-graph* (set) (set (cons #f (transition initial (set)))) (hash) (hash))))

(define (print-fresh-info F)
    (for (((s Fs) F))
      (printf "~a ~a\n" (state->statei s) (state-repr s))
      (for (((κ Fκ) Fs))
        (printf "\t~a ~a\n" (ctx->ctxi κ) (~a (if κ (ctx-λ κ) #f) #:max-width 30))
        (for (((decl FU) Fκ))
          (printf "\t\t~a -> ~a\n" decl FU)))
      (newline)))
                  
(define (fresh? ae Fκ parent ⊥)
  (match ae
    ((«id» _ x)
     (let* ((decl (get-declaration x ae parent))
            (freshness (hash-ref Fκ decl ⊥)))
       (equal? freshness (set FRESH))))
    (_ #f)))

(define (state-κ s)
  (match s
    ((ev _ _ _ _ κ _) κ)
    ((ko _ _ _ κ _) κ)))

(define (state-σ s σ)
  (match s
    ((ev _ _ σi _ _ _) (vector-ref σ σi))
    ((ko _ σi _ _ _) (vector-ref σ σi))))

(define (state-Ξ s Ξ)
  (match s
    ((ev _ _ _ _ _ Ξi) (vector-ref Ξ Ξi))
    ((ko _ _ _ _ Ξi) (vector-ref Ξ Ξi))))

(define (call-state-analysis sys)
  (let* ((graph (system-graph sys))
         (σ (system-σ sys))
         (Ξ (system-Ξ sys))
         (γ (lattice-γ (system-lattice sys))))

    (for/fold ((call-states (hash))) (((s ts) graph))
      (match s
        ((ev (? «app»? e) ρ σi ι κ Ξi)
         (for/fold ((call-states call-states)) ((t ts))
           (match t
             ((transition (ev _ _ _ '() κ* _) _)
              (let* ((A-existing (hash-ref call-states κ* (set)))
                     (σ (vector-ref σ σi))
                     (Ξ (vector-ref Ξ Ξi))
                     (A-updated (set-union A-existing (reachable (s-referenced s Ξ) σ γ))))
                     ;(A-updated (set-union A-existing (list->set (hash-keys σ)))))
                (hash-set call-states κ* A-updated)))
             (_ call-states))))
        (_ call-states)))))

(define GENERATES "GEN")
(define OBSERVES "OBS")

(define (traverse-graph graph initial Ξ observable? escapes?)

  (define parent (make-parent (ev-e initial)))

  (define (add-read-dep res λ R)
    (hash-set R res (set-add (hash-ref R res (set)) λ)))
  
  (define (add-observer λ F)
    (hash-set F λ (set-add (hash-ref F λ (set)) OBSERVES)))
  
  (define (add-observers res F O)
    (let ((λ-os (hash-ref O res (set))))
      (for/fold ((F F)) ((λ-o λ-os))
        (add-observer λ-o F))))

  (define (traverse-graph* S W F R O)
    (if (set-empty? W)
        F
        (let ((s (set-first W)))
          (if (set-member? S s)
              (traverse-graph* S (set-rest W) F R O)
              (let-values (((W* F* R* O*)
                            (for/fold ((W W) (F F) (R R) (O O)) ((t (hash-ref graph s (set))))
                              (match t
                                ((transition s* E)
                                 (let ((W (set-add (set-remove W s) s*)))
                                   (for/fold ((W W) (F F) (R R) (O O)) ((eff E))
                                     (let-values (((F R O) (handle-effect eff s F R O)))
                                       (values W F R O)))))))))
                (let* ((unchanged (and (equal? F F*) (equal? R R*) (equal? O O*)))
                       (S* (if unchanged (set-add S s) (set))))
                  (traverse-graph* S* W* F* R* O*)))))))

  (define (update-O-write res R O)
    (let ((λ-rs (hash-ref R res (set))))
      (for/fold ((O O)) ((λ-r λ-rs))
        (hash-set O res (set-add (hash-ref O res (set)) λ-r)))))

  (define (walk-stack-write eff res s S W F)
    (if (set-empty? W)
        F
        (let ((κdyn (set-first W)))
          (if (set-member? S κdyn)
              (walk-stack-write eff res s S (set-rest W) F)
              (let ((κ (car κdyn)))
                (if κ
                    (let ((dyn (cdr κdyn))) ;TODO λ to `inner?`?
                      (if (observable? eff κ s dyn)
                          (let* ((λ (ctx-λ κ))
                                 (F* (hash-set F λ (set-add (hash-ref F λ (set)) GENERATES)))
                                 (ικs (stack-lookup (state-Ξ s Ξ) κ))
                                 (dyn* (and dyn (not (escapes? λ)))))
                            (walk-stack-write eff res s (set-add S κdyn) (set-union (set-rest W) (for/set ((ικ ικs)) (cons (cdr ικ) dyn*))) F*))
                          (walk-stack-write eff res s (set-add S κdyn) (set-rest W) F)))
                    (walk-stack-write eff res s S (set-rest W) F)))))))

  (define (walk-stack-read eff res s S W F R O)
    (if (set-empty? W)
        (values F R)
        (let ((κdyn (set-first W)))
          (if (set-member? S κdyn)
              (walk-stack-read eff res s S (set-rest W) F R O)
              (let ((κ (car κdyn)))
                (if κ
                    (let ((dyn (cdr κdyn))) ;TODO λ to `inner?`?
                      (if (observable? eff κ s dyn)
                          (let* ((λ (ctx-λ κ))
                                 (F* (add-observers res F O))
                                 (R* (add-read-dep res λ R))
                                 (dyn* (and dyn (not (escapes? λ))))
                                 (ικs (stack-lookup (state-Ξ s Ξ) κ)))
                            (walk-stack-read eff res s (set-add S κdyn) (set-union (set-rest W) (for/set ((ικ ικs)) (cons (cdr ικ) dyn*))) F* R* O))
                          (walk-stack-read eff res s (set-add S κdyn) (set-rest W) F R O)))
                    (walk-stack-read eff res s S (set-rest W) F R O)))))))

  (define (handle-read-effect eff res s F R O)
    (let-values (((F* R*) (walk-stack-read eff res s (set) (set (cons (state-κ s) #t)) F R O)))
      (values F* R* O)))

  (define (handle-write-effect eff res s F R O)
       (let ((O* (update-O-write res R O))
             (F* (walk-stack-write eff res s (set) (set (cons (state-κ s) #t)) F)))
           (values F* R O*)))
    
    
  (define (handle-effect eff s F R O)
    (match eff
      ((wv a x)
       (handle-write-effect eff a s F R O))
      ((wp a n x)
       (handle-write-effect eff (cons a n) s F R O))
      ((rv a x)
       (handle-read-effect eff a s F R O))
      ((rp a n x)
       (handle-read-effect eff (cons a n) s F R O))
      (_ (values F R O))))
  
  (traverse-graph* (set) (set initial) (hash) (hash) (hash)))

(define (a-observable-effect? call-states)
  (lambda (eff κ s dyn)
    (match eff
      ((wv a _)
       (let ((A (hash-ref call-states κ)))
         (set-member? A a)))
      ((wp a _ _)
       (let ((A (hash-ref call-states κ)))
         (set-member? A a)))
      ((rv a _)
       (let ((A (hash-ref call-states κ)))
         (set-member? A a)))
      ((rp a _ _)
       (let ((A (hash-ref call-states κ)))
         (set-member? A a))))))

(define (sa-observable-effect? call-states parent)
  (lambda (eff κ s dyn)
    (match eff
      ((wv a x)
       (if dyn
           (let ((decl (get-declaration («id»-x x) x parent))
                 (λ (ctx-λ κ)))
             (if (inner-scope-declaration? decl λ)
                 #f
                 (let ((A (hash-ref call-states κ)))
                   (set-member? A a))))
           (let ((A (hash-ref call-states κ)))
             (set-member? A a))))
      ((wp a _ _)
       (let ((A (hash-ref call-states κ)))
         (set-member? A a)))
      ((rv a x)
       (if dyn
           (let ((decl (get-declaration («id»-x x) x parent))
                 (λ (ctx-λ κ)))
             (if (inner-scope-declaration? decl λ)
                 #f
                 (let ((A (hash-ref call-states κ)))
                   (set-member? A a))))
           (let ((A (hash-ref call-states κ)))
             (set-member? A a))))
      ((rp a _ _)
       (let ((A (hash-ref call-states κ)))
         (set-member? A a))))))

(define (sfa-observable-effect? call-states parent fresh?)
  (lambda (eff κ s dyn)
    (match eff
      ((wv a x)
       (if dyn
           (let ((decl (get-declaration («id»-x x) x parent))
                 (λ (ctx-λ κ)))
             (if (inner-scope-declaration? decl λ)
                 #f
                 (let ((A (hash-ref call-states κ)))
                   (set-member? A a))))
           (let ((A (hash-ref call-states κ)))
             (set-member? A a))))
      ((wp a _ x)
       (if dyn
           (if (fresh? x s κ)
               #f
               (let ((A (hash-ref call-states κ)))
                 (set-member? A a)))
           (let ((A (hash-ref call-states κ)))
             (set-member? A a))))
      ((rv a x)
       (if dyn
           (let ((decl (get-declaration («id»-x x) x parent))
                 (λ (ctx-λ κ)))
             (if (inner-scope-declaration? decl λ)
                 #f
                 (let ((A (hash-ref call-states κ)))
                   (set-member? A a))))
           (let ((A (hash-ref call-states κ)))
             (set-member? A a))))
      ((rp a _ x)
       (if dyn
           (if (fresh? x s κ)
               #f
               (let ((A (hash-ref call-states κ)))
                 (set-member? A a)))
           (let ((A (hash-ref call-states κ)))
             (set-member? A a)))))))

(define (a-purity-analysis sys)
  (let* ((call-states (call-state-analysis sys))
         (observable? (a-observable-effect? call-states))
         (escapes? (lambda _ #t)))
    (traverse-graph (system-graph sys) (system-initial sys) (system-Ξ sys) observable? escapes?)))
    
(define (sa-purity-analysis sys)
  (let* ((call-states (call-state-analysis sys))
         (initial (system-initial sys))
         (ast (ev-e initial))
         (parent (make-parent ast))
         (lattice (system-lattice sys))
         (⊥ (lattice-⊥ lattice))
         (⊔ (lattice-⊔ lattice))
         (escapes? (lambda _ #t))
         (observable? (sa-observable-effect? call-states parent)))
    (traverse-graph (system-graph sys) (system-initial sys) (system-Ξ sys) observable? escapes?)))

(define (sfa-purity-analysis sys)
  (let* ((call-states (call-state-analysis sys))
         (initial (system-initial sys))
         (ast (ev-e initial))
         (parent (make-parent ast))
         (lattice (system-lattice sys))
         (⊥ (lattice-⊥ lattice))
         (⊔ (lattice-⊔ lattice))
         (escapes? (lambda _ #t))
         (F (fresh-analysis sys ⊥ ⊔ escapes?))
         (fresh? (lambda (x s κ)
                   (let* ((Fs (hash-ref F s (hash)))
                          (Fκ (hash-ref Fs κ (hash))))
                     (fresh? x Fκ parent ⊥))))
         (observable? (sfa-observable-effect? call-states parent fresh?)))
    (traverse-graph (system-graph sys) (system-initial sys) (system-Ξ sys) observable? escapes?)))

(define (msfa-purity-analysis sys)
  (let* ((call-states (call-state-analysis sys))
         (initial (system-initial sys))
         (ast (ev-e initial))
         (parent (make-parent ast))
         (lattice (system-lattice sys))
         (⊥ (lattice-⊥ lattice))
         (⊔ (lattice-⊔ lattice))
         (M (escape-analysis sys))
         (escapes? (lambda (λ) (set-member? M λ)))
         (F (fresh-analysis sys ⊥ ⊔ escapes?))
         (fresh? (lambda (x s κ)
                   (let* ((Fs (hash-ref F s (hash)))
                          (Fκ (hash-ref Fs κ (hash))))
                     (fresh? x Fκ parent ⊥))))
         (observable? (sfa-observable-effect? call-states parent fresh?)))
    (traverse-graph (system-graph sys) (system-initial sys) (system-Ξ sys) observable? escapes?)))

(define PURE "PURE")
(define OBSERVER "OBS")
(define PROCEDURE "PROC")

(define (extend-to-applied F Ξ)
  (for/hash ((κ (hash-keys (vector-ref Ξ (sub1 (vector-length Ξ))))))
    (let ((λ (ctx-λ κ)))
      (values λ (hash-ref F λ (set))))))

(define (F->C F)
  (for/hash (((λ f) F))
    (cond
      ((set-empty? f) (values λ PURE))
      ((set-member? f GENERATES) (values λ PROCEDURE))
      (else (values λ OBSERVES)))))

(define (print-purity-info C)
  (for (((λ c) C))
    (printf "~a -> ~a\n" (~a λ #:max-width 30) c)))

(define (count-classes C)
  (for/fold ((summary (hash))) (((λ c) C))
    (when (PRINT-PER-LAMBDA)
      (printf "~a -> ~a\n" (~a λ #:max-width 30) c))
    (hash-set summary c (add1 (hash-ref summary c 0)))))

(define (a-purity-benchmark sys)
  (purity-benchmark sys a-purity-analysis))

(define (sa-purity-benchmark sys)
  (purity-benchmark sys sa-purity-analysis))

(define (sfa-purity-benchmark sys)
  (purity-benchmark sys sfa-purity-analysis))

(define (msfa-purity-benchmark sys)
  (purity-benchmark sys msfa-purity-analysis))

(define FLOW-TIME "flow-time")
(define STATE-COUNT "state-count")
(define FLOW-EXIT "flow-exit")
(define FLOW-MSG "flow-msg")
(define NUM-LAMBDAS "num-lambdas")
(define NUM-CALLED "num-called")

(define (purity-benchmark sys analysis)
  (define (nodes ast) (for/fold ((cs (list ast))) ((c (children ast))) (append cs (nodes c))))
  (define (lambdas ast) (filter «lam»? (nodes ast)))  
  (with-handlers ((exn:fail? (lambda (exc) (if (THROW) (raise exc) (hash 'exit 'error 'msg exc)))))
    (let* ((flow-exit (system-exit sys))
           (summary (make-hash)))
      (hash-set! summary FLOW-TIME (system-duration sys))
      (hash-set! summary STATE-COUNT (vector-length (system-states sys)))
      (hash-set! summary FLOW-EXIT flow-exit)
      (hash-set! summary FLOW-MSG (if (eq? flow-exit 'ok) (answer-value sys) (system-msg sys)))
      (when (eq? flow-exit 'ok)
        (let* ((initial (system-initial sys))
               (ast (ev-e initial))
               (Ξ (system-Ξ sys))
               (F (extend-to-applied (analysis sys) Ξ))
               (C (F->C F))
               (count-summary (count-classes C)))
          (for (((k v) count-summary))
            (hash-set! summary k v))
          (hash-set! summary NUM-LAMBDAS (length (lambdas ast)))
          (hash-set! summary NUM-CALLED (set-count (list->set (hash-keys F))))))
      summary)))

(define (print-purity-summary summary)
  (let ((flow-time (hash-ref summary FLOW-TIME "?"))
        (state-count (hash-ref summary STATE-COUNT "?"))
        (exit (hash-ref summary FLOW-EXIT "?"))
        (num-lambdas (hash-ref summary NUM-LAMBDAS "?"))
        (num-called (hash-ref summary NUM-CALLED "?"))
        (num-pure (hash-ref summary PURE 0))
        (num-obs (hash-ref summary OBSERVER 0))
        (num-proc (hash-ref summary PROCEDURE 0))
        (msg (hash-ref summary FLOW-MSG "")))
    (printf "#~a flow-time ~a lams ~a called ~a pure ~a obs ~a proc ~a | ~a\n"
            (~a (if (eq? exit 'ok) state-count (format ">~a" state-count)) #:min-width 7)
            (~a flow-time #:min-width 7)
            (~a num-lambdas #:min-width 3)
            (~a num-called #:min-width 3)
            (~a num-pure #:min-width 2)
            (~a num-obs #:min-width 2)
            (~a num-proc #:min-width 2)
            (~a msg #:max-width 72))))
  

(define THROW (make-parameter #t))
(define PRINT-PER-LAMBDA (make-parameter #f))

(define purity-result #f)

(define (purity-test . ens)
  (when (null? ens)
    (set! ens '(fib fib-mut blur eta mj09 gcipd kcfa2 kcfa3 rotate loop2 sat collatz rsa primtest factor
                    purity1 purity2 purity3 purity4 purity5 purity6 purity7 purity8 purity9 purity10 purity11 purity12 purity13
                    purity14 purity15 purity16 purity17 purity18
                    fresh1 fresh2
                    treenode1 treeadd treeadd2 treeadd3 purity19 grid)))
  (define configs (list (cons 'a a-purity-benchmark)
                        (cons 'sa sa-purity-benchmark)
                        (cons 'sfa sfa-purity-benchmark)
                        (cons 'msfa msfa-purity-benchmark)
                        ))
  (define machs (list (cons 'conc conc-mach) (cons 'type type-mach-0)))
  (set! purity-result
    (for/list ((en ens))
      (newline)
      (let* ((e (eval en)))
        (cons en
              (for/list ((machc machs))
                (let* ((mach-name (car machc))
                       (mach (cdr machc))
                       (sys (mach e)))
                  (cons mach-name
                  (for/list ((config configs))
                    (printf "~a ~a ~a" (~a en #:min-width 14) (~a mach-name #:min-width 4) (~a (car config) #:min-width 5))
                    (let ((result ((cdr config) sys)))
                      (print-purity-summary result)
                (cons (car config) result))))))))))
  (printf "Results in purity-result\n"))

(define (server-purity-test)
  (parameterize ((CESK-TIMELIMIT 60) (THROW #f))
    (let ((results (apply purity-test '(fib fib-mut
                                        treenode1
                                        nqueens dderiv destruct mceval
                                     ; regex boyer 
                                     )))) 
      (printf "Done.\n")
      results)))

#|
(define t2 '(letrec ((f (lambda (b) (if b (let ((x (let ((y (cons 1 2))) y))) (let ((u (set-car! x 3))) (f #f))) 'done)))) (f #t)))
(define sys2 (conc-mach t2))
(generate-dot (system-graph sys2) "t2")
(let* ((lattice (system-lattice sys2))
       (⊥ (lattice-⊥ lattice))
       (⊔ (lattice-⊔ lattice))
       (escapes? (lambda _ #t))
       (F (fresh-analysis sys2 ⊥ ⊔ escapes?)))
       (print-fresh-info F))
(parameterize ((PRINT-PER-LAMBDA #t))
(print-purity-info (sfa-purity-analysis sys2)))

(define t1 '(letrec ((make-grid (lambda (start dims)
                                  (let ((v (make-vector dims start)))
                                    (let ((_43 (zero? dims)))
                                      (let ((_44 (not _43)))
                                        (let ((_54 (if _44
                                                       (letrec ((loop (lambda (i)
                                                                        (let ((_45 dims))
                                                                          (let ((_46 (>= i _45)))
                                                                            (if _46
                                                                                #t
                                                                                (let ((_47 (- dims 1)))
                                                                                  (let ((_50 (make-grid start _47)))
                                                                                    (let ((_51 (vector-set! v i _50)))
                                                                                      (let ((_53 (+ i 1)))
                                                                                        (loop _53)))))))))))
                                                         (loop 0))
                                                       #t)))
                                          v)))))))
              (make-grid 0 2)))

(define sys1 (type-mach-0 t1))
(generate-dot (system-graph sys1) "t1")
(print-fresh-info (fresh-analysis sys1 (set) set-union))
(print-variable-info (variable-analysis sys1))
(print-purity-info (sfa-purity-analysis sys1))

(define t3 '(letrec ((f (lambda (h) (let ((z (cons 1 2))) (if h (h) (f (lambda () (set-car! z 3)))))))) (f #f)))
(define sys3 (conc-mach t3))
(generate-dot (system-graph sys3) "t3")
(parameterize ((PRINT-PER-LAMBDA #t))
  (print-purity-info (a-purity-analysis sys3))
  (newline)
  (print-purity-info (sa-purity-analysis sys3))
  (newline)
  (print-purity-info (sfa-purity-analysis sys3))
  (newline)
  (print-fresh-info (fresh-analysis sys3 (set) set-union))
  )

;; Lower-bound for printing time (if smaller, prints \epsilon), in seconds
(define TIMECUTOFF (make-parameter 1))
(define TIMEFORMAT (make-parameter
                    ;; Round to seconds by default: 1
                    (lambda (time) (format "~a''" (inexact->exact (round time))))
                    ;; Other possibility: 1.234''
                    ;; (lambda (n) (~a time "''"))
                    ))
(define (display-size-tex result)
  (define (to-states benchmark)
    (~a (if (eq? (benchmark-exit benchmark) 'user) "$>$" "") (benchmark-state-count benchmark)))
  
  (printf "\\begin{tabular}{lllll} Program & Variance & Base & Summarizing & Self-adjusting \\\\ \\hline \n")
  (for/list ((res result))
    (match res
      ((list res-0 res-0-summ res-0-sa res-1 res-1-summ res-1-sa)
       ;; 0-CFA
       (printf "\\code{~a}      & 0CFA         & ~a   & ~a     & ~a          \\\\"
               (~a "benchmark-name res-0") 
               (~a (to-states res-0))      
               (~a (to-states res-0-summ))
               (~a (to-states res-0-sa))
               )
       ;; 1-CFA
       (printf "                & 1CFA         & ~a   & ~a    & ~a          \\\\[6pt]\n"
               (~a (to-states res-1))
               (~a (to-states res-1-summ))
               (~a (to-states res-1-sa)) 
               ))))
  (printf "\\end{tabular}\n"))

(define (display-time-tex result)
  (define (to-time benchmark)
    (if (eq? (benchmark-exit benchmark) 'user)
        "$\\infty$"
        (let ((duration (benchmark-duration benchmark)))
          (if (< duration 1000)
              "$\\epsilon$" 
              (format "~a''" (inexact->exact (round (/ duration 1000))))))))
  
  (printf "\\begin{tabular}{lllll} Program & Variance & Base & Summarizing & Self-adjusting \\\\ \\hline \n")
  (for/list ((res result))
    (match res
      ((list res-0 res-0-summ res-0-sa res-1 res-1-summ res-1-sa)
       ;; 0-CFA
       (printf "\\code{~a}      & 0CFA         & ~a   & ~a      & ~a          \\\\"
               (~a "benchmark-name res-0") 
               (~a (to-time res-0))      
               (~a (to-time res-0-summ))
               (~a (to-time res-0-sa)))
       ;; 1-CFA
       (printf "                & 1CFA         & ~a   & ~a      & ~a          \\\\[6pt]\n"
               (~a (to-time res-1))
               (~a (to-time res-1-summ))
               (~a (to-time res-1-sa))))))
  (printf "\\end{tabular}\n"))
|#