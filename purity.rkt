#lang racket

(require "general.rkt")
(require "ast.rkt")
(require "lattice.rkt")
(require "cesk.rkt")
(require "test.rkt")

(provide (all-defined-out))

;;

(define (inner-scope-declaration? decl e)
  (or (eq? decl e)
      (for/or ((e* (children e)))
        (inner-scope-declaration? decl e*))))

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

(struct escape-result (lams time) #:transparent)
(define (escape-analysis sys)
  (let* ((graph (system-graph sys))
         (initial (system-initial sys))
         (ast (ev-e initial))
         (α (lattice-α (system-lattice sys)))
         (γ (lattice-γ (system-lattice sys)))
         (state-σ (system-state-σ sys)))

    (define (touchesd d)
      (if (set? d)
          (for/fold ((as (set)) (lams (set))) ((v (in-set d)))
            (let-values (((A L) (touchesd v)))
              (values (set-union as A) (set-union lams L))))
          (match d
            ((clo lam ρ) (values (env-addresses ρ) (set lam)))
            ((letk _ _ ρ) (values (env-addresses ρ) (set)))
            ((letreck _ _ ρ) (values (env-addresses ρ) (set)))
            ((addr a) (values (set a) (set)))
            ((cons x y) (touchesd (set x y)))
            (_ (values (set) (set))))))

    (define (reachabled A L σ)
      (let loop ((A A) (L L) (R (set)))
        (if (set-empty? A)
            L
            (let ((a (set-first A)))
              (if (set-member? R a)
                  (loop (set-rest A) L R)
                  (let ((v (γ (store-lookup σ a))))
                    (let-values (((ΔA ΔL) (touchesd v)))
                      (loop (set-union (set-rest A) ΔA) (set-union L ΔL) (set-add R a)))))))))

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
        (let-values (((A L) (touchesd d)))
          (set-union M L))))

    (define (handle-state s M)
        (match s
          ((ev («app» _ _ aes) ρ σi _ _)
           (let ((σ (state-σ σi)))
             (for/fold ((M M)) ((ae (in-list aes)))
               (set-union M (check-values ae ρ σ M)))))
          ((ev («set!» _ _ ae) ρ σi _ _)
           (let ((σ (state-σ σi)))
             (check-values ae ρ σ M)))
          ((ev («cons» _ ae1 ae2) ρ σi _ _)
           (let ((σ (state-σ σi)))
             (set-union (check-values ae1 ρ σ M) (check-values ae2 ρ σ M))))
          ((ev («set-car!» _ _ ae) ρ σi _ _)
           (let ((σ (state-σ σi)))
             (check-values ae ρ σ M)))
          ((ev («set-cdr!» _ _ ae) ρ σi _ _)
           (let ((σ (state-σ σi)))
             (check-values ae ρ σ M)))
          ((ev («vector-set!» _ _ _ ae) ρ σi _ _)
           (let ((σ (state-σ σi)))
             (check-values ae ρ σ M)))
          ((ev (? ae? ae) ρ σi '() _)
           (let ((σ (state-σ σi)))
             (check-values ae ρ σ M)))
          (_ M)))

    (define (traverse-graph graph)
      (for/fold ((M (set))) (((s t) (in-hash graph)))
        (let ((M* (handle-state s M)))
          ;(printf "state ~a contributes ~a\n" (state-repr s) (set-map (set-subtract M* M) «lam»-l))
          M*)))


    (define start (current-milliseconds))
    (define M (traverse-graph graph))
    (define time (- (current-milliseconds) start))
    ;(for ((lam M)) (printf "~a ~a\n" («lam»-l lam) (~a lam #:max-width 40)))
    (escape-result M time)))


(struct freshness-result (fresh? time state->Fs))
(define (freshness-analysis sys escapes?)
  (define lattice (system-lattice sys))
  (define ⊥ type-⊥)
  (define ⊔ type-⊔)
  (define α type-α)
  ;(define γ (lattice-γ lattice))
  (define UNFRESH (α "unfresh"))

  (let* ((graph (system-graph sys))
         (Ξ (system-Ξ sys))
         (initial (system-initial sys))
         (ast (ev-e initial))
         (parent (make-parent ast)))

    (define (freshness ae Fκ)
      (match ae
        ((«id» _ x)
         (let* ((decl (get-declaration x ae parent)))
                (hash-ref Fκ decl UNFRESH)))
        (_ ⊥)))

    (define (handle-binding ψ ι κ Ξ Fs)
      (let ((ικGs (stack-pop ι κ Ξ (set))))
        (for/fold ((Fs Fs)) ((ικG ικGs))
          (let* ((ι* (car ικG))
                 (κ* (cadr ικG))
                 (Fκ (hash-ref Fs κ* (hash)))
                 (Fκ* (match ι*
                        ((cons (letk x e ρ*) ι*)
                         (let ((declx x))
                           ;(printf "~a ~a -> ~a ~a ~a\n" "?" (ctx->ctxi κ) (ctx->ctxi κ*) "?" declx)
                           (hash-set Fκ declx (⊔ (hash-ref Fκ x ⊥) ψ))))
                        ((cons (letreck x e ρ*) ι*)
                         (let ((declx x))
                           (hash-set Fκ declx (⊔ (hash-ref Fκ x ⊥) ψ))))
                        ((cons (haltk) _)
                         Fκ)
                        )))
            (hash-set Fs κ* Fκ*)))))

    (define (handle-state s Fs)
      ;(printf "handling ~a\n" (state->statei s))
      (match s
        ((ev (? ae? ae) _ _ ι κ)
         (let* ((Fκ (hash-ref Fs κ (hash)))
                (ψ (freshness ae Fκ)))
           (handle-binding ψ ι κ Ξ Fs)))
        ((ev («quo» _ e) _ _ ι κ)
         (let* ((Fκ (hash-ref Fs κ (hash)))
                (ψ (if (pair? e) UNFRESH ⊥)))
           (handle-binding ψ ι κ Ξ Fs)))
        ((ev («set!» _ x ae) ρ _ ι κ)
         (let ((declx (get-declaration («id»-x x) x parent)))

           (define (walk-stack-set S W Fs)
             (if (set-empty? W)
                 Fs
                 (let ((κstat (set-first W)))
                   (if (set-member? S κstat)
                       (walk-stack-set S (set-rest W) Fs)
                       (let ((κ (car κstat)))
                         (if κ
                             (let* ((stat (cdr κstat))
                                    (Fκ (hash-ref Fs κ (hash)))
                                    (ψ (if stat
                                           (freshness ae Fκ)
                                           UNFRESH))
                                    (Fκ* (hash-set Fκ declx (⊔ (hash-ref Fκ declx ⊥) ψ)))
                                    (Fs* (hash-set Fs κ Fκ*))
                                    (λ (ctx-λ κ))
                                    (ικs (stack-lookup Ξ κ))
                                    (stat* (and stat (not (escapes? λ))))
                                    (W* (set-union (set-rest W) (for/set ((ικ ικs)) (cons (cdr ικ) stat*)))))
                               (walk-stack-set (set-add S κstat) W* Fs*))
                             (walk-stack-set (set-add S κstat) (set-rest W) Fs)))))))

           (let ((Fs* (walk-stack-set (set) (set (cons κ #t)) Fs)))
             (handle-binding ⊥ ι κ Ξ Fs*))))
        ((ev («cons» _ _ _) _ _ ι κ)
         (let* ((Fκ (hash-ref Fs κ (hash)))
                (ψ ⊥))
           (handle-binding ψ ι κ Ξ Fs)))
        ((ev («make-vector» _ _ _) _ _ ι κ)
         (let* ((Fκ (hash-ref Fs κ (hash)))
                (ψ ⊥))
           (handle-binding ψ ι κ Ξ Fs)))
        ((ev («car» _ _) _ _ ι κ)
         (let* ((Fκ (hash-ref Fs κ (hash)))
                (ψ UNFRESH))
           (handle-binding ψ ι κ Ξ Fs)))
        ((ev («cdr» _ _) _ _ ι κ)
         (let* ((Fκ (hash-ref Fs κ (hash)))
                (ψ UNFRESH))
           (handle-binding ψ ι κ Ξ Fs)))
        ((ev («vector-ref» _ _ _) _ _ ι κ)
         (let* ((Fκ (hash-ref Fs κ (hash)))
                (ψ UNFRESH))
           (handle-binding ψ ι κ Ξ Fs)))
        ((ev («set-car!» _ _ _) _ _ ι κ)
         (let* ((Fκ (hash-ref Fs κ (hash)))
                (ψ ⊥))
           (handle-binding ψ ι κ Ξ Fs)))
        ((ev («set-cdr!» _ _ _) _ _ ι κ)
         (let* ((Fκ (hash-ref Fs κ (hash)))
                (ψ ⊥))
           (handle-binding ψ ι κ Ξ Fs)))
        ((ev («vector-set!» _ _ _ _) _ _ ι κ)
         (let* ((Fκ (hash-ref Fs κ (hash)))
                (ψ ⊥))
           (handle-binding ψ ι κ Ξ Fs)))
        ((ev («let» _ x (? ae? ae) e1) _ _ ι κ) ; only on ae, and only for this impl (because of ae fastpath in CESK)
         (let* ((declx x)
                (Fκ (hash-ref Fs κ (hash)))
                (ψ (freshness ae Fκ))
                (Fκ* (hash-set Fκ declx (⊔ (hash-ref Fκ declx ⊥) ψ)))) ;hash-ref with ⊥, cause introducing! "alloc"
           (hash-set Fs κ Fκ*)))
        ((ev («let» _ _ _ _) _ _ _ _) ; only on ae, and only for this impl (because of ae fastpath in CESK)
         Fs)
        ((ev («letrec» _ x (? ae? ae) e1) _ _ ι κ) ; only on ae, and only for this impl (because of ae fastpath in CESK)
         (let* ((declx x)
                (Fκ (hash-ref Fs κ (hash)))
                (ψ (freshness ae Fκ))
                (Fκ* (hash-set Fκ declx (⊔ (hash-ref Fκ declx ⊥) ψ)))) ;hash-ref with ⊥, cause introducing!
           (hash-set Fs κ Fκ*)))
        ((ev («letrec» _ _ _ _) _ _ _ _) ; only on ae, and only for this impl (because of ae fastpath in CESK)
         Fs)
        ((ev («app» _ _ _) _ _ ι κ)
         (for/fold ((Fs Fs)) ((t (hash-ref graph s (set))))
           (let ((s* (transition-s t)))
             (match s*
               ((ev e ρ* _ _ κ*)
                (let ((Fκ* (for/fold ((Fκ (hash-ref Fs κ* (hash)))) ((name (hash-keys ρ*)))
                             (let ((decl (get-declaration name e parent)))
                               ;(printf "~a ~a -> ~a ~a ~a\n" (state->statei s) (ctx->ctxi κ) (ctx->ctxi κ*) name decl)
                               (hash-set Fκ decl (⊔ (hash-ref Fκ decl ⊥) UNFRESH))))))
                  (hash-set Fs κ* Fκ*)))
               ((ko _ _ _ κ)
                (handle-binding ⊥ ι κ Ξ Fs))))))
        ((ev («if» _ _ _ _) _ _ _ _)
         Fs)
        ((ko _ _ _ _)
         Fs)
        ))

  (define (traverse-graph S W Fs F)
    (if (set-empty? W)
        F
        (let ((s (set-first W)))
          (if (set-member? S s)
              (traverse-graph S (set-rest W) Fs F)
                (let* ((Fs* (handle-state s Fs))
                       (F* (hash-set F s Fs*)))
                  (let* ((W* (set-union (set-rest W) (for/set ((t (hash-ref graph s (set))))
                                                              (transition-s t))))
                         (unchanged (equal? Fs Fs*))
                         (S* (if unchanged (set-add S s) (set))))
                    (traverse-graph S* W* Fs* F*)))))))

    (define start (current-milliseconds))
    (define state->Fs (traverse-graph (set) (set initial) (hash) (hash)))
    (define time (- (current-milliseconds) start))

      (define (fresh? ae state κ)
        (match ae
          ((«id» _ x)
           (let* ((Fs (hash-ref state->Fs state))
                  (Fκ (hash-ref Fs κ))
                  (decl (get-declaration x ae parent))
                  (ψ (freshness ae Fκ)))
             (equal? ψ ⊥)))))
          ;(_ #t)))

    (define (print-fresh-info F)
      (for (((s Fs) F))
           (printf "~a ~a\n" (state->statei s) (state-repr s))
           (for (((κ Fκ) Fs))
                (printf "\t~a ~a\n" (ctx->ctxi κ) (~a (if κ (ctx-λ κ) #f) #:max-width 30))
                (for (((decl FU) Fκ))
                     (when (equal? FU ⊥)
                       (printf "\t\t~a -> ~a\n" decl FU))))
                (newline)))
    ;(print-fresh-info state->Fs)


    (freshness-result fresh? time state->Fs)))


(define REACHABILITY (make-parameter #t))
(struct call-store-result (ctx->addrs time) #:transparent)
(define (call-store-analysis sys)
  (define graph (system-graph sys))
  (define state-σ (system-state-σ sys))
  (define Ξ (system-Ξ sys))
  (define γ (lattice-γ (system-lattice sys)))
  (define start (current-milliseconds))
  (define reachability (REACHABILITY))
  (define call-stores (for/fold ((call-stores (hash))) (((s ts) (in-hash graph)))
                        (match s
                          ((ev (? «app»? e) ρ σi ι κ)
                           (for/fold ((call-stores call-stores)) ((t (in-set ts)))
                             (match t
                               ((transition (ev _ _ _ '() κ*) _)
                                (let* ((A-existing (hash-ref call-stores κ* (set)))
                                       (σ (state-σ σi))
                                       (A-updated (if reachability
                                                      (set-union A-existing (reachable (s-referenced s Ξ) σ γ))
                                                      (set-union A-existing (list->set (hash-keys σ)))
                                                      )
                                                  ))
                                  (hash-set call-stores κ* A-updated)))
                               (_ call-stores))))
                          (_ call-stores))))
  (define time (- (current-milliseconds) start))
  (call-store-result call-stores time))


(struct side-effect-result (state->ctx->side-effects time observable-count) #:transparent)
(define (side-effect-analysis sys observable? escapes?)

  (define graph (system-graph sys))
  (define initial (system-initial sys))
  (define Ξ (system-Ξ sys))
  (define parent (make-parent (ev-e initial)))

  (define observable-count 0)

  (define (traverse-stack eff s S W ctx->side-effects)
    (if (set-empty? W)
        ctx->side-effects
        (let ((κstat (set-first W)))
          (if (set-member? S κstat)
              (traverse-stack eff s S (set-rest W) ctx->side-effects)
              (let ((κ (car κstat)))
                (if κ
                    (let ((stat (cdr κstat)))
                      (if (observable? eff κ s stat)
                          (let* ((lam (ctx-λ κ))
                                 (ικs (stack-lookup Ξ κ))
                                 (stat* (and stat (not (escapes? lam))))
                                 (ctx->side-effects* (hash-set ctx->side-effects κ (set-add (hash-ref ctx->side-effects κ (set)) eff))))
                            (set! observable-count (add1 observable-count))
                            (traverse-stack eff s (set-add S κstat) (set-union (set-rest W) (for/set ((ικ ικs)) (cons (cdr ικ) stat*))) ctx->side-effects*))
                          (traverse-stack eff s (set-add S κstat) (set-rest W) ctx->side-effects)))
                    (traverse-stack eff s S (set-rest W) ctx->side-effects)))))))
  
  (define (traverse-graph S W state->ctx->side-effects)
    (if (set-empty? W)
        state->ctx->side-effects
        (let ((s (set-first W)))
          (if (set-member? S s)
              (traverse-graph S (set-rest W) state->ctx->side-effects)
              (let-values (((W* ctx->side-effects)
                            (for/fold ((W (set-rest W)) (ctx->side-effects (hash))) ((t (hash-ref graph s (set))))
                              (match t
                                ((transition s* E)
                                 (let ((ctx->side-effects* (for/fold ((ctx->side-effects ctx->side-effects)) ((eff E))
                                                             (traverse-stack eff s (set) (set (cons (state-κ s) #t)) ctx->side-effects))))
                                   (values (set-add W s*) ctx->side-effects*)))))))
                (traverse-graph (set-add S s) W* (hash-set state->ctx->side-effects s ctx->side-effects)))))))

  (define start (current-milliseconds))
  (define state->ctx->side-effects (traverse-graph (set) (set initial) (hash)))
  (define time (- (current-milliseconds) start))
  (side-effect-result state->ctx->side-effects time observable-count))

(define (a-observable-effect? call-stores)
  (lambda (eff κ s stat)
    (match eff
      ((wv a _)
       (let ((A (hash-ref call-stores κ)))
         (set-member? A a)))
      ((wp a _ _)
       (let ((A (hash-ref call-stores κ)))
         (set-member? A a)))
      ((rv a _)
       (let ((A (hash-ref call-stores κ)))
         (set-member? A a)))
      ((rp a _ _)
       (let ((A (hash-ref call-stores κ)))
         (set-member? A a))))))

(define (sa-observable-variable-effect? a x κ stat call-stores parent)
  (if (and stat
           (let ((decl (get-declaration («id»-x x) x parent))
                 (λ (ctx-λ κ)))
             (inner-scope-declaration? decl λ)))
      #f
      (let ((A (hash-ref call-stores κ)))
              (set-member? A a))))

(define (fa-observable-property-effect? a x s κ stat call-stores fresh?)
  (if (and stat
           (fresh? x s κ))
      #f
      (let ((A (hash-ref call-stores κ)))
        (set-member? A a))))

(define (sa-observable-effect? call-stores parent)
  (lambda (eff κ s stat)
    (match eff
      ((wv a x)
       (sa-observable-variable-effect? a x κ stat call-stores parent))
      ((wp a _ _)
       (let ((A (hash-ref call-stores κ)))
         (set-member? A a)))
      ((rv a x)
       (sa-observable-variable-effect? a x κ stat call-stores parent))
      ((rp a _ _)
       (let ((A (hash-ref call-stores κ)))
         (set-member? A a))))))

(define (sfa-observable-effect? call-stores parent fresh?)
  (lambda (eff κ s stat)
    (match eff
      ((wv a x)
       (sa-observable-variable-effect? a x κ stat call-stores parent))
      ((wp a _ x)
       (fa-observable-property-effect? a x s κ stat call-stores fresh?))
      ((rv a x)
       (sa-observable-variable-effect? a x κ stat call-stores parent))
      ((rp a _ x)
       (fa-observable-property-effect? a x s κ stat call-stores fresh?)))))

(define (fresh-var? parent)
  (lambda (x κ)
    (let ((decl (get-declaration («id»-x x) x parent))
          (λ (ctx-λ κ)))
      (inner-scope-declaration? decl λ))))

(define (fresh-addr? call-stores)
  (lambda (a κ)
    (let ((A (hash-ref call-stores κ)))
      (not (set-member? A a)))))

(define (observable? fresh-addr? fresh-var? fresh-obj?)
  (lambda (eff κ s stat)
    (match eff
      ((wv a x)
       (not (or (and stat (fresh-var? x κ))
                (fresh-addr? a κ))))
      ((wp a _ x)
       (not (or (and stat (fresh-obj? x s κ))
                (fresh-addr? a κ))))
      ((rv a x)
       (not (or (and stat (fresh-var? x κ))
                (fresh-addr? a κ))))
      ((rp a _ x)
       (not (or (and stat (fresh-obj? x s κ))
                (fresh-addr? a κ)))))))

(define (a-side-effect-analysis sys call-stores)
  (let* ((fresh-addr? (fresh-addr? call-stores))
         (observable? (observable? fresh-addr? (lambda _ #f) (lambda _ #f)))
         (escapes? (lambda _ #t)))
    (side-effect-analysis sys observable? escapes?)))

(define (sa-side-effect-analysis sys call-stores )
  (let* ((initial (system-initial sys))
         (ast (ev-e initial))
         (parent (make-parent ast))
         (fresh-addr? (fresh-addr? call-stores))
         (observable? (observable? fresh-addr? (fresh-var? parent) (lambda _ #f)))
         (escapes? (lambda _ #t)))
    (side-effect-analysis sys observable? escapes?)))

(define (sfa-side-effect-analysis sys call-stores fresh-obj?)
  (let* ((initial (system-initial sys))
         (ast (ev-e initial))
         (parent (make-parent ast))
         (fresh-addr? (fresh-addr? call-stores))
         (observable? (observable? fresh-addr? (fresh-var? parent) fresh-obj?))
         (escapes? (lambda _ #t)))
    (side-effect-analysis sys observable? escapes?)))

(define (msfa-side-effect-analysis sys call-stores fresh-obj? esc-lams)
  (let* ((initial (system-initial sys))
         (ast (ev-e initial))
         (parent (make-parent ast))
         (fresh-addr? (fresh-addr? call-stores))
         (observable? (observable? fresh-addr? (fresh-var? parent) fresh-obj?))
         (escapes? (lambda (lam) (set-member? esc-lams lam))))
    (side-effect-analysis sys observable? escapes?)))

(define GENERATES "GEN")
(define OBSERVES "OBS")
(struct purity-result (lam->summary time) #:transparent)
(define (purity-analysis sys state->ctx->side-effects)

  (define graph (system-graph sys))
  (define initial (system-initial sys))
  (define Ξ (system-Ξ sys))
  (define state-σ (system-state-σ sys))
  (define γ (lattice-γ (system-lattice sys)))
         
  (define parent (make-parent (ev-e initial)))

  (define lam->summary (hash))
  (define lam->summaryi 0)


  (define (add-effect! lam effect)
    ;(printf " OBS! ~a " («lam»-l lam))
    (define existing-effects (hash-ref lam->summary lam #f))
    (if existing-effects
        (unless (set-member? existing-effects effect)
          (set! lam->summaryi (add1 lam->summaryi))
          (set! lam->summary (hash-set lam->summary lam (set-add existing-effects effect))))
        (begin
          ;x(set! lam->summaryi (add1 lam->summaryi))
          (set! lam->summary (hash-set lam->summary lam (set effect))))))

  (define (add-read-dep res lam R)
    ;(printf " R ~a " («lam»-l lam))
    (hash-set R res (set-add (hash-ref R res (set)) lam)))

  (define (add-observer! res lam O)
    (when (set-member? (hash-ref O res (set)) lam)
      ;(printf "O lam ~a  res ~a\n" («lam»-l lam) res)
      (add-effect! lam OBSERVES)))

  (define (update-O-write res R O)
    (let ((λ-rs (hash-ref R res (set))))
      (for/fold ((O O)) ((λ-r λ-rs))
        ;(printf " O ~a " («lam»-l λ-r))
        (hash-set O res (set-add (hash-ref O res (set)) λ-r)))))

  (define (walk-stack-write eff res ctx->side-effects) ; -> void
    (for (((κ side-effects) (in-hash ctx->side-effects)))
         (when (and κ (set-member? side-effects eff))
           (let ((lam (ctx-λ κ)))
             (add-effect! lam GENERATES)))))

  (define (walk-stack-read eff res ctx->side-effects R O) ; -> R
    (for/fold ((R R)) (((κ side-effects) (in-hash ctx->side-effects)))
      (if (set-member? side-effects eff)
          (let ((lam (ctx-λ κ)))
            (add-observer! res lam O)
            (add-read-dep res lam R))
          R)))
                  
  (define (handle-read-effect eff res ctx->side-effects R O)
    (let ((R* (walk-stack-read eff res ctx->side-effects R O)))
      (values R* O)))

  (define (handle-write-effect eff res ctx->side-effects R O)
    (let ((O* (update-O-write res R O)))
      (walk-stack-write eff res ctx->side-effects)
      (values R O*)))

  (define (handle-effect eff ctx->side-effects R O)
    ;(printf "\ns ~a effect ~a " (state->statei s) eff)
    (match eff
      ((wv a x)
       (handle-write-effect eff a ctx->side-effects R O))
      ((wp a n x)
       (handle-write-effect eff (cons a n) ctx->side-effects R O))
      ((rv a x)
       (handle-read-effect eff a ctx->side-effects R O))
      ((rp a n x)
       (handle-read-effect eff (cons a n) ctx->side-effects R O))
      (_ (values R O))))

  (define (traverse-graph-precise)

    (define A-cache (hash))
    
    (define (dis R)
      (for/hash (((res lams) (in-hash R)))
           (values res (set-map lams (lambda (lam) («lam»-l lam))))))

               
;          (printf "\ns ~a\nR ~a\nO ~a\nafter\nR ~a\nO ~a\nseen\nR ~a\nO ~a\n" (state->statei s) (dis R) (dis O) (dis (car RO)) (dis (cdr RO))
 ;                 (if RO-S (dis (car RO-S)) #f) (if RO-S (dis (cdr RO-S)) #f))
    
    (define (traverse-graph S W)
      (unless (set-empty? W)
        (let* ((sRO (set-first W))
               (s (car sRO))
               (RO-S (hash-ref S s #f))
               ;(RO (gcRO (cadr sRO) (cddr sRO) s)))
               (RO (cons (cadr sRO) (cddr sRO))))
          (if (equal? RO-S RO)
              (traverse-graph S (set-rest W))
              (let ((R (if RO-S (hash-⊔ (car RO) (car RO-S) set-union (set)) (car RO)))
                    (O (if RO-S (hash-⊔ (cdr RO) (cdr RO-S) set-union (set)) (cdr RO))))
                (let-values (((W*) (for/fold ((W (set-rest W))) ((t (hash-ref graph s (set))))
                                     (match t
                                       ((transition s* E)
                                        (let-values (((R* O*) (for/fold ((R R) (O O)) ((eff E))
                                                                (handle-effect eff (hash-ref state->ctx->side-effects s) R O))))
                                          (values (set-add W (cons s* (cons R* O*))))))))))
                  (traverse-graph (hash-set S s RO) W*)))))))
    (traverse-graph (hash) (set (cons initial (cons (hash) (hash))))))
  
  
  (define (traverse-graph S W R O)
    (unless (set-empty? W)
      (let ((s (set-first W)))
        (if (set-member? S s)
            (traverse-graph S (set-rest W) R O)
            (let ((oldi lam->summaryi))
              ;(printf "~a ~a\n" (set-count S) (set-count W))
              (let-values (((W* R* O*) (for/fold ((W (set-rest W)) (R R) (O O)) ((t (hash-ref graph s (set))))
                                         (match t
                                           ((transition s* E)
                                            (let-values (((R* O*) (for/fold ((R R) (O O)) ((eff E))
                                                                    (handle-effect eff (hash-ref state->ctx->side-effects s) R O))))
                                              (values (set-add W s*) R* O*)))))))
                (let* ((unchanged (and (= lam->summaryi oldi) (equal? R R*) (equal? O O*)))
                       (S* (if unchanged (set-add S s) (set))))
                  (traverse-graph S* W* R* O*))))))))

  (define (extend-to-applied lam->summary)
    (for/hash ((κ (hash-keys Ξ)))
              (let ((lam (ctx-λ κ)))
                (values lam (hash-ref lam->summary lam (set))))))

  (define start (current-milliseconds))
  (traverse-graph-precise)
  ;(traverse-graph (set) (set initial) (hash) (hash)))
  (define time (- (current-milliseconds) start))
  (purity-result (extend-to-applied lam->summary) time))

(define PURE "PURE")
(define OBSERVER "OBS")
(define PROCEDURE "PROC")
(define IMPURE "IMPURE")
(define (gl-classifier summary)
  (cond ((set-empty? summary) PURE)
        ((set-member? summary GENERATES) PROCEDURE)
        ((set-member? summary OBSERVES) OBSERVER)
        (else (error "?"))))

(define (purity-classifier lam->summary classifier)
  (for/hash (((lam summary) lam->summary))
     (values lam (classifier summary))))

;(define (print-purity-info C)
;  (for (((λ c) C))
;    (printf "~a -> ~a\n" (~a λ #:max-width 30) c)))

(define (count-classes lam->class)
  (for/fold ((class->count (hash))) (((lam clss) lam->class))
    (when (PRINT-PER-LAMBDA)
      (printf "~a -> ~a\n" (~a lam #:max-width 30) clss))
    (hash-set class->count clss (add1 (hash-ref class->count clss 0)))))

(define (summary-pattern lam->summary sorted-lams)
  (map (lambda (lam) (hash-ref lam->summary lam #f)) sorted-lams))

(define (filter-expected-lams lam->x expected sorted-lams)

  (define (helper acc expected sorted-lams)
    (if (null? expected)
        (if (null? sorted-lams)
            acc
            (error "mismatch"))
        (if (car expected)
            (helper (hash-set acc (car sorted-lams) (hash-ref lam->x (car sorted-lams))) (cdr expected) (cdr sorted-lams))
            (helper acc (cdr expected) (cdr sorted-lams)))))

  (helper (hash) expected sorted-lams))


(define (summary-patterns-match? expected actual)
  (if (null? expected)
      (null? actual)
      (let ((s1 (car expected)))
        (and (or (not s1) (equal? s1 (car actual))) (summary-patterns-match? (cdr expected) (cdr actual))))))

(define (lambdas ast) (filter «lam»? (nodes ast)))

(define (fresh-profile sys fr)
  (define graph (system-graph sys))
  (define initial (system-initial sys))
  (define parent (make-parent (ev-e initial)))
  (define (handle e ref->freshness Fκ)
    (if («id»? e)
        (handle-ref e ref->freshness Fκ)
        ref->freshness))
  (define (handle-ref x ref->freshness Fκ)
    (let ((decl (get-declaration x x parent))
          (key  (string-append (~a x) (~a («id»-l x)))))
      (hash-set ref->freshness key (type-⊔ (hash-ref ref->freshness key type-⊥) (hash-ref Fκ decl type-⊥)))))
  (define ref->freshness
    (for/fold ((ref->freshness (hash))) (((s ts) graph))
      (define κ (state-κ s))
      (define Fκ (hash-ref (hash-ref (freshness-result-state->Fs fr) s) κ))
      (match s
        ((ev (? ae? ae) _ _ _ κ)
         (handle ae ref->freshness Fκ))
        ((ev («set!» _ x ae) ρ _ ι κ)
         (handle-ref x ref->freshness Fκ))
        ((ev («cons» _ e1 e2) _ _ ι κ)
         (handle e1 (handle e2 ref->freshness Fκ) Fκ))
        ((ev («make-vector» _ _ ae) _ _ ι κ)
         (handle ae ref->freshness Fκ))
        ((ev («car» _ x) _ _ ι κ)
         (handle-ref x ref->freshness Fκ))
        ((ev («cdr» _ x) _ _ ι κ)
         (handle-ref x ref->freshness Fκ))
        ((ev («vector-ref» _ x1 x2) _ _ ι κ)
         (handle x1 (handle x2 ref->freshness Fκ) Fκ))
        ((ev («set-car!» _ e1 e2) _ _ ι κ)
         (handle e1 (handle e2 ref->freshness Fκ) Fκ))
        ((ev («set-cdr!» _ e1 e2) _ _ ι κ)
         (handle e1 (handle e2 ref->freshness Fκ) Fκ))
        ((ev («vector-set!» _ e1 e2 e3) _ _ ι κ)
         (handle e1 (handle e2 (handle e3 ref->freshness Fκ) Fκ) Fκ))
        ((ev («let» _ x e0 e1) _ _ ι κ) ; only on ae, and only for this impl (because of ae fastpath in CESK)
         (handle e0 (handle e1 ref->freshness Fκ) Fκ))
        ((ev («letrec» _ x e0 e1) _ _ ι κ) ; only on ae, and only for this impl (because of ae fastpath in CESK)
         (handle e0 (handle e1 ref->freshness Fκ) Fκ))
        ((ev («app» _ e es) _ _ ι κ)
         (for/fold ((ref->freshness (handle e ref->freshness Fκ))) ((e es))
           (handle e ref->freshness Fκ)))
        ((ev («if» _ e0 e1 e2) _ _ _ _)
         (handle e0 (handle e1 (handle e2 ref->freshness Fκ) Fκ) Fκ))
        (_ ref->freshness)
        )))
  ref->freshness)

(define (fresh-fp conc-ref->freshness abst-ref->freshness)
  (for/fold ((xx 0) (yy 0)) (((ref conc-freshness) conc-ref->freshness))
    (let ((abst-freshness (hash-ref abst-ref->freshness ref)))
      (if (and (equal? conc-freshness type-⊥) (not (equal? abst-freshness type-⊥)))
          (values (add1 xx) (add1 yy))
          (if (and (not (equal? conc-freshness type-⊥)) (equal? abst-freshness type-⊥))
              (error "fresh-fp subs")
              (values xx (add1 yy)))))))

(define (purity-benchmark e mach expected)
  (newline)  
  (printf "eval... ")
  (define sys (mach e))
  (define flow-time (system-duration sys))
  (define exit (system-exit sys))
  (printf "~a ms ~a\n" flow-time exit)
  (when (not (eq? 'ok exit))
    (define msg (system-msg sys))
    (printf "~a\n" msg)
    (hash 'exit 'error 'msg msg))
  (define state-count (vector-length (system-states sys)))
  (define result-value (answer-value sys))
  (define graph (system-graph sys))
  (define edge-count 0)
  (define nodes-covered (set))
  (define (cover e)
    (match e
      ((«lam» _ x e0) (set-union (set e) (list->set x)))
      ((«let» _ x e0 e1) (set-union (set e x) (cover e0)))
      ((«letrec» _ x e0 e1) (set-union (set e x) (cover e0)))
      ((«if» _ ae e1 e2) (set-union (set e) (cover ae)))
      ((«car» _ x) (set e x))
      ((«cdr» _ x) (set e x))
      ((«set!» _ x ae) (set-union (set e x) (cover ae)))
      ((«set-car!» _ x ae) (set-union (set e x) (cover ae)))
      ((«set-cdr!» _ x ae) (set-union (set e x) (cover ae)))
      ((«cons» _ ae1 ae2) (set-union (set e) (cover ae1) (cover ae2)))
      ((«make-vector» _ ae1 ae2) (set-union (set e) (cover ae1) (cover ae2)))
      ((«vector-ref» _ x ae) (set-union (set e x) (cover ae)))
      ((«vector-set!» _ x ae1 ae2) (set-union (set e x) (cover ae1) (cover ae2)))
      ((«app» _ rator rands) (apply set-union (append (list (set e) (cover rator)) (map cover rands))))
      (_ (set e))))
  (for (((s ts) graph))
       (when (ev? s)
         (let ((e (ev-e s)))
           (set! nodes-covered (set-union nodes-covered (cover e)))))
       (for ((t ts))
            (match t
              ((transition s* E) (set! edge-count (+ edge-count (set-count ts)))))))
  (define covered-count (set-count nodes-covered))  
  (printf "state/edges ~a/~a value ~a\n" state-count edge-count (~a result-value #:max-width 80))
  (define initial (system-initial sys))
  (define ast (ev-e initial))
  (define Ξ (system-Ξ sys))
  (define lattice (system-lattice sys))
  (define ⊥ (lattice-⊥ lattice))
  (define ⊔ (lattice-⊔ lattice))
  (define sorted-lams (sort (lambdas ast) < #:key «lam»-l))
  (define lam-count (length sorted-lams))
  (define called-lams (list->set (map ctx-λ (hash-keys Ξ))))
  (define called-count (set-count called-lams))
  (define es (nodes ast))
  (define node-count (length es))
  ;(printf "not covered ~a\n" (set-subtract (list->set es) nodes-covered)) 
  (define set!-count (length (filter «set!»? es)))
  (define set-car!-count (length (filter «set-car!»? es)))
  (define set-cdr!-count (length (filter «set-cdr!»? es)))
  (define vector-set!-count (length (filter «vector-set!»? es)))
  (define cons-count (length (filter «cons»? es)))
  (define make-vector-count (length (filter «make-vector»? es)))

  (printf "escape analysis... ")
  (define er (escape-analysis sys))
  (define escape-time (escape-result-time er))
  (printf "~a ms\n" escape-time)
  (define esc-lams (escape-result-lams er))

  (printf "freshness analysis without esc... ")
  (define fr (freshness-analysis sys (lambda _ #t)))
  (define freshness-time (freshness-result-time fr))
  (printf "~a ms\n" freshness-time)
  (define fresh? (freshness-result-fresh? fr))

  (define fresh-ref-obj-count2d 0)
  (define unfresh-ref-obj-count2d 0)
  (define fresh-ref-obj-count2df 0)
  (define unfresh-ref-obj-count2df 0)
  (for (((s Fs) (freshness-result-state->Fs fr)))
       (for (((κ Fκ) Fs))
            (for (((x freshness) Fκ))
                 (if (equal? freshness type-⊥)
                   (set! fresh-ref-obj-count2d (add1 fresh-ref-obj-count2d))
                   (set! unfresh-ref-obj-count2d (add1 unfresh-ref-obj-count2d)))
                   (when (or (not κ) (set-member? called-lams (ctx-λ κ)))
                     (if (equal? freshness type-⊥)
                         (set! fresh-ref-obj-count2df (add1 fresh-ref-obj-count2df))
                         (set! unfresh-ref-obj-count2df (add1 unfresh-ref-obj-count2df)))
                       ))))

  (define freshness-profile (fresh-profile sys fr))

  (printf "call-store analysis... ")
  (define csr (call-store-analysis sys))
  (define call-store-time (call-store-result-time csr))
  (printf "~a ms\n" call-store-time)
  (define ctx->addrs (call-store-result-ctx->addrs csr))

  (define (handle-side-effect-result ser)
    (define side-effect-time (side-effect-result-time ser))
    (printf "~a ms\n" side-effect-time)
    (define state->ctx->side-effects (side-effect-result-state->ctx->side-effects ser))

    ; global, graph-based
    (define eff-count 0)
    (define eff-ctx-count 0) 
    (define eff-ctx-obs-count 0) 
    (define eff-fctx-count 0) ; filtered on ca
    (define eff-fctx-obs-count 0) ; filtered on called lams
    
    ; number of different side-effect (grouped in sets)
    (define eff-set (set))
    (define lam->effs (hash))
    (define lam->obs-effs (hash))
    
    (for (((s ts) graph))
         (let ((ctx->side-effects (hash-ref state->ctx->side-effects s)))
               
           (for ((t ts))
                (match t
                  ((transition s* E)
                   (set! eff-count (+ eff-count (set-count E)))
                   (set! eff-set (set-union eff-set E))
                   
                   (for ((eff E))
                        
                        (for ((τ (stack-contexts (state-κ s) Ξ)))
                             (let ((observable-E (hash-ref ctx->side-effects τ (set)))
                                   (lam (ctx-λ τ)))
                               (set! eff-ctx-count (add1 eff-ctx-count))
                               (set! lam->effs (hash-set lam->effs lam (set-add (hash-ref lam->effs lam (set)) eff)))
                               (when (set-member? observable-E eff)
                                 (set! lam->obs-effs (hash-set lam->obs-effs lam (set-add (hash-ref lam->obs-effs lam (set)) eff)))
                                 (set! eff-ctx-obs-count (add1 eff-ctx-obs-count)))
                               (when (set-member? called-lams lam)
                                 (set! eff-fctx-count (add1 eff-fctx-count))
                                 (when (set-member? observable-E eff)
                                   (set! eff-fctx-obs-count (add1 eff-fctx-obs-count))))))
                        )
                   )
                  )
                )))
    (define eff-set-count (set-count eff-set))
    (define lam-eff-set-count (for/sum (((lam effs) lam->effs)) (set-count effs)))
    (define lam-obs-eff-set-count (for/sum (((lam effs) lam->obs-effs)) (set-count effs)))

    (printf "purity analysis... ")
    (define pr (purity-analysis sys state->ctx->side-effects))
    (define purity-time (purity-result-time pr))
    (printf "~a ms\n" purity-time)
    (define lam->summary (purity-result-lam->summary pr))
    (define filtered-lam->summary (filter-expected-lams lam->summary expected sorted-lams))
    (define lam->effect-class (purity-classifier filtered-lam->summary gl-classifier))
    (define class-count (count-classes lam->effect-class))
    (define gen-count (for/sum ((summary (hash-values filtered-lam->summary))) (if (set-member? summary GENERATES) 1 0)))
    (define obs-count (for/sum ((summary (hash-values filtered-lam->summary))) (if (set-member? summary OBSERVES) 1 0)))
    (define correct (if expected
                        (let ((actual (summary-pattern filtered-lam->summary sorted-lams)))
                          (if (equal? expected actual)
                              "OK"
                              (begin
                                ;(printf "expected ~a\ngot ~a\n" expected actual)
                                "NOK")))
                        "?"))

    (define lam->effect-class-unf (purity-classifier lam->summary gl-classifier))
    (define class-count-unf (count-classes lam->effect-class-unf))

    ;(define observable-count (side-effect-result-observable-count ser))
    ; NEW
    (define observable-count (for/sum (((state ctx->side-effects) state->ctx->side-effects))
                                      (for/sum (((ctx side-effects) ctx->side-effects))
                                               (set-count side-effects))))
    ;

    
    (hash 'side-effect-time side-effect-time 'lam->effs lam->effs 'lam->obs-effs lam->obs-effs 'eff-set eff-set
          'eff-count eff-count 'eff-ctx-count eff-ctx-count 'eff-ctx-obs-count eff-ctx-obs-count 'eff-fctx-count eff-fctx-count 'eff-fctx-obs-count eff-fctx-obs-count
          'eff-set-count eff-set-count 'lam-eff-set-cont lam-eff-set-count 'lam-obs-eff-set-count lam-obs-eff-set-count
          'purity-time purity-time 'class-count class-count 'gen-count gen-count 'obs-count obs-count 'lam->summary filtered-lam->summary 'correct correct
          'lam->effect-class-unf lam->effect-class-unf 'class-count-unf class-count-unf
          'observable-count observable-count
          ))

  (printf "a-side-effect analysis... ")
  (define a-ser (a-side-effect-analysis sys ctx->addrs))
  (define a-results (handle-side-effect-result a-ser))

  (printf "sa-side-effect analysis... ")
  (define sa-ser (sa-side-effect-analysis sys ctx->addrs))
  (define sa-results (handle-side-effect-result sa-ser))

  (printf "sfa-side-effect analysis... ")
  (define sfa-ser (sfa-side-effect-analysis sys ctx->addrs fresh?))
  (define sfa-results (handle-side-effect-result sfa-ser))

  (printf "msfa-side-effect analysis... ")
  (define msfa-ser (msfa-side-effect-analysis sys ctx->addrs fresh? esc-lams))
  (define msfa-results (handle-side-effect-result msfa-ser))

  (hash 'node-count node-count 'covered-count covered-count 'set!-count set!-count 'set-car!-count set-car!-count 'set-cdr!-count set-cdr!-count 'vector-set!-count vector-set!-count 'cons-count cons-count 'make-vector-count make-vector-count
        'exit 'ok 'msg result-value 'flow-time flow-time 'state-count state-count 'edge-count edge-count 'lam-count lam-count 'called-count called-count 'called-lams called-lams
        'a a-results 'sa sa-results 'sfa sfa-results 'msfa msfa-results
        'call-store-time call-store-time
        'freshness-time freshness-time 'freshness-profile freshness-profile 
        'fresh-ref-obj-count2d fresh-ref-obj-count2d 'unfresh-ref-obj-count2d unfresh-ref-obj-count2d 
        'fresh-ref-obj-count2df fresh-ref-obj-count2df 'unfresh-ref-obj-count2df unfresh-ref-obj-count2df
        'escape-time escape-time 'esc-lams esc-lams
        ))

(define THROW (make-parameter #t))
(define PRINT-PER-LAMBDA (make-parameter #f))

(define test-result #f)

(define (se-subsumes? se1 se2)
  (for/and (((lam side-effects2) se2))
           (let ((side-effects1 (hash-ref se1 lam (set))))
             (subset? side-effects2 side-effects1))))

(define (real-lses-⊑ lses1 lses2 α ⊑)
  (for/and (((lam ses1) lses1))
           (let ((ses2 (hash-ref lses2 lam (set))))
             (real-ses-⊑ ses1 ses2 α ⊑))))

(define (eff-α eff α)
  (match eff
    ((wv _ x) (wv #f x))
    ((wp _ "car" x) (wp #f "car" x))
    ((wp _ "cdr" x) (wp #f "cdr" x))
    ((wp _ n x) (wp #f (α n) x))
    ((rv _ x) (rv #f x))
    ((rp _ "car" x) (rp #f "car" x))
    ((rp _ "cdr" x) (rp #f "cdr" x))
    ((rp _ n x) (rp #f (α n) x))))

(define (eff-⊑ eff1 eff2 ⊑)
  (match eff1
    ((wv _ x1)
     (match eff2
       ((wv _ x2) (equal? x1 x2))
       (_ #f)))
    ((wp _ "car" x1)
     (match eff2
       ((wp _ "car" x2) (equal? x1 x2))
       (_ #f)))
    ((wp _ "cdr" x1)
     (match eff2
       ((wp _ "cdr" x2) (equal? x1 x2))
       (_ #f)))
    ((wp _ n1 x1)
     (match eff2
       ((wp _ n2 x2)
        (and (equal? x1 x2) (⊑ n1 n2)))
       (_ #f)))
    ((rv _ x1)
     (match eff2
       ((rv _ x2) (equal? x1 x2))
       (_ #f)))
    ((rp _ "car" x1)
     (match eff2
       ((rp _ "car" x2) (equal? x1 x2))
       (_ #f)))
    ((rp _ "cdr" x1)
     (match eff2
       ((rp _ "cdr" x2) (equal? x1 x2))
       (_ #f)))
    ((rp _ n1 x1)
     (match eff2
       ((rp _ n2 x2)
        (and (equal? x1 x2) (⊑ n1 n2)))
       (_ #f)))))

(define (real-ses-⊑ ses1 ses2 α ⊑)

  (define (se-⊑ se1 se2)
    (match se1
      ((wv a x)
       (match se2
         ((wv _ x) #t)
         (_ #f)))
      ((wp a "car" x)
       (match se2
         ((wp _ "car" x) #t)
         (_ #f)))
      ((wp a "cdr" x)
       (match se2
         ((wp _ "cdr" x) #t)
         (_ #f)))
      ((wp a n1 x)
       (match se2
         ((wp _ n2 x)
          (and (not (string? n2)) (⊑ (α n1) n2)))
         (_ #f)))
      ((rv a x)
       (match se2
         ((rv _ x) #t)
         (_ #f)))
      ((rp a "car" x)
       (match se2
         ((rp _ "car" x) #t)
         (_ #f)))
      ((rp a "cdr" x)
       (match se2
         ((rp _ "cdr" x) #t)
         (_ #f)))
      ((rp a n1 x)
       (match se2
         ((rp _ n2 x) (and (not (string? n2)) (⊑ (α n1) n2)))
         (_ #f)))))


             (for/and ((se1 ses1))
                      (let ((ok (for/or ((se2 ses2))
                              (se-⊑ se1 se2))))
                        ;(unless ok
                          ;(set! DEB1 se1)(set! DEB2 ses2)
                          ;(printf "~a IN\n~a\n" se1 ses2))
                        ok
                        )))

;;;;

(define (count-lses-⊑ lses1 lses2 ⊑ α) ; conc abst
  (for/fold ((xx 0) (yy 0)) (((lam ses1) lses1)) ; xx number of eff in 2 that do not subsume eff in 1, yy number of eff in 2
    (let ((ses2 (hash-ref lses2 lam (set)))
          (ases1 (list->set (set-map ses1 (lambda (se) (eff-α se α))))))
      (let ((subs2 (for/fold ((subs2 (set))) ((ase1 ases1))
                     (for/fold ((subs2 subs2)) ((se2 ses2))
                       (if (eff-⊑ ase1 se2 ⊑)
                           (set-add subs2 se2)
                           subs2)))))
        (let ((ses2-count (set-count ses2)))
          (values (+ xx (- ses2-count (set-count subs2))) (+ yy ses2-count)))))))

;;;;;

(define (perform-purity-test tests)

  (set! test-result
  (for/list ((test tests))
       (newline)
       (define name (car test))
       (define e (cadr test))
       (define expected (cddr test))
       (printf "\n~a\n" name)

       (define conc-results (purity-benchmark e conc-mach expected))
       (define conc-a-eff-set (hash-ref (hash-ref conc-results 'a) 'eff-set))
       (define conc-a-lam->effs (hash-ref (hash-ref conc-results 'a) 'lam->effs))
       (define conc-a-lam->obs-effs (hash-ref (hash-ref conc-results 'a) 'lam->obs-effs))
       (define conc-a-lam->summary (hash-ref (hash-ref conc-results 'a) 'lam->summary))

       (define conc-sa-eff-set (hash-ref (hash-ref conc-results 'sa) 'eff-set))
       (define conc-sa-lam->effs (hash-ref (hash-ref conc-results 'sa) 'lam->effs))
       (define conc-sa-lam->obs-effs (hash-ref (hash-ref conc-results 'sa) 'lam->obs-effs))
       (define conc-sa-lam->summary (hash-ref (hash-ref conc-results 'sa) 'lam->summary))
       
       (define conc-sfa-eff-set (hash-ref (hash-ref conc-results 'sfa) 'eff-set))
       (define conc-sfa-lam->effs (hash-ref (hash-ref conc-results 'sfa) 'lam->effs))
       (define conc-sfa-lam->obs-effs (hash-ref (hash-ref conc-results 'sfa) 'lam->obs-effs))
       (define conc-sfa-lam->summary (hash-ref (hash-ref conc-results 'sfa) 'lam->summary))

       (define conc-msfa-eff-set (hash-ref (hash-ref conc-results 'msfa) 'eff-set))
       (define conc-msfa-lam->effs (hash-ref (hash-ref conc-results 'msfa) 'lam->effs))
       (define conc-msfa-lam->obs-effs (hash-ref (hash-ref conc-results 'msfa) 'lam->obs-effs))
       (define conc-msfa-lam->summary (hash-ref (hash-ref conc-results 'msfa) 'lam->summary))

       (define type-results (purity-benchmark e type-mach-0 expected))
       (define type-a-eff-set (hash-ref (hash-ref type-results 'a) 'eff-set))
       (define type-a-lam->effs (hash-ref (hash-ref type-results 'a) 'lam->effs))
       (define type-a-lam->obs-effs (hash-ref (hash-ref type-results 'a) 'lam->obs-effs))
       (define type-a-lam->summary (hash-ref (hash-ref type-results 'a) 'lam->summary))

       (define type-sa-eff-set (hash-ref (hash-ref type-results 'sa) 'eff-set))
       (define type-sa-lam->effs (hash-ref (hash-ref type-results 'sa) 'lam->effs))
       (define type-sa-lam->obs-effs (hash-ref (hash-ref type-results 'sa) 'lam->obs-effs))
       (define type-sa-lam->summary (hash-ref (hash-ref type-results 'sa) 'lam->summary))

       (define type-sfa-eff-set (hash-ref (hash-ref type-results 'sfa) 'eff-set))
       (define type-sfa-lam->effs (hash-ref (hash-ref type-results 'sfa) 'lam->effs))
       (define type-sfa-lam->obs-effs (hash-ref (hash-ref type-results 'sfa) 'lam->obs-effs))
       (define type-sfa-lam->summary (hash-ref (hash-ref type-results 'sfa) 'lam->summary))
       
       (define type-msfa-eff-set (hash-ref (hash-ref type-results 'msfa) 'eff-set))
       (define type-msfa-lam->effs (hash-ref (hash-ref type-results 'msfa) 'lam->effs))
       (define type-msfa-lam->obs-effs (hash-ref (hash-ref type-results 'msfa) 'lam->obs-effs))
       (define type-msfa-lam->summary (hash-ref (hash-ref type-results 'msfa) 'lam->summary))

       ; (CORRECTNESS) conc-a result must be correct
       (unless (eq? "OK" (hash-ref (hash-ref conc-results 'a) 'correct))
         (error "conc-a-results"))

       ; (SOUNDNESS) all conc results must be equal
       (unless (equal? conc-a-eff-set conc-sa-eff-set)
         (error "conc-sa-eff-set"))
       (unless (equal? conc-a-lam->effs conc-sa-lam->effs)
         (error "conc-sa-lam->effs"))
       (unless (equal? conc-a-lam->obs-effs conc-sa-lam->obs-effs)
         (error "conc-sa-lam->obs-effs"))
       (unless (equal? conc-a-lam->summary conc-sa-lam->summary)
         (error "conc-sa-lam->summary"))

       (unless (equal? conc-a-eff-set conc-sfa-eff-set)
         (error "conc-sfa-eff-set"))
       (unless (equal? conc-a-lam->effs conc-sfa-lam->effs)
         (error "conc-sfa-lam->effs"))
       (unless (equal? conc-a-lam->obs-effs conc-sfa-lam->obs-effs)
         (error "conc-sfa-lam->obs-effs"))
       (unless (equal? conc-a-lam->summary conc-sfa-lam->summary)
         (error "conc-sfa-lam->summary"))

       (unless (equal? conc-a-eff-set conc-msfa-eff-set)
         (error "conc-msfa-eff-set"))
       (unless (equal? conc-a-lam->effs conc-msfa-lam->effs)
         (error "conc-msfa-lam->effs"))
       (unless (equal? conc-a-lam->obs-effs conc-msfa-lam->obs-effs)
         (error "conc-msfa-lam->obs-effs"))
       (unless (equal? conc-a-lam->summary conc-msfa-lam->summary)
         (error "conc-msfa-lam->summary"))

       ; (SOUNDNESS) all type results must subsume conc results
       (define α type-α)
       (define ⊑ type-⊑)

       (unless (real-ses-⊑ conc-a-eff-set type-a-eff-set α ⊑)
         (error "type-a-eff-set"))
       (unless (real-lses-⊑ conc-a-lam->effs type-a-lam->effs α ⊑)
         (error "type-a-lam->effs"))
       (unless (real-lses-⊑ conc-a-lam->obs-effs type-a-lam->obs-effs α ⊑)
         (error "type-a-lam->obs-effs"))
       (unless (se-subsumes? type-a-lam->summary conc-a-lam->summary)
         (error "type-a-lam->summary"))

       (unless (real-ses-⊑ conc-a-eff-set type-sa-eff-set α ⊑)
         (error "type-sa-eff-set"))
       (unless (real-lses-⊑ conc-a-lam->effs type-sa-lam->effs α ⊑)
         (error "type-sa-lam->effs"))
       (unless (real-lses-⊑ conc-a-lam->obs-effs type-sa-lam->obs-effs α ⊑)
         (error "type-sa-lam->obs-effs"))
       (unless (se-subsumes? type-sa-lam->summary conc-a-lam->summary)
         (error "type-sa-lam->summary")) 

       (unless (real-ses-⊑ conc-a-eff-set type-sfa-eff-set α ⊑)
         (error "type-sfa-eff-set"))
       (unless (real-lses-⊑ conc-a-lam->effs type-sfa-lam->effs α ⊑)
         (error "type-sfa-lam->effs"))
       (unless (real-lses-⊑ conc-a-lam->obs-effs type-sfa-lam->obs-effs α ⊑)
         (error "type-sfa-lam->obs-effs"))
       (unless (se-subsumes? type-sfa-lam->summary conc-a-lam->summary)
         (error "type-sfa-lam->summary"))

       (unless (real-ses-⊑ conc-a-eff-set type-msfa-eff-set α ⊑)
         (error "type-msfa-eff-set"))
       (unless (real-lses-⊑ conc-a-lam->effs type-msfa-lam->effs α ⊑)
         (error "type-msfa-lam->effs"))
       (unless (real-lses-⊑ conc-a-lam->obs-effs type-msfa-lam->obs-effs α ⊑)
         (error "type-msfa-lam->obs-effs"))
       (unless (se-subsumes? type-msfa-lam->summary conc-a-lam->summary)
         (error "type-msfa-lam->summary"))

       ; (USEFULNESS) extra analyses must improve results (less-optimized subsumes more-optimized)
       (unless (se-subsumes? type-a-lam->summary type-sa-lam->summary)
         (error "type-a -> sa"))
       (unless (se-subsumes? type-sa-lam->summary type-sfa-lam->summary)
         (error "type-sa -> sfa"))
       (unless (se-subsumes? type-sfa-lam->summary type-msfa-lam->summary)
         (error "type-sfa -> msfa"))


       ; SOUNDNESS esc

       (define conc-esc-lams (hash-ref conc-results 'esc-lams))
       (define type-esc-lams (hash-ref type-results 'esc-lams))
       (unless (subset? conc-esc-lams type-esc-lams)
         (error "esc-lams"))

       ; SOUNDNESS fresh ; dnw purity-19
       ;(define conc-fr-profile (hash-ref conc-results 'freshness-profile))
       ;(define type-fr-profile (hash-ref type-results 'freshness-profile))
       ;(define (fresh-subsumes? fr1 fr2)
       ;  (for/and (((ref2 ψ2) fr2))
       ;    (let ((ψ1 (hash-ref fr1 ref2 (set))))
       ;      (type-⊑ ψ2 ψ1))))
       ;(unless (fresh-subsumes? type-fr-profile conc-fr-profile)
       ;  (error "type-fresh"))

       (list (substring (symbol->string name) 5) conc-results type-results)
       ))
  )


(define (print-purity-result result)

  (define correct-counts (make-hash))
  (define (add1-correct-count! mach config)
    (let ((existing (hash-ref correct-counts (cons mach config) 0)))
      (hash-set! correct-counts (cons mach config) (add1 existing))))
  (define benefits-from-freshness (mutable-set))
  (define benefits-from-escape (mutable-set)) ; w.r.t. freshness

  (define (print-config-result mach name result)
    (define class-count (hash-ref result 'class-count))
    (define correct (hash-ref result 'correct))
    (when (eq? "OK" correct)
      (add1-correct-count! mach name))
    (printf "~a ~a pure ~a obs ~a proc ~a | gen ~a obs ~a | se ~a purity ~a \n"
            (~a name #:min-width 4)
            (~a correct #:min-width 4)
            (~a (hash-ref class-count PURE 0) #:min-width 2)
            (~a (hash-ref class-count OBSERVER 0) #:min-width 2)
            (~a (hash-ref class-count PROCEDURE 0) #:min-width 2)
            (~a (hash-ref result 'gen-count) #:min-width 2)
            (~a (hash-ref result 'obs-count) #:min-width 2)
            (~time (hash-ref result 'side-effect-time))
            (~time (hash-ref result 'purity-time))
            ))

  (define (print-mach-result benchmark-name name result)
    (define exit (hash-ref result 'exit))
    (define msg (hash-ref result 'msg))
    (define state-count (hash-ref result 'state-count))
    (printf "~a states ~a lams ~a called ~a | flow ~a call ~a esc ~a fresh ~a fresh-esc ~a | ~a\n"
            name
            (~a (if (eq? exit 'ok) state-count (format ">~a" state-count)) #:min-width 7)
            (hash-ref result 'lam-count) (hash-ref result 'called-count)
            (~time (hash-ref result 'flow-time))
            (~time (hash-ref result 'call-store-time))
            (~time (hash-ref result 'escape-time))
            (~time (hash-ref result 'freshness-time))
            (~time (hash-ref result 'freshness-esc-time))
            (~a msg #:max-width 72))
    (define a-result (hash-ref result 'a))
    (define sa-result (hash-ref result 'sa))
    (define sfa-result (hash-ref result 'sfa))
    (define msfa-result (hash-ref result 'msfa))
    (print-config-result name "a" a-result)
    (print-config-result name "sa" sa-result)
    (print-config-result name "sfa" sfa-result)
    (print-config-result name "msfa" msfa-result)
    (when (or (< (hash-ref sfa-result 'gen-count) (hash-ref a-result 'gen-count))
              (< (hash-ref sfa-result 'obs-count) (hash-ref a-result 'obs-count)))
      (set-add! benefits-from-freshness benchmark-name))
    (when (or (< (hash-ref msfa-result 'gen-count) (hash-ref sfa-result 'gen-count))
              (< (hash-ref msfa-result 'obs-count) (hash-ref sfa-result 'obs-count)))
      (set-add! benefits-from-escape benchmark-name))
    )


  (for ((r result))
       (let ((benchmark-name (car r)))
         (printf "~a\n" benchmark-name)
         (print-mach-result benchmark-name "conc" (cadr r))
         (print-mach-result benchmark-name "type" (caddr r))))

  (printf "conc-a    ~a\n" (hash-ref correct-counts (cons "conc" "a") 0))
  (printf "conc-sa   ~a\n" (hash-ref correct-counts (cons "conc" "sa") 0))
  (printf "conc-sfa  ~a\n" (hash-ref correct-counts (cons "conc" "sfa") 0))
  (printf "conc-msfa ~a\n" (hash-ref correct-counts (cons "conc" "msfa") 0))
  (printf "type-a    ~a\n" (hash-ref correct-counts (cons "type" "a") 0))
  (printf "type-sa   ~a\n" (hash-ref correct-counts (cons "type" "sa") 0))
  (printf "type-sfa  ~a\n" (hash-ref correct-counts (cons "type" "sfa") 0))
  (printf "type-msfa ~a\n" (hash-ref correct-counts (cons "type" "msfa") 0))
  (printf "benefits from freshness: (~a) ~a\n" (set-count benefits-from-freshness) benefits-from-freshness)
  (printf "benefits from escape   : (~a) ~a\n" (set-count benefits-from-escape) benefits-from-escape)
  (set-intersect! benefits-from-freshness benefits-from-escape)
  (printf "benefits from both     : (~a) ~a\n" (set-count benefits-from-freshness) benefits-from-freshness)
  )

(define (~time ms)
  (~a
   (if (< ms 1000)
       "eps"
       (format "~a''" (inexact->exact (round (/ ms 1000)))))
   #:min-width 5))

(define (print-se-result result)

  (define (print-config-result mach name result)

    (define effect-count (hash-ref result 'effect-count))
    (define effect-ctx-count (hash-ref result 'effect-ctx-count))
    (define effect-ctx-observable-count (hash-ref result 'effect-ctx-observable-count))
    (printf "~a eff ~a eff-ctx ~a eff-ctx-obs ~a | se-time ~a\n"
            (~a name #:min-width 4)
            (~a (hash-ref result 'effect-count) #:min-width 2)
            (~a (hash-ref result 'effect-ctx-count) #:min-width 2)
            (~a (hash-ref result 'effect-ctx-observable-count) #:min-width 2)
            (~time (hash-ref result 'side-effect-time))
            ))

  (define (print-mach-result benchmark-name name result)
    (define exit (hash-ref result 'exit))
    (define msg (hash-ref result 'msg))
    (define state-count (hash-ref result 'state-count))
    (printf "~a states ~a lams ~a called ~a | flow ~a call ~a esc ~a fresh ~a fresh-esc ~a | ~a\n"
            name
            (~a (if (eq? exit 'ok) state-count (format ">~a" state-count)) #:min-width 7)
            (hash-ref result 'lam-count) (hash-ref result 'called-count)
            (~time (hash-ref result 'flow-time))
            (~time (hash-ref result 'call-store-time))
            (~time (hash-ref result 'escape-time))
            (~time (hash-ref result 'freshness-time))
            (~time (hash-ref result 'freshness-esc-time))
            (~a msg #:max-width 72))
    (define a-result (hash-ref result 'a))
    (define sa-result (hash-ref result 'sa))
    (define sfa-result (hash-ref result 'sfa))
    (define msfa-result (hash-ref result 'msfa))
    (print-config-result name "a" a-result)
    (print-config-result name "sa" sa-result)
    (print-config-result name "sfa" sfa-result)
    (print-config-result name "msfa" msfa-result)
    )


  (for ((r result))
       (let ((benchmark-name (car r)))
         (printf "~a\n" benchmark-name)
         (print-mach-result benchmark-name "conc" (cadr r))
         (print-mach-result benchmark-name "type" (caddr r))))
  )


(define (summary sys)
  ;(generate-dot (system-graph sys) "a-purity")
  (printf "call-store analysis... ")
  (define csr (call-store-analysis sys))
  (define call-store-time (call-store-result-time csr))
  (printf "~a ms\n" call-store-time)
  (define ctx->addrs (call-store-result-ctx->addrs csr))
  (printf "a-side-effect analysis... ")
  (define a-ser (a-side-effect-analysis sys ctx->addrs))
  (define side-effect-time (side-effect-result-time a-ser))
  (printf "~a ms\n" side-effect-time)
  (printf "purity analysis... ")
  (define pr (purity-analysis sys (side-effect-result-state->ctx->side-effects a-ser)))
  (define purity-time (purity-result-time pr))
  (printf "~a ms\n" purity-time)
  (define lam->side-effect-summary (purity-result-lam->summary pr))
  (for (((lam side-effect-summary) lam->side-effect-summary))
       (printf "~a ~a\n" (~a lam #:max-width 50) side-effect-summary))
  (define ast (ev-e (system-initial sys)))
  (define sorted-lams (sort (lambdas ast) < #:key «lam»-l))
  (summary-pattern lam->side-effect-summary sorted-lams))

#|
(define t2 '(letrec ((f (lambda (h) (let ((z (cons 1 2))) (if h (h) (f (lambda () (set-car! z 3)))))))) (f #f)))
(define sys2 (conc-mach t2))
(generate-dot (system-graph sys2) "t2")

(let* ((lattice (system-lattice sys2))
       (⊥ (lattice-⊥ lattice))
       (⊔ (lattice-⊔ lattice))
       (M (escape-analysis sys2))
       (escapes? (lambda (λ) (set-member? M λ)))
       (F (fresh-analysis sys2 ⊥ ⊔ escapes?)))
  (print-fresh-info F)
  (print-escape-info M)
  (parameterize ((PRINT-PER-LAMBDA #t))
    (print-purity-info (msfa-purity-analysis sys2))))




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
