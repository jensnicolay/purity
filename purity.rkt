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

(define FRESH "fresh")
(define UNFRESH "unfresh")

(define (fresh-analysis sys ⊥ ⊔)
  (let* ((graph (system-graph sys))
         (Ξ (system-Ξ sys))
         (initial (system-initial sys))
         (ast (ev-e initial))
         (parent (make-parent ast)))

    (define (add-fresh Fκ decl)
      (hash-set Fκ decl (⊔ (hash-ref Fκ decl ⊥) (set FRESH))))
      
    (define (add-unfresh Fκ decl)
      (hash-set Fκ decl (⊔ (hash-ref Fκ decl ⊥) (set UNFRESH))))
      
    (define (handle-state s E F sF)
      (let ((F (if (and (ev? s)
                        («lam»? (parent (ev-e s))))
                   (let* ((lam (parent (ev-e s)))
                          (κ (state-κ s))
                          (Fκ (hash-ref F κ (hash)))
                          (Fκ* (for/fold ((Fκ Fκ)) ((decl («lam»-x lam)))
                                 (add-unfresh Fκ decl)))
                          (F* (hash-set F κ Fκ*)))
                     F*)
                   F)))
        (match s
          ((ev («set!» _ x ae) ρ _ ι κ Ξi)
           (let* ((decl (get-declaration («id»-x x) x parent))
                  (ctxs (set-add (stack-contexts κ (vector-ref Ξ Ξi)) #f)) ; adding top-level ctx '#f', because freshness also deals with top-level stuff
                  (F* (for/fold ((F F)) ((κ ctxs))
                        (let ((Fκ (hash-ref F κ (hash))))
                              (let ((Fκ* (if (fresh? ae Fκ parent ⊥)
                                             (add-fresh Fκ decl)
                                             (add-unfresh Fκ decl))))
                                (hash-set F κ Fκ*))
                              ))))
             (values F* (hash-set sF s F*))))
          ((ev («let» _ x (? ae? ae) e1) ρ _ ι κ Ξi) ; only on ae!
           (let* ((decl (get-declaration («id»-x x) x parent))
                  (ctxs (set-add (stack-contexts κ (vector-ref Ξ Ξi)) #f)) ; adding top-level ctx '#f', because freshness also deals with top-level stuff
                  (F* (for/fold ((F F)) ((κ ctxs))
                        (let ((Fκ (hash-ref F κ (hash))))
                              (let ((Fκ* (if (fresh? ae Fκ parent ⊥)
                                             (add-fresh Fκ decl)
                                             (add-unfresh Fκ decl))))
                                (hash-set F κ Fκ*))
                              ))))
             (values F* (hash-set sF s F*))))
          ((ko v _ (cons (letk x e ρ) ι) κ Ξi) ; when e0 in let is not ae, letk is used
           (let* ((decl (get-declaration («id»-x x) x parent))
                  (ctxs (set-add (stack-contexts κ (vector-ref Ξ Ξi)) #f)) ; adding top-level ctx '#f', because freshness also deals with top-level stuff
                  (F* (for/fold ((F F)) ((κ ctxs))
                        (let ((Fκ (hash-ref F κ (hash))))
                              (let ((Fκ* (if (set-member? E (fr))
                                             (add-fresh Fκ decl)
                                             (add-unfresh Fκ decl))))
                                (hash-set F κ Fκ*))
                              ))))
             (values F* (hash-set sF s F*))))
          (_ (let ((Fκ (hash-ref F (state-κ s) (hash))))
               (values F (hash-set sF s F)))))))
      
    (define (traverse-graph* S W F sF)
      (if (set-empty? W)
          sF
          (let* ((t (set-first W)))
            (if (set-member? S t)
                (traverse-graph* S (set-rest W) F sF)
                (let* ((s (transition-s t))
                       (E (transition-E t)))
                  (let-values (((F* sF*) (handle-state s E F sF)))
                    (let* ((W* (set-union (set-rest W) (hash-ref graph s (set))))
                           (unchanged (equal? F F*))
                           (S* (if unchanged (set-add S t) (set))))
                    (traverse-graph* S* W* F* sF*))))))))

    (traverse-graph* (set) (set (transition initial (set))) (hash) (hash))))

(define (print-fresh-info sF)
    (for (((s F) sF))
      (printf "~a ~a\n" (state->statei s) (state-repr s))
      (for (((κ Fκ) F))
        (printf "\t~a ~a\n" (ctx->ctxi κ) (~a κ #:max-width 30))
        (for (((decl FU) Fκ))
          (printf "\t\t~a -> ~a\n" decl FU)))
      (newline)))
                  
(define (fresh? e Fκ parent ⊥)
  (match e
    ((«id» _ x)
     (let* ((decl (get-declaration x e parent))
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

(define (traverse-graph graph initial Ξ observable-effect?)

  (define (add-read-dep a λ R)
    (hash-set R a (set-add (hash-ref R a (set)) λ)))
  
  (define (add-observer λ F)
    (hash-set F λ (set-add (hash-ref F λ (set)) OBSERVES)))
  
  (define (add-observers a F O)
    (let ((λ-os (hash-ref O a (set))))
      (for/fold ((F F)) ((λ-o λ-os))
        (add-observer λ-o F))))

  (define (observable-effect2? eff κ s)
    (let ((o? (observable-effect? eff κ s)))
      (when o?
        (printf "observable ~a κ ~a s ~a\n" eff (ctx->ctxi κ) (state->statei s)))
      o?))
          
  
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
                                     (match eff
                                       ((wv a _)
                                        (let ((λ-rs (hash-ref R a (set))))
                                          (let ((O (for/fold ((O O)) ((λ-r λ-rs))
                                                      (hash-set O a (set-add (hash-ref O a (set)) λ-r)))))
                                            (let ((F (for/fold ((F F)) ((κ (stack-contexts (state-κ s) (state-Ξ s Ξ))))
                                                       (if (observable-effect? eff κ s)
                                                           (let ((λ (ctx-λ κ)))
                                                             (hash-set F λ (set-add (hash-ref F λ (set)) GENERATES)))
                                                           F))))
                                              (values W F R O)))))
                                       ((wp a n _)
                                        (let* ((res (cons a n))
                                              (λ-rs (hash-ref R res (set))))
                                          (let ((O (for/fold ((O O)) ((λ-r λ-rs))
                                                     (hash-set O res (set-add (hash-ref O res (set)) λ-r)))))
                                            (let ((F (for/fold ((F F)) ((κ (stack-contexts (state-κ s) (state-Ξ s Ξ))))
                                                       (if (observable-effect? eff κ s)
                                                           (let ((λ (ctx-λ κ)))
                                                             (hash-set F λ (set-add (hash-ref F λ (set)) GENERATES)))
                                                           F))))
                                              (values W F R O)))))
                                       ((rv a _)
                                        (let-values (((F R)
                                                      (for/fold ((F F) (R R)) ((κ (stack-contexts (state-κ s) (state-Ξ s Ξ))))
                                                        (if (observable-effect? eff κ s)
                                                            (let ((λ (ctx-λ κ)))
                                                              (values (add-observers a F O)
                                                                      (add-read-dep a λ R)))
                                                            (values F R)))))
                                          (values W F R O)))
                                       ((rp a n _)
                                        (let ((res (cons a n)))
                                          (let-values (((F R)
                                                        (for/fold ((F F) (R R)) ((κ (stack-contexts (state-κ s) (state-Ξ s Ξ))))
                                                          (if (observable-effect? eff κ s)
                                                              (let ((λ (ctx-λ κ)))
                                                                (values (add-observers res F O)
                                                                        (add-read-dep res λ R)))
                                                              (values F R)))))
                                            (values W F R O))))
                                       (_ (values W F R O))))))))))
                (let* ((unchanged (and (equal? F F*) (equal? R R*) (equal? O O*)))
                       (S* (if unchanged (set-add S s) (set))))
                  (traverse-graph* S* W* F* R* O*)))))))
  
  (traverse-graph* (set) (set initial) (hash) (hash) (hash)))

(define (a-observable-effect? call-states)
  (lambda (eff κ _)
    (let ((A (hash-ref call-states κ)))
      (match eff
        ((wv a _)
         (set-member? A a))
        ((wp a _ _)
         (set-member? A a))
        ((rv a _)
         (set-member? A a))
        ((rp a _ _)
         (set-member? A a))))))

(define (sa-observable-effect? parent call-states)
  (lambda (eff κ _s)
      (match eff
        ((wv a x)
         (let ((decl (get-declaration («id»-x x) x parent))
               (λ (ctx-λ κ)))
           (let ((scope-o? (if (inner-scope-declaration? decl λ)
                               #f
                               (set-member? (hash-ref call-states κ) a)))
                 (address-o? (set-member? (hash-ref call-states κ) a)))
             (when (not (eq? scope-o? address-o?))
               (printf "disagree ~a ~a a ~a scope ~a s ~a\n" eff (ctx->ctxi κ) address-o? scope-o? (state-repr _s)))
             scope-o?)))
        ((wp a _ _)
         (let ((A (hash-ref call-states κ)))
           (set-member? A a)))
        ((rv a x)
         (let ((decl (get-declaration («id»-x x) x parent))
               (λ (ctx-λ κ)))
           (and (not (inner-scope-declaration? decl λ))
                (set-member? (hash-ref call-states κ) a))))
        ((rp a _ _)
         (let ((A (hash-ref call-states κ)))
           (set-member? A a))))))

(define (sfa-observable-effect? parent call-states fresh?)
  (lambda (eff κ s)
    (match eff
      ((wv a x)
       (let ((decl (get-declaration («id»-x x) x parent))
             (λ (ctx-λ κ)))
         (and (not (inner-scope-declaration? decl λ))
              (set-member? (hash-ref call-states κ) a))))
      ((wp a _ x)
       (if (fresh? x s κ)
           #f
           (let ((A (hash-ref call-states κ)))
              (set-member? A a))))
      ((rv a x)
       (let ((decl (get-declaration («id»-x x) x parent))
             (λ (ctx-λ κ)))
         (and (not (inner-scope-declaration? decl λ))
              (set-member? (hash-ref call-states κ) a))))
      ((rp a _ x)
       (if (fresh? x s κ)
           #f
           (let ((A (hash-ref call-states κ)))
             (set-member? A a)))))))

(define (a-purity-analysis sys)
  (let* ((call-states (call-state-analysis sys))
         (observable-effect? (a-observable-effect? call-states)))
    (traverse-graph (system-graph sys) (system-initial sys) (system-Ξ sys) observable-effect?)))
    
(define (sa-purity-analysis sys)
  (let* ((call-states (call-state-analysis sys))
         (initial (system-initial sys))
         (ast (ev-e initial))
         (parent (make-parent ast))
         (observable-effect? (sa-observable-effect? parent call-states)))
    (traverse-graph (system-graph sys) (system-initial sys) (system-Ξ sys) observable-effect?)))
    
(define (sfa-purity-analysis sys)
  (let* ((call-states (call-state-analysis sys))
         (lattice (system-lattice sys))
         (⊥ (lattice-⊥ lattice))
         (⊔ (lattice-⊔ lattice))
         (sF (fresh-analysis sys ⊥ ⊔))
         (initial (system-initial sys))
         (ast (ev-e initial))
         (parent (make-parent ast))
         (fresh? (lambda (x s κ)
                   (let* ((F (hash-ref sF s (hash)))
                          (Fκ (hash-ref F κ (hash))))
                     (fresh? x Fκ parent ⊥))))
         (observable-effect? (sfa-observable-effect? parent call-states fresh?)))
    (traverse-graph (system-graph sys) (system-initial sys) (system-Ξ sys) observable-effect?)))
    
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
                    treenode1 helloset! hellomemoset!)))
  (define configs (list (cons 'a a-purity-benchmark)
                        (cons 'sa sa-purity-benchmark)
                        (cons 'sfa sfa-purity-benchmark)
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

(define t3 '(let ((f (lambda (h) (h)))) (let ((z #t)) (let ((g (lambda () (set! z #f)))) (f g)))))
(define sys3 (conc-mach t3))
(generate-dot (system-graph sys3) "t3")
(parameterize ((PRINT-PER-LAMBDA #t))
  (print-purity-info (a-purity-analysis sys3))
  (newline)
  (print-purity-info (sa-purity-analysis sys3)))


#|

(define t1 (add-map '(let ((env '())) (let ((eval (lambda () (map (lambda (x) (set! env 123)) '(4))))) (eval)))))
(define sys1 (type-mach-0 t1))
(generate-dot (system-graph sys1) "t1")
(print-fresh-info (fresh-analysis sys1 (set) set-union))
(print-purity-info (sfa-purity-analysis sys1))


(define t2 mceval2) 
(define sys2 (conc-mach t2))
(parameterize ((PRINT-PER-LAMBDA #t))
  (print-purity-info (a-purity-analysis sys2))
  (newline)
  (print-purity-info (sa-purity-analysis sys2)))


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


; P FRESH
(define (handle-wp-fresh x ctxs ctx-λ Fκ ast C R O)
  (let stack-walk ((ctxs ctxs) (C C))
    (if (set-empty? ctxs)
        (values C R O)
        (let* ((κ (set-first ctxs))
               (fresh (hash-ref Fκ κ (set))))
          (if (fresh? x fresh ast)
              (stack-walk (set-rest ctxs) C)
              (let* ((λ (ctx-λ κ))
                     (C* (mark-proc C λ)))
                (stack-walk (set-rest ctxs) C*)))))))
(define (handle-rp-fresh a n x ctxs ctx-λ Fκ ast C R O)
  (let stack-walk ((ctxs ctxs) (C C) (R R))
    (if (set-empty? ctxs)
        (values C R O)
        (let* ((κ (set-first ctxs))
               (fresh (hash-ref Fκ κ (set))))
          (if (fresh? x fresh ast)
              (stack-walk (set-rest ctxs) C R)
              (let* ((λ (ctx-λ κ))
                     (R* (add-read-dep R a n λ))
                     (potential-o (hash-ref O (cons a n) (set)))
                     (C* (if (set-member? potential-o λ)
                             (mark-obs C λ)
                             C)))
                (stack-walk (set-rest ctxs) C* R*)))))))



(define (make-address-handler ctx-Aσ)
  (lambda (sys)
    (lambda (effect state ast Ξ ctx-λ C R O)
      (let* ((κ (if (ev? state) (ev-κ state) (ko-κ state)))
             (ctxs (stack-contexts κ Ξ)))
        (match effect
          ((wv a x)
           (let* ((decl (get-declaration («id»-x x) x ast))
                  (r-deps (hash-ref R (cons a decl) (set)))
                  (O* (let update-o ((O O) (r-deps r-deps))
                        (if (set-empty? r-deps)
                            O
                            (let* ((r-dep (set-first r-deps))
                                   (O* (add-potential-obs O a decl r-dep)))
                              (update-o O* (set-rest r-deps)))))))
             (handle-wv-address a x ctxs ctx-λ ctx-Aσ C R O)))
          ((wp a n x)
           (let* ((r-deps (hash-ref R (cons a n) (set)))
                  (O* (let update-o ((O O) (r-deps r-deps))
                        (if (set-empty? r-deps)
                            O
                            (let* ((r-dep (set-first r-deps))
                                   (O* (add-potential-obs O a n r-dep)))
                              (update-o O* (set-rest r-deps)))))))
             (handle-wp-address a n x ctxs ctx-λ ctx-Aσ C R O*)))
          ((rv a x)
           (handle-rv-address a x ctxs ctx-λ ctx-Aσ ast C R O))
          ((rp a n x)
           (handle-rp-address a n x ctxs ctx-λ ctx-Aσ C R O))
          (_ (values C R O)))))))

(define (make-non-address-handler)
  (lambda (sys)
    (let ((Fς (fresh-analysis sys)))
      (lambda (effect state ast Ξ ctx-λ C R O)
        (let* ((κ (if (ev? state) (ev-κ state) (ko-κ state)))
               (ctxs (stack-contexts κ Ξ)))
          (match effect
            ((wv a x)
             (let* ((decl (get-declaration («id»-x x) x ast))
                    (r-deps (hash-ref R (cons a decl) (set)))
                    (O* (let update-o ((O O) (r-deps r-deps))
                          (if (set-empty? r-deps)
                              O
                              (let* ((r-dep (set-first r-deps))
                                     (O* (add-potential-obs O a decl r-dep)))
                                (update-o O* (set-rest r-deps)))))))
               (handle-wv-scope x ctxs ctx-λ ast C R O*)))
            ((wp a n x)
             (let* ((r-deps (hash-ref R (cons a n) (set)))
                    (O* (let update-o ((O O) (r-deps r-deps))
                          (if (set-empty? r-deps)
                              O
                              (let* ((r-dep (set-first r-deps))
                                     (O* (add-potential-obs O a n r-dep)))
                                (update-o O* (set-rest r-deps)))))))
               (handle-wp-fresh x ctxs ctx-λ (hash-ref Fς state) ast C R O)))
            ((rv a x)
             (handle-rv-scope a x ctxs ctx-λ ast C R O))
            ((rp a n x)
             (handle-rp-fresh a n x ctxs ctx-λ (hash-ref Fς state) ast C R O))
            (_ (values C R O))))))))

|#