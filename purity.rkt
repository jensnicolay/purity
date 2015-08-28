#lang racket
;(require (submod racket/performance-hint))

(include "general.rkt")
(include "ast.rkt")
(include "cesk.rkt")
(include "lattice.rkt")
(include "test.rkt")

;; machines and evaluators
(define (do-eval e mach)
  (let ((sys (mach e)))
    (if (eq? (system-exit sys) 'ok)
        (answer-value sys)
        (raise (system-msg sys)))))

(define (ctx-lim e clo rvs σ A)
  (ctx #f (clo-λ clo) #f (hash-keys σ) A))

(define (ctx-lim2 e clo rvs σ A)
  (ctx #f (clo-λ clo) #f #f A))

(define (ctx-lim3 e clo rvs σ A)
  (ctx #f #f #f #f A))

(define conc-mach (make-machine conc-global conc-α conc-γ conc-⊥ conc-⊔ conc-alloc ctx-lim strong-update conc-true? conc-false? conc-eq?))
(define type-mach-0 (make-machine type-global type-α type-γ type-⊥ type-⊔ mono-alloc ctx-lim weak-update type-true? type-false? type-eq?))
(define type-mach-1 (make-machine type-global type-α type-γ type-⊥ type-⊔ poly-alloc ctx-lim weak-update type-true? type-false? type-eq?))

(define (conc-eval e)
  (do-eval e conc-mach))
(define (type-eval-0 e)
  (do-eval e type-mach-0))
(define (type-eval-1 e)
  (do-eval e type-mach-1))
;;
(define (outer-scope-declaration? decl e ast)
  (let up ((e e))
    (let ((p (parent e ast)))
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

(define (get-declaration name e ast)
  (let up ((e e))
    (let ((p (parent e ast)))
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

(define (fresh-analysis system)
  (let* ((graph (system-graph system))
         (Ξ (system-Ξ system))
         (initial (system-initial system))
         (ast (ev-e initial)))
    
    (define (handle-state state E fresh)
      (match state
        ((ev («set!» _ x ae) ρ σ ι κ)
         (let ((decl (get-declaration («id»-x x) x ast)))
           (if (fresh? ae fresh ast)
               (set-add fresh decl)
               (set-remove fresh decl))))
        ((ev («let» _ x e0 e1) ρ σ ι κ)
         (let ((decl (get-declaration («id»-x x) x ast)))
           (if (fresh? e0 fresh ast)
               (set-add fresh decl)
               (set-remove fresh decl))))
        ((ko (cons (letk x e ρ) ι) κ v σ)
         (let ((decl (get-declaration («id»-x x) x ast)))
           (if (set-member? E (fr))
               (set-add fresh decl)
               ;(set-remove fresh decl)))) ; can never overrule ev let
               fresh)))
        (_ fresh)))
    
    (define (traverse S W Fκ Fς)
      (if (set-empty? W)
          Fς
          (let* ((sE (set-first W))
                 (state (car sE))
                 (E (cdr sE)))
            (if (set-member? S state)
                (traverse S (set-rest W) Fκ Fς)
                (let* ((κ (if (ev? state) (ev-κ state) (ko-κ state)))
                       (fresh (hash-ref Fκ κ (set)))
                       (fresh* (handle-state state E fresh))
                       (Fκ* (hash-set Fκ κ fresh*))
                       (Fς* (hash-set Fς state fresh*))
                       (ΔW (hash-ref graph state)))
                  (traverse (set-add S state) (set-union (set-rest W) ΔW) Fκ* Fς*))))))
    
    (traverse (set) (set (cons initial (set))) (hash) (hash))))

(define (fresh? e fresh ast)
  (match e
    ((«id» _ x)
     (let ((decl (get-declaration x e ast)))
       (set-member? fresh decl)))
    (_ #f)))

(define (mark-proc C λ)
  (let ((current-class (hash-ref C λ)))
    (if (eq? current-class "PROC")
        C
        (hash-set C λ "PROC"))))

(define (mark-obs C λ)
  (let ((current-class (hash-ref C λ)))
    (if (or (eq? current-class "OBS") (eq? current-class "PROC"))
        C
        (hash-set C λ "OBS"))))

(define (mark-pure C λ)
  (let ((current-class (hash-ref C λ)))
    (if (or (eq? current-class "PURE") (eq? current-class "OBS") (eq? current-class "PROC"))
        C
        (hash-set C λ "PURE"))))

(define (add-read-dep R a decl λ)
  (let* ((key (cons a decl))
         (current-deps (hash-ref R key (set))))
    (if (set-member? current-deps λ)
        R
        (hash-set R key (set-add current-deps λ)))))

(define (add-potential-obs O a decl λ)
  (let* ((key (cons a decl))
         (current-os (hash-ref O key (set))))
    (if (set-member? current-os λ)
        O
        (hash-set O key (set-add current-os λ)))))

; ADDRESS
(define (handle-wv-address a x ctxs C R O P observable-address?)
  (let stack-walk ((ctxs ctxs) (C C))
    (if (set-empty? ctxs)
        (values C R O P)
        (let* ((τ (set-first ctxs)))
          (if (observable-address? a τ)
              (let* ((λ (ctx-λ τ))
                     (C* (mark-proc C λ)))
                (stack-walk (set-rest ctxs) C*))
              (stack-walk (set-rest ctxs) C))))))
(define (handle-wp-address a n x ctxs C R O P observable-address?)
  (let stack-walk ((ctxs ctxs) (C C))
    (if (set-empty? ctxs)
        (values C R O P)
        (let* ((τ (set-first ctxs)))               
          (if (observable-address? a τ)
              (let* ((λ (ctx-λ τ))
                     (C* (mark-proc C λ)))
                (stack-walk (set-rest ctxs) C*))
              (stack-walk (set-rest ctxs) C))))))
(define (handle-rv-address a x ctxs ast C R O P observable-address?)
  (let ((decl (get-declaration («id»-x x) x ast)))
    (let stack-walk ((ctxs ctxs) (C C) (R R))
      (if (set-empty? ctxs)
          (values C R O P)
          (let* ((τ (set-first ctxs)))               
            (if (observable-address? a τ)
                (let* ((λ (ctx-λ τ))
                       (R* (add-read-dep R a decl λ))
                       (potential-o (hash-ref O (cons a decl) (set)))
                       (C* (if (set-member? potential-o λ)
                               (mark-obs C λ)
                               C)))
                  (stack-walk (set-rest ctxs) C* R*))
                (stack-walk (set-rest ctxs) C R)))))))
(define (handle-rp-address a n x ctxs C R O P observable-address?)
  (let stack-walk ((ctxs ctxs) (C C) (R R))
    (if (set-empty? ctxs)
        (values C R O P)
        (let* ((τ (set-first ctxs)))               
          (if (observable-address? a τ)
              (let* ((λ (ctx-λ τ))
                     (R* (add-read-dep R a n λ))
                     (potential-o (hash-ref O (cons a n) (set)))
                     (C* (if (set-member? potential-o λ)
                             (mark-obs C λ)
                             C)))
                (stack-walk (set-rest ctxs) C* R*))
              (stack-walk (set-rest ctxs) C R))))))

; V SCOPE
(define (handle-wv-scope x ctxs ast C R O P)
  (let ((decl (get-declaration («id»-x x) x ast)))
    (let stack-walk ((ctxs ctxs) (C C))
      (if (set-empty? ctxs)
          (values C R O P)
          (let* ((τ (set-first ctxs))
                 (λ (ctx-λ τ)))
            (if (outer-scope-declaration? decl λ ast)
                (let ((C* (mark-proc C λ)))
                  (stack-walk (set-rest ctxs) C*))
                (stack-walk (set-rest ctxs) C)))))))
(define (handle-rv-scope a x ctxs ast C R O P)
  (let ((decl (get-declaration («id»-x x) x ast)))
    (let stack-walk ((ctxs ctxs) (C C) (R R))
      (if (set-empty? ctxs)
          (values C R O P)
          (let* ((τ (set-first ctxs))
                 (λ (ctx-λ τ)))
            (if (inner-scope-declaration? decl λ)
                (stack-walk (set-rest ctxs) C R)
                (if (outer-scope-declaration? decl λ ast)
                    (let* ((R* (add-read-dep R a decl λ))
                           (potential-o (hash-ref O (cons a decl) (set)))
                           (C* (if (set-member? potential-o λ)
                                   (mark-obs C λ)
                                   C)))
                      (stack-walk (set-rest ctxs) C* R*))
                    (stack-walk (set-rest ctxs) C R))))))))

(define (make-handler ast Ξ Fς observable-address?) 
  (lambda (effect state C R O P)
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
           (handle-wv-scope x ctxs ast C R O* P)))
        ((wp a n x)
         (let* ((r-deps (hash-ref R (cons a n) (set)))
                (O* (let update-o ((O O) (r-deps r-deps))
                      (if (set-empty? r-deps)
                          O
                          (let* ((r-dep (set-first r-deps))
                                 (O* (add-potential-obs O a n r-dep)))
                            (update-o O* (set-rest r-deps))))))
                (p-deps (hash-ref P a (set)))
                (C* (for/fold ((C C)) ((λ p-deps))
                      (mark-pure C λ))))
           (if (fresh? x (hash-ref Fς state) ast) ; freshness is ONLY about observability!
               (values C* R O* P)
               (handle-wp-address a n x ctxs C* R O* P observable-address?))))  
        ((rv a x)
         (handle-rv-scope a x ctxs ast C R O P))
        ((rp a n x)
         (if (fresh? x (hash-ref Fς state) ast)
             (values C R O P)
             (handle-rp-address a n x ctxs C R O P observable-address?)))
        (_ (values C R O P))))))

(define (observable-address? a κ)
  (let ((Aσ (ctx-σ κ)))
    (member a Aσ)))

(define (purity-analysis system handler)
  
  (let* ((graph (system-graph system))
         (Ξ (system-Ξ system))
         (γ (system-γ system))
         (initial (system-initial system))
         (ast (ev-e initial)))
    
    (define (C0)
      (for/hash ((κ (hash-keys Ξ)))
        (let* ((λ (ctx-λ κ)))
          (values λ "RT"))))
    
    (define (traverse S W C R O P)
      (if (set-empty? W)
          C
          (let ((state (set-first W)))
            (if (set-member? S state)
                (traverse S (set-rest W) C R O P)
                (let ((P*
                       (match state
                         ((ko ι κ v σ)
                          (let* ((ικGs (stack-pop ι κ Ξ (set)))
                                 (G (for/fold ((G (set))) ((ικG ικGs))
                                      (set-union G (caddr ικG)))))
                            (for/fold ((P P)) ((w (γ v)))
                              (match w
                                ((addr a)
                                 (let ((A (reachable (set a) σ γ)))
                                   (for/fold ((P P)) ((κ* G))
                                     (for/fold ((P P)) ((a* A))
                                       (hash-set P a* (set-add (hash-ref P a* (set)) (ctx-λ κ*)))))))
                                (_ P)))))
                         (_ P))))
                  (let* ((κ (if (ev? state) (ev-κ state) (ko-κ state)))
                         (ctxs (stack-contexts κ Ξ)))
                    (let succ-loop ((succs (hash-ref graph state)) (ΔW (set)) (C* C) (R* R) (O* O) (P* P*))
                      (if (set-empty? succs)
                          (let ((unchanged (and (equal? C C*) (equal? R R*) (equal? O O*) (equal? P P*))))
                            (traverse (if unchanged (set-add S state) (set)) (set-union (set-rest W) ΔW) C* R* O* P*))
                          (match-let (((cons s* E) (set-first succs)))
                            (let effect-loop ((E E) (C** C*) (R** R*) (O** O*) (P** P*))
                              (if (set-empty? E)
                                  (succ-loop (set-rest succs) (set-add ΔW s*) C** R** O** P**)
                                  (let-values (((C*** R*** O*** P***) (handler (set-first E) state C** R** O** P**)))
                                    (effect-loop (set-rest E) C*** R*** O*** P***)))))))))))))
    
    (traverse (set) (set initial) (C0) (hash) (hash) (hash))))



(define (flow-test . ens)
  (when (null? ens)
    (set! ens '(fac fib fib-mut blur eta mj09 gcipd kcfa2 kcfa3 rotate loop2 sat collatz rsa primtest factor nqueens)))
  (define (perform name e)
    (let* ((sys (type-mach-0 e))
          (flow-duration (system-duration sys))
          (flow-state-count (vector-length (system-states sys)))
          (flow-exit (system-exit sys))
          (flow-msg (if (eq? flow-exit 'ok) (answer-value sys) (system-msg sys))))
      (printf "~a states ~a time ~a | ~a\n"
              (~a name #:min-width 12)
              (~a (if (eq? flow-exit 'ok) flow-state-count (format ">~a" flow-state-count)) #:min-width 7)
              (~a flow-duration #:min-width 7)
              (~a flow-msg #:max-width 72))))
  (for-each (lambda (en) (perform en (eval en)))
            ens))

(define (server-flow-test)
  (parameterize ((CESK-TIMELIMIT 60) (THROW #f))
    (apply flow-test '(fac fib fib-mut blur eta mj09 gcipd kcfa2 kcfa3 rotate loop2
                                     sat collatz rsa primtest factor nqueens boyer dderiv mceval))))

(define THROW (make-parameter #t))

(struct benchmark (name state-count duration exit msg num-called num-rt num-pure num-obs num-proc))

(define (test . ens)  
  (when (null? ens)
    (set! ens '(fac fib fib-mut blur eta mj09 gcipd kcfa2 kcfa3 rotate loop2 sat collatz rsa primtest factor)))
  (printf "Benchmarks: ~a\n" ens)
  (for/list ((en ens))
    (let ((e (eval en)))
      (perform-benchmark en e type-mach-0))))

(define (server-test)
  (parameterize ((CESK-TIMELIMIT 60) (THROW #f))
    (let ((results (apply test '(fac fib fib-mut blur eta mj09 gcipd kcfa2 kcfa3 rotate loop2
                                     sat collatz rsa primtest factor nqueens boyer dderiv mceval
                                     ; regex
                                     )))) 
      (printf "Done.")
      results)))              
      

(define (benchmark-eval name e mach)
  (with-handlers ((exn:fail? (lambda (exc) (if (THROW) (raise exc) (benchmark name -1 -1 'error exc 0 0 0 0 0)))))
    (let* ((sys (mach e))
           (flow-duration (system-duration sys))
           (flow-state-count (vector-length (system-states sys)))
           (flow-exit (system-exit sys))
           (msg (if (eq? flow-exit 'ok) (answer-value sys) (system-msg sys))))
      (if (eq? flow-exit 'ok)
          (let* ((initial (system-initial sys))
                 (ast (ev-e initial))
                 (Ξ (system-Ξ sys))
                 (Fς (fresh-analysis sys))
                 (handler (make-handler ast Ξ Fς (lambda _ #t)))
                 (C (purity-analysis sys handler))
                 (num-called (set-count (list->set (map (lambda (κ) (ctx-λ κ)) (hash-keys Ξ))))))
            (let-values (((num-rt num-pure num-obs num-proc) (for/fold ((num-rt 0) (num-pure 0) (num-obs 0) (num-proc 0)) (((λ c) C))
                                                               (printf "~a -> ~a\n" (~a λ #:max-width 30) c)
                                                               (cond
                                                                 ((eq? c "RT") (values (+ num-rt 1) num-pure num-obs num-proc))
                                                                 ((eq? c "PURE") (values num-rt (+ num-pure 1) num-obs num-proc))
                                                                 ((eq? c "OBS") (values num-rt num-pure (+ num-obs 1) num-proc))
                                                                 ((eq? c "PROC") (values num-rt num-pure num-obs (+ num-proc 1)))
                                                                 (else (raise "unknown effect class"))))))
            (benchmark name flow-state-count flow-duration flow-exit msg num-called num-rt num-pure num-obs num-proc)))
          (benchmark name flow-state-count flow-duration flow-exit msg 0 0 0 0 0)))))
           
(define (perform-benchmark name e mach)
  (printf (~a name #:min-width 12))
  (let* ((bench (benchmark-eval name e mach))
         (exit (benchmark-exit bench))
         (msg (benchmark-msg bench))
         (state-count (benchmark-state-count bench))
         (duration (benchmark-duration bench)))
    (printf "states ~a flow-time ~a called ~a rt ~a pure ~a obs ~a proc ~a | ~a\n"
            (~a (if (eq? exit 'ok) state-count (format ">~a" state-count)) #:min-width 7)
            (~a duration #:min-width 7)
            (~a (benchmark-num-called bench) #:min-width 3)
            (~a (benchmark-num-rt bench) #:min-width 3)
            (~a (benchmark-num-pure bench) #:min-width 3)
            (~a (benchmark-num-obs bench) #:min-width 3)
            (~a (benchmark-num-proc bench) #:min-width 3)
            (~a msg #:max-width 72))
    bench))

(define (state-repr s)
  (match s
    ((ev e ρ σ ι κ) (format "~a | ~a" (~a e #:max-width 20) (ctx->ctxi κ)))
    ((ko ι κ v σ) (format "~a | ~a" (~a v #:max-width 20) (ctx->ctxi κ)))))

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
               (~a (benchmark-name res-0)) 
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
               (~a (benchmark-name res-0)) 
               (~a (to-time res-0))      
               (~a (to-time res-0-summ))
               (~a (to-time res-0-sa)))
       ;; 1-CFA
       (printf "                & 1CFA         & ~a   & ~a      & ~a          \\\\[6pt]\n"
               (~a (to-time res-1))
               (~a (to-time res-1-summ))
               (~a (to-time res-1-sa))))))
  (printf "\\end{tabular}\n"))



(define (generate-dot sys name)
  
  (let* ((graph (system-graph sys))
         (states (system-states sys))
         (dotf (open-output-file (format "~a.dot" name) #:exists 'replace)))
    (fprintf dotf "digraph G {\n")
    (for ((i (vector-length states)))
      (let ((s (vector-ref states i)))
        (fprintf dotf "~a [label=\"~a | ~a\"];\n" i i (state-repr s))))
    (hash-for-each graph (lambda (s out)
                           (let ((i1 (vector-member s states))
                                 (is (set-map out (lambda (s2E) (vector-member (car s2E) states)))))
                             (for-each (lambda (i2)
                                         (fprintf dotf "~a -> ~a;\n" i1 i2)) is))))
    (fprintf dotf "}")
    (close-output-port dotf))
  
  sys)

(define (graph e mach name)
  (parameterize ((CESK-TIMELIMIT 1))
    (generate-dot (mach e) name)))

