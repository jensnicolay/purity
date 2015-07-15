#lang racket

(random-seed 111) ; deterministic random
(define TIMELIMIT (make-parameter 2)) ; timeout in minutes
(define STATELIMIT (make-parameter 999999)) ; state limit (NOT YET IMPLEMENTED)
(define THROW (make-parameter #t)) ; let exceptions bubble up (#t) during benchmarking, or catch and log them (#f)

(define %random (lambda (n) (if (zero? n) 0 (random n))))

(include "general.rkt")
(include "ast.rkt")

(define (index v x)
  (let ((i (vector-member x v)))
    (if i
        i
        (let ((i (add1 (vector-ref v 0))))
          (vector-set! v 0 i)
          (vector-set! v i x)
          i))))
;(define frameis (make-vector 1000))
;(define (frame->framei frame) (index frameis frame))
(define ctxis (make-vector 1000))
(define (ctx->ctxi ctx) (index ctxis ctx))
;(define stateis (make-vector 1000))
;(define (state->statei q) (index stateis q))
;(define storeis (make-vector 1000))
;(define (store->storei σ) (index storeis σ))

;; domain helpers
(define (env-lookup ρ x)
  (hash-ref ρ x))
(define (env-addresses ρ)
  (list->set (hash-values ρ)))
(define (store-lookup σ a)
  (hash-ref σ a))
(define (store-⊒ σ1 σ2 ⊒)
  (if (eq? σ1 σ2)
      #t
      (if (< (hash-count σ1) (hash-count σ2))
          #f
          (for/and (((k v) σ1))
            (and (hash-has-key? σ2)
                 (⊒ v (hash-ref σ2 k)))))))
(define (stack-lookup Ξ τ)
  (hash-ref Ξ τ))
;;

;; machine
(struct ev (e ρ σ ι κ) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "EV ~a\nρ ~a\nσ ~a\nι ~a\nκ ~a" (ev-e v) (ev-ρ v) (ev-σ v) (ev-ι v) (ev-κ v))))
(struct ko (ι κ v σ) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "KO ι ~a\nκ ~a\nv ~a\nσ ~a" (ko-ι v) (ko-κ v) (ko-v v) (ko-σ v))))
(struct ctx (e clo vs σ A) #:transparent)
(struct letk (x e ρ) #:transparent)
(struct letreck (a e ρ) #:transparent)
(struct haltk () #:transparent)
(struct clo (λ ρ) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "<clo ~a>" («lam»-l (clo-λ v)))))
(struct prim (name proc) #:methods gen:equal+hash ((define equal-proc (lambda (s1 s2 requal?)
                                                                        (equal? (prim-name s1) (prim-name s2))))
                                                   (define hash-proc (lambda (s rhash) (equal-hash-code (prim-name s))))
                                                   (define hash2-proc (lambda (s rhash) (equal-secondary-hash-code (prim-name s))))))
(struct prim2 (name proc) #:methods gen:equal+hash ((define equal-proc (lambda (s1 s2 requal?)
                                                                         (equal? (prim2-name s1) (prim2-name s2))))
                                                    (define hash-proc (lambda (s rhash) (equal-hash-code (prim2-name s))))
                                                    (define hash2-proc (lambda (s rhash) (equal-secondary-hash-code (prim2-name s))))))
(struct addr (a) #:transparent)
(struct system (states duration initial graph Ξ ⊥ ⊔ answer? exit msg) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "<sys #~a ~a ~a>" (vector-length (system-states v)) (system-exit v) (~a (system-msg v) #:max-width 70))))

(define (touches d)
  (if (set? d)
      (for/fold ((as (set))) ((v d)) (set-union as (touches v)))
      (match d
        ((clo _ ρ) (env-addresses ρ))
        ((letk _ _ ρ) (env-addresses ρ))
        ((letreck _ _ ρ) (env-addresses ρ))
        ((addr a) (set a))
        ((cons x y) (set-union (touches x) (touches y)))
        (_ (set)))))
(define (reachable A σ γ)
  (let loop ((A A) (R (set)))
    (if (set-empty? A)
        R
        (let ((a (set-first A)))
          (if (set-member? R a)
              (loop (set-rest A) R)
              (let* ((v (γ (store-lookup σ a)))
                     (T (touches v)))
                (loop (set-union (set-rest A) T) (set-add R a))))))))
(define (gc q Ξ γ)
  (match q
    ((ev e ρ σ ι κ)
     (let* ((ρ* (↓ ρ (free e)))
            (R (reachable (set-union (env-addresses ρ*) (stack-addresses ι κ)) σ γ))
            (σ* (↓ σ R)))
       (ev e ρ* σ* ι κ)))
    ((ko ι κ v σ)
     (let* ((R (reachable (set-union (touches v) (stack-addresses ι κ)) σ γ))
            (σ* (↓ σ R)))
       (ko ι κ v σ*)))))
(define (stack-frames ι κ Ξ)
  (let loop ((todo (set (cons ι κ))) (result (set)) (seen (set)))
    (if (set-empty? todo)
        result
        (match-let (((cons ι κ) (set-first todo)))
          (let* ((result* (set-union result (list->set ι))))
            (if (or (not κ) (set-member? seen κ))
                (loop (set-rest todo) result* seen)
                (let ((ικs (stack-lookup Ξ κ)))
                  (loop (set-union (set-rest todo) ικs) result* (set-add seen κ)))))))))
(define (stack-pop ι κ Ξ G)
  (if (null? ι)
      (if (set-member? G κ)
          (set)
          (let ((ικs (stack-lookup Ξ κ)))
            (apply set-union (set-map ικs (lambda (ικ) (stack-pop (car ικ) (cdr ικ) Ξ (set-add G κ)))))))
      (set (list ι κ G)))) 
(define (stack-contexts κ Ξ)
  (let loop ((todo (set (cons #f κ))) (seen (set)))
    (if (set-empty? todo)
        seen
        (let ((κ (cdr (set-first todo))))
          (if (or (not κ) (set-member? seen κ))
              (loop (set-rest todo) seen)
              (loop (set-union (set-rest todo) (stack-lookup Ξ κ)) (set-add seen κ)))))))
(define (stack-addresses ι κ)
  (set-union (if (null? ι) (set) (apply set-union (map touches ι))) (if κ (ctx-A κ) (set))))

(define (make-machine global α γ ⊥ ⊔ alloc store-update true? false? α-eq?)
  
  (define (explore e)
    (define Ξ (make-hash))
    (define Ξi 0)
    
    (include "primitives.rkt")
    
    (define (inject e)
      (let ((global* (append global
                             `(("eq?" . ,(α (prim "eq?" prim-eq?)))
                               ("~a" . ,(α (prim "~a" prim-to-string)))
                               ("error" . ,(α (prim "error" prim-error)))
                               ("pair?" . ,(α (prim "pair?" prim-pair)))
                               ("cons" . ,(α (prim "cons" prim-cons)))
                               ("car" . ,(α (prim "car" prim-car)))
                               ("set-car!" . ,(α (prim "set-car!" prim-set-car!)))
                               ("cdr" . ,(α (prim "cdr" prim-cdr)))
                               ("set-cdr!" . ,(α (prim "set-cdr!" prim-set-cdr!))))))
            (compiled-e (compile e)))
        (set! conc-alloc-counter 0)
        (let loop ((global global*) (ρ (hash)) (σ (hash)))
          (match global
            ('()
             (gc (ev compiled-e (↓ ρ (free compiled-e)) σ `(,(haltk)) #f) (hash) γ))
            ((cons (cons x v) r)
             (let ((a (conc-alloc x 0)))
               (loop r (hash-set ρ x a) (hash-set σ a v))))))))
    
    ;(define (stack-to-string stack)
    ;  (cons (map frame->framei (car stack)) (ctx->ctxi (cdr stack))))
    
    (define (env-bind ρ x a)
      (hash-set ρ x a))
    
    (define (store-alloc σ a v)
      (let ((current (hash-ref σ a ⊥)))
        (hash-set σ a (⊔ current v))))
    
    (define (stack-alloc! τ stack)
      ;(printf "allocing ctx ~a stack ~a " (ctx->ctxi τ) (stack-to-string stack))
      (let ((stacks (hash-ref Ξ τ #f)))
        (if stacks
            (unless (set-member? stacks stack)
              ;(printf "ADDING to ~a\n" (set-map stacks stack-to-string))
              (hash-set! Ξ τ (set-add stacks stack))
              (set! Ξi (add1 Ξi)))
            (begin
              ;(printf "NEW CTX\n")
              (hash-set! Ξ τ (set stack))
              (set! Ξi (add1 Ξi))))))
    
    (define (alloc-literal e σ)
      (if (pair? e)
          (match-let (((cons car-v car-σ) (alloc-literal (car e) σ)))
            (match-let (((cons cdr-v cdr-σ) (alloc-literal (cdr e) car-σ)))
              (let ((a (alloc "%$lit" e)))
                (cons (α (addr a)) (store-alloc cdr-σ a (α (cons car-v cdr-v)))))))
          (cons (α e) σ)))
    
    (define (eval-atom ae ρ σ)
      (match ae
        ((«lit» _ v)
         (α v))
        ((«id» _ x)
         (let ((a (env-lookup ρ x)))
           (store-lookup σ a)))
        ((«lam» _ x e)
         (let ((cl (clo ae ρ)))
           (α cl)))
        ((«quo» _ atom) (α atom))
        (_ (error "cannot handle ae" ae))))
    
    (define (apply-let-kont x e ρ ι κ v σ)
      (let* ((a (alloc x (and κ (ctx-e κ))))
             (ρ* (env-bind ρ («id»-x x) a))
             (σ* (store-alloc σ a v)))
        (ev e ρ* σ* ι κ)))
    (define (apply-letrec-kont a e ρ ι κ v σ)
      (let ((σ* (store-update σ a v)))
        (ev e ρ σ* ι κ)))
    (define (apply-local-kont ι κ v σ)
      (match ι
        ((cons (letk x e ρ) ι)
         (apply-let-kont x e ρ ι κ v σ))
        ((cons (letreck a e ρ) ι)
         (apply-letrec-kont a e ρ ι κ v σ))
        (_ (ko ι κ v σ))))
    
    ;(define (print-state q)
    ;  (match q
    ;   ((ev e ρ σ ι κ m) (printf "EV ~a\nρ ~a σ ~a\nι ~a κ ~a frames ~a\n" (~a e #:max-width 40) ρ (store->storei σ) (map frame->framei ι) (ctx->ctxi κ) (set-map (stack-frames ι κ Ξ) frame->framei)))
    ;    ((ko ι κ v σ m) (printf "KO ~a σ ~a\nι ~a κ ~a frames ~a\n" v (store->storei σ) (map frame->framei ι) (ctx->ctxi κ) (set-map (stack-frames ι κ Ξ) frame->framei)))))
    
    (define (step q)
      ;(check-safety q Ξ)
      (match q
        ((ev (? ae? ae) ρ σ ι κ)
         (let ((v (eval-atom ae ρ σ)))
           (cons (set (ko ι κ v σ)) (set))))
        ((ev («if» _ ae e1 e2) ρ σ ι κ)
         (cons
          (let ((v (eval-atom ae ρ σ)))
            (set-union (if (true? v)
                           (if (ae? e1)
                               (let ((v (eval-atom e1 ρ σ)))
                                 (set (ko ι κ v σ)))
                               (set (ev e1 ρ σ ι κ)))
                           (set))
                       (if (false? v)
                           (if (ae? e2)
                               (let ((v (eval-atom e2 ρ σ)))
                                 (set (ko ι κ v σ)))
                               (set (ev e2 ρ σ ι κ)))
                           (set))))
          (set)))
        ((ev («let» _ x e0 e1) ρ σ ι κ)
         (cons 
          (if (ae? e0)
              (let ((v (eval-atom e0 ρ σ)))
                (set (apply-let-kont x e1 ρ ι κ v σ)))
              (set (ev e0 ρ σ (cons (letk x e1 ρ) ι) κ)))
          (set)))
        ((ev («letrec» _ x e0 e1) ρ σ ι κ)
         (cons
          (let* ((a (alloc x (and κ (ctx-e κ))))
                 (ρ* (env-bind ρ («id»-x x) a))
                 (σ* (store-alloc σ a ⊥)))
            (if (ae? e0)
                (let ((v (eval-atom e0 ρ* σ*)))
                  (set (apply-letrec-kont a e1 ρ* ι κ v σ*)))
                (set (ev e0 ρ* σ* (cons (letreck a e1 ρ*) ι) κ))))
          (set)))
        ((ev («set!» _ x ae) ρ σ ι κ)
         (let* ((v (eval-atom ae ρ σ))
                (a (env-lookup ρ («id»-x x)))
                (σ* (store-update σ a v)))
           (cons (set (ko ι κ v σ*))
                     (set))))
        ((ev («quo» _ e) ρ σ ι κ)
         (match-let (((cons v σ) (alloc-literal e σ)))
           (cons (set (ko ι κ v σ)) (set))))
        ((ev (and («app» _ rator rands) e) ρ σ ι κ)
         (cons
          (let ((v (eval-atom rator ρ σ)))
            (let rands-loop ((rands rands) (rvs '()))
              (if (null? rands)
                  (for/fold ((states (set))) ((w (γ v)))
                    (match w
                      ((clo («lam» _ x e0) ρ**)
                       (let* ((A (stack-addresses ι κ))
                              (τ (ctx e w rvs σ A)))
                         
                         (define (bind-loop x vs ρ* σ*)
                           (match x
                             ('()
                              (stack-alloc! τ (cons ι κ))
                              (set-union states (set (ev e0 ρ* σ* '() τ))))
                             ((cons x xs)
                              (if (null? vs)
                                  (set)
                                  (let ((a (alloc x e)))
                                    (bind-loop xs (cdr vs) (env-bind ρ* («id»-x x) a) (store-alloc σ* a (car vs))))))))
                         
                         
                         (bind-loop x (reverse rvs) ρ** σ)))
                      ((prim _ proc)
                       (set-union states (list->set (set-map (proc e (reverse rvs) σ ι κ Ξ) (lambda (vσ) (ko ι κ (car vσ) (cdr vσ)))))))
                      ((prim2 _ proc)
                       (set-union states (set (ko ι κ (apply proc (reverse rvs)) σ))))
                      (_ (set))))
                  (let ((v (eval-atom (car rands) ρ σ)))
                    (rands-loop (cdr rands) (cons v rvs))))))
          (set)))
        ((ko (cons (haltk) _) #f v _)
         (cons (set) (set)))
        ((ko ι κ v σ)
         (let* ((ικGs (stack-pop ι κ Ξ (set))))
           (let loop ((ικGs ικGs) (states (set)) (invs (set)))
             (if (set-empty? ικGs)
                 (cons states invs)
                 (let* ((ικG (set-first ικGs))
                        (ι (car ικG))
                        (κ (cadr ικG))
                        (s (apply-local-kont ι κ v σ)))
                   (loop (set-rest ικGs)
                         (set-add states s)
                             invs))))))
        )) ; end step
    
    (define visited (mutable-set))
    (define graph (make-hash))
    (define states (mutable-set))
    (define initial (inject e))
    (define (make-system duration exit msg)
      (system (list->vector (set->list states)) duration initial graph Ξ ⊥ ⊔ answer? exit msg))
    
    ;(define state-limit (STATELIMIT))
    (define time-limit (+ (current-milliseconds) (* (TIMELIMIT) 60000)))
    
    (let ((start (current-milliseconds)))
      (with-handlers ((exn:fail? (lambda (exc) (make-system (- (current-milliseconds) start) 'error exc)))) 
        (let loop ((todo (set initial)))
          (if (and (zero? (remainder (set-count states) 1000))
                   (> (current-milliseconds) time-limit))
              (make-system (- (current-milliseconds) start) 'user "time out")
              (if (set-empty? todo)
                  (make-system (- (current-milliseconds) start) 'ok "")
                  (let* ((q (set-first todo)))
                    (if (set-member? visited q)
                        (loop (set-rest todo))
                        (let ((old-Ξi Ξi))
                          ;(printf "q ~a\n" (state->statei q))
                          (set-add! visited q)
                          (match-let (((cons new-states2 invs) (step q)))
                            (let ((new-states-gc 
                                   (list->set (set-map new-states2 (lambda (q)
                                                                     (gc q Ξ γ))))))
                              ;(printf "-> ~a\n" (set-map new-states-gc state->statei))
                              (set-add! states q)
                              (let* ((existing (hash-ref graph q (set)))
                                     (updated (set-union existing new-states-gc)))
                                (hash-set! graph q updated))
                              (when (> Ξi old-Ξi)
                                (set-clear! visited))
                                  (loop (set-union new-states-gc (set-rest todo)))                                
                                  ))))))))))) ; end explore  
  (define (answer? s)
    (match s
      ((ko (cons (haltk) _) _ v _) #t)
      (_ #f)))
  
  explore)

(define (answer-set sys)
  (let ((answer? (system-answer? sys)))
    (for/fold ((v (set))) ((s (system-states sys)))
      (if (answer? s)
          (set-add v s)
          v))))

(define (answer-value sys)
  (let* ((⊥ (system-⊥ sys))
         (⊔ (system-⊔ sys)))
    (for/fold ((v ⊥)) ((s (answer-set sys)))
      (⊔ (ko-v s) v))))
;;

;; allocators
(define conc-alloc-counter 0)
(define conc-alloc
  (lambda (_ __)
    (set! conc-alloc-counter (add1 conc-alloc-counter))
    conc-alloc-counter))

(define (mono-alloc x _)
  x)

(define (poly-alloc x ctx)
  (cons x ctx))
;  (cons x (if ctx
;              (clo-λ (ctx-clo ctx))
;              ctx)))
;;

;; Store updates
(define (weak-update σ a v)
  (hash-set σ a (type-⊔ (hash-ref σ a) v)))

(define (strong-update σ a v)
  (hash-set σ a v))

(include "lattice.rkt")
(include "test.rkt")

;; machines and evaluators
(define (do-eval e mach)
  (let ((sys (mach e)))
    (if (eq? (system-exit sys) 'ok)
        (answer-value sys)
        (raise (system-msg sys)))))

(define conc-mach (make-machine conc-global conc-α conc-γ conc-⊥ conc-⊔ conc-alloc strong-update conc-true? conc-false? conc-eq?))
(define type-mach-0 (make-machine type-global type-α type-γ type-⊥ type-⊔ mono-alloc weak-update type-true? type-false? type-eq?))
(define type-mach-1 (make-machine type-global type-α type-γ type-⊥ type-⊔ poly-alloc weak-update type-true? type-false? type-eq?))

(define (conc-eval e)
  (do-eval e conc-mach))
(define (type-eval-0 e)
  (do-eval e type-mach-0))
(define (type-eval-1 e)
  (do-eval e type-mach-1))
;;
(define (parent-scope-declaration? decl e ast)
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
  
(define (purity-analysis system)
  (let* ((graph (system-graph system))
         (Ξ (system-Ξ system))
         (initial (system-initial system))
         (ast (ev-e initial)))
    
    (define (traverse S W C)
      (if (set-empty? W)
          C
          (let ((state (set-first W)))
            (if (set-member? S state)
                (traverse S (set-rest W) C)
                (let ((update? #f)
                      (successors (hash-ref graph state)))

                  ;(printf "\n\n~a\n" state)                
                  
                  (define (mark-proc C clo)
                    (let ((current-class (hash-ref C clo)))
                      (if (eq? current-class "PROC")
                          C
                          (begin
                            (set! update? #t)
                            (hash-set C clo "PROC")))))
                  
                  (define (handle-state state C)
                    (match state
                      ((ev («set!» _ x ae) ρ _ _ κ)
                       (let ((a (env-lookup ρ («id»-x x)))
                             (ctxs (stack-contexts κ Ξ))
                             (decl (get-declaration («id»-x x) (ev-e state) ast)))
                         (let stack-walk ((ctxs ctxs) (C C))
                           (if (set-empty? ctxs)
                               C
                               (let* ((τ (set-first ctxs))
                                      (clo (ctx-clo τ))
                                      (λ (clo-λ clo)))
                                 (if (parent-scope-declaration? decl λ ast)
                                     ;(printf "in outer scope ~a ~a: marking ~a proc\n" decl λ clo)
                                     (let ((C* (mark-proc C clo)))
                                       (stack-walk (set-rest ctxs) C*))
                                     (stack-walk (set-rest ctxs) C)))))))
                      (_ C)))
                  
                  (let ((C* (handle-state state C)))
                    (traverse (if update? (set) (set-add S state)) (set-union (set-rest W) successors) C*))))))
      ); end traverse
    (let ((C
           (for/hash ((κ (hash-keys Ξ)))
             (let ((clo (ctx-clo κ)))
               (values clo "RT")))))
      (traverse (set) (set initial) C))))
;;


(define (memo-test . ens)
  
  (when (null? ens)
    (set! ens '(fac fib fib-mut blur eta mj09 gcipd kcfa2 kcfa3 rotate loop2 sat ;'small' benchies
                          ;sat collatz rsa primtest factor
                          ))) 
  
  
  (printf "Warmup...\n\n")
  (type-mach-0 (file->value "test/fac.scm") )
  (type-mach-0 (file->value "test/eta.scm") )
  (type-mach-0 (file->value "test/rotate.scm"))
  (type-mach-0 (file->value "test/mj09.scm"))
  (type-mach-1 (file->value "test/loop2.scm"))
  (type-mach-1 (file->value "test/kcfa2.scm"))
  (type-mach-1 (file->value "test/fib.scm"))
  (type-mach-1 (file->value "test/kcfa3.scm"))
  
  (printf "Benchmarks: ~a\n" ens)
  (for/list ((en ens))
    (for/list ((mach (list type-mach-0 type-mach-1)))
      ;    (for/list ((mach (list conc-mach conc-mach-summ conc-mach-rt)))
      (let ((e (eval en)))
        (perform-benchmark en e mach)))))

(define server-results #f)
(define size-results #f)
(define time-results #f)
(define (server-test)
  (parameterize ((TIMELIMIT 30) (THROW #f))
    (let ((results (apply memo-test '(fac fib fib-mut blur eta mj09 gcipd kcfa2 kcfa3 rotate loop2
                                          sat collatz rsa primtest factor regex nqueens mceval boyer dderiv))))
      (set! server-results results)
      (set! size-results results)
      (set! time-results (filter (lambda (bench) (member (benchmark-name bench) '(sat collatz rsa primtest factor regex nqueens dderiv mceval boyer))) results))
      (printf "All results in server-results\nSize benchmarks in size-results\nTime benchmarks in time-results\n"))))

(define (purity-test)
  (define (test e expected)
    (let* ((C (purity-analysis (type-mach-0 e)))
           (C* (make-hash (hash-map C (lambda (k v) (cons («lam»-l (clo-λ k)) v))))))
      (unless (equal? (make-hash expected) C*)
          (printf "error ~a\n~a ~a\n" e expected C*))))
  (test fac '((2 . "RT")))
  (test fib '((2 . "RT")))
  (test fib-mut '((2 . "RT") (12 . "PROC")))
  (test blur '((2 . "RT") (7 . "RT") (12 . "RT")))
  (test eta '((29 . "RT") (17 . "RT") (6 . "RT") (2 . "RT")))
  (test mj09 '((6 . "RT") (11 . "RT") (25 . "RT") (2 . "RT")))
  (test gcipd '((2 . "RT") (7 . "RT") (35 . "RT")))
  (test kcfa2 '((2 . "RT") (6 . "RT") (10 . "RT")))
  (test kcfa3 '((2 . "RT") (6 . "RT") (10 . "RT") (14 . "RT")))
  (test rotate '((2 . "RT")))
  (test loop2 '((2 . "RT") (16 . "RT") (57 . "RT")))
  (test '(let ((z #f)) (let ((f (lambda () (set! z #t)))) (f))) '((5 . "PROC")))
  (test '(let ((z #f)) (let ((h (lambda () (set! z #t)))) (let ((g (lambda () (h)))) (let ((f (lambda () (g)))) (f))))) '((5 . "PROC") (11 . "PROC") (16 . "PROC")))
  (test '(let ((z #f)) (let ((f (lambda () (let ((g (lambda () (let ((h (lambda () (set! z #t)))) (h))))) (g))))) (f))) '((5 . "PROC") (8 . "PROC") (11 . "PROC")))
  (test '(let ((f (lambda () (let ((z #f)) (let ((g (lambda () (let ((h (lambda () (set! z #t)))) (h))))) (g)))))) (f)) '((2 . "RT") (8 . "PROC") (11 . "PROC")))
  (test '(letrec ((f (lambda () (let ((z #f)) (let ((g (lambda () (let ((u (set! z #t))) (f))))) (g)))))) (f)) '((2 . "RT") (8 . "PROC")))
  (test '(letrec ((f (lambda () (let ((z #f)) (let ((g (lambda () (set! z #t)))) (let ((u (g))) (f))))))) (f)) '((2 . "RT") (8 . "PROC")))
  (test '(let ((f (lambda (x) (let ((xx #f)) (let ((u (set! xx x))) xx))))) (let ((v (f 123))) (f v))) '((2 . "RT")))
  (test '(letrec ((f (lambda (n) (let ((m (- n 1))) (f m))))) (f 123)) '((2 . "RT")))
  (test '(letrec ((f (lambda (n) (let ((m (- n 1))) (let ((u (set! n m))) (f n)))))) (f 123)) '((2 . "RT")))
  (test '(letrec ((f (lambda (n) (let ((u (set! n 333))) (f n))))) (f 123)) '((2 . "RT")))
  )


(include "output.rkt")



