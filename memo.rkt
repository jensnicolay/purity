#lang racket

(require "general.rkt")
(require "ast.rkt")
(require "lattice.rkt")
(require "cesk.rkt")
(require "purity.rkt")
(require "test.rkt")

(provide (all-defined-out))

(define (memoize f)
  (let ((cache (make-hash)))
    (lambda args
      (hash-ref cache args (lambda ()
                             (let ((value (apply f args)))
                               (hash-set! cache args value)
                               value))))))
              
(define MRETVAL "mretval")
(struct memo-result (lam->summary time) #:transparent)
(define (memo-analysis sys state->ctx->side-effects)

  (define graph (system-graph sys))
  (define initial (system-initial sys))
  (define Ξ (system-Ξ sys))
  (define state-σ (system-state-σ sys))
  (define γ (lattice-γ (system-lattice sys)))
  (define ⊥ (lattice-⊥ (system-lattice sys)))
         
  (define parent (make-parent (ev-e initial)))

  (define lam->summary (hash))


  (define (add-effect! lam effect)
    ;(printf " OBS! ~a " («lam»-l lam))
    (define existing-effects (hash-ref lam->summary lam #f))
    (if existing-effects
        (unless (set-member? existing-effects effect)
          (set! lam->summary (hash-set lam->summary lam (set-add existing-effects effect))))
        (set! lam->summary (hash-set lam->summary lam (set effect)))))

  (define (add-read-dep res lam R)
    ;(printf " R ~a " («lam»-l lam))
    (hash-set R res (set-add (hash-ref R res (set)) lam)))

  (define (add-retval-dep a lam V)
    ;(printf " V ~a " («lam»-l lam))
    (hash-set V a (set-add (hash-ref V a (set)) lam)))

  (define (add-observer! res lam O)
    (when (set-member? (hash-ref O res (set)) lam)
      ;(printf "O lam ~a  res ~a\n" («lam»-l lam) res)
      (add-effect! lam OBSERVES)))

  (define (update-O-write res R O)
    (let ((λ-rs (hash-ref R res (set))))
      (for/fold ((O O)) ((λ-r λ-rs))
        ;(printf " O ~a " («lam»-l λ-r))
        (hash-set O res (set-add (hash-ref O res (set)) λ-r)))))

  (define (add-mretval! a V)
    (let ((λ-vs (hash-ref V a (set))))
      (for ((λ-v λ-vs))
           (printf " V ~a " («lam»-l λ-v))
        (add-effect! λ-v MRETVAL))))

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

  (define (handle-write-effect eff res ctx->side-effects R O V)
    (let ((O* (update-O-write res R O)))
      (walk-stack-write eff res ctx->side-effects)
      (values R O*)))

  (define (handle-effect eff ctx->side-effects R O V)
    ;(printf "\ns ~a effect ~a " (state->statei s) eff)
    (match eff
      ((wv a x)
       (add-mretval! a V)
       (handle-write-effect eff a ctx->side-effects R O V))
      ((wp a n x)
       (add-mretval! a V)
       (handle-write-effect eff (cons a n) ctx->side-effects R O V))
      ((rv a x)
       (handle-read-effect eff a ctx->side-effects R O))
      ((rp a n x)
       (handle-read-effect eff (cons a n) ctx->side-effects R O))
      (_ (values R O V))))

  (define (handle-state s V)
    (match s
      ((ko d σi ι κ)
         (if (eq? d ⊥)
             V
             (let* ((Ad (reachable (touches d) (state-σ σi) γ))
                    (ικGs (stack-pop ι κ Ξ (set))))
               (for/fold ((V V)) ((ικG ικGs))
                 (let* ((ι (car ικG))
                        (κ (cadr ικG))
                        (G (caddr ικG)))
                   (for/fold ((V V)) ((κ G))
                     (let ((lam (ctx-λ κ)))
                       (for/fold ((V V)) ((a Ad))
                         (add-retval-dep a lam V)))))))))
      (_ V)))

  (define (traverse-graph-precise)

    (define A-cache (hash))
    
    (define (dis R)
      (for/hash (((res lams) (in-hash R)))
           (values res (set-map lams (lambda (lam) («lam»-l lam))))))

               
;          (printf "\ns ~a\nR ~a\nO ~a\nafter\nR ~a\nO ~a\nseen\nR ~a\nO ~a\n" (state->statei s) (dis R) (dis O) (dis (car RO)) (dis (cdr RO))
 ;                 (if RO-S (dis (car RO-S)) #f) (if RO-S (dis (cdr RO-S)) #f))
    
    (define (traverse-graph S W)
      (unless (set-empty? W)
        (let* ((sROV (set-first W))
               (s (car sROV))
               (ROV-S (hash-ref S s #f))
               ;(RO (gcRO (cadr sRO) (cddr sRO) s)))
               (ROV (cdr sROV)))
          (if (equal? ROV-S ROV)
              (traverse-graph S (set-rest W))
              (let ((R (if ROV-S (hash-⊔ (car ROV) (car ROV-S) set-union (set)) (car ROV)))
                    (O (if ROV-S (hash-⊔ (cadr ROV) (cadr ROV-S) set-union (set)) (cadr ROV)))
                    (V (if ROV-S (hash-⊔ (caddr ROV) (caddr ROV-S) set-union (set)) (caddr ROV))))
                (let ((V* (handle-state s V)))
                  (let-values (((W*) (for/fold ((W (set-rest W))) ((t (hash-ref graph s (set))))
                                       (match t
                                         ((transition s* E)
                                          (let-values (((R* O*) (for/fold ((R R) (O O)) ((eff E))
                                                                  (handle-effect eff (hash-ref state->ctx->side-effects s) R O V))))
                                            (values (set-add W (cons s* (list R* O* V*))))))))))
                  (traverse-graph (hash-set S s ROV) W*))))))))
    (traverse-graph (hash) (set (cons initial (list (hash) (hash) (hash))))))
  
 
  (define (extend-to-applied lam->summary)
    (for/hash ((κ (hash-keys Ξ)))
              (let ((lam (ctx-λ κ)))
                (values lam (hash-ref lam->summary lam (set))))))

  (define start (current-milliseconds))
  (traverse-graph-precise)
  ;(traverse-graph (set) (set initial) (hash) (hash)))
  (define time (- (current-milliseconds) start))
  (memo-result (extend-to-applied lam->summary) time))

(define (a-memo sys)
  ;(generate-dot (system-graph sys) "a-purity")
  (printf "call-state analysis... ")
  (define csr (call-state-analysis sys))
  (define call-state-time (call-state-result-time csr))
  (printf "~a ms\n" call-state-time)
  (define ctx->addrs (call-state-result-ctx->addrs csr))
  (printf "a-side-effect analysis... ")
  (define a-ser (a-side-effect-analysis sys ctx->addrs))
  (define side-effect-time (side-effect-result-time a-ser))
  (printf "~a ms\n" side-effect-time)
  (printf "purity analysis... ")
  (define mr (memo-analysis sys (side-effect-result-state->ctx->side-effects a-ser)))
  (define memo-time (memo-result-time mr))
  (printf "~a ms\n" memo-time)
  (define lam->side-effect-summary (memo-result-lam->summary mr))
  (for (((lam side-effect-summary) lam->side-effect-summary))
       (printf "~a ~a\n" (~a lam #:max-width 50) side-effect-summary))
  (define ast (ev-e (system-initial sys)))
  (define sorted-lams (sort (lambdas ast) < #:key «lam»-l))
  (define initial (system-initial sys))
  (define r (rewrite-memo (ev-e initial) lam->side-effect-summary))
  r)


(define (rewrite-memo ast lam->side-effect-summary)
  (define (rewrite ast)
    (match ast
      ((«lam» l x e) (if (set-empty? (hash-ref lam->side-effect-summary ast (set #f)))
                         («app» 0 («id» 0 "memoize") (list («lam» l x (rewrite e))))
                         («lam» l x (rewrite e))))
      ((«let» l x e0 e1) («let» l x (rewrite e0) (rewrite e1)))
      ((«letrec» l x e0 e1) («letrec» l x (rewrite e0) (rewrite e1)))
      ((«if» l ae e1 e2) («if» l (rewrite ae) (rewrite e1) (rewrite e2)))
      ((«set!» l x ae) («set!» l x (rewrite ae)))
      ((«set-car!» l x ae) («set-car!» l x (rewrite ae)))
      ((«set-cdr!» l x ae) («set-cdr!» l x (rewrite ae)))
      ((«cons» l ae1 ae2) («cons» l (rewrite ae1) (rewrite ae2)))
      ((«make-vector» l ae1 ae2) («make-vector» l ae1 (rewrite ae2)))
      ((«vector-set!» l x ae1 ae2) («vector-set!» l x ae1 (rewrite ae2)))
      ((«app» l rator rands) («app» l (rewrite rator) (map rewrite rands)))
      (_ ast)))
  (rewrite ast))
