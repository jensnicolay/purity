  (define (prim-cons e rands σ ι κ Ξ)
    (if (= (length rands) 2)
        (let* ((a (alloc "!%cons" e))
               (v (α (cons (car rands) (cadr rands))))
               (σ* (store-alloc σ a v)))
          (set (cons (α (addr a)) σ*)))
        (set)))

  (define (prim-car e rands σ ι κ Ξ)
    (if (= (length rands) 1)
        (for/fold ((states (set))) ((w (γ (car rands))))
          (match w
            ((addr a)
             (set-union states 
                        (for/fold ((states2 (set))) ((ww (γ (store-lookup σ a))))
                          (match ww
                            ((cons v _) (set-add states2 (cons v σ)))
                            (_ states2)))))
            (_ states)))
        (set)))

  (define (prim-set-car! e rands σ ι κ Ξ)
    (if (= (length rands) 2)
        (for/fold ((states (set))) ((w (γ (car rands))))
          (match w
            ((addr a)
             (set-union states 
                        (for/fold ((states2 (set))) ((ww (γ (store-lookup σ a))))
                          (match ww
                            ((cons _ vcdr)
                             (let ((σ* (store-update σ a (α (cons (cadr rands) vcdr)))))
                               (set-add states2 (cons (cadr rands) σ*))))
                            (_ states2)))))
            (_ states)))
        (set)))

  (define (prim-cdr e rands σ ι κ Ξ)
    (if (= (length rands) 1)
        (for/fold ((states (set))) ((w (γ (car rands))))
          (match w
            ((addr a)
             (set-union states 
                        (for/fold ((states2 (set))) ((ww (γ (store-lookup σ a))))
                          (match ww
                            ((cons _ v) (set-add states2 (cons v σ)))
                            (_ states2)))))
            (_ states)))
        (set)))

  (define (prim-set-cdr! e rands σ ι κ Ξ)
    (if (= (length rands) 2)
        (for/fold ((states (set))) ((w (γ (car rands))))
          (match w
            ((addr a)
             (set-union states 
                        (for/fold ((states2 (set))) ((ww (γ (store-lookup σ a))))
                          (match ww
                            ((cons vcar _)
                             (let ((σ* (store-update σ a (α (cons vcar (cadr rands))))))
                               (set-add states2 (cons (cadr rands) σ*))))
                            (_ states2)))))
            (_ states)))
        (set)))

  (define (prim-pair e rands σ ι κ Ξ)
    (if (= (length rands) 1)
        (let ((v (for/fold ((v ⊥)) ((w (γ (car rands))))
                   (match w
                     ((addr a)
                      (for/fold ((v2 v)) ((ww (γ (store-lookup σ a))))
                        (match ww
                             ((cons _ _) (⊔ v2 (α #t)))
                             (_ (⊔ v2 (α #f))))))
                     (_ (⊔ v (α #f)))))))
          (set (cons v σ)))
        (set)))  

  (define (prim-to-string e rands σ ι κ Ξ)
    (define (helper v seen)
      (match v
        ((addr a)
         (if (set-member? seen a)
             (set (cons (α (~a v)) σ))
             (begin
               (apply set-union (set-map (γ (store-lookup σ a)) (lambda (w) (helper w (set-add seen a))))))))
        ((cons v1 v2)
         (let ((s1 (helper v1 seen))
               (s2 (helper v2 seen)))
           (for*/set ((sσ1 s1) (sσ2 s2))
             (cons (α (~a (cons (car sσ1) (car sσ2)))) σ))))
        (_ (set (cons (α (~a v)) σ)))))
    (if (= (length rands) 1)
        (apply set-union (set-map (γ (car rands)) (lambda (w) (helper w (set)))))
        (set)))

  (define (eq?-helper v1 v2 σ)
    (match* (v1 v2)
      (((addr a1) (addr a2))
       (α (equal? a1 a2)))
      ((_ _) (α-eq? v1 v2))))

  (define (prim-eq? e rands σ ι κ Ξ)
    (if (= (length rands) 2)
        (let* ((w1 (γ (car rands)))
               (w2 (γ (cadr rands)))
               (v (for*/fold ((v ⊥)) ((v1 w1) (v2 w2)) (⊔ v (eq?-helper v1 v2 σ)))))
          (set (cons v σ)))
        (set)))

  (define (prim-error e rands σ ι κ Ξ)
    (set))
