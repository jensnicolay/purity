  (define (prim-cons e rands ι κ Ξ)
    (if (= (length rands) 2)
        (let* ((a (alloc e e))
               (v (α (cons (car rands) (cadr rands)))))
          (store-alloc! a v)
          (set (list (α (addr a)) (set (fr)))))
        (set)))

  (define (prim-car e rands ι κ Ξ)
    (if (= (length rands) 1)
        (let-values (((v E)
                      (for/fold ((v ⊥) (E (set))) ((w (γ (car rands))))
                        (match w
                          ((addr a)
                           (values (for/fold ((v v)) ((ww (γ (store-lookup σ a))))
                                     (match ww
                                       ((cons v-car _) (⊔ v v-car))
                                       (_ v)))
                                   (set-add E (rp a "car" (car («app»-aes e))))))
                          (_ (values v E))))))
          (set (list v E)))
        (set)))

  (define (prim-cdr e rands ι κ Ξ)
    (if (= (length rands) 1)
        (let-values (((v E)
                      (for/fold ((v ⊥) (E (set))) ((w (γ (car rands))))
                        (match w
                          ((addr a)
                           (values (for/fold ((v v)) ((ww (γ (store-lookup σ a))))
                                     (match ww
                                       ((cons _ v-cdr) (⊔ v v-cdr))
                                       (_ v)))
                                   (set-add E (rp a "cdr" (car («app»-aes e))))))
                          (_ (values v E))))))
          (set (list v E)))
        (set)))

                        
(define (prim-set-car! e rands ι κ Ξ)
    (if (= (length rands) 2)
        (let ((E
               (for/fold ((E (set))) ((w (γ (car rands))))
                 (match w
                   ((addr a)
                    (for/fold ((E E)) ((ww (γ (store-lookup σ a))))
                      (match ww
                        ((cons _ v-cdr)
                         (store-update! a (α (cons (cadr rands) v-cdr)))
                         (set-add E (wp a "car" (car («app»-aes e)))))
                        (_ E))))
                   (_ E)))))
          (if (set-empty? E) (set) (set (list (α 'undefined) E))))
        (set)))

(define (prim-set-cdr! e rands ι κ Ξ)
  (if (= (length rands) 2)
      (let ((E
             (for/fold ((E (set))) ((w (γ (car rands))))
               (match w
                 ((addr a)
                  (for/fold ((E E)) ((ww (γ (store-lookup σ a))))
                    (match ww
                      ((cons v-car _)
                       (store-update! a (α (cons v-car (cadr rands))))
                       (set-add E (wp a "cdr" (car («app»-aes e)))))
                      (_ E))))
                 (_ E)))))
        (if (set-empty? E) (set) (set (list (α 'undefined) E))))
      (set)))

  (define (prim-pair e rands ι κ Ξ)
    (if (= (length rands) 1)
        (let ((v (for/fold ((v ⊥)) ((w (γ (car rands))))
                   (match w
                     ((addr a)
                      (for/fold ((v v)) ((ww (γ (store-lookup σ a))))
                        (⊔ v (α (pair? ww)))))
                     (_ (α #f))))))
          (set (list v (set))))
        (set)))

  (define (prim-to-string e rands ι κ Ξ)
    (define (helper v seen)
      (match v
        ((addr a)
         (if (set-member? seen a)
             (set (list (α (~a v)) (set)))
             (begin
               (apply set-union (set-map (γ (store-lookup σ a)) (lambda (w) (helper w (set-add seen a))))))))
        ((cons v1 v2)
         (let ((s1 (helper v1 seen))
               (s2 (helper v2 seen)))
           (for*/set ((sσ1 s1) (sσ2 s2))
             (list (α (~a (cons (car sσ1) (car sσ2)))) (set)))))
        (_ (set (list (α (~a v)) (set))))))
    (if (= (length rands) 1)
        (apply set-union (set-map (γ (car rands)) (lambda (w) (helper w (set)))))
        (set)))

  (define (eq?-helper v1 v2)
    (match* (v1 v2)
      (((addr a1) (addr a2))
       (α (equal? a1 a2)))
      ((_ _) (α-eq? v1 v2))))

  (define (prim-eq? e rands ι κ Ξ)
    (if (= (length rands) 2)
        (let* ((w1 (γ (car rands)))
               (w2 (γ (cadr rands)))
               (v (for*/fold ((v ⊥)) ((v1 w1) (v2 w2)) (⊔ v (eq?-helper v1 v2)))))
          (set (list v (set))))
        (set)))

  (define (prim-error e rands ι κ Ξ)
    (set))
