(let ((f (lambda (x)
           (let ((g (lambda ()
                      x)))
             (g)))))
  (let ((u (f 123)))
    (f "hiho")))
  