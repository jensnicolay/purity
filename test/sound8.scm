(let ((a 123))
  (let ((b "abc"))
    (let ((f (lambda (x)
               (let ((c (< x 0)))
                 (if c
                     b
                     a)))))
      (let ((u (f -1)))
        (let ((v (set! b #f)))
          (f 1))))))