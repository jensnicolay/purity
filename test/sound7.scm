(let ((f (lambda (x)
           (let ((c (> x 0)))
             (if c
                 123
                 "abc")))))
  (let ((u (f -1)))
    (f 1)))