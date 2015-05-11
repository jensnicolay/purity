(let ((f (lambda ()
           (if #f
               (let ((x 0))
                 (let ((y 1))
                   (let ((z 2))
                     123)))
               "abc"))))
  (let ((u (f)))
    (f)))
               