(let ((f (lambda (x)
           (car x))))
  (let ((g (lambda (y)
             (let ((c (cons y 2)))
               (f c)))))
    (let ((u (g "hey")))
      (g 123))))
    
               