(let ((f (lambda ()
           (let ((x (cons 1 2)))
             (lambda () x)))))
  (let ((f1 (f)))
    (let ((f2 (f)))
      (let ((c1 (f1)))
        (let ((u1 (set-car! c1 99)))
          (let ((c2 (f1)))
            (let ((c3 (f2)))
              (let ((car1 (car c2)))
                (let ((car2 (car c3)))
                  (+ car1 car2))))))))))                            