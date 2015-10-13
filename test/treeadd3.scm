  (letrec ((create-tree (lambda (levels)
                          (let ((c (= levels 0)))
                                (if c
                                    'null
                                    (let ((n (cons 'null 'null)))
                                      (let ((levels* (- levels 1)))
                                        (let ((left (create-tree levels*)))
                                          (let ((ul (set-car! n left)))
                                              (let ((right (create-tree levels*)))
                                                (let ((ur (set-cdr! n right)))
                                                  n))))))))))) 
    (letrec ((add-tree (lambda (node)
                         (let ((total 1))
                           (let ((left (car node)))
                             (let ((lc (eq? left 'null)))
                               (let ((ul (if lc
                                             #f
                                             (let ((total-left (add-tree left)))
                                               (let ((total* (+ total total-left)))
                                                 (set! total total*))))))
                                 (let ((right (cdr node)))
                                   (let ((rc (eq? left 'null)))
                                     (let ((ur (if rc
                                                   #f
                                                   (let ((total-right (add-tree right)))
                                                     (let ((total* (+ total total-right)))
                                                       (set! total total*))))))
                                       total))))))))))
      (let ((tree (create-tree 4)))
        (add-tree tree))))
                                                     
                                       
    
                              