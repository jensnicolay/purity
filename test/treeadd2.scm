(let ((tree-node (lambda ()
                   (let ((c1 (cons 'null 'null)))
                     (cons 1 c1)))))
  (letrec ((create-tree (lambda (levels)
                          (let ((c (= levels 0)))
                                (if c
                                    'null
                                    (let ((n (tree-node)))
                                      (let ((levels* (- levels 1)))
                                        (let ((lr (cdr n)))
                                          (let ((left (create-tree levels*)))
                                            (let ((ul (set-car! lr left)))
                                              (let ((right (create-tree levels*)))
                                                (let ((ur (set-cdr! lr right)))
                                                  n)))))))))))) 
    (letrec ((add-tree (lambda (node)
                         (let ((total (car node)))
                           (let ((leftright (cdr node)))
                             (let ((left (car leftright)))
                               (let ((lc (eq? left 'null)))
                                 (let ((ul (if lc
                                               #f
                                               (let ((total-left (add-tree left)))
                                                 (let ((total* (+ total total-left)))
                                                   (set! total total*))))))
                                   (let ((right (cdr leftright)))
                                     (let ((rc (eq? left 'null)))
                                       (let ((ur (if rc
                                                     #f
                                                     (let ((total-right (add-tree right)))
                                                       (let ((total* (+ total total-right)))
                                                         (set! total total*))))))
                                         total)))))))))))
      (let ((tree (create-tree 4)))
        (add-tree tree)))))
                                                     
                                       
    
                              