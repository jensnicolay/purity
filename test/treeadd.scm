(let ((tree-node (lambda (v l r)
                   (let ((c1 (cons l r)))
                     (cons v c1)))))
  (letrec ((make-tree-nodes (lambda (levels)
                              (let ((c (<= levels 1)))
                                (if c
                                    (tree-node 1 'null 'null)
                                    (let ((levels* (- levels 1)))
                                      (let ((left (make-tree-nodes levels*)))
                                        (let ((right (make-tree-nodes levels*)))
                                          (tree-node 1 left right)))))))))
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
      (let ((tree (make-tree-nodes 4)))
        (add-tree tree)))))
                                                     
                                       
    
                              