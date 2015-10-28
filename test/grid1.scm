(letrec ((make-grid (lambda (start dims)
                                  (let ((v (make-vector dims start)))
                                    (let ((_43 (zero? dims)))
                                      (let ((_44 (not _43)))
                                        (let ((_54 (if _44
                                                       (letrec ((loop (lambda (i)
                                                                        (let ((_45 dims))
                                                                          (let ((_46 (>= i _45)))
                                                                            (if _46
                                                                                #t
                                                                                (let ((_47 (- dims 1)))
                                                                                  (let ((_50 (make-grid start _47)))
                                                                                    (let ((_51 (vector-set! v i _50)))
                                                                                      (let ((_53 (+ i 1)))
                                                                                        (loop _53)))))))))))
                                                         (loop 0))
                                                       #t)))
                                          v)))))))
              (make-grid 0 2))