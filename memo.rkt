#lang racket
(define (memoize f)
  (let ((cache (make-hash)))
    (lambda args
      (hash-ref cache args (lambda ()
                             (let ((value (apply f args)))
                               (hash-set! cache args value)
                               value))))))
              
(define (fib n k)
  (if (< n 2)
      n
      (+ (fib (- n 1) k) (fib (- n 2) k))))

