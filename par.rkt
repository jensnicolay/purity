#lang racket

(provide main)

(define (fib n)
  (if (< n 2)
      n
      (+ (fib (- n 1)) (fib (- n 2)))))

(define (main)
  (place ch
         (define l (place-channel-get ch))
         (place-channel-put ch (l))))
