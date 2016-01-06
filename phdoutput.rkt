#lang racket

(require "general.rkt")
(require "ast.rkt")
(require "lattice.rkt")
(require "cesk.rkt")
(require "test.rkt")
(require "purity.rkt")
(require "purity-test.rkt")

(define (~time ms)
  (~a
   (if (< ms 1000)
       "\\eps"
       (format "~a''" (inexact->exact (round (/ ms 1000)))))
   #:min-width 5))

(define (~perc n)
  (~a
   (format "~a\\%" (exact->inexact (/ (round (* n 10000)) 100))) #:min-width 7))

;;;;;;;;
(define (print-flow-row name result)
  (define flow-time (hash-ref result 'flow-time))
  (define state-count (hash-ref result 'state-count))
  (define edge-count (hash-ref result 'edge-count))
  (printf "\\code{~a} & ~a & ~a & ~a\\\\\n"
          (~a name #:min-width 14)
          (~time flow-time)
          (~a state-count #:min-width 7)
          (~a edge-count #:min-width 7)))

(define (print-flow-conc)
  (printf "flow-conc\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (results (cadr r)))
         (print-flow-row benchmark-name results))))
  
(define (print-flow-type)
  (printf "flow-type\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (results (caddr r)))
         (print-flow-row benchmark-name results))))
  
;;;;;;;;;

(define (print-se-row name result)
  (define eff-ctx-count (hash-ref result 'eff-ctx-count))
  (define eff-ctx-obs-count (hash-ref result 'eff-ctx-obs-count))
  (printf "\\code{~a} & ~a & ~a & ~a & ~a\\\\\n"
                 (~a name #:min-width 14)
                 (~time (hash-ref result 'side-effect-time))
                 (~a (hash-ref result 'eff-count) #:min-width 5)
                 (~a eff-ctx-count #:min-width 5)
                 (~a eff-ctx-obs-count #:min-width 5)
                 ))

(define (print-se-a-conc-result)
  (printf "se-a-conc\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (results (cadr r))
              (a-result (hash-ref results 'a)))
         (print-se-row benchmark-name a-result))))

(define (print-se-a-type-result)
  (printf "se-a-type\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (results (caddr r))
              (a-result (hash-ref results 'a)))
         (print-se-row benchmark-name a-result))))

;;;;;;;;;;

(define (print-se-conc-type-perc-row name conc-result type-result)
  (define conc-eff-ctx-count (hash-ref conc-result 'eff-ctx-count))
  (define conc-eff-ctx-obs-count (hash-ref conc-result 'eff-ctx-obs-count))
  (define type-eff-ctx-count (hash-ref type-result 'eff-ctx-count))
  (define type-eff-ctx-obs-count (hash-ref type-result 'eff-ctx-obs-count))
  (printf "\\code{~a} & ~a & ~a\\\\\n"
          (~a name #:min-width 14)
          (~perc (/ conc-eff-ctx-obs-count conc-eff-ctx-count))
          (~perc (/ type-eff-ctx-obs-count type-eff-ctx-count))
          ))

(define (print-se-a-conc-type-perc)
  (printf "se-a-conc-type-perc\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (conc-results (cadr r))
              (type-results (caddr r))
              (conc-result (hash-ref conc-results 'a))
              (type-result (hash-ref type-results 'a)))
         (print-se-conc-type-perc-row benchmark-name conc-result type-result))))

(define (print-se-msfa-conc-type-perc)
  (printf "se-msfa-conc-type-perc\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (conc-results (cadr r))
              (type-results (caddr r))
              (conc-result (hash-ref conc-results 'msfa))
              (type-result (hash-ref type-results 'msfa)))
         (print-se-conc-type-perc-row benchmark-name conc-result type-result))))  


;;;;;;;;;;

(define (print-se-percs-row name conc-result a-type-result sa-type-result sfa-type-result msfa-type-result)
  (define conc-eff-ctx-count (hash-ref conc-result 'eff-ctx-count))
  (define conc-eff-ctx-obs-count (hash-ref conc-result 'eff-ctx-obs-count))
  (define a-type-eff-ctx-count (hash-ref a-type-result 'eff-ctx-count))
  (define a-type-eff-ctx-obs-count (hash-ref a-type-result 'eff-ctx-obs-count))
  (define sa-type-eff-ctx-count (hash-ref sa-type-result 'eff-ctx-count))
  (define sa-type-eff-ctx-obs-count (hash-ref sa-type-result 'eff-ctx-obs-count))
  (define sfa-type-eff-ctx-count (hash-ref sfa-type-result 'eff-ctx-count))
  (define sfa-type-eff-ctx-obs-count (hash-ref sfa-type-result 'eff-ctx-obs-count))
  (define msfa-type-eff-ctx-count (hash-ref msfa-type-result 'eff-ctx-count))
  (define msfa-type-eff-ctx-obs-count (hash-ref msfa-type-result 'eff-ctx-obs-count))
  (printf "\\code{~a} & ~a & ~a & ~a & ~a & ~a\\\\\n"
          (~a name #:min-width 14)
          (~perc (/ conc-eff-ctx-obs-count conc-eff-ctx-count))
          (~perc (/ a-type-eff-ctx-obs-count a-type-eff-ctx-count))
          (~perc (/ sa-type-eff-ctx-obs-count sa-type-eff-ctx-count))
          (~perc (/ sfa-type-eff-ctx-obs-count sfa-type-eff-ctx-count))
          (~perc (/ msfa-type-eff-ctx-obs-count msfa-type-eff-ctx-count))
          ))

(define (print-se-percs)
  (printf "se-percs\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (conc-results (cadr r))
              (type-results (caddr r))
              (conc-result (hash-ref conc-results 'a))
              (a-type-result (hash-ref type-results 'a))
              (sa-type-result (hash-ref type-results 'sa))
              (sfa-type-result (hash-ref type-results 'sfa))
              (msfa-type-result (hash-ref type-results 'msfa))
              )
         (print-se-percs-row benchmark-name conc-result a-type-result sa-type-result sfa-type-result msfa-type-result))))

;;;;;;;;;;;;;;;;;

(define (main)

  (purity-test)

  ; Setting
  (print-flow-conc)
  (print-flow-type)

  ; Side-effects
  (print-se-a-conc-result)
  (print-se-a-type-result)
  ;(print-se-a-conc-type-perc)
  ;(print-se-msfa-conc-type-perc)
  (print-se-percs)

  )



