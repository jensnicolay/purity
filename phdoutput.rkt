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

(define (print-se-result name result)
  (printf "\\code{~a} & ~a & ~a & ~a & ~a\\\\\n"
                 (~a name #:min-width 14)
                 (~time (hash-ref result 'side-effect-time))
                 (~a (hash-ref result 'eff-count) #:min-width 5)
                 (~a (hash-ref result 'eff-ctx-count) #:min-width 5)
                 (~a (hash-ref result 'eff-ctx-obs-count) #:min-width 5)))

(define (print-se-a-conc-result)
  (printf "se-a-conc\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (results (cadr r))
              (a-result (hash-ref results 'a)))
         (print-se-result benchmark-name a-result))))

(define (print-se-a-type-result)
  (printf "se-a-type\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (results (caddr r))
              (a-result (hash-ref results 'a)))
         (print-se-result benchmark-name a-result))))
#|
(define (check-se-soundness)
  (printf "se-soundness\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (conc-results (cadr r))
              (type-results (caddr r))
              (a-conc-results (hash-ref conc-results 'a))
              (sa-conc-results (hash-ref conc-results 'sa))
              (sfa-conc-results (hash-ref conc-results 'sfa))
              (msfa-conc-results (hash-ref conc-results 'msfa))
              (a-type-results (hash-ref type-results 'a))
              (sa-type-results (hash-ref type-results 'sa))
              (sfa-type-results (hash-ref type-results 'sfa))
              (msfa-type-results (hash-ref type-results 'msfa)))

         ; (SOUNDNESS) all conc results must be equal
       (unless (equal? conc-a-lam->summary conc-sa-lam->summary)
         (error "conc-sa"))
       (unless (equal? conc-a-lam->summary conc-sfa-lam->summary)
         (error "conc-sfa"))
       (unless (equal? conc-a-lam->summary conc-msfa-lam->summary)
         (error "conc-msfa"))

       ; (SOUNDNESS) all type results must subsume conc results
       (unless (se-subsumes? type-a-lam->summary conc-a-lam->summary)
         (error "type-a"))
       (unless (se-subsumes? type-sa-lam->summary conc-a-lam->summary)
         (error "type-sa"))
       (unless (se-subsumes? type-sfa-lam->summary conc-a-lam->summary)
         (error "type-sfa"))
       (unless (se-subsumes? type-msfa-lam->summary conc-a-lam->summary)
         (error "type-msfa"))

       ; (USEFULNESS) extra analyses must improve results (less-optimized subsumes more-optimized)
       (unless (se-subsumes? type-a-lam->summary type-sa-lam->summary)
         (error "type-a -> sa"))
       (unless (se-subsumes? type-sa-lam->summary type-sfa-lam->summary)
         (error "type-sa -> sfa"))
       (unless (se-subsumes? type-sfa-lam->summary type-msfa-lam->summary)
         (error "type-sfa -> msfa"))
         )))
|#


(define (main)

  (purity-test)
  
  (print-se-a-conc-result)
  (print-se-a-type-result)

  )