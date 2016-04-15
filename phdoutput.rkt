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

(define (~perc x y)
  (if (and (zero? x) (zero? y))
      (~a "0\\%" #:min-width 7)
      (~a
       (format "~a\\%" (/ (round (* (exact->inexact (/ x y)) 10000)) 100)) #:min-width 7)))

(define (~perc-r-0 x y)
  (if (and (zero? x) (zero? y))
      (~a "0\\%" #:min-width 7)
      (~a
       (format "~a\\%" (round (* (exact->inexact (/ x y)) 100)))  #:min-width 5)))

(define (~perc2 x y)
  (~a
   (format "~a/~a" x y) #:min-width 7))

;;;;;;;;
(define (print-benchmark-row name results)
  (define node-count (hash-ref results 'node-count))
  (define lam-count (hash-ref results 'lam-count))
  (define set!-count (hash-ref results 'set!-count))
  (define set-car!-count (hash-ref results 'set-car!-count))
  (define set-cdr!-count (hash-ref results 'set-cdr!-count))
  (define vector-set!-count (hash-ref results 'vector-set!-count))
  (define cons-count (hash-ref results 'cons-count))
  (define make-vector-count (hash-ref results 'make-vector-count))
  (printf "\\code{~a} & ~a & ~a & ~a & ~a & ~a & ~a & ~a & ~a\\\\\n"
          (~a name #:min-width 14)
          (~a node-count #:min-width 6)
          (~a lam-count #:min-width 3)
          (~a set!-count #:min-width 3)
          (~a cons-count #:min-width 3)
          (~a set-car!-count #:min-width 3)
          (~a set-cdr!-count #:min-width 3)
          (~a make-vector-count #:min-width 3)
          (~a vector-set!-count #:min-width 3)
          ))

(define (print-benchmarks)
  (printf "benchmarks\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (results (cadr r)))
         (print-benchmark-row benchmark-name results))))

;;;;;;;;
(define (print-flow-row name result)
  (define flow-time (hash-ref result 'flow-time))
  (define state-count (hash-ref result 'state-count))
  (define edge-count (hash-ref result 'edge-count))
  (define node-count (hash-ref result 'node-count))
  (define covered-count (hash-ref result 'covered-count))
  (printf "\\code{~a} & ~a & ~a & ~a & ~a\\\\\n"
          (~a name #:min-width 14)
          (~a state-count #:min-width 7)
          (~a edge-count #:min-width 7)
          (~perc covered-count node-count)
          (~time flow-time)
          ))

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
  (define eff-ctx-count (hash-ref result 'eff-fctx-count))
  (define eff-ctx-obs-count (hash-ref result 'eff-fctx-obs-count))
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
  (define conc-eff-ctx-count (hash-ref conc-result 'eff-fctx-count))
  (define conc-eff-ctx-obs-count (hash-ref conc-result 'eff-fctx-obs-count))
  (define type-eff-ctx-count (hash-ref type-result 'eff-fctx-count))
  (define type-eff-ctx-obs-count (hash-ref type-result 'eff-fctx-obs-count))
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
(define (print-se-obs-row name conc-result a-type-result sa-type-result sfa-type-result msfa-type-result)
  (define conc-eff-ctx-obs-count (hash-ref conc-result 'observable-count))
  (define a-type-eff-ctx-obs-count (hash-ref a-type-result 'observable-count))
  (define sa-type-eff-ctx-obs-count (hash-ref sa-type-result 'observable-count))
  (define sfa-type-eff-ctx-obs-count (hash-ref sfa-type-result 'observable-count))
  (define msfa-type-eff-ctx-obs-count (hash-ref msfa-type-result 'observable-count))
  (printf "\\code{~a} & ~a & ~a & ~a & ~a \\\\\n"
          (~a name #:min-width 14)
          (~a a-type-eff-ctx-obs-count #:min-width 4)
          (~a sa-type-eff-ctx-obs-count #:min-width 4)
          (~a sfa-type-eff-ctx-obs-count #:min-width 4)
          (~a msfa-type-eff-ctx-obs-count #:min-width 4)
          ;(~a conc-eff-ctx-obs-count)
          ))

(define (print-se-obs)
  (printf "se-obs\n")
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
         (print-se-obs-row benchmark-name conc-result a-type-result sa-type-result sfa-type-result msfa-type-result))))



(define (print-se-fp-row name conc-result a-type-result sa-type-result sfa-type-result msfa-type-result)
  (define conc-lam-effs (hash-ref conc-result 'lam->obs-effs))
  (define a-type-lam-effs (hash-ref a-type-result 'lam->obs-effs))
  (define sa-type-lam-effs (hash-ref sa-type-result 'lam->obs-effs))
  (define sfa-type-lam-effs (hash-ref sfa-type-result 'lam->obs-effs))
  (define msfa-type-lam-effs (hash-ref msfa-type-result 'lam->obs-effs))
  ;(printf "~a \n~a\n\n" conc-lam-effs msfa-type-lam-effs)
  (let-values (((xx-a yy-a) (count-lses-⊑ conc-lam-effs a-type-lam-effs type-⊑ type-α)))
  (let-values (((xx-sa yy-sa) (count-lses-⊑ conc-lam-effs sa-type-lam-effs type-⊑ type-α)))
  (let-values (((xx-sfa yy-sfa) (count-lses-⊑ conc-lam-effs sfa-type-lam-effs type-⊑ type-α)))
  (let-values (((xx-msfa yy-msfa) (count-lses-⊑ conc-lam-effs msfa-type-lam-effs type-⊑ type-α)))
    (printf "\\code{~a} & ~a/~a (~a)& ~a/~a (~a) & ~a/~a (~a) & ~a/~a (~a)\\\\\n"
            (~a name #:min-width 14)
            (~a xx-a #:min-width 4)
            (~a yy-a #:min-width 4)
            (~perc-r-0 xx-a yy-a)
            (~a xx-sa #:min-width 4)
            (~a yy-sa #:min-width 4)
            (~perc-r-0 xx-sa yy-sa)
            (~a xx-sfa #:min-width 4)
            (~a yy-sfa #:min-width 4)
            (~perc-r-0 xx-sfa yy-sfa)
            (~a xx-msfa #:min-width 4)
            (~a yy-msfa #:min-width 4)
            (~perc-r-0 xx-msfa yy-msfa)
            ))))))

(define (print-se-fp)
  (printf "se-fp\n")
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
         (print-se-fp-row benchmark-name conc-result a-type-result sa-type-result sfa-type-result msfa-type-result))))



;;;;;;;;;;;;;;;;;
(define (print-type-fresh-row name type-results)
  (let* (
         (type-fresh-ref-obj-count2d (hash-ref type-results 'fresh-ref-obj-count2d))
         (type-unfresh-ref-obj-count2d (hash-ref type-results 'unfresh-ref-obj-count2d))
         (type-freshness-time (hash-ref type-results 'freshness-time))
         )
     (printf "\\code{~a} & ~a & ~a \\\\\n"
            (~a name #:min-width 14)
            (~a type-fresh-ref-obj-count2d)
            (~time type-freshness-time)
            )))

(define (print-type-fresh)
  (printf "type-fresh\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (type-results (caddr r))
              )
         (print-type-fresh-row benchmark-name type-results))))


;;;;;;;;;;;;;;;;;
(define (print-conc-type-fresh-row name conc-results type-results)
  (let* (
         (conc-fresh-ref-obj-count2df (hash-ref conc-results 'fresh-ref-obj-count2df))
         (conc-unfresh-ref-obj-count2df (hash-ref conc-results 'unfresh-ref-obj-count2df))
         (type-fresh-ref-obj-count2df (hash-ref type-results 'fresh-ref-obj-count2df))
         (type-unfresh-ref-obj-count2df (hash-ref type-results 'unfresh-ref-obj-count2df))
         (type-freshness-time (hash-ref type-results 'freshness-time))
         (conc-fresh-profile (hash-ref conc-results 'freshness-profile))
         (type-fresh-profile (hash-ref type-results 'freshness-profile))
         )
    (let-values (((xx yy) (fresh-fp conc-fresh-profile type-fresh-profile)))
     (printf "\\code{~a} & ~a/~a (~a) & ~a & ~a\\\\\n"
            (~a name #:min-width 14)
            (~a xx)
            (~a yy)
            (~perc xx yy)
            (~time type-freshness-time)
            (~perc conc-fresh-ref-obj-count2df (+ conc-fresh-ref-obj-count2df conc-unfresh-ref-obj-count2df))
            ))))

(define (print-conc-type-fresh)
  (printf "conc-type-fresh\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (conc-results (cadr r))
              (type-results (caddr r))
              )
         (print-conc-type-fresh-row benchmark-name conc-results type-results))))




;;;;;;;;;;;;;;;;;
(define (print-escape-row name conc-results type-results)
  (let* ((lam-count (hash-ref conc-results 'lam-count))
         (conc-called-count (hash-ref conc-results 'called-count))
         (type-called-count (hash-ref type-results 'called-count))
         (conc-esc-lams (hash-ref conc-results 'esc-lams))
         (conc-esc-lams-count (set-count conc-esc-lams))
         (type-escape-time (hash-ref type-results 'escape-time))
         (type-esc-lams (hash-ref type-results 'esc-lams))
         (type-esc-lams-count (set-count type-esc-lams)))
     (printf "\\code{~a} & ~a & ~a (~a) & ~a (~a) & ~a\\\\\n"
            (~a name #:min-width 14)
            (~a lam-count #:min-width 4)
            (~a type-called-count #:min-width 4)
            (~a conc-called-count #:min-width 4)
            (~a type-esc-lams-count #:min-width 4)
            (~a conc-esc-lams-count #:min-width 4)
            (~time type-escape-time)
            )))

(define (print-escape)
  (printf "escape\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (conc-results (cadr r))
              (type-results (caddr r))
              )
         (print-escape-row benchmark-name conc-results type-results))))


;;;;;;;;;;;;;;;;;
(define (print-purity-row name conc-result type-a-result type-msfa-result)
  (let* (;(lam-count (hash-ref conc-results 'lam-count))
         ;(conc-called-count (hash-ref conc-results 'called-count))
         ;(type-called-count (hash-ref type-results 'called-count))
         ;(purity-time (hash-ref type-result 'purity-time))
         (conc-gen-count (hash-ref conc-result 'gen-count))
         (conc-obs-count (hash-ref conc-result 'obs-count))
         (type-a-gen-count (hash-ref type-a-result 'gen-count))
         (type-a-obs-count (hash-ref type-a-result 'obs-count))
         (type-msfa-gen-count (hash-ref type-msfa-result 'gen-count))
         (type-msfa-obs-count (hash-ref type-msfa-result 'obs-count)))
    (printf "\\code{~a} & ~a & ~a & ~a & ~a & ~a & ~a\\\\\n"
            (~a name #:min-width 14)
            (~a type-a-obs-count #:min-width 4)
            (~a type-a-obs-count #:min-width 4)
            (~a type-msfa-obs-count #:min-width 4)
            (~a type-msfa-obs-count #:min-width 4)
            (~a conc-obs-count #:min-width 4)
            (~a conc-obs-count #:min-width 4)
            )))
    
(define (print-purity)
  (printf "purity\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (conc-results (cadr r))
              (conc-a-result (hash-ref conc-results 'a))
              (type-results (caddr r))
              (type-a-result (hash-ref type-results 'a))
              (type-msfa-result (hash-ref type-results 'msfa))
              )
         (print-purity-row benchmark-name conc-a-result type-a-result type-msfa-result))))
  
;;;;;;;;;;;;;;;;;
(define (print-purity-class-row name conc-results conc-result type-result)
  (let* ((lam-count (hash-ref conc-results 'lam-count))
         (called-count (hash-ref conc-results 'called-count))
         (purity-time (hash-ref type-result 'purity-time))
         (conc-class-count (hash-ref conc-result 'class-count))
         (conc-pure-count (hash-ref conc-class-count PURE 0))
         (conc-obs-count (hash-ref conc-class-count OBSERVER 0))
         (conc-proc-count (hash-ref conc-class-count PROCEDURE 0))
         (type-class-count (hash-ref type-result 'class-count))
         (type-pure-count (hash-ref type-class-count PURE 0))
         (type-obs-count (hash-ref type-class-count OBSERVER 0))
         (type-proc-count (hash-ref type-class-count PROCEDURE 0)))
    (printf "\\code{~a} & ~a & ~a & ~a & ~a & ~a & ~a & ~a\\\\\n"
            (~a name #:min-width 14)
            (~a called-count #:min-width 4)
            ;(~time purity-time)
            (~a conc-pure-count #:min-width 4)
            (~a conc-obs-count #:min-width 4)
            (~a conc-proc-count #:min-width 4)
            (~a type-pure-count #:min-width 4)
            (~a type-obs-count #:min-width 4)
            (~a type-proc-count #:min-width 4)
            )))
      
(define (print-conc-a-type-msfa-purity-class)
  (printf "conc-a-type-msfa-purity-class\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (conc-results (cadr r))
              (type-results (caddr r))
              (conc-a-result (hash-ref conc-results 'a))
              (type-msfa-result (hash-ref type-results 'msfa))
              )
         (print-purity-class-row benchmark-name conc-results conc-a-result type-msfa-result))))

(define (print-type-a-type-msfa-purity-class)
  (printf "type-a-type-msfa-purity-class\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (conc-results (cadr r))
              (type-results (caddr r))
              (type-a-result (hash-ref type-results 'a))
              (type-msfa-result (hash-ref type-results 'msfa))
              )
         (print-purity-class-row benchmark-name conc-results type-a-result type-msfa-result))))
  
;;;;;;;;;;;;;;;;;
(define (print-purity-timing-row name result1 result2 result3 result4)
  (let* ((purity-time1 (hash-ref result1 'purity-time))
         (purity-time2 (hash-ref result2 'purity-time))
         (purity-time3 (hash-ref result3 'purity-time))
         (purity-time4 (hash-ref result4 'purity-time))
         )
         
    (printf "\\code{~a} & ~a & ~a & ~a & ~a\\\\\n"
            (~a name #:min-width 14)
            (~time purity-time1)
            (~time purity-time2)
            (~time purity-time3)
            (~time purity-time4)
            )))
      
(define (print-purity-timing)
  (printf "purity-timing\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (type-results (caddr r))
              (type-a-result (hash-ref type-results 'a))
              (type-sa-result (hash-ref type-results 'sa))
              (type-sfa-result (hash-ref type-results 'sfa))
              (type-msfa-result (hash-ref type-results 'msfa))
              )
         (print-purity-timing-row benchmark-name type-a-result type-sa-result type-sfa-result type-msfa-result))))

;;;;;;;;;;;;;;;;;
(define (print-se-timing-row name result1 result2 result3 result4)
  (let* ((se-time1 (hash-ref result1 'side-effect-time))
         (se-time2 (hash-ref result2 'side-effect-time))
         (se-time3 (hash-ref result3 'side-effect-time))
         (se-time4 (hash-ref result4 'side-effect-time))
         )
         
    (printf "\\code{~a} & ~a & ~a & ~a & ~a\\\\\n"
            (~a name #:min-width 14)
            (~time se-time1)
            (~time se-time2)
            (~time se-time3)
            (~time se-time4)
            )))
      
(define (print-se-timing)
  (printf "se-timing\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (type-results (caddr r))
              (type-a-result (hash-ref type-results 'a))
              (type-sa-result (hash-ref type-results 'sa))
              (type-sfa-result (hash-ref type-results 'sfa))
              (type-msfa-result (hash-ref type-results 'msfa))
              )
         (print-se-timing-row benchmark-name type-a-result type-sa-result type-sfa-result type-msfa-result))))

;;;;;;;;;;;;;;;;;
(define (print-timing-row name results type-a-result type-sa-result type-sfa-result type-msfa-result)
  (let* ((flow-time (hash-ref results 'flow-time))
         (call-store-time (hash-ref results 'call-store-time))
         (escape-time (hash-ref results 'escape-time))
         (fresh-time (hash-ref results 'freshness-time))
         (a-side-effect-time (hash-ref type-a-result 'side-effect-time))
         (a-purity-time (hash-ref type-a-result 'purity-time))
         (sa-side-effect-time (hash-ref type-sa-result 'side-effect-time))
         (sa-purity-time (hash-ref type-sa-result 'purity-time))
         (sfa-side-effect-time (hash-ref type-sfa-result 'side-effect-time))
         (sfa-purity-time (hash-ref type-sfa-result 'purity-time))
         (msfa-side-effect-time (hash-ref type-msfa-result 'side-effect-time))
         (msfa-purity-time (hash-ref type-msfa-result 'purity-time))
         )
         
    (printf "\\code{~a} & ~a & ~a & ~a & ~a\\\\\n"
            (~a name #:min-width 14)
            (~time (+ flow-time call-store-time a-side-effect-time a-purity-time))
            (~time (+ flow-time call-store-time sa-side-effect-time sa-purity-time))
            (~time (+ flow-time call-store-time sfa-side-effect-time fresh-time sfa-purity-time))
            (~time (+ flow-time call-store-time msfa-side-effect-time escape-time fresh-time msfa-purity-time))
            )))
      
(define (print-timing)
  (printf "timing\n")
  (for ((r test-result))
       (let* ((benchmark-name (car r))
              (type-results (caddr r))
              (type-a-result (hash-ref type-results 'a))
              (type-sa-result (hash-ref type-results 'sa))
              (type-sfa-result (hash-ref type-results 'sfa))
              (type-msfa-result (hash-ref type-results 'msfa))
              )
         (print-timing-row benchmark-name type-results type-a-result type-sa-result type-sfa-result type-msfa-result))))

;;;;;;;

(define (main)

  ;(purity-test)

  ; Benchmarks
  (print-benchmarks)

  ; Setting
  (print-flow-conc)
  (print-flow-type)

  ; Side-effects
  ;(print-se-a-conc-result)
  ;(print-se-a-type-result)
  ;(print-se-a-conc-type-perc)
  ;(print-se-msfa-conc-type-perc)
  ;(print-se-percs)
  (print-se-fp)
  (print-se-obs)
  (print-se-timing)

  ; Escape
  (print-escape)

  ; Fresh
  ;(print-type-fresh)
  (print-conc-type-fresh)

  ; Purity
  ;(print-purity)

  (print-conc-a-type-msfa-purity-class)
  (print-type-a-type-msfa-purity-class)
  (print-purity-timing)

  (print-timing)
  )



