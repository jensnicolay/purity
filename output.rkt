(struct benchmark (name state-count duration exit msg))

(define (benchmark-eval name e mach)
  (let* ((sys (mach e))
         (duration (system-duration sys))
         (state-count (vector-length (system-states sys)))
         (exit (system-exit sys))
         (msg (if (eq? exit 'ok) (answer-value sys) (system-msg sys))))
    (when (and (THROW) (eq? exit 'error))
      (raise msg))
    (benchmark name state-count duration exit msg)))

(define (perform-benchmark name e mach)
  (printf (~a name #:min-width 12))
  (let* ((bench (benchmark-eval name e mach))
         (exit (benchmark-exit bench))
         (msg (benchmark-msg bench))
         (state-count (benchmark-state-count bench))
         (duration (benchmark-duration bench)))
    (printf "states ~a time ~a | ~a\n"
            (~a (if (eq? exit 'ok) state-count (format ">~a" state-count)) #:min-width 7)
            (~a duration #:min-width 7)
            (~a msg #:max-width 72))
    bench))

(define (state-repr s)
  (match s
    ((ev e ρ σ ι κ) (format "~a | ~a" (~a e #:max-width 20) (ctx->ctxi κ)))
    ((ko ι κ v σ) (format "~a | ~a" (~a v #:max-width 20) (ctx->ctxi κ)))))

;; Lower-bound for printing time (if smaller, prints \epsilon), in seconds
(define TIMECUTOFF (make-parameter 1))
(define TIMEFORMAT (make-parameter
                    ;; Round to seconds by default: 1
                    (lambda (time) (format "~a''" (inexact->exact (round time))))
                    ;; Other possibility: 1.234''
                    ;; (lambda (n) (~a time "''"))
                    ))
(define (display-size-tex result)
  (define (to-states benchmark)
    (~a (if (eq? (benchmark-exit benchmark) 'user) "$>$" "") (benchmark-state-count benchmark)))

  (printf "\\begin{tabular}{lllll} Program & Variance & Base & Summarizing & Self-adjusting \\\\ \\hline \n")
  (for/list ((res result))
    (match res
      ((list res-0 res-0-summ res-0-sa res-1 res-1-summ res-1-sa)
       ;; 0-CFA
       (printf "\\code{~a}      & 0CFA         & ~a   & ~a     & ~a          \\\\"
               (~a (benchmark-name res-0)) 
               (~a (to-states res-0))      
               (~a (to-states res-0-summ))
               (~a (to-states res-0-sa))
               )
       ;; 1-CFA
       (printf "                & 1CFA         & ~a   & ~a    & ~a          \\\\[6pt]\n"
               (~a (to-states res-1))
               (~a (to-states res-1-summ))
               (~a (to-states res-1-sa)) 
               ))))
  (printf "\\end{tabular}\n"))

(define (display-time-tex result)
  (define (to-time benchmark)
    (if (eq? (benchmark-exit benchmark) 'user)
        "$\\infty$"
        (let ((duration (benchmark-duration benchmark)))
          (if (< duration 1000)
              "$\\epsilon$" 
              (format "~a''" (inexact->exact (round (/ duration 1000))))))))
          
  (printf "\\begin{tabular}{lllll} Program & Variance & Base & Summarizing & Self-adjusting \\\\ \\hline \n")
  (for/list ((res result))
    (match res
      ((list res-0 res-0-summ res-0-sa res-1 res-1-summ res-1-sa)
       ;; 0-CFA
       (printf "\\code{~a}      & 0CFA         & ~a   & ~a      & ~a          \\\\"
               (~a (benchmark-name res-0)) 
               (~a (to-time res-0))      
               (~a (to-time res-0-summ))
               (~a (to-time res-0-sa)))
       ;; 1-CFA
       (printf "                & 1CFA         & ~a   & ~a      & ~a          \\\\[6pt]\n"
               (~a (to-time res-1))
               (~a (to-time res-1-summ))
               (~a (to-time res-1-sa))))))
  (printf "\\end{tabular}\n"))



(define (generate-dot e sys name)
  
  (let* ((graph (system-graph sys))
         (states (system-states sys))
         (dotf (open-output-file (format "~a.dot" name) #:exists 'replace)))
    (fprintf dotf "digraph G {\n")
    (for ((i (vector-length states)))
      (let ((s (vector-ref states i)))
        (fprintf dotf "~a [label=\"~a | ~a\"];\n" i i (state-repr s))))
    (hash-for-each graph (lambda (s out)
                           (let ((i1 (vector-member s states))
                                 (is (set-map out (lambda (s2E) (vector-member (car s2E) states)))))
                             (for-each (lambda (i2)
                                         (fprintf dotf "~a -> ~a;\n" i1 i2)) is))))
    (fprintf dotf "}")
    (close-output-port dotf))
  
  sys)

(define (graph e mach name)
  (parameterize ((TIMELIMIT 1))
    (generate-dot e (mach e) name)))

