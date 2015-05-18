(struct benchmark (name state-count duration memo-table read-table memo-count exit msg))

(define (benchmark-eval name e mach)
  (let* ((sys (explore e mach))
         (duration (system-duration sys))
         (state-count (vector-length (system-states sys)))
         (memo-table (system-memo-table sys))
         (read-table (system-read-table sys))
         (memo-count (set-count (system-memo-edges sys)))
         (exit (system-exit sys))
         (msg (if (eq? exit 'ok) (answer-value sys) (system-msg sys))))
    (when (and (THROW) (eq? exit 'error))
      (raise msg))
    (benchmark name state-count duration memo-table read-table memo-count exit msg)))

(define (perform-benchmark name e mach)
  (printf (~a name #:min-width 12))
  (let* ((bench (benchmark-eval name e mach))
         (exit (benchmark-exit bench))
         (msg (benchmark-msg bench))
         (state-count (benchmark-state-count bench))
         (memo-count (benchmark-memo-count bench))
         (duration (benchmark-duration bench)))
    (printf "states ~a time ~a memo ~a | ~a\n"
            (~a (if (eq? exit 'ok) state-count (format ">~a" state-count)) #:min-width 7)
            (~a duration #:min-width 7)
            (~a memo-count #:min-width 4)
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
(define (display-tex result)
  (define (to-states benchmark)
    (~a (if (eq? (benchmark-exit benchmark) 'user) "$>$" "") (benchmark-state-count benchmark)))
  (define (to-time benchmark)
    (let ((time (exact->inexact (/ (benchmark-duration benchmark) 1000))))
      (if (eq? (benchmark-exit benchmark) 'user)
          "$\\infty$"
          (if (< time (TIMECUTOFF)) "$\\epsilon$" ((TIMEFORMAT) time)))))
  (define (to-size-kB benchmark)
    (let ((size (exact->inexact (/ (string-length (~a (benchmark-memo-table benchmark))) 1024))))
      (if (<= size 1)
          "$\\leq$ 1kB"
          (~a (inexact->exact (round size)) "kB"))))
  (define (to-size-pct benchmark-summ benchmark-sa)
    (let ((size-summ (string-length (~a (benchmark-memo-table benchmark-summ))))
          (size-sa (string-length (~a (benchmark-memo-table benchmark-sa)))))
      (~a (exact->inexact (/ size-sa size-summ)) #:width 4)))

  (printf "\\begin{table*}[t]
\\centering
\\begin{tabular}{|l|r|r|r|r|r|r|r|r|r|}
\\hline
\\multicolumn{1}{|l|}{\\multirow{2}{*}{Program}} &
\\multicolumn{1}{|r|}{\\multirow{2}{*}{$m$}} &
\\multicolumn{2}{|c|}{base} &
\\multicolumn{3}{|c|}{Summ} &
\\multicolumn{4}{|c|}{SA} \\\\
\\cline{3-11} &      & $n$      & $t$        & $n$      & $t$        & $\\#m$    & $n$      & $t$        & $s$        & $\\#m$    \\\\\\hline\\hline\n")

  (for/list ((res result))
    (match res
      ((list res-0 res-0-summ res-0-sa res-1 res-1-summ res-1-sa)
       ;; 0-CFA
       (printf "~a & ~a & ~a & ~a & ~a & ~a & ~a & ~a & ~a & ~a \\\\\n"
               (~a (benchmark-name res-0) #:min-width 12) ; name
               (~a 0 #:min-width 4)                       ; k
               ;; Base
               (~a (to-states res-0) #:min-width 8)      ; number of states
               (~a (to-time res-0) #:min-width 10)       ; time
               ;; Summ
               (~a (to-states res-0-summ) #:min-width 8) ; number of states
               (~a (to-time res-0-summ) #:min-width 10)  ; time
               ;; (~a (to-size-kB res-0-summ) #:min-width 6)   ; size
               (~a (benchmark-memo-count res-0-summ) #:min-width 8) ; memo count
               ;; SA
               (~a (to-states res-0-sa) #:min-width 8) ; number of states
               (~a (to-time res-0-sa) #:min-width 10)  ; time
               ;; (~a (to-size-kB res-0-sa) #:min-width 6)   ; size
               ;;(~a (to-size-pct res-0-summ res-0-sa) #:min-width 10) ; size in percent
               (~a (benchmark-memo-count res-0-sa) #:min-width 8)) ; memo count
       ;; 1-CFA
       (printf "~a & ~a & ~a & ~a & ~a & ~a & ~a & ~a & ~a & ~a \\\\ \\hline\n"
               (~a "" #:min-width 12) ; name
               (~a 1 #:min-width 4)                       ; k
               ;; Base
               (~a (to-states res-1) #:min-width 8)      ; number of states
               (~a (to-time res-1) #:min-width 10)       ; time
               ;; Summ
               (~a (to-states res-1-summ) #:min-width 8) ; number of states
               (~a (to-time res-1-summ) #:min-width 10)  ; time
               ;; (~a (to-size res-1-summ) #:min-width 6)   ; size
               (~a (benchmark-memo-count res-1-summ) #:min-width 8) ; memo count
               ;; SA
               (~a (to-states res-1-sa) #:min-width 8) ; number of states
               (~a (to-time res-1-sa) #:min-width 10)  ; time
               ;; (~a (to-size res-1-sa) #:min-width 6)   ; size
               ;;(~a (to-size-pct res-0-summ res-0-sa) #:min-width 10) ; size in percent
               (~a (benchmark-memo-count res-1-sa) #:min-width 8))))) ; memo count
  (printf "\\end{tabular}
\\end{table*}\n"))

(define (display-tex-table2 result)
    (define (poly-count benchmark)
    (length (filter (lambda (x) (and (string? x) (string=? "POLY" x))) (hash-values (benchmark-memo-table benchmark)))))
  (define (impure-count benchmark)
    (length (filter (lambda (x) (and (string? x) (string=? "IMPURE" x))) (hash-values (benchmark-memo-table benchmark)))))

    (printf "\\begin{table*}[t]
\\centering
\\begin{tabular}{|l|r|r|r|}
\\hline
Program      & $m$  & \\textbf{poly} & \\textbf{impure}  \\\\\\hline\\hline\n")

  (for/list ((res result))
    (match res
      ((list _ _ res-0-sa _ _ res-1-sa)
       (printf "~a & ~a & ~a & ~a \\\\\n"
               (~a (benchmark-name res-0-sa) #:min-width 12) ; name
               (~a 0 #:min-width 4)                          ; k
               (~a (poly-count res-0-sa) #:min-width 13)     ; number of poly
               (~a (impure-count res-0-sa) #:min-width 16)   ; number of impure
               )
       (printf "~a & ~a & ~a & ~a \\\\ \\hline\n"
               (~a "" #:min-width 12) ; name
               (~a 1 #:min-width 4)                          ; k
               (~a (poly-count res-1-sa) #:min-width 13)     ; number of poly
               (~a (impure-count res-1-sa) #:min-width 16)   ; number of impure
               ))))

  (printf "\\end{tabular}
\\end{table*}\n"))


(define (display-size-tex result)
  (define (to-states benchmark)
    (~a (if (eq? (benchmark-exit benchmark) 'user) "$>$" "") (benchmark-state-count benchmark)))

  (printf "\\begin{tabular}{lllll} Program & Variance & Base & Summarizing & Self-adjusting \\\\ \\hline \n")
  (for/list ((res result))
    (match res
      ((list res-0 res-0-summ res-0-sa res-1 res-1-summ res-1-sa)
       ;; 0-CFA
       (printf "\\code{~a}      & 0CFA         & ~a   & ~a (~a)     & ~a (~a)         \\\\"
               (~a (benchmark-name res-0)) 
               (~a (to-states res-0))      
               (~a (to-states res-0-summ))
               (~a (benchmark-memo-count res-0-summ))
               (~a (to-states res-0-sa))
               (~a (benchmark-memo-count res-0-sa)))
       ;; 1-CFA
       (printf "                & 1CFA         & ~a   & ~a (~a)     & ~a (~a)         \\\\[6pt]\n"
               (~a (to-states res-1))
               (~a (to-states res-1-summ))
               (~a (benchmark-memo-count res-1-summ))
               (~a (to-states res-1-sa)) 
               (~a (benchmark-memo-count res-1-sa))))))
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
                                 (is (set-map out (lambda (s2) (vector-member s2 states)))))
                             (for-each (lambda (i2)
                                         (fprintf dotf "~a -> ~a;\n" i1 i2)) is))))
    (fprintf dotf "}")
    (close-output-port dotf))
  
  sys)

(define (graph e mach name)
  (parameterize ((TIMELIMIT 1))
    (generate-dot e (explore e mach) name)))

