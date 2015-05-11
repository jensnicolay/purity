;; conc lattice
(define (conc-α v)
  v)

(define (conc-γ v)
  (set v))

(define conc-⊥ "conc-⊥")

(define (conc-⊔ v1 v2)
  (match* (v1 v2)
    (((== conc-⊥) v) v)
    ((v (== conc-⊥)) v)
    ((v v) v)
    ((_ _) (error "concrete join" v1 v2))))

(define (conc-true? v)
  v)

(define (conc-false? v)
  (not v))

(define conc-global
  `(("=" . ,(conc-α (prim2 "=" =)))
    ("<" . ,(conc-α (prim2 "<" <)))
    (">" . ,(conc-α (prim2 ">" >)))
    ("<=" . ,(conc-α (prim2 "<=" <=)))
    (">=" . ,(conc-α (prim2 ">=" >=)))
    ("+" . ,(conc-α (prim2 "+" +)))
    ("-" . ,(conc-α (prim2 "-" -)))
    ("*" . ,(conc-α (prim2 "*" *)))
    ("/" . ,(conc-α (prim2 "/" /)))
    ("not" . ,(conc-α (prim2 "not" not)))
    ("and" . ,(conc-α (prim2 "and" (lambda l
                                     (for/fold ((res #t))
                                               ((el l))
                                       (and res el))))))
    ("or" . ,(conc-α (prim2 "or" (lambda l
                                   (for/fold ((res #f))
                                             ((el l))
                                     (or res el))))))
    ("gcd" . ,(conc-α (prim2 "gcd" gcd)))
    ("modulo" . ,(conc-α (prim2 "modulo" modulo)))
    ("remainder" . ,(conc-α (prim2 "remainder" remainder)))
    ("quotient" . ,(conc-α (prim2 "quotient" quotient)))
    ("ceiling" . ,(conc-α (prim2 "ceiling" ceiling)))
    ("log" . ,(conc-α (prim2 "log" log)))
    ("even?" . ,(conc-α (prim2 "even?" even?)))
    ("odd?" . ,(conc-α (prim2 "odd?" odd?)))
    ("symbol?" . ,(conc-α (prim2 "symbol?" symbol?)))
    ("null?" . ,(conc-α (prim2 "null?" null?)))
    ("char?" . ,(conc-α (prim2 "char?" char?)))
    ("printf" . ,(conc-α (prim2 "printf" printf)))
    ("integer?" . ,(conc-α (prim2 "integer?" integer?)))
    ("number->string" . ,(conc-α (prim2 "number->string" number->string)))
    ("string?" . ,(conc-α (prim2 "string?" string?)))
    ("string->symbol" . ,(conc-α (prim2 "string->symbol" string->symbol)))
    ("symbol->string" . ,(conc-α (prim2 "symbol->string" symbol->string)))
    ("string-length" . ,(conc-α (prim2 "string-length" string-length)))
    ("string-ref" . ,(conc-α (prim2 "string-ref" string-ref)))
    ;("list?" . ,(conc-α (prim2 "list?" list?)))
    ;("pair?" . ,(conc-α (prim2 "pair?" pair?)))
    ("string-append" . ,(conc-α (prim2 "string-append" string-append)))
    ("char->integer" . ,(conc-α (prim2 "char->integer" char->integer)))
    ("char-alphabetic?" . ,(conc-α (prim2 "char-alphabetic?" char-alphabetic?)))
    ("char-numeric?" . ,(conc-α (prim2 "char-numeric?" char-numeric?)))
    ("char=?" . ,(conc-α (prim2 "char=?" char=?)))
    ("number?" . ,(conc-α (prim2 "number?" number?)))
    ("%random" . ,(conc-α (prim2 "%random" %random)))))

(define (conc-eq? v1 v2)
  (eq? v1 v2))    
;;

;; type lattice
(define NUM "NUM")
(define BOOL "BOOL")
(define STR "STR")
(define SYM "SYM")
(define CHAR "CHAR")

(define (type-α v)
  (cond
    ((number? v) (set NUM))
    ((boolean? v) (set BOOL))
    ((symbol? v) (set SYM))
    ((string? v) (set STR))
    ((char? v) (set CHAR))
    ((clo? v) (set v))
    ((prim? v) (set v))
    ((prim2? v) (set v))
    ((addr? v) (set v))
    ((pair? v) (set v))
    ((null? v) (set v))
    (else (error "bwek" v))))

(define (type-γ v)
  v)

(define type-⊥ (set))

(define type-⊔ set-union)

(define (type-true? v)
  #t)

(define (type-false? v)
  #t)

(define type-global
  (let ((->bool
         (lambda vs
           (set BOOL)))
        (->num
         (lambda vs
           (set NUM)))
        (->str
         (lambda vs
           (set STR)))
        (->char
         (lambda vs
           (set CHAR)))
        (->sym
         (lambda vs
           (set SYM)))
        )
    `(("=" . ,(type-α (prim2 "=" ->bool)))
      ("<" . ,(type-α (prim2 "<" ->bool)))
      ("<=" . ,(type-α (prim2 "<=" ->bool)))
      (">" . ,(type-α (prim2 ">" ->bool)))
      (">=" . ,(type-α (prim2 ">=" ->bool)))
      ("+" . ,(type-α (prim2 "+" ->num)))
      ("-" . ,(type-α (prim2 "-" ->num)))
      ("*" . ,(type-α (prim2 "*" ->num)))
      ("/" . ,(type-α (prim2 "/" ->num)))
      ("not" . ,(type-α (prim2 "not" ->bool)))
      ("and" . ,(type-α (prim2 "and" ->bool)))
      ("or" . ,(type-α (prim2 "or" ->bool)))
      ("gcd" . ,(type-α (prim2 "gcd" ->num)))
      ("modulo" . ,(type-α (prim2 "modulo" ->num)))
      ("remainder" . ,(type-α (prim2 "remainder" ->num)))
      ("quotient" . ,(type-α (prim2 "quotient" ->num)))
      ("ceiling" . ,(type-α (prim2 "ceiling" ->num)))
      ("log" . ,(type-α (prim2 "log" ->num)))
      ("even?" . ,(type-α (prim2 "even?" ->bool)))
      ("odd?" . ,(type-α (prim2 "odd?" ->bool)))
      ("symbol?" . ,(type-α (prim2 "symbol?" ->bool)))
      ("null?" . ,(type-α (prim2 "null?" ->bool)))
      ("char?" . ,(type-α (prim2 "char?" ->bool)))
      ("%random" . ,(type-α (prim2 "%random" ->num)))
      ("integer?" . ,(type-α (prim2 "integer?" ->bool)))
      ("random" . ,(type-α (prim2 "random" ->num)))
      ("string-length" . ,(type-α (prim2 "string-length" ->num)))
      ("string-ref" . ,(type-α (prim2 "string-ref" ->char)))
      ("list->string" . ,(type-α (prim2 "list->string" ->str)))
      ("number?" . ,(type-α (prim2 "number?" ->bool)))
      ("number->string" . ,(type-α (prim2 "number->string" ->str)))
      ("string?" . ,(type-α (prim2 "string?" ->bool)))
      ("string->symbol" . ,(type-α (prim2 "string->symbol" ->sym)))
      ("symbol->string" . ,(type-α (prim2 "symbol->string" ->str)))
      ;("list?" . ,(type-α (prim2 "list?" any->bool)))
      ;("pair?" . ,(type-α (prim2 "pair?" any->bool)))
      ("string-append" . ,(type-α (prim2 "string->append" ->str)))
      ("char->integer" . ,(type-α (prim2 "char->integer" ->num)))
      ("char-alphabetic?" . ,(type-α (prim2 "char-alphabetic?" ->bool)))
      ("char-numeric?" . ,(type-α (prim2 "char-numeric?" ->bool)))
      ("char=?" . ,(type-α (prim2 "char=?" ->bool))))))

(define (type-eq? v1 v2)
  (set BOOL))
;;
