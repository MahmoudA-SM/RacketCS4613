#lang plait #:untyped

(define-type RFLANG
  [Num  (val : Number)]
  [Add  (l : RFLANG) (r : RFLANG)]
  [Sub  (l : RFLANG) (r : RFLANG)]
  [Mul  (l : RFLANG) (r : RFLANG)]
  [Div  (l : RFLANG) (r : RFLANG)]
  [Id   (name : Symbol)]
  [If (test : RFLANG) (then-part : RFLANG) (else-part : RFLANG)]
  [Let1 (id : Symbol) (named-expr : RFLANG) (bound-body : RFLANG)]
  [Rec (id : Symbol) (named-expr : RFLANG) (bound-body : RFLANG)]
  [Lam  (param : Symbol) (body : RFLANG)]
  [Call (lam : RFLANG) (val : RFLANG)]
  [Set (id : Symbol) (body : RFLANG)]
  [Begin (bodies : (Listof RFLANG))])

(define-type VAL
  [NumV (n : Number)]
  [LamV (arg : Symbol) (body : RFLANG) (env : ENV)]
  [BogusV])

(define (val->number v)
  (type-case VAL v
    [(NumV num) num]
    [else (error 'val-number "not a number")]))

(define-type ENV
  [EmptyEnv]
  [Extend (name : Symbol) (val : (Boxof VAL)) (end : ENV)])

(define (lookup name env)
  (type-case ENV env
    [(EmptyEnv) (error 'lookup (string-append "no binding for " (to-string name)))]
    [(Extend id boxed-val rest-env)
     (if (eq? id name) boxed-val (lookup name rest-env))]))
;; gets a Racket numeric binary operator, and uses it let1in a NumV
;; wrapper

(define (arith-op op val1 val2)
  (local
      [(define (NumV->number v)
         (type-case VAL v
           [(NumV n) n]
           [else (error 'arith-op (string-append "expects a number, got: " (to-string v)))]))]
    (NumV (op (NumV->number val1) (NumV->number val2)))))

;; evaluates RFLANG expressions by reducing them to values
(define (interp expr env)
  (type-case RFLANG expr
    [(Num n) (NumV n)]
    [(Add l r) (arith-op + (interp l env) (interp r env))]
    [(Sub l r) (arith-op - (interp l env) (interp r env))]
    [(Mul l r) (arith-op * (interp l env) (interp r env))]
    [(Div l r) (arith-op / (interp l env) (interp r env))]
    [(If test then-part else-part)
     (if (eq? 0 (val->number (interp test env)))
         (interp else-part env)
         (interp then-part env))]
    [(Let1 bound-id named-expr bound-body)
     (interp bound-body
           (Extend bound-id (box (interp named-expr env)) env))]
    [(Rec bound-id named-expr bound-body)
     (interp bound-body
           (extend-rec bound-id named-expr env))]
    [(Id name) (unbox (lookup name env))]
    [(Lam bound-id bound-body)
     (LamV bound-id bound-body env)]
    [(Begin bodies)
     (interp-body bodies env)]
    [(Set bound-id bound-body)
     (begin
     (set-box! (lookup bound-id env) (interp bound-body env))
     (BogusV))]
    [(Call lam-expr arg-expr)
     (let ([fval (interp lam-expr env)])
       (type-case VAL fval
         [(LamV bound-id bound-body f-env)
          (interp bound-body
                (Extend bound-id (box (interp arg-expr env)) f-env))]
         [else (error 'eval (string-append "`call' expects a function, got: "
                                           (to-string fval)))]))]))

;; evaluates a list of expressions, returns the last value.
(define (interp-body [expr-list : (Listof RFLANG)] [env : ENV])
    (if (empty? (rest expr-list))
        (interp (first expr-list) env)
        (begin
          (interp (first expr-list) env)
          (interp-body (rest expr-list) env))))

(define (extend-rec id expr rest-env)
  (let ([new-cell (box (NumV 42))])
    (let ([new-env (Extend id new-cell rest-env)])
      (let ([value (interp expr new-env)])
        (begin
          (set-box! new-cell value)
          new-env)))))

(define (parse-error sx)
  (error 'parse-sx (string-append "parse error: " (to-string sx))))

(define (sx-ref sx n) (list-ref (s-exp->list sx) n))

(define (parse-sx sx)
  (local
      [(define (px i) (parse-sx (sx-ref sx i)))
       (define (let1-rec-pieces sx)
         (let* ([def (sx-ref sx 1)]
                [id (s-exp->symbol (sx-ref def 0))]
                [val (parse-sx (sx-ref def 1))]
                [expr (parse-sx (sx-ref sx 2))])
           (values id val expr)))]
    (cond
      [(s-exp-number? sx) (Num (s-exp->number sx))]
      [(s-exp-symbol? sx) (Id (s-exp->symbol sx))]
      [(s-exp-match? `(let1 (SYMBOL ANY) ANY) sx)
       (local [(define-values (id val expr) (let1-rec-pieces sx))]
         (Let1 id val expr))]
      [(s-exp-match? `(rec (SYMBOL ANY) ANY) sx)
       (local [(define-values (id val expr) (let1-rec-pieces sx))]
         (Rec id val expr))]
      [(s-exp-match? `(if ANY ANY ANY) sx)
       (If (px 1) (px 2) (px 3))]
      [(s-exp-match? `(set! SYMBOL ANY) sx)
       (let* ([id (s-exp->symbol (sx-ref sx 1))]
              [body (parse-sx (sx-ref sx 2))])
         (Set id body))]

      [(s-exp-match? `(begin ANY ...) sx)
       (if (empty? (rest (s-exp->list sx)))
           (parse-error sx)
           (local
               ((define (list-parser lst mylst)
                 (if (empty? lst)
                     mylst
                     (cons (parse-sx (first lst)) (list-parser (rest lst) mylst)))))
             (Begin (list-parser (rest (s-exp->list sx)) empty))))]
      
      [(s-exp-match? `(lam SYMBOL ANY) sx)
       (let* ([id (s-exp->symbol (sx-ref sx 1))]
              [body (parse-sx (sx-ref sx 2))])
         (Lam id body))]
      [(s-exp-match? `(ANY ANY) sx)
       (Call (parse-sx (sx-ref sx 0)) (parse-sx (sx-ref sx 1)) )]
      [(s-exp-match? `(SYMBOL ANY ANY) sx)
       (let ([l (parse-sx (sx-ref sx 1))]
             [r (parse-sx (sx-ref sx 2))])
         (case (s-exp->symbol (sx-ref sx 0))
           [(+) (Add l r)]
           [(-) (Sub l r)]
           [(*) (Mul l r)]
           [(/) (Div l r)]
           [else (parse-error sx)]))]
      [else (parse-error sx)])))


;; evaluate a RFLANG program contained in a string
(define (run sx)
  (let ([result (interp (parse-sx sx) (EmptyEnv))])
    (type-case VAL result
      [(NumV n) n]
      [else (error 'run
                   (string-append
                    "evaluation returned a non-number " (to-string result)))])))

;; test(s) for recursion
(module+ test
  (test
   (run
    `{rec
      {fact
       {lam n
            {if n
                {* n {fact {- n 1}}}
                1}}}
      {fact 5}})
   120))

;; error handling paths
(module+ test
  (test/exn (val->number (LamV 'x (Id 'x) (EmptyEnv))) "not a number")
  (test/exn (parse-sx `{}) "parse error")
  (test/exn (parse-sx `{foo 1 2}) "parse error")
  (test/exn (run `{+ x 1}) "no binding")
  (test/exn (run `{+ 1 {lam x x}}) "expects a number")
  (test/exn (run `{1 1}) "expects a function")
  (test/exn (run `{lam x x}) "returned a non-number"))

;; lexical scope tests, from lectures
(module+ test
  (test (run `{let1 {x 3}
                    {let1 {f {lam y {+ x y}}}
                          {let1 {x 5}
                                {f 4}}}})    7)
  (test (run `{{let1 {x 3}
                     {lam y {+ x y}}}
               4})    7)
  (test (run `{{{lam x {x 1}}
                {lam x {lam y {+ x y}}}}
               123})
        124))

;; Coverage tests for arithmetic
(module+ test
  (test (run `(let1 (x 0) (let1 (y (set! x 1 )) x))) 1)
  (test (run `{/ 6 7}) 6/7)
  (test/exn (run `(let1 (x 3) (set! x 5))) "a non-number ")
  (test (run `{let1 {x 1}
                  {begin
                    {set! x 2}
                    x}}) 2)
  (test (run `{let1 {x 1}
                  {begin
                    {set! x 2}
                    x}}) 2)


(test (run `{let1 {x 1}
                  {begin
                    {set! x {+ x 1}}
                    x}}) 2)

(test (run `{let1 {make-counter
                   {lam initial
                        {let1 {c initial}
                              {lam dummy
                                   {begin
                                     {set! c {+ 1 c}}
                                     c}}}}}
                  {let1 {c1 {make-counter 0}}
                        {let1  {c2 {make-counter 0}}
                               {*  {* {c1 0} {c1 0}}
                                   {* {c2 0} {c1 0}}}}}})
      6)
  (test/exn (run `(begin )) "parse error")
  )


(define minutes-spent 180)
