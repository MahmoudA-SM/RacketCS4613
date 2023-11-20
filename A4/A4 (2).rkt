#lang plait

(define-type FLANG
  [Num  (val : Number)]
  [Add  (l : FLANG) (r : FLANG)]
  [Sub  (l : FLANG) (r : FLANG)]
  [Mul  (l : FLANG) (r : FLANG)]
  [Div  (l : FLANG) (r : FLANG)]
  [Id   (name : Symbol)]
  [Let1 (id : Symbol) (named-expr : FLANG) (bound-body : FLANG)]
  [Lam  (params : (Listof Symbol)) (body : FLANG)]
  [Call (fun : FLANG) (vals : (Listof FLANG))]) ; first type!

(define (parse-error sx)
  (error 'parse-sx (string-append "parse error: " (to-string sx))))

(define (sx-ref sx n) (list-ref (s-exp->list sx) n))

(define (parse-sx sx)
  (local
      [(define (px n) (parse-sx (sx-ref sx n)))
       (define (mx? pattern) (s-exp-match? pattern sx))]
    (cond
      [(s-exp-number? sx) (Num (s-exp->number sx))]
      [(s-exp-symbol? sx) (Id (s-exp->symbol sx))]
      [(mx? `(let1 (SYMBOL ANY) ANY))
       (let* ([def (sx-ref sx 1)]
              [id (s-exp->symbol (sx-ref def 0))]
              [val (parse-sx (sx-ref def 1))]
              [expr (parse-sx (sx-ref sx 2))])
         (Let1 id val expr))]
      [(mx? `(lam (SYMBOL ...) ANY))
       (let* ([ids (map s-exp->symbol (s-exp->list (sx-ref sx 1)))]
              [body (px 2)])
         (Lam ids body))]
    [(mx? `(+ ANY ANY)) (Add (px 1) (px 2))]
    [(mx? `(- ANY ANY)) (Sub (px 1) (px 2))]
    [(mx? `(* ANY ANY)) (Mul (px 1) (px 2))]
    [(mx? `(/ ANY ANY)) (Div (px 1) (px 2))]
    [(mx? `(ANY ANY ...))
     (let ([exprs (map parse-sx (s-exp->list sx))])
       (Call (first exprs) (rest exprs)))]
    [else (parse-error sx)])))

(define-type ENV
  [EmptyEnv]
  [Extend (name : Symbol) (val : VAL) (rest : ENV)])

(define-type VAL
  [NumV (n : Number)]
  [FunV (args : (Listof Symbol)) (body : FLANG) (env : ENV)])

(define (lookup name env)
  (type-case ENV env
    [(EmptyEnv) (error 'lookup (string-append "no binding for " (to-string name)))]
    [(Extend id val rest-env)
     (if (eq? id name) 
	 val 
	 (lookup name rest-env))]))

;; gets a Racket numeric binary operator, 
;; uses it within a NumV wrapper
(define (arith-op op val1 val2)
  (local 
      [(define (NumV->number v)
         (type-case VAL v
           [(NumV n) n]
           [else (error 'arith-op 
                        (string-append "expects a number, got: " (to-string v)))]))]
    (NumV (op (NumV->number val1) 
              (NumV->number val2)))))

;; evaluates FLANG expressions by reducing them to values
(define (interp expr env)
  (type-case FLANG expr
    [(Num n) (NumV n)]
    [(Add l r) (arith-op + (interp l env) (interp r env))]
    [(Sub l r) (arith-op - (interp l env) (interp r env))]
    [(Mul l r) (arith-op * (interp l env) (interp r env))]
    [(Div l r) (arith-op / (interp l env) (interp r env))]
    [(Let1 bound-id named-expr bound-body)
     (interp bound-body
             (Extend bound-id (interp named-expr env) env))]
    [(Id name) (lookup name env)]
    [(Lam params bound-body)
     (FunV params bound-body env)]
    [(Call fun-expr arg-exprs)
     (let ([fval (interp fun-expr env)])
       (type-case VAL fval
         [(FunV params bound-body f-env)
          (letrec ([rec-env (lambda ([prms : (Listof Symbol)] [args : (Listof FLANG)] [envs : ENV])
                             (if(empty? args) (begin
                                                (display "envs1")
                                                (display envs)
                                                envs)
                                               (begin
                                                 (Extend (first prms) (interp (first args) env) envs)
                                                 (display "prms")
                                                 (display prms)
                                                 (display "args")
                                                 (display args)
                                                 (display "envs2")
                                                 (display envs)
                                                 (display "after envs2")
                                                 (rec-env (rest prms) (rest args) envs))))])
            (interp bound-body (rec-env params arg-exprs f-env)))]
         [else (error 'interp
                      (string-append "`call' expects a function, got: "
                                     (to-string fval)))]))]))
(module+ test
  ;; test no arguments
  (test (run `{let1 {g {lam {} 42}}
                    {g}})
        42)

  


  (test (parse-sx `(* 2 3)) (Mul (Num 2) (Num 3)))

  

  ;; test multiple arguments, lexical scope
  (test (run `{let1 {z 3}
                    {let1 {f {lam {x y} {/ {- x y} z}}}
                          {let1 {z 2}
                                {f 15 12}}}})
        1)

  ;; higher order function
  (test (run `{let1 {identity {lam {x} x}}
                    {let1 {plus {lam {x y} {+ x y}}}
                          {{identity plus}  123 1}}})
        124)

  ;; higher order function with multiple arguments
  (test (run `{let1 {apply {lam {f x y} {f x y}}}
                    {let1 {plus {lam {x y} {+ x y}}}
                          {apply plus 123 1}}})
        124)
  )

;; evaluate a FLANG program contained in an s-expression
(define (run s-exp)
  (let ([result (interp (parse-sx s-exp) (EmptyEnv))])
    (type-case VAL result
      [(NumV n) n]
      [else (error 'run
                   (string-append "evaluation returned a non-number: " (to-string result)))])))

;; error handling paths
(module+ test
  (test/exn (parse-sx `{}) "parse error")
  (test/exn (run `{+ x 1}) "no binding")
  (test/exn (run `{+ 1 {lam {x} x}}) "expects a number")
  (test/exn (run `{1 1}) "expects a function")
  (test/exn (run `{lam {x} x}) "returned a non-number")
  )

(module+ test
  
  (test (run `{let1 {x 3}
                    {let1 {f {lam {y} {+ x y}}}
                          {let1 {x 5}
                                {f 4}}}})    7)
  (test (run `{{let1 {x 3}
                     {lam {y} {+ x y}}}
               4})    7)
  (test (run `{{{lam {x} {x 1}}
                {lam {x} {lam {y} {+ x y}}}}
               123})
        124)

  (test (run `{{lam {x} {+ x 1}} 4})  5)
  (test (run `{let1 {add3 {lam {x} {+ x 3}}}
                    {add3 1}})   
        4)
  (test (run `{let1 {add3 {lam {x} {+ x 3}}}
                    {let1 {add1 {lam {x} {+ x 1}}}
                          {let1 {x 3}
                                {add1 {add3 x}}}}})  7)


  (test (run `{let1 {identity {lam {x} x}}
                    {let1 {foo {lam {x} {+ x 1}}}
                          {{identity foo} 
                           123}}})         124)
  )

(define (duplicate-symbol? lst)
  (cond
    [(empty? lst) #f]
    [(check-member (first lst) (rest lst)) #t]
    [else (duplicate-symbol? (rest lst))]))

(define (check-member x lst)
  (cond
    [(empty? lst) #f]
    [(equal? x (first lst)) #t]
    [else (member x (rest lst))]))

(module+ test
  (test (duplicate-symbol? '()) #f)
  (test (duplicate-symbol? '(a b c)) #f)
  (test (duplicate-symbol? '(a b c d b e)) #t)
  




  )

(define minutes-spent 1200)



