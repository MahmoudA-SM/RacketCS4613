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
    [(Id name) (lookup name env)]
    [(Let1 id named-expr bound-body) 
     (let ([val (interp named-expr env)])
       (interp bound-body (Extend id val env)))]
    [(Lam params body) (FunV params body env)]
    [(Call fun vals)
     (let* ([fun-val (interp fun env)]
            [FunV fun-params fun-body fun-env (type-case VAL fun-val
                                                 [FunV x] x
                                                 [else (error 'interp 
                                                              (string-append "not a function: " (to-string fun-val)))])]
            [arg-vals (map (lambda (arg) (interp arg env)) vals)]
            [new-env (foldl (lambda (param val acc) (Extend param val acc)) fun-env (map cons fun-params arg-vals))])
       (interp fun-body new-env))]))


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
