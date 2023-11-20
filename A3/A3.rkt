
#lang plait

(print-only-errors #t)

(define-type BRANG
  [Num  (n : Number)]
  [Add  (l : BRANG) (r : BRANG)]
  [Sub  (l : BRANG) (r : BRANG)]
  [Mul  (l : BRANG) (r : BRANG)]
  [Div  (l : BRANG) (r : BRANG)]
  [Id   (s : Symbol)]
  [Let1 (id : Symbol) (bound-expr : BRANG) (body : BRANG)]
  [Lam  (arg : Symbol) (body : BRANG)]
  [Call (func : BRANG) (argval : BRANG)]) ; Note first type


(define-type CORE
  [CNum  (n : Number)]
  [CAdd  (l : CORE) (r : CORE)]
  [CSub  (l : CORE) (r : CORE)]
  [CMul  (l : CORE) (r : CORE)]
  [CDiv  (l : CORE) (r : CORE)]
  [CRef  (ref : Number)]
  [CLet1 (l : CORE) (r : CORE)]
  [CLam  (body : CORE)]
  [CCall (l : CORE) (r : CORE)]) 

(define (parse-error sx)
  (error 'parse-sx (string-append "parse error: " (to-string sx))))

(define (sx-ref sx n) (list-ref (s-exp->list sx) n))

(define (parse-sx sx)
  (cond
    [(s-exp-number? sx) (Num (s-exp->number sx))]
    [(s-exp-symbol? sx) (Id (s-exp->symbol sx))]
    [(s-exp-match? `(let1 (SYMBOL ANY) ANY) sx)
     (let* ([def (sx-ref sx 1)]
            [id (s-exp->symbol (sx-ref def 0))]
            [val (parse-sx (sx-ref def 1))]
            [expr (parse-sx (sx-ref sx 2))])
       (Let1 id val expr))]
    [(s-exp-match? `(lam SYMBOL ANY) sx)
     (let* ([id (s-exp->symbol (sx-ref sx 1))]
            [body (parse-sx (sx-ref sx 2))])
       (Lam id body))]
    [(s-exp-match? `(ANY ANY) sx)
     (Call (parse-sx (sx-ref sx 0))
           (parse-sx (sx-ref sx 1)))]
    [(s-exp-list? sx)
     (let* ([l (lambda () (parse-sx (sx-ref sx 1)))]
            [r (lambda () (parse-sx (sx-ref sx 2)))])
       (case (s-exp->symbol (sx-ref sx 0))
         [(+) (Add (l) (r))]
         [(-) (Sub (l) (r))]
         [(*) (Mul (l) (r))]
         [(/) (Div (l) (r))]
         [else (parse-error sx)]))]
    [else (parse-error sx)]))

(define-type VAL
  [NumV (n : Number)]
  [LamV (body : CORE)])

(define (arith-op op expr1 expr2)
  (local
      [(define (NumV->number e)
         (type-case VAL e
           [(NumV n) n]
           [else (error 'arith-op "expects a number")]))]
    (NumV (op (NumV->number expr1) 
              (NumV->number expr2)))))

(define-type-alias DE-ENV (Listof Symbol))

(define (de-lookup sym env)
  (cond
    [(empty? env) (error 'de-lookup (string-append "undefined identifier " (to-string sym)))]
    [(eq? sym (first env)) 0]
    [else (add1 (de-lookup sym (rest env)))]))

(define (de-extend s l) (cons s l))

(define (de-empty-env) empty)

(module+ test
  (test/exn (de-lookup 'x (de-empty-env))  "undefined identifier")
  (test (de-lookup 'x (de-extend 'x (de-empty-env))) 0)
  (test (de-lookup 'x (de-extend 'y (de-extend 'x (de-empty-env)))) 1)
  (test (de-lookup 'x (de-extend 'x (de-extend 'x (de-empty-env)))) 0)
  (test (de-lookup
         'y
         (de-extend 'x
                    (de-extend 'x
                               (de-extend 'y (de-empty-env))))) 2)
  (test/exn (de-lookup 'x (de-empty-env)) "undefined identifier")
  )

(define (preprocess brang-exp env)
  (type-case BRANG brang-exp
    [(Num n) (CNum n)]
    [(Add l r) (CAdd (preprocess l env) (preprocess r env))]
    [(Sub l r) (CSub (preprocess l env) (preprocess r env))]
    [(Mul l r) (CMul (preprocess l env) (preprocess r env))]
    [(Div l r) (CDiv (preprocess l env) (preprocess r env))]
    [(Let1 bound-id named-expr bound-body) (CLet1
                                            (preprocess named-expr
                                                        (de-extend bound-id env))
                                            (preprocess bound-body
                                                        (de-extend bound-id env)))]
    [(Id name) (CRef (de-lookup name env))]
    [(Lam bound-id bound-body) (CLam
                                (preprocess bound-body
                                            (de-extend bound-id env))
                                )
                               ]
    [(Call fun-expr arg-expr) (CCall
                               (preprocess fun-expr env)
                               (preprocess arg-expr env))
                              ]
    )
  )

(module+ test
  (define test-env (de-extend 'x (de-extend 'z (de-extend 'y (de-empty-env)))))
  (test (preprocess (Id 'x) test-env) (CRef 0))
  ;testing addition for preprocess
  (test (preprocess (Add (Id 'x) (Id 'y)) test-env) (CAdd (CRef 0) (CRef 2)))
  ;testing addition for preprocess
  (test (preprocess (Sub (Id 'x) (Id 'y)) test-env) (CSub (CRef 0) (CRef 2)))
  (test (preprocess (Mul (Id 'x) (Id 'y)) test-env) (CMul (CRef 0) (CRef 2)))
  (test (preprocess (Div (Id 'x) (Id 'y)) test-env) (CDiv (CRef 0) (CRef 2)))

  (test (preprocess (parse-sx `{{lam x {+ x 1}} 4}) (de-empty-env))
        (CCall (CLam (CAdd (CRef 0) (CNum 1))) (CNum 4)))

  (test (preprocess (parse-sx `{{lam x {+ x z}} 4}) test-env)
        (CCall (CLam (CAdd (CRef 0) (CRef 2))) (CNum 4)))

  (test (preprocess (parse-sx `{let1 {add3 {lam x {+ x 3}}} {add3 1}})
                    (de-empty-env))
        (CLet1 (CLam (CAdd (CRef 0) (CNum 3))) (CCall (CRef 0) (CNum 1))))
  )

;; replaces a reference to scope `level' with val
(define (subst expr level val)
  (type-case CORE expr
    [(CNum n) expr]
    [(CAdd l r) (CAdd (subst l level val) (subst r level val))]
    [(CSub l r) (CSub (subst l level val) (subst r level val))]
    [(CMul l r) (CMul (subst l level val) (subst r level val))]
    [(CDiv l r) (CDiv (subst l level val) (subst r level val))]
    [(CRef offset) (if
                    (eq? offset level)
                    val
                    (subst expr (+ 1 level) val)) ]
    [(CLet1 named-expr bound-body) (CLet1 (subst named-expr level val)
                                       bound-body)]
    [(CCall l r) (CCall
                  (subst l level val)
                  (subst r level val))]
    [(CLam bound-body)
     (CLam
      (subst bound-body level val))
     ]
    )
  )

(module+ test
  ;; {+ x 1}}[3/x]
  (test (subst (CAdd (CRef 0) (CNum 1)) 0 (CNum 3))
        (CAdd (CNum 3) (CNum 1)))
  (test (subst (CSub (CRef 0) (CNum 1)) 0 (CNum 3))
        (CSub (CNum 3) (CNum 1)))
  (test (subst (CMul (CRef 0) (CNum 1)) 0 (CNum 3))
        (CMul (CNum 3) (CNum 1)))
  (test (subst (CDiv (CRef 0) (CNum 1)) 0 (CNum 3))
        (CDiv (CNum 3) (CNum 1)))
  ;; {let1 {x 3} {+ x 1}}[2/x]
  (test (subst (CLet1 (CNum 3) (CAdd (CRef 0) (CNum 1))) 0 (CNum 2))
        (CLet1 (CNum 3) (CAdd (CRef 0) (CNum 1))))
  ;; {let1 {x 3} {lam y {+ x 1}}} => {lam y {+ x 1}}[3/x]
  (test (subst (CLam (CAdd (CRef 1) (CNum 1))) 0 (CNum 3))
        (CLam (CAdd (CNum 3) (CNum 1))))

 

  )

(define (eval expr)
  (type-case CORE expr
    [(CNum n) (NumV n)]
    [(CAdd l r) (arith-op + (eval l) (eval r))]
    [(CSub l r) (arith-op - (eval l) (eval r))]
    [(CMul l r) (arith-op * (eval l) (eval r))]
    [(CDiv l r) (arith-op / (eval l) (eval r))]
    [(CLet1 named-expr bound-body) (eval (subst bound-body 0 named-expr))]
    [(CRef offset) (NumV offset)]
    [(CLam bound-body) (LamV bound-body)]
    [(CCall fun arg-expr)
     (type-case VAL (eval fun)
       [(LamV bound-body)
        (eval
         (subst bound-body 0 arg-expr))]
       [else
        (error 'eval "non-function")
        ]
       )
     ]
    )
  )



(module+ test
  (test (eval (CCall (CLam (CAdd (CRef 0) (CNum 1))) (CNum 4))) (NumV 5))
  ; adds the value of the lambda expression argument to 2
  (test (eval (CCall (CLam (CAdd (CRef 0) (CNum 2))) (CNum 4))) (NumV 6))
  ; multiplies the value of the lambda expression argument by 3
  (test (eval (CCall (CLam (CMul (CRef 0) (CNum 3))) (CNum 4))) (NumV 12))
  ; subtracts 1 from the value of the lambda expression argument 
  (test (eval (CCall (CLam (CSub (CRef 0) (CNum 1))) (CNum 4))) (NumV 3))
  ; divides the value of the lamda expression argument by 2
  (test (eval (CCall (CLam (CDiv (CRef 0) (CNum 2))) (CNum 4))) (NumV 2))
  ;adds the value of the lambda expression argument to 1
  (test (eval (CCall (CLam (CAdd (CNum 1) (CRef 0))) (CNum 4))) (NumV 5))
  ;checks if the expression raises an exception with a specific
  ;error message. In this case, the expected error message is "non-function".
  (test/exn (eval (CCall (CNum 4) (CNum 4))) "non-function")
  ; The CRef form is expected to return a NumV with
  ;the same value as the offset, which is 1 in this case.
  (test (eval (CRef 1)) (NumV 1))



  
  (test (eval
         (CLet1 (CLam (CAdd (CRef 0) (CNum 3))) (CCall (CRef 0) (CNum 1))))
        (NumV 4))

  )



;; evaluate a BRANG program contained in a s-expr
(define (run sx)
  (let ([result (eval (preprocess (parse-sx sx) empty))])
    (type-case VAL result
      [(NumV n) n]
      [else (error 'run
                   (string-append "evaluation returned a non-number: " (to-string result)))])))

(module+ test
  (test (run `{{lam x {+ x 1}} 4})
        5)
  (test (run `{let1 {add3 {lam x {+ x 3}}}
                    {add3 1}})
        4)

  (test/exn (run `(let1 (y 5)(lam x (+ x y)))) "evaluation returned a non-number")
  ;parse addition test
  (test (run `{{lam x (+ x 2)}2}) 4)

  ;parse subtraction test
  (test (run `{{lam x (- x 2)}2}) 0)

  ;parse multiplication test
  (test (run `{{lam x (* x 2)}3}) 6)

  ;parse division test
  (test (run `{{lam x (/ x 2)} 2}) 1)

  (test/exn (parse-sx ` "tooMuch")"parse-sx")
  
  ;parse error test
  (test/exn (run `{{lam x (p x 4)} 2}) "parse-sx")
  ;arith op expects a number test
  (test/exn (arith-op * (LamV (CNum 8)) (NumV 22)) "expects a number")

  )



(define minutes-spent 600)
