#lang plait
(define-type FAE
  [Num (n : Number)]
  [Bool (b : Boolean)]
  [Not (expr : FAE)]
  [Add (lhs : FAE)
       (rhs : FAE)]
  [Sub (lhs : FAE)
       (rhs : FAE)]
  [Mul (lhs : FAE)
       (rhs : FAE)]
  [Cons (fst : FAE)
        (rst : FAE)]
  [Lst (elements : (Listof FAE))]
  [If0 (test-expr : FAE)
       (then-expr : FAE)
       (else-expr : FAE)]
  [Rec (name : Symbol)
       (ty : TE)
       (rhs-expr : FAE)
       (body-expr : FAE)]
  [Id (name : Symbol)]
  [Lam (param : Symbol)
       (argty : TE)
       (body : FAE)]
  [Call (fun-expr : FAE)
        (arg-expr : FAE)])

(define-type TE
  [NumTE]
  [BoolTE]
  [ArrowTE (arg : TE)
           (result : TE)]
  [GuessTE]
  [ListTE (element-te : TE)])

(define-type FAE-Value
  [NumV (n : Number)]
  [BoolV (b : Boolean)]
  [ClosureV (param : Symbol)
            (body : FAE)
            (env : ValueEnv)]
  [ListV (elements : (Listof FAE-Value))])

(define-type ValueEnv
  [EmptyValueEnv]
  [BindValue (name : Symbol)
             (value : FAE-Value)
             (rest : ValueEnv)]
  [RecBindValue (name : Symbol)
                (value-box : (Boxof FAE-Value))
                (rest : ValueEnv)])

(define-type Type
  [NumT]
  [BoolT]
  [ArrowT (arg : Type)
          (result : Type)]
  [VarT (id : Number)
        (val : (Boxof (Optionof Type)))]
  [ListT (element : Type)])

(define-type TypeEnv
  [EmptyTypeEnv]
  [BindType (name : Symbol)
            (type : Type)
            (rest : TypeEnv)])


(define (numzero? x) (= 0 (NumV-n x)))

;; interp : FAE Env -> FAE-Value
(define (interp a-fae env)
  (type-case FAE a-fae
    [(Num n) (NumV n)]
    [(Bool b) (BoolV b)]
    [(Not e) (BoolV (not (BoolV-b (interp e env))))]
    [(Add l r) (num+ (interp l env) (interp r env))]
    [(Sub l r) (num- (interp l env) (interp r env))]
    [(Mul l r) (num* (interp l env) (interp r env))]
    [(Id name) (lookup name env)]
    [(If0 test then-part else-part)
     (if (numzero? (interp test env))
         (interp then-part env)
         (interp else-part env))]
    [(Cons l r) ....]
    [(Lst elements) ....]
    [(Rec bound-id type named-expr body-expr)
     (let* ([value-holder (box (NumV 42))]
            [new-env (RecBindValue bound-id value-holder env)])
       (begin
         (set-box! value-holder (interp named-expr new-env))
         (interp body-expr new-env)))]
    [(Lam param arg-te body-expr)
     (ClosureV param body-expr env)]
    [(Call fun-expr arg-expr)
     (local [(define fun-val
               (interp fun-expr env))
             (define arg-val
               (interp arg-expr env))]
       (interp (ClosureV-body fun-val)
             (BindValue (ClosureV-param fun-val)
                        arg-val
                        (ClosureV-env fun-val))))]))

;; num-op : (Number Number -> Number) -> (FAE-Value FAE-Value -> FAE-Value)
(define (num-op op op-name x y)
  (NumV (op (NumV-n x) (NumV-n y))))

(define (num+ x y) (num-op + '+ x y))
(define (num- x y) (num-op - '- x y))
(define (num* x y) (num-op * '* x y))

(define (lookup name env)
  (type-case ValueEnv env
    [(EmptyValueEnv) (error 'lookup "free variable")]
    [(BindValue sub-name num rest-env)
     (if (equal? sub-name name)
         num
         (lookup name rest-env))]
    [(RecBindValue sub-name val-box rest-env)
     (if (equal? sub-name name)
         (unbox val-box)
         (lookup name rest-env))]))

(define (parse-error sx)
  (error 'parse (string-append "parse error: " (to-string sx))))

(define (sx-ref sx n) (list-ref (s-exp->list sx) n))
(define (parse sx)
  (local
      [(define (px i) (parse (sx-ref sx i)))]
    (cond
      [(s-exp-number? sx) (Num (s-exp->number sx))]
      [(s-exp-symbol? sx)
       (let ([sym (s-exp->symbol sx)])
         (case sym
           [(true) (Bool #t)]
           [(false) (Bool #f)]
           [else (Id sym)]))]
      [(s-exp-match? `(list ANY ...) sx)
       (Lst (map (lambda (elt) (parse elt)) (rest (s-exp->list sx))))]
      [(s-exp-match? `(lam (SYMBOL : ANY) ANY) sx)
       (let* ([args (sx-ref sx 1)]
              [id (s-exp->symbol (sx-ref args 0))]
              [te (parse-te (sx-ref args 2))]
              [body (px 2)])
         (Lam id te body))]
      [(s-exp-match? `(rec (SYMBOL : ANY) ANY ANY) sx)
       (let* ([args (sx-ref sx 1)]
              [id (s-exp->symbol (sx-ref args 0))]
              [te (parse-te (sx-ref args 2))]
              [rhs (px 2)]
              [body (px 3)])
         (Rec id te rhs body))]
      [(s-exp-match? `(ANY ANY) sx)
       (cond
         [(equal? (sx-ref sx 0) `not) (Not (px 1))]
         [else (Call (px 0) (px 1))])]
      [(s-exp-list? sx)
       (case (s-exp->symbol (sx-ref sx 0))
         [(+) (Add (px 1) (px 2))]
         [(-) (Sub (px 1) (px 2))]
         [(*) (Mul (px 1) (px 2))]
         [(if0) (If0 (px 1) (px 2) (px 3))]
         [(cons) (Cons (px 1) (px 2))]
         [else (parse-error sx)])]
      [else (parse-error sx)])))

(define (parse-te sx)
  (cond
    [(s-exp-symbol? sx)
     (case (s-exp->symbol sx)
       [(num) (NumTE)]
       [(bool) (BoolTE)]
       [(?) (GuessTE)])]
    [(s-exp-match? `(list ANY) sx)
     (ListTE (parse-te (sx-ref sx 1)))]
    [(s-exp-match? `(ANY -> ANY) sx)
     (ArrowTE (parse-te (sx-ref sx 0)) (parse-te (sx-ref sx 2)))]))

(module+ test
  (define fact-rec
    (Rec 'fact (ArrowTE (NumTE) (NumTE))
         (Lam 'n (NumTE)
              (If0 (Id 'n)
                   (Num 1)
                   (Mul (Id 'n) (Call (Id 'fact) (Sub (Id 'n) (Num 1))))))
         (Call (Id 'fact) (Num 5))))

  (define fact-rec-concrete
    `{rec {fact : {num -> num}}
          {lam {n : num}
               {if0 n 1
                    {* n {fact {- n 1}}}}}
          {fact 5}})

  (define fib-rec
    (Rec 'fib (ArrowTE (NumTE) (NumTE))
         (Lam 'x (NumTE)
              (If0 (Id' x)
                   (Num 1)
                   (If0 (Sub (Id 'x) (Num 1))
                        (Num 1)
                        (Add (Call (Id 'fib) (Sub (Id 'x) (Num 1)))
                             (Call (Id 'fib) (Sub (Id 'x) (Num 2)))))))
         (Call (Id 'fib) (Num 4))))

  (define fib-rec-concrete
    `{rec {fib : {num -> num}}
          {lam {x : num}
               {if0 x 1
                    {if0 {- x 1}
                         1
                         {+ {fib {- x 1}}
                            {fib {- x 2}}}}}}
          {fib 4}})
  )

(module+ test
  (print-only-errors #t)
  (test (parse `3) (Num 3))
  (test (parse `x) (Id 'x))
  (test (parse `{+ 1 2}) (Add (Num 1) (Num 2)))
  (test (parse `{- 1 2}) (Sub (Num 1) (Num 2)))
  (test (parse `{lam {x : num} x}) (Lam 'x (NumTE) (Id 'x)))
  (test (parse `{f 2}) (Call (Id 'f) (Num 2)))
  (test (parse `{if0 0 1 2}) (If0 (Num 0) (Num 1) (Num 2)))

  ;; parse multi-element list
  (test (parse `{list f 2}) (Lst (list (Id 'f) (Num 2))))

  ;; parse single elementt list in function
  (test (parse `{lam {x : num} {list x}})
        (Lam 'x (NumTE) (Lst (list (Id 'x)))))

  ;; parse list type annotation
  (test (parse `{lam {x : {list num}} x}) (Lam 'x (ListTE (NumTE)) (Id 'x)))

  (test/exn (parse `"foo") "parse error")
  (test/exn (parse `{foo}) "parse error")
  (test (parse
         `{{lam {x : num}
                {{lam {f : {num -> num}}
                      {+ {f 1}
                         {{lam {x : num}
                               {f 2}}
                          3}}}
                 {lam {y : num} {+ x y}}}}
           0})
        (Call (Lam 'x (NumTE)
                   (Call (Lam 'f (ArrowTE (NumTE) (NumTE))
                              (Add (Call (Id 'f) (Num 1))
                                   (Call (Lam 'x (NumTE)
                                              (Call (Id 'f)
                                                    (Num 2)))
                                         (Num 3))))
                         (Lam 'y (NumTE)
                              (Add (Id 'x) (Id 'y)))))
              (Num 0)))

  (test (parse fib-rec-concrete) fib-rec))

;; ----------------------------------------

(define (type-lookup name-to-find env)
  (type-case TypeEnv env
    [(EmptyTypeEnv ) (error 'type-lookup "free variable, so no type")]
    [(BindType name ty rest)
     (if (symbol=? name-to-find name)
         ty
         (type-lookup name-to-find rest))]))

;; ----------------------------------------

(define gen-tvar-id!
  (let ((counter 0))
    (lambda ()
      (begin
        (set! counter (add1 counter))
        counter))))

(define (parse-type te)
  (type-case TE te
    [(NumTE) (NumT)]
    [(BoolTE) (BoolT)]
    [(ArrowTE a b) (ArrowT (parse-type a)
                           (parse-type b))]
    [(GuessTE)(VarT (gen-tvar-id!) (box (none)))]
    [(ListTE element-te) (ListT (parse-type element-te))]))

(define (resolve t)
  (type-case Type t
    [(VarT id val)
     (type-case (Optionof Type) (unbox val)
       [(none) t]
       [(some t2) (resolve t2)])]
    [else t]))

(define (uses-type-var? id t)
  (type-case Type (resolve t)
    [(VarT t-id val) (= id t-id)]
    [(ArrowT a b)
     (or (uses-type-var? id a)
         (uses-type-var? id b))]
    [else #f]))

(define (occurs? r t)
  (type-case Type r
    [(VarT id val)
     (type-case Type (resolve t)
       [(ArrowT a b) (uses-type-var? id t)]
       [else #f])]
    [else #f]))

(define (type-error fae t1 t2)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string fae)
                      (string-append
                       " type "
                       (string-append
                        (to-string t1)
                        (string-append
                         " vs. "
                         (to-string t2))))))))

(define (unify-type-var! T tau2 expr)
  (type-case Type T
    [(VarT id val)
     (type-case (Optionof Type) (unbox val)
       [(some tau1) (unify! tau1 tau2 expr)]
       [(none)
        (let ([t3 (resolve tau2)])
          (cond
            [(equal? T t3) (void)] ;; nothing to unify, same type variables
            [(occurs? T t3)  (type-error expr T t3)]
            [else  (set-box! val (some t3))]))])]
    [else
     (error 'unify-type-var! (string-append "not a type variable " (to-string T)))]))

(define (unify-assert! tau type-val expr)
  (unless (equal? tau type-val)
    (type-error expr tau type-val)))

;; third argument is just for error reporting
(define (unify! t1 t2 expr)
  (type-case Type t1
    [(VarT id is1) (unify-type-var! t1 t2 expr)]
    [else
     (type-case Type t2
       [(VarT id2 is2) (unify-type-var! t2 t1 expr)]
       [(NumT) (unify-assert! t1 (NumT) expr)]
       [(BoolT) (unify-assert! t1 (BoolT) expr)]
       [(ListT elt-type) ....]
       [(ArrowT a2 b2)
        (type-case Type t1
          [(ArrowT a1 b1)
           (begin
             (unify! a1 a2 expr)
             (unify! b1 b2 expr))]
          [else (type-error expr t1 t2)])])]))

(define (typecheck [fae : FAE] [env : TypeEnv]) : Type
  (type-case FAE fae
    [(Num n) (NumT)]
    [(Bool b) (BoolT)]
    [(Not ex) (begin
                (unify! (typecheck ex env) (BoolT) ex)
                (BoolT))]
    [(Mul l r) (begin
                 (unify! (typecheck l env) (NumT) l)
                 (unify! (typecheck r env) (NumT) r)
                 (NumT))]
    [(Add l r) (begin
                 (unify! (typecheck l env) (NumT) l)
                 (unify! (typecheck r env) (NumT) r)
                 (NumT))]
    [(Sub l r) (begin
                 (unify! (typecheck l env) (NumT) l)
                 (unify! (typecheck r env) (NumT) r)
                 (NumT))]
    [(Cons l r) ....]
    [(Lst elements) ....]
    [(Id name) (type-lookup name env)]
    [(Lam name te body)
     (let* ([arg-type (parse-type te)]
            [res-type (typecheck body (BindType name arg-type env))])
       (ArrowT arg-type res-type))]
    [(Call fn arg)
     (let ([r-type (VarT (gen-tvar-id!) (box (none)))]
           [a-type (typecheck arg env)]
           [fn-type (typecheck fn env)])
       (begin
         (unify! (ArrowT a-type r-type) fn-type fn)
         r-type))]
    [(If0 test-expr then-expr else-expr)
     (let ([test-ty (typecheck test-expr env)]
           [then-ty (typecheck then-expr env)]
           [else-ty (typecheck else-expr env)])
       (begin
         (unify! test-ty (NumT) test-expr)
         (unify! then-ty else-ty else-expr)
         then-ty))]
    [(Rec name ty rhs-expr body-expr)
     (let* ([type-ann (parse-type ty)]
            [new-env (BindType name type-ann env)]
            [rhs-ty (typecheck rhs-expr new-env)])
       (begin
         (unify! type-ann rhs-ty rhs-expr)
         (typecheck body-expr new-env)))]))

;; ----------------------------------------
(define (run s-expr)
  (interp (parse s-expr) (EmptyValueEnv)))

(define (check s-expr)
  (typecheck (parse s-expr) (EmptyTypeEnv)))

(define-syntax-rule (test/type expr type)
  (test
   (begin (unify! (check expr) type expr) type)
   type))

(define-syntax-rule (test/notype expr) (test/exn (check expr) "no type"))

(module+ test
  ;; lists of numbers
  (test (run `{list 1 2})
        (ListV (list (NumV 1) (NumV 2))))
  (test/type `{list 1 2} (ListT (NumT)))

  ;; lists of booleans
  (test (run `{list false true})
        (ListV (list (BoolV #f) (BoolV #t))))

  ;; report error for mixed types
  (test/notype  `{list 1 true})

  ;; infer type of list
  (test/type `{lam {x : num} {list x}} (ArrowT (NumT) (ListT (NumT))))

  ;; report error for mixed inferred types
  (test/notype `{lam {x : num} {list true x}})

  ;; infer type of function parameter from list element
  (test/type `{lam {x : ?} {list x 1}} (ArrowT (NumT) (ListT (NumT))))

  ;; complain about cyclic type (Y-combinator) inside list
  (test/notype `{lam {x : ?} {list {x x}}})

  ;; infer type of list from function application
  (test/type `{{lam {x : ?} {list x}} 2} (ListT (NumT)))
  )

(module+ test
  ;; cons to empty list
  (test (run `{cons 1 {list}}) (ListV (list (NumV 1))))
  (test/type `{cons 1 {list}} (ListT (NumT)))

  ;; cons to non-empty list
  (test (run `{cons 1 {list 2}}) (ListV (list (NumV 1) (NumV 2))))
  (test/type `{cons 1 {list 2}} (ListT (NumT)))

  ;; infer type of cons
  (test/type `{lam {x : ?} {cons x {list 1}}} (ArrowT (NumT) (ListT (NumT)))) ;; inferen

  ;; report error for cyclic type
  (test/notype `{lam {x : ?} {cons x x}})
  )

(module+ test
  (print-only-errors #t)

  (test (check `{+ 1 2}) (NumT))
  (test/exn (run `x) "free variable")
  (test (run `{not false}) (BoolV #t))
  (test (run `10) (NumV 10))
  (test (run `{+ 10 17}) (NumV 27))
  (test (run `{- 10 7}) (NumV 3))
  (test (run `{{lam {x : num} {+ x 12}} {+ 1 17}}) (NumV 30))

  (test (interp (Id 'x)
              (BindValue 'x (NumV 10) (EmptyValueEnv)))
        (NumV 10))

  (define fun-lam
    `{{lam {x : num}
           {{lam {f : (num -> num)}
                 {+ {f 1}
                    {{lam {x : num}
                          {f 2}}
                     3}}}
            {lam {y : num}
                 {+ x y}}}}
      0})

  (test (run fun-lam)
        (NumV 3))
  )

(module+ test
  (print-only-errors #t)

  (test/notype `x)

  (test/notype `{not 1})

  (test/type `{not false} (BoolT))

  (test/type fun-lam (NumT))

  (test/type  `10 (NumT))

  (test/type `{+ 10 17} (NumT))
  (test/type `{- 10 7} (NumT))

  (test/notype `{+ false 17})
  (test/notype `{- false 17})
  (test/notype `{+ 17 false})
  (test/notype `{- 17 false})

  (test/type `{lam {x : num} {+ x 12}}
             (ArrowT (NumT) (NumT)))

  (test/notype `{{lam {x : num} x} true})

  (test/type `{lam {x : num} {lam {y : bool} x}}
             (ArrowT (NumT) (ArrowT (BoolT)  (NumT))))

  (test/type `{{lam {x : num} {+ x 12}} {+ 1 17}} (NumT))

  (test/notype `{1 2})

  (test/notype `{+ {lam {x : num}  12} 2})

  ;; Added coverage test for type-to-string
  (test/notype `{{lam {f : {num -> num}}
                      {f 1}}
                 1})
  )

(module+ test
  (print-only-errors #t)
  ;; Tests for if0
  (test (run `{if0 0 1 0}) (NumV 1))
  (test (run `{if0 1 1 0}) (NumV 0))

  (test/type `{if0 0 1 0} (NumT))
  (test/type `{if0 1 1 0} (NumT))

  (test/notype `{if0 0 {lam {x : num} x} 0})
  (test/notype `{if0 {lam {x : num} x} 0 0})
  )

(module+ test
  (print-only-errors #t)

  ;; Tests for Rec
  (test (parse fact-rec-concrete) fact-rec)

  (test/type fib-rec-concrete (NumT))
  (test (interp fib-rec (EmptyValueEnv)) (NumV 5))

  (test/type fact-rec-concrete (NumT))
  (test (interp fact-rec (EmptyValueEnv)) (NumV 120))

  (test/notype `{rec {x : num} {lam {y : num} 3} 10})

  ;; Contrived test to get full coverage of lookup
  (test (interp (Rec 'x (NumTE)
                   (Num 10)
                   (Rec 'y (NumTE)
                        (Num 10)
                        (Id 'x)))
              (EmptyValueEnv))
        (NumV 10)))

(module+ test

  (test/type `{{lam {x : ?} {+ x 12}} {+ 1 17}} (NumT))

  ;; illustrate that the return of our typecheck function can be a bit messy
  (define wrapped-type (check `{{lam {x : ?} {+ x 12}} {+ 1 17}}))
  (test (VarT? wrapped-type) #t)
  (test (VarT-val wrapped-type) (box (some (NumT))))

  (test/type  `{lam {x : ?} {+ x 12}} (ArrowT (NumT) (NumT)))

  (test/type  `{lam {x : ?} {if0 0 x x}} (ArrowT (NumT) (NumT)))

  (test/exn (unify! (typecheck (Lam 'x (GuessTE) (Add (Id 'x) (Num 12)))
                               (EmptyTypeEnv))
                    (ArrowT (BoolT) (NumT))
                    (Num -1))
            "no type")

  ;; soundness bug still exists
  #;(test/exn (typecheck (Rec 'f (ArrowTE (NumTE) (NumTE)) (Id 'f) (Call (Id 'f) (Num 10)))
                         (EmptyTypeEnv))
              "no type"))
