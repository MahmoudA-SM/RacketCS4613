#lang plait

(print-only-errors #f)

(define-type ArgPair
  [argpair (arg : Symbol) (expr : L*AE)])

(define-type L*AE
  [Num  (val : Number)]
  [Add  (l : L*AE) (r : L*AE)]
  [Sub  (l : L*AE) (r : L*AE)]
  [Mul  (l : L*AE) (r : L*AE)]
  [Div  (l : L*AE) (r : L*AE)]
  [Id   (name : Symbol)]
  [Let1 (name : Symbol) (val : L*AE) (expr : L*AE)]
  [Let* (argslist : (Listof ArgPair)) (body :  L*AE)])

(define (parse-error sx)
  (error 'parse-sx (string-append "parse error: " (to-string sx))))

(define (sx-ref sx n) (list-ref (s-exp->list sx) n))

(define (parse-args arglist acc)
  (if (empty? arglist)
      (reverse acc)
      (let* ([pair (first arglist)]
             [name  (s-exp->symbol (sx-ref pair 0))]
             [expr (parse-sx (sx-ref pair 1))])
        (parse-args (rest arglist) (cons (argpair name expr) acc)))))

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
    [(s-exp-match? `(lets ((SYMBOL ANY) ...) ANY) sx)
     (let* ([defs (parse-args (s-exp->list (sx-ref sx 1)) empty)]
            [expr (parse-sx (sx-ref sx 2))])
       (Let* defs expr))]

    [(s-exp-match? `(ANY ANY ANY) sx)
     (let* ([l (lambda () (parse-sx (sx-ref sx 1)))]
            [r (lambda () (parse-sx (sx-ref sx 2)))])
         (case (s-exp->symbol (sx-ref sx 0))
           [(+) (Add (l) (r))]
           [(-) (Sub (l) (r))]
           [(*) (Mul (l) (r))]
           [(/) (Div (l) (r))]
           [else (parse-error sx)]))]
    [else (parse-error sx)]))




;; expr[to/from]
(define (subst expr from to)
  (type-case L*AE expr
    [(Num n) expr]
    [(Add l r) (Add (subst l from to) (subst r from to))]
    [(Sub l r) (Sub (subst l from to) (subst r from to))]
    [(Mul l r) (Mul (subst l from to) (subst r from to))]
    [(Div l r) (Div (subst l from to) (subst r from to))]
    [(Id name) (if (eq? name from) to expr)]
    [(Let1 bound-id named-expr bound-body)
           (Let1 bound-id (subst named-expr from to)
                 (if (eq? bound-id from)bound-body (subst bound-body from to)))]
    [(Let* arglist bound-body)
           (Let1 (argpair-arg (first arglist)) (subst (argpair-expr (first arglist)) from to)
                 (if (empty? (rest arglist)) bound-body (Let* (rest arglist) bound-body)
                                                        ))]))


;; evaluate a WAE program contained in an s-expression
(define (run sx)
  (eval (parse-sx sx)))

;; evaluates WAE expressions
(define (eval expr)
  (type-case L*AE expr
    [(Num n) n]
    [(Add l r) (+ (eval l) (eval r))]
    [(Sub l r) (- (eval l) (eval r))]
    [(Mul l r) (* (eval l) (eval r))]
    [(Div l r) (/ (eval l) (eval r))]
    [(Let1 bound-id named-expr bound-body)
          (eval (subst bound-body
                       bound-id
                       (Num (eval named-expr))))] ; <-***
    [(Id name) (error 'eval (string-append "free identifier: " (to-string name)))]
    [(Let* arglist bound-body)
        (eval (Let1 (argpair-arg (first arglist)) (argpair-expr (first arglist))
                 (if (empty? (rest arglist)) bound-body (
                                                        Let* (rest arglist) bound-body))))]))


;;TESTS

(module+ test
  (test/exn  (parse-sx `"hi mom") "parse error")
  (test/exn  (parse-sx `{& 1 2}) "parse error")
  (test/exn  (parse-sx `{+ 1 2 3}) "parse error")
  (test/exn (parse-sx `{lets {{x 1} {y 2}}}) "parse error")
  (test (parse-sx `{lets {{x 1} {y 2}} {+ x y}}) (Let* (list (argpair 'x (Num 1))
                                                         (argpair 'y (Num 2)))
                                                         (Add (Id 'x) (Id 'y)))))



(module+ test
  (test (run `5) 5)
  (test (run `{+ 5 5}) 10)
  (test (run `{* 5 5}) 25)
  (test (run `{/ 5 5}) 1)
  (test (run `{let1 {x {+ 5 5}} {+ x x}}) 20)
  (test (run `{let1 {x 5} {+ x x}}) 10)
  (test (run `{let1 {x 5} {* x x}}) 25)
  (test (run `{let1 {x 5} {/ x x}}) 1)
  (test (run `{let1 {x {+ 5 5}} {let1 {y {- x 3}} {+ y y}}}) 14)
  (test (run `{let1 {x 5} {let1 {y {- x 3}} {+ y y}}}) 4)
  (test (run `{let1 {x 5} {+ x {let1 {x 3} 10}}}) 15)
  (test (run `{let1 {x 5} {+ x {let1 {x 3} x}}}) 8)
  (test (run `{let1 {x 5} {+ x {let1 {y 3} x}}}) 10)
  (test (run `{let1 {x 5} {let1 {y x} y}}) 5)
  (test (run `{let1 {x 5} {let1 {x x} x}}) 5)
  (test/exn (run `{let1 {x 1} y}) "free identifier"))


(test (run `(lets ((x 5) (y (- x 3))) y))  2)
(test (run `(lets ((x 5) (y (- x 3))) y))  2)
(test (run `(lets ((x 5) (y (- x 3))) (+ y y)))  4)
(test (run `(lets ((x 8) (y (- x 3))) (* y y)))  25)
(test (run `(lets ((x 5) (y (- x 3))) (+ y (* y y))))  6)
(test (run `(lets ((x 5) (y (- x 3))) (+ y (* y y)))) 6)
(test (run `(lets ((x 1) (y (- x 1))) (+ y (* y y)))) 0)
(test (run `(lets ((x 0) (y x)) (* y (* y y)))) 0)
(test (run `(lets ((x -1) (y (- x 1))) (* y (* y y)))) -8)
(test (run `(lets ((x 5) (y (* x 2)) (z (+ y 3))) (+ z z))) 26)
(test (run `(lets ((x 5) (y (* x 2)) (z (+ y 3))) (* z z))) 169)




(define minutes-spent 480)


(test (run `{lets {{x 5}
                    {y {- x 3}}} {+ y y}})  4)
(test (run `{lets {{x 5}
                    {y x}} y}) 5)
(test (run `{lets {{x 5}
                    {x x}} x}) 5)

