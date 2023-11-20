#lang plait

#| BNF for the AE language:
   ae: NUMBER
       | { + ae ae }
       | { - ae ae }
       | { * ae ae }
       | { / ae ae }
|#

;; AE abstract syntax trees
(define-type AE
  [Num (val : Number)]
  [Add (l : AE) (r : AE)]
  [Sub (l : AE) (r : AE)]
  [Mul (l : AE) (r : AE)]
  [Div (l : AE) (r : AE)])

;; to convert s-expressions into AEs
(define (parse-sx sx)
  (let ([rec (lambda (fn sx)
               (parse-sx (fn (s-exp->list sx))))])
    (cond
      [(s-exp-match? `NUMBER sx)
       (Num (s-exp->number sx))]
      [(s-exp-match? `(+ ANY ANY) sx)
       (Add (rec second sx) (rec third sx))]
      [(s-exp-match? `(ANY + ANY) sx) ;;Changed it from (+ ANY ANY) to
                                      ;;(ANY + ANY) to match the expression we expect to encounter.
       (Add (rec first sx) (rec third sx))] ;; Because of the change in the previous line, we the
                                            ;; first became and expression instead of the second
      [(s-exp-match? `(- ANY ANY) sx)
       (Sub (rec second sx) (rec third sx))]
      [(s-exp-match? `(ANY - ANY) sx) ;;Changed it from (- ANY ANY) to (ANY - ANY)
                                      ;;to match the expression we expect to encounter.
       (Sub (rec first sx) (rec third sx))] ;; Because of the change in the previous line,
                                            ;;we the first became and expression instead of the second
      [(s-exp-match? `(* ANY ANY) sx)
       (Mul (rec second sx) (rec third sx))]
      [(s-exp-match? `(ANY * ANY) sx) ;;Changed it from (* ANY ANY) to (ANY * ANY)
                                      ;;to match the expression we expect to encounter.
       (Mul (rec first sx) (rec third sx))] ;; Because of the change in the previous line,
                                            ;;we the first became and expression instead of the second
      [(s-exp-match? `(/ ANY ANY) sx) ;;Changed it from (/ ANY ANY) to
                                      ;;(ANY / ANY) to match the expression we expect to encounter.
       (Div (rec second sx) (rec third sx))] ;; Because of the change in the previous
                                             ;;line, we the first became and expression
                                             ;;instead of the second
      [(s-exp-match? `(ANY / ANY) sx)
       (Div (rec first sx) (rec third sx))]
      [else (error 'parse-sx (to-string sx))])))

;; consumes an AE and computes the corresponding number
(define (eval expr)
  (type-case AE expr
    [(Num n)   n]
    [(Add l r) (+ (eval l) (eval r))]
    [(Sub l r) (- (eval l) (eval r))]
    [(Mul l r) (* (eval l) (eval r))]
    [(Div l r) (if (= (eval r) 0)(if(<(eval l) 0) '-inf.0 '+inf.0) (/ (eval l) (eval r)))])) #|
To implement the "infinity" changes required,
we need to check if r = 0, if it is,
we check if l is negative. If r is not 0 we jump
to the last eval (l/r). If l is negative,
return -inf.0. If l is not negative, return +inf.0                                                                                              
                                                                                             |#


;; evaluate an AE program contained in an s-expr
(define (run sx)
  (eval (parse-sx sx)))

(test (run `3)  3)
(test (run `{+ 3 4}) 7)
(test (run `{+ {- 3 4} 7}) 6)


(test (run `3)  3)
(test (run `{3 + 4})  7)
(test (run `{{3 - 4} + 7})  6)
(test (run `{8 * 9})  72)
(test (run `{8 / 2})  4)



(test (run `{-8 / 0})  -inf.0)
(test (run `{8 / {5 - 5}})  +inf.0)
(test (run `{1 / {1 / 0}}) 0.0)

;;Tests by Mahmoud

(test (run `[0 / 0]) +inf.0) ;According to code it will check if 'r' is 0. If it is,
;;it will check if l is negative. l
;;is not negative therefore it returns +inf.0(ACCORDING TO THE CODE)

(test (run `[-inf.0 / -inf.0]) +nan.0)

(test (run `[+inf.0 / -inf.0]) +nan.0) ;; NAN is not a number; therefore, 

(test (run `[[* 2 4] / [/ 4 0]]) 0) ;; 4/0 = inf.0 and 8/+inf.0 = 0.
;;Makes sense (According to the code)

(test/exn (run `(23 + 24 + 25)) "parse-sx: `(23 + 24 + 25)")




;;minutes spent
(define minutes-spent 50)