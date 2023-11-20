#lang plait #:untyped


(define-syntax-rule (lambda/rec fun def)
  ((lambda (f)
     ((lambda (x) (f (lambda (n) ((x x) n))))
      (lambda (x) (f (lambda (n) ((x x) n))))))
   (lambda (fun) def)))


(define-syntax-rule (lambda/rec* (f x ...)E)
  (let ([g (lambda/rec
            f
            (lambda(dummy)
              (lambda (x ...)
                (let ((f (lambda (x ...) ((f 1) x ...))))
                  E))))])
    (g #f)))


(define (ackermann-wrapper-4 m n)
  (let ([ackermann (lambda/rec*  (ackermann m n)
                       (cond [(zero? m) (+ n 1)]
                             [(zero? n) (ackermann (- m 1) 1)]
                             [else      (ackermann (- m 1)
                                                   (ackermann m (- n 1)))]))])
    (ackermann m n)))
(test (ackermann-wrapper-4 3 3)  61)

(define-syntax-rule (define/fun (id x ...) body)
  (define id
    (lambda (x ...) body)))




(let
    ([fact
      (lambda/rec fact
         (lambda (n)
           (if (zero? n) 1
               (* n (fact (- n 1))))))])
  (fact 5))


(define (fact-wrapper-0 n)
  (let*
      ([fact
        (lambda/rec fact
            (lambda (n)
              (if (zero? n) 1
                  (* n (fact (- n 1))))))])
    (fact n)))

(test (fact-wrapper-0 5) 120)


(define (fact-wrapper-1 n)
  (let* ([fact (lambda (f)
                 (lambda (n)
                   (if (zero? n)
                       1
                       (* n ((f f) (- n 1))))))]
         [fact-f (fact fact)])
    (fact-f n)))

(test (fact-wrapper-1 5) 120)




(define (ackermann m n)
  (cond [(zero? m) (+ n 1)]
        [(zero? n) (ackermann (- m 1) 1)]
        [else      (ackermann (- m 1)
                              (ackermann m (- n 1)))]))
  

(define (ackermann-wrapper-1 m n)
  (let ([ackermann
         (lambda/rec ackermann
                     (lambda (m)
                       (lambda (n)
                         (cond [(zero? m) (+ n 1)]
                               [(zero? n) ((ackermann (- m 1)) 1)]
                               [else      ((ackermann (- m 1))
                                                     ((ackermann m) (- n 1)))]))))])
    ((ackermann m) n)))

(test (ackermann-wrapper-1 3 3) 61)
(test (ackermann-wrapper-1 3 5) 253)


(define (ackermann-wrapper-2 m n) 
  (let* ([ackermann
          (lambda (m n)
            (cond [(zero? m) (+ n 1)]
                  [(zero? n) (ackermann (- m 1) 1)]
                  [else      (ackermann (- m 1)
                                        (ackermann m (- n 1)))]))])
    (ackermann m n)))

(test (ackermann-wrapper-2 3 3) 61)
(test (ackermann-wrapper-2 3 5) 253)
(test (ackermann-wrapper-2 0 0) 1)
(test (ackermann-wrapper-2 1 0) 2)


(define (ackermann-wrapper-3 m n)
  (let* ([ackermann (lambda (f)
                      (lambda (m n)
                        (cond [(zero? m) (+ n 1)]
                              [(zero? n) ((f f) (- m 1) 1)]
                              [else ((f f) (- m 1)                                               ((f f) m (- n 1)))])))]
         [ackermann-f (ackermann ackermann)])
    (ackermann-f m n)))
(test (ackermann-wrapper-3 3 3) 61)

