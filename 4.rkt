#lang racket/base
(module bccae plait
  (define-type AE
    [Num (n : Number)]
    [Error (n : Number)]
    [Add (l : AE) (r : AE)])

  ;; Continuations
  (define tag:EmptyCont 0)
  (define tag:addSecondK 1)
  (define tag:doAddK 2)

  ;; Code
  (define tag:Num 8)
  (define tag:Add 9)

  ;; Values
  (define tag:NumV 15)
  (define tag:Bind 17)

  (define tag:Error 19)
  (define tag:ErrorV 20)
  ;; ----------------------------------------

  (define (compile ast)
    (type-case AE ast
      [(Error n)  (code-malloc1 tag:Error n)]
      [(Num n) (code-malloc1 tag:Num n)]
      [(Add l r) (code-malloc2 tag:Add (compile l) (compile r))]))

  ;; ----------------------------------------
  ;; Allocator for code, which is never freed;
  ;; use code-ref instead of ref to refer to code

  (define (code-incptr n)
    (begin
      (set! code-ptr (+ code-ptr n))
      (- code-ptr n)))

  ;; code-malloc1 : number number -> number
  (define (code-malloc1 tag a)
    (begin
      (vector-set! code-memory code-ptr tag)
      (vector-set! code-memory (+ code-ptr 1) a)
      (code-incptr 2)))

  ;; code-malloc2 : number number number -> number
  (define (code-malloc2 tag a b)
    (begin
      (vector-set! code-memory code-ptr tag)
      (vector-set! code-memory (+ code-ptr 1) a)
      (vector-set! code-memory (+ code-ptr 2) b)
      (code-incptr 3)))

  ;; code-ref : number number -> number
  (define (code-ref n d)
    (vector-ref code-memory (+ n d)))

  (define MEMORY-SIZE 128)

  (define memory  (make-vector MEMORY-SIZE 0))

  (define (incptr n)
    ;; Increment the allocation pointer, fail
    ;;  if there's not enough room for the next
    (begin
      (set! ptr (+ ptr n))
      (when (>= (+ ptr 5) MEMORY-SIZE)
        (error 'malloc "out of memory"))
      (- ptr n)))

  (define (malloc1 tag a)
    (begin
      (vector-set! memory ptr tag)
      (vector-set! memory (+ ptr 1) a)
      (incptr 2)))

  (define (malloc2 tag a b)
    (begin
      (vector-set! memory ptr tag)
      (vector-set! memory (+ ptr 1) a)
      (vector-set! memory (+ ptr 2) b)
      (incptr 3)))

  (define (ref n d)
    (vector-ref memory (+ n d)))

  (define-syntax-rule (switch v [tv ex ...] ...)
    (let ([the-v v]) ; prevent repeated evaluation
      (cond
        [(equal? the-v tv)
         (begin ex ...)] ...
                         [else (error 'switch (string-append "unknown value "
                                                             (to-string v)))])))

  (define-syntax-rule (display* thing ...)
    (begin (display thing) ...))

  (define trace-level (make-parameter 0))

  (define (bctrace where)
    (when (> (parameter-ref trace-level) 0)
      (display* "\n" where
                "\nPC " PC
                "\nv-reg " v-reg
                "\nk-reg " k-reg
                "\nptr " ptr
                "\nmemory " memory "\n")))
  (define (num-op op op-name)
    (lambda (x y)
      (malloc1 tag:NumV (op (ref x 1) (ref y 1)))))

  (define num+ (num-op + '+))
  (define num- (num-op - '-))

  (define (init-k) (malloc1 0 0))

  (define (run flang)
    (begin
      (reset!)
      (set! PC (compile flang))
      (set! k-reg (init-k))
      (interp)))

  (define code-memory (make-vector 2048 0))
  (define code-ptr 0)
  (define ptr 0)
  (define k-reg 0)
  (define v-reg 0)
  (define PC 0)

  (define (reset!)
    (begin
      (set! code-ptr 0)
      (set! ptr 0)
      (set! v-reg 0)
      (set! PC 0)
      (set! k-reg 0)
      (void)))
  (define (interp)
    (begin
      (bctrace 'interp)
      (switch (code-ref PC 0)
              [tag:Error
               (malloc1 tag:ErrorV (code-ref PC 1))]
              [tag:Num
               (begin
                 (set! v-reg (malloc1 tag:NumV (code-ref PC 1)))
                 (continue))]
              [tag:Add
               (begin
                 (set! k-reg (malloc2 tag:addSecondK (code-ref PC 2) k-reg))
                 (set! PC (code-ref PC 1))
                 (interp))])))

  (define (continue)
    (begin
      (bctrace 'continue)
      (switch (ref k-reg 0)
              [tag:EmptyCont v-reg]
              [tag:addSecondK
               (begin
                 (set! PC (ref k-reg 1))
                 (set! k-reg (malloc2 tag:doAddK v-reg (ref k-reg 2)))
                 (interp))]
              [tag:doAddK
               (begin
                 (set! v-reg (num+ (ref k-reg 1) v-reg))
                 (set! k-reg (ref k-reg 2))
                 (continue))])))

  (define (flang->int flang)
    (let ([loc (run flang)])
      (switch (ref loc 0)
              [tag:NumV (ref loc 1)]
              [tag:ErrorV (ref loc 1)])))

  (print-only-errors #t)

  (define ret-loc (run (Add (Num 1) (Error 7))))
  (test (ref ret-loc 0) tag:ErrorV)
  (test (ref ret-loc 1) 7)

  (test (flang->int (Add (Num 40) (Num 2))) 42)

  (test (flang->int (Add (Num 1) (Add (Num 2) (Num 3)))) 6)
  (test (flang->int (Add (Add (Num 2) (Num 3)) (Num 1))) 6)
  (test (flang->int (Error -1)) -1)
  (test (flang->int (Add (Num 40) (Error 2))) 2)
  (test (flang->int (Add (Num 1) (Add (Error 2) (Num 3)))) 2)
  (test (flang->int (Add (Add (Num 2) (Num 3)) (Error -1))) -1)
  (test (flang->int (Add (Add (Num 2) (Error 3)) (Num -1))) 3)
  (test (flang->int
         (Add (Num 1) (Add (Num 2) (Add (Num 3) (Add (Num 4) (Error -1))))))
        -1)
  )
(require (only-in 'bccae))