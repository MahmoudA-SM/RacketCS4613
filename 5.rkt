#lang racket/base

(module gencount plai/gc2/collector
  ;; two metadata slots, bump pointer allocator.
  ;; Heap layout: PTR GEN user-data ...
  (define (get-ptr) (heap-ref 0))
  (define (set-ptr! v) (heap-set! 0 v))

  (define (get-gen) (heap-ref 1))
  (define (set-gen! v) (heap-set! 1 v))

  (define (init-allocator)
    (set-gen! 0)
    (set-ptr! 2))

  (define (malloc size)
    (define ptr (get-ptr))
    (define next-ptr (+ ptr size))
    (when (>= next-ptr (heap-size))
      (error 'malloc "out of space"))
    (set-ptr! next-ptr)
    ptr)

  (define (alloc/header tag . vals)
    (define loc (malloc (+ 2 (length vals))))
    (heap-set! loc tag)
    (heap-set! (+ 1 loc) 0)  ;; how many lives
    (for ([i (in-range (length vals))]
          [v (in-list vals)])
      (heap-set! (+ loc i 2) v))
    loc)

  (define (expect addr tag)
    (unless (equal? (heap-ref addr) tag)
      (error 'check-pair "expecting ~a @ ~a" tag addr)))
  (define (heap-get tag addr offset)
    (expect addr tag)
    (heap-ref (+ addr offset)))
  (define (heap-put tag addr offset val)
    (expect addr tag)
    (heap-set! (+ addr offset) val))

  (define (gc:flat? addr) (equal? (heap-ref addr) 'flat))
  (define (gc:alloc-flat x) (alloc/header 'flat x))
  (define (gc:deref addr) (heap-get 'flat addr 2))

  (define (gc:cons f r) (alloc/header 'cons  (read-root f) (read-root r)))
  (define (gc:cons? addr) (equal? (heap-ref addr) 'cons))
  (define (gc:first addr) (heap-get 'cons addr 2))
  (define (gc:rest addr) (heap-get 'cons addr 3))
  (define (gc:set-first! addr v) (heap-put 'cons addr 2 v))
  (define (gc:set-rest! addr v) (heap-put 'cons addr 3 v))

  (define (gc:closure code-pointer free-vars)
    (apply alloc/header 'clos code-pointer free-vars))

  (define (gc:closure? addr) (equal? (heap-ref addr) 'clos))
  (define (gc:closure-code-ptr addr) (heap-get 'clos addr 2))
  (define (gc:closure-env-ref addr i)
    (expect 'clos addr)
    (heap-ref (+ addr 3 i)))


  (define (mark-live! . roots)
    (set-gen! (+ 1 (get-gen)))
    (define stop-at (if (equal? (length roots) 2)
                      (second roots)
                      2))
    (mlhelper stop-at (first roots)
              )
    )
  
  (define (mlhelper stop-at address)

    (cond
      [(when (>= address stop-at) 
           (when (or (gc:flat? address) (gc:cons? address))
               (begin
                 (display address)
                 (heap-set! (+ 1 address) (+ 1 (heap-ref (+ 1 address))))
                 (mlhelper stop-at (- address 1)))
               (mlhelper stop-at (- address 1)))
           )]
      
      
      )
    )
  #;(define (mark-live! . roots) 
    (set-gen! (+ (get-gen) 1));; heap is live so increment position 1
    (define (until) (if (equal? (length roots) 1) 2
                        (second roots)))
    (local
      [(define (iter-incr address)
         (if (>= address (until))
             (begin
               (if (gc:cons? address) (heap-set! (+ address 1) (+ (heap-ref (+ address 1)) 1))
                   (if (gc:flat? address) (heap-set! (+ address 1) (+ (heap-ref (+ address 1)) 1))
                       (void)))
               (iter-incr (- address 1)))
             (void)))]
      (iter-incr (first roots)))
    )
  
  
;#(19 0 flat 0 1 flat 0 2 flat 0 () cons 0 5 8 cons 0 2 11 #f)
;#(19 1 flat 1 1 flat 1 2 flat 1 () cons 1 5 8 cons 1 2 11 #f)
;#(19 2 flat 2 1 flat 2 2 flat 2 () cons 2 5 8 cons 1 2 11 #f)
(print-only-errors #t)
(with-heap (make-vector 20 #f)
  (init-allocator)
  ;; allocate a list (1 2) aka (cons 1 (cons 2 '()))
  (gc:cons
   (simple-root (gc:alloc-flat 1))
   (simple-root
    (gc:cons
     (simple-root (gc:alloc-flat 2))
     (simple-root (gc:alloc-flat empty)))))
  (test (current-heap) #(19 0 flat 0 1 flat 0 2 flat 0 () cons 0 5 8 cons 0 2 11 #f))
  ;; marking from the cons at 15, everything is alive
  (mark-live! 15)
  (test (current-heap) #(19 1 flat 1 1 flat 1 2 flat 1 () cons 1 5 8 cons 1 2 11 #f))
  ;; marking from the cons at 11, and seperately the flat at 2,
  ;; everything but top level cons is alive
  (mark-live! 11 2)
  (test (current-heap) #(19 2 flat 2 1 flat 2 2 flat 2 () cons 2 5 8 cons 1 2 11 #f))
  )
)
(require (only-in 'gencount))