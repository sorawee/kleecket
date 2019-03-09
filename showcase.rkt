#lang s-exp "kleecket.rkt"

(#:comment "Perform symbolic execution using BFS strategy"
 "Should have state 3 outputted before state 1 and 2")

(if (= 99 (symbolic b1 int))
    (if (symbolic b2 bool) 1 2)
    3)

(#:comment "We check for division by 0"
 "Should have an assertion error")

(/ 7 (+ 1 (symbolic x int)))

(#:comment "We can guard division by 0"
 "Should have no warning")

(let ([x (symbolic x int)])
  (when (not (= x -1))
    (/ 7 (+ 1 x))))

(#:comment "If true branch"
 "Should result in 42")

(if #t 42 99)

(#:comment "Yet another if true branch"
 "Should result in 42")

(if 0 42 99)

(#:comment "If false branch"
 "Should result in 99")

(if #f 42 99)

(#:comment "Loop"
 "Should display 0 to 4")

(let ([x 0])
  (while (< x 5)
    (begin
      (displayln x)
      (set! x (+ x 1)))))

(#:comment "Add annihilation"
 "Should have two paths: 1001 and 110")

(+ (if (symbolic b bool) 1 10)
   (if (not (symbolic b bool)) 100 1000))

(#:comment "Loop on constrained symbolic value"
 "Should terminate (while Rosette would not)")

(let ([x (symbolic x int)])
  (when (<= x 5)
    (let ([i 0])
      (begin
        (while (< i x)
          (begin
            (displayln i)
            (set! i (+ 1 i))))
        i))))

(#:comment "Separated heap"
 "Should have two paths: 11 and 101. 111 should not happen")

(let ([x 1])
  (if (symbolic b bool)
      (set! x (+ 10 x))
      (set! x (+ 100 x))))

(#:comment "Unbound id"
 "Should have an unbound id error")

a

(#:comment "Reserved id"
 "Should have a reserved id error")

set!

(#:comment "No static check"
 "Should have no error")

(when #f set!)

(#:comment "Set symbolic value"
 "Should have x = 9 for STDOUT")

(let ([x (symbolic x int)])
  (begin
    (set! x (+ 1 x))
    (when (= x 10)
      (displayln x))))

(#:comment "Plus has arity 2 as specified"
 "Should have a syntax error")

(+ 1 2 3)

(#:comment "list is always concrete"
 "Should have two paths: one with 1 and one with error")

(let ([x (if (symbolic b bool) (cons 1 (empty)) (empty))])
  (car x))

(#:comment "list can be mapped"
 "Should have two paths: one with '(2 3 4) and one with '(7 6)")

(let ([xs (if (symbolic b bool)
              (cons 1 (cons 2 (cons 3 (empty))))
              (cons 6 (cons 5 (empty))))])
  (letrec ([map (lambda (f)
                  (lambda (xs)
                    (if (empty? xs)
                        (empty)
                        (cons (f (car xs)) ((map f) (cdr xs))))))])
    ((map (lambda (x) (+ 1 x))) xs)))

(#:comment "Report error gracefully"
 "Should report error on primitive exception")

(when (symbolic b bool) (+ #t 1))

;; Please add more!
