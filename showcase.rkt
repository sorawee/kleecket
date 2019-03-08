#lang s-exp "kleecket.rkt"

(#:comment
 "We perform symbolic execution using BFS strategy"
 "For example, state 3 should be outputted before state 1 and 2")

(if (= 99 (symbolic b1 int))
    (if (symbolic b2 bool) 1 2)
    3)

(#:comment "We check for division by 0")

(/ 7 (+ 1 (symbolic x int)))

(#:comment "We can guard division by 0")

(let ([x (symbolic x int)])
  (if (= x -1)
      (displayln "x is 0")
      (/ 7 (+ 1 x))))

(#:comment "If true branch")

(if #t 42 99)

(#:comment "Yet another if true branch")

(if 123 42 99)

(#:comment "If false branch")

(if #f 42 99)

(#:comment "Loop")

(let ([x 0])
  (while (< x 10)
    (begin
      (displayln x)
      (set! x (+ x 1)))))

;; Please add more!