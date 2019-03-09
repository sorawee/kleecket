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
  (when (not (= x -1))
    (/ 7 (+ 1 x))))

(#:comment "If true branch")

(if #t 42 99)

(#:comment "Yet another if true branch")

(if 0 42 99)

(#:comment "If false branch")

(if #f 42 99)

(#:comment "Loop")

(let ([x 0])
  (while (< x 5)
    (begin
      (displayln x)
      (set! x (+ x 1)))))

(#:comment "Add annihilation")

(+ (if (symbolic b bool) 1 10)
   (if (not (symbolic b bool)) 100 1000))

(#:comment "Loop on symbolic value. BMC and Rosette would not terminate")

(let ([x (symbolic x int)])
  (when (<= x 5)
    (let ([i 0])
      (begin
        (while (< i x)
          (begin
            (displayln i)
            (set! i (+ 1 i))))
        i))))

(#:comment "Separated heap")

(let ([x 1])
  (if (symbolic b bool)
      (set! x (+ 10 x))
      (set! x (+ 100 x))))

(#:comment "Reserved id")

set!

(#:comment "No static check")

(if #f set! 1)

(#:comment "Set symbolic value (STDOUT should have x = 9)")

(let ([x (symbolic x int)])
  (begin
    (set! x (+ 1 x))
    (when (= x 10)
      (displayln x))))

;; Please add more!
