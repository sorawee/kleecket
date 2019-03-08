#lang s-exp "kleecket.rkt"

;; We perform symbolic execution using BFS strategy
;; For example, state 3 should be outputted before state 1 and 2

(if (symbolic b1)
    (if (symbolic b2)
        1
        2)
    3)

;; We check for division by 0

(/ 7 (symbolic x))

;; We can guard division by 0

(let ([x (symbolic x)])
  (if (= x 0)
      (displayln "x is 0")
      (/ 7 x)))

;; Please add more!
