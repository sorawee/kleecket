#lang racket

(require racket/control
         data/queue
         (prefix-in rosette: rosette))

(provide (rename-out [module-begin #%module-begin]))

(define queue (make-queue))

(define symbol-store (make-hash))
(define location 0)

(struct state (val st pc) #:transparent)
(struct closure (x body env))

(define (lift/int x) (rosette:if x 1 0))

(define Z `(lambda (f)
             (app
              (lambda (x) (app f (lambda (v) (app (app x x) v))))
              (lambda (x) (app f (lambda (v) (app (app x x) v)))))))

(define (interp stx env st pc)
  (match stx
    [(? number?) (state stx st pc)]
    [(? symbol?)
     (state (hash-ref st (hash-ref env stx
                                   (thunk (error "unbound identifier" stx)))) st pc)]
    [(? string?) (state stx st pc)]
    
    [`(not ,e) (interp `(if ,e 0 1) env st pc)]
    [`(and ,e-left ,e-right) (interp `(if ,e-left ,e-right 0) env st pc)]
    [`(or ,e-left ,e-right) (interp `(if ,e-left 1 ,e-right) env st pc)]
    
    [`(= ,e-left ,e-right)
     (match-define (state val-left st-left pc-left) (interp e-left env st pc))
     (match-define (state val-right st-right pc-right) (interp e-right env st-left pc-left))
     (state (lift/int (rosette:= val-left val-right)) st-right pc-right)]
    [`(+ ,e-left ,e-right)
     (match-define (state val-left st-left pc-left) (interp e-left env st pc))
     (match-define (state val-right st-right pc-right) (interp e-right env st-left pc-left))
     (state (rosette:+ val-left val-right) st-right pc-right)]
    [`(- ,e-left ,e-right)
     (match-define (state val-left st-left pc-left) (interp e-left env st pc))
     (match-define (state val-right st-right pc-right) (interp e-right env st-left pc-left))
     (state (rosette:- val-left val-right) st-right pc-right)]    
    [`(* ,e-left ,e-right)
     (match-define (state val-left st-left pc-left) (interp e-left env st pc))
     (match-define (state val-right st-right pc-right) (interp e-right env st-left pc-left))
     (state (lift/int (rosette:* val-left val-right)) st-right pc-right)]
    [`(/safe ,e-left ,e-right)
     (match-define (state val-left st-left pc-left) (interp e-left env st pc))
     (match-define (state val-right st-right pc-right) (interp e-right env st-left pc-left))
     (state (rosette:quotient val-left val-right) st-right pc-right)]
    [`(/ ,e-left ,e-right)
     (interp `(let ([$x ,e-left])
                (let ([$y ,e-right])
                  (begin
                    (assert (not (= $y 0)))
                    (/safe $x $y)))) env st pc)]
    
    [`(lambda (,x) ,e) (state (closure x e env) st pc)]
    [`(begin) (state (void) st pc)]
    [`(let ([,x ,v]) ,e) (interp `(app (lambda (,x) ,e) ,v) env st pc)]
    [`(letrec ([,x ,e]) ,body) (interp `(let ([,x (app ,Z ,e)]) ,body) env st pc)]
    [`(while ,c ,body)
     (interp `(letrec ([loop (lambda (loop)
                               (lambda (_)
                                 (if ,c
                                   (begin
                                     ,body
                                     (app loop 0))
                                   (begin))))])
                (app loop 0)) env st pc)]
    [`(displayln ,e)
     (match-define (state val-e st-e pc-e) (interp e env st pc))
     (displayln val-e)
     (state val-e st-e pc-e)]
    [`(assert 0) (error "assertion fails with path condition" pc)]
    [`(assert ,e) (interp `(if ,e (begin) (assert 0)) env st pc)]
    [`(app ,f ,a)
     (match-define (state val-f st-f pc-f) (interp f env st pc))
     (match-define (state val-a st-a pc-a) (interp a env st-f pc-f))
     (match val-f
       [(closure x body env)
        (set! location (add1 location))
        (interp body (hash-set env x location) (hash-set st-a location val-a) pc-a)]
       [_ (error "not a function" val-f)])]
    [`(set! ,x ,e)
     (match-define (state val-e st-e pc-e) (interp e env st pc))
     (state val-e (hash-set st (hash-ref env x) val-e) pc-e)]
    [`(begin ,e) (interp e env st pc)]
    [`(begin ,e ,xs ...)
     (match-define (state _ st-e pc-e)(interp e env st pc))
     (interp `(begin ,@xs) env st-e pc-e)]
    [`(symbolic ,e)
     (state (hash-ref! symbol-store e
                       (thunk (rosette:constant (datum->syntax #f e)
                                                rosette:integer?)))
            st
            pc)]
    [`(if ,c ,t ,e)
     (match-define (state val-c st-c pc-c) (interp c env st pc))
     (match val-c
       [0 (interp e env st-c pc-c)]
       [(? integer?) (interp t env st-c pc-c)]
       [condition (shift
                   k
                   (let ([new-pc (cons (rosette:not (rosette:= 0 condition))
                                       pc-c)])
                     (when (rosette:sat?
                            (rosette:solve (rosette:assert
                                            (apply rosette:&& new-pc))))
                       (enqueue! queue (thunk (k (interp t env st-c new-pc))))))
                   (let ([new-pc (cons (rosette:= 0 condition)
                                       pc-c)])
                     (when (rosette:sat?
                            (rosette:solve (rosette:assert
                                            (apply rosette:&& new-pc))))
                       (enqueue! queue (thunk (k (interp e env st-c new-pc)))))))])]))

(define-syntax-rule (module-begin stx ...)
  (#%module-begin (begin
                    (enqueue! queue (thunk
                                     (interp (transform 'stx) (hash) (hash) '())))
                    (main)
                    (displayln "\n-----------------------------\n"))
                  ...))

(define (transform stx)
  (match stx
    [(cons x y) (cons (transform x) (transform y))]
    [(? symbol?) (if (string-prefix? (symbol->string stx) "$")
                     (string->symbol (string-append "$" (symbol->string stx)))
                     stx)]
    [_ stx]))

(define (main)
  (cond
    [(queue-empty? queue)
     (hash-clear! symbol-store)
     (rosette:clear-state!)
     (void)]
    [else
     (define to-run (dequeue! queue))
     (match (reset (to-run))
       [(? void?) (void)]
       [x (printf "Output: ~a\n" x)
          (printf "Rosette assertion store: ~a\n" (rosette:asserts))])
     (main)]))






