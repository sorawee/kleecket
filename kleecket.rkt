#lang racket/base

(require racket/control
         racket/function
         racket/match
         racket/string
         racket/format
         racket/list
         racket/stxparam
         data/queue
         (prefix-in rosette: rosette)
         (for-syntax syntax/parse
                     racket/function
                     racket/syntax
                     racket/base))

(provide (rename-out [module-begin #%module-begin]))

(define queue (make-queue))
(define symbol-store (make-hash))
(define location 0)
(define sep (make-string 72 #\#))

(struct state (val st pc) #:transparent)
(struct closure (x body env))

(define error raise-user-error)
(define (assert x #:msg [msg #f] . xs)
  (when (not x) (apply error (or msg "Assertion error") x xs)))
(define (solve pc)
  (assert (empty? (rosette:asserts))
          #:msg "Rosette assertion store is not empty (pc attached)"
          (rosette:asserts) pc)
  (rosette:solve (rosette:assert (apply rosette:&& pc))))

(define-syntax-parameter threading
  (curry raise-syntax-error #f "wrong use outside of match+lift-rosette"))

(define-syntax threading*
  (syntax-parser
    #:datum-literals (<-)
    [(_ env:id st:id pc:id (_ (~seq id:id <- e:expr) ... #:explicit ret:expr))
     #'(let ([st st] [pc pc])
         (match-let* ([(state id st pc) (interp e env st pc)] ...)
           ret))]
    [(_ env:id st:id pc:id (whatever ... ret:expr))
     #'(threading* env st pc (whatever ... #:explicit (state ret st pc)))]))

(define-syntax (match+lift-rosette expr)
  (syntax-parse expr
    [(_ stx:id env:id st:id pc:id (sym:id ...) clauses ...)
     (with-syntax ([(rosette-sym ...) (map (curry format-id expr "rosette:~a")
                                           (syntax->list #'(sym ...)))])
       #`(syntax-parameterize ([threading (λ (stx*) #`(threading* env st pc #,stx*))])
           (match stx
             [`(sym ,e-left ,e-right)
              (threading val-left <- e-left
                         val-right <- e-right
                         (rosette-sym val-left val-right))] ...
             clauses ...)))]))

(define (clear-assert! v)
  (rosette:clear-asserts!)
  v)

(define (interp stx env st pc)
  (match+lift-rosette
   stx env st pc
   (= > < <= >= + - *)
   [(? number?) (state stx st pc)]
   [(? boolean?) (state stx st pc)]
   [(? string?) (state stx st pc)]

   [(? symbol?)
    (state (hash-ref st (hash-ref env stx
                                  (thunk (error "unbound identifier" stx)))) st pc)]

   [`(not ,e) (interp `(if ,e #f #t) env st pc)]
   [`(and ,e-left ,e-right) (interp `(if ,e-left ,e-right #f) env st pc)]
   [`(or ,e-left ,e-right) (interp `(if ,e-left #t ,e-right) env st pc)]

   [`(/safe ,e-left ,e-right)
    (threading val-left <- e-left
               val-right <- e-right
               (clear-assert! (rosette:quotient val-left val-right)))]
   [`(/ ,e-left ,e-right)
    (interp `(let ([$x ,e-left])
               (let ([$y ,e-right])
                 (begin
                   (assert (not (= $y 0)))
                   (/safe $x $y)))) env st pc)]

   [`(lambda (,x) ,e) (state (closure x e env) st pc)]
   [`(let ([,x ,v]) ,e) (interp `(app (lambda (,x) ,e) ,v) env st pc)]
   [`(letrec ([,x ,e]) ,body) (interp `(let ([,x 0])
                                         (begin
                                           (set! ,x ,e)
                                           ,body)) env st pc)]
   [`(while ,c ,body)
    (interp `(letrec ([$loop (lambda (_) (if ,c (begin ,body (app $loop 0)) (begin)))])
               (app $loop 0)) env st pc)]
   [`(displayln ,e)
    (threading val <- e
               (begin (printf "STDOUT: ~a\n\n" val) val))]
   [`(assert #f) (error 'ERROR
                        (~a "assertion fails with path condition ~s "
                            "with example model ~s\n")
                        pc (solve pc))]
   [`(assert ,e) (interp `(if ,e (begin) (assert #f)) env st pc)]
   [`(app ,f ,a)
    (threading val-f <- f
               val-a <- a
               #:explicit
               (match val-f
                 [(closure x body env)
                  (set! location (add1 location))
                  (interp body
                          (hash-set env x location)
                          (hash-set st location val-a) pc)]
                 [_ (error "not a function" val-f)]))]
   [`(set! ,x ,e)
    (match-define (state val-e st-e pc-e) (interp e env st pc))
    (state val-e (hash-set st (hash-ref env x) val-e) pc-e)]
   [`(begin) (state (void) st pc)]
   [`(begin ,e) (interp e env st pc)]
   [`(begin ,e ,xs ...)
    (threading _ <- e
               v <- `(begin ,@xs)
               v)]
   [`(symbolic ,e ,type)
    (state (hash-ref! symbol-store (cons e type)
                      (thunk (rosette:constant (datum->syntax #f e)
                                               (match type
                                                 ['int rosette:integer?]
                                                 ['bool rosette:boolean?]))))
           st
           pc)]
   [`(if ,c ,t ,e)
    (match-define (state val-c st-c pc-c) (interp c env st pc))
    (match val-c
      [#f (interp e env st-c pc-c)]
      [(? (negate rosette:term?)) (interp t env st-c pc-c)]
      [condition
       (shift
        k
        (for ([new-condition (list (rosette:not (rosette:not condition))
                                   (rosette:not condition))]
              [expr (list t e)])
          (define new-pc (cons new-condition pc-c))
          (when (rosette:sat? (solve new-pc))
            (enqueue! queue (thunk (k (interp expr env st-c new-pc)))))))])]))

(define-syntax module-form
  (syntax-parser
    [(_ (#:comment x ...))
     #'(printf "~a\n~a~a\n\n" sep (~a (~a " " 'x "\n") ...) sep)]
    [(_ stx) #'(begin
                 (enqueue! queue (thunk (interp (transform 'stx) (hash) (hash) '())))
                 (main)
                 (displayln "-----------------------------\n"))]))

(define-syntax-rule (module-begin form ...) (#%module-begin (module-form form) ...))

;; make user-defined variables not conflict with generated ids and deal with comments
(define (transform stx)
  (match stx
    [(cons x y) (cons (transform x) (transform y))]
    [(? symbol?) (if (string-prefix? (symbol->string stx) "$")
                     (string->symbol (string-append "$" (symbol->string stx)))
                     stx)]
    [_ stx]))

;; the main loop
(define (main)
  (cond
    [(queue-empty? queue)
     ;; these are totally unnecessary
     (hash-clear! symbol-store)
     (rosette:clear-state!)
     (set! location 0)]
    [else
     (define to-run (dequeue! queue))
     (match (reset (to-run))
       [(? void?) (void)] ; catch immediate return and all errors
       [(state (? rosette:term? t) _ pc)
        (printf "PATH TERMINATED with pc: ~s\n" pc)
        (printf " Example model: ~s\n" (solve pc))
        (printf " Symbolic result: ~s\n" t)
        (printf " Example result: ~s\n\n" (rosette:evaluate t (solve pc)))]
       [(state x _ pc)
        (printf "PATH TERMINATED with pc: ~s\n" pc)
        (printf " Example model: ~s\n" (solve pc))
        (printf " Concrete result: ~s\n\n" x)])
     (main)]))
