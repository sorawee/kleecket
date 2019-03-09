#lang racket/base

(require racket/control
         racket/function
         racket/match
         racket/string
         racket/format
         racket/list
         racket/stxparam
         syntax/parse/define
         data/queue
         (prefix-in rosette: rosette)
         (for-syntax racket/function
                     racket/syntax
                     racket/base))

(provide (rename-out [module-begin #%module-begin]))

(struct state (val st pc) #:transparent)
(struct closure (x body env))

(define queue (make-queue))
(define symbol-store (make-hash))
(define location 0)
(define reserved-id '(= > < <= >= + - * / set! /no-check lambda displayln raise
                        symbolic if not and or let when begin assert letrec while))
(define sep (make-string 72 #\#))
(define error raise-user-error)

(define (assert x #:msg [msg #f] . xs)
  (when (not x) (apply error (or msg "Assertion error") x xs)))

(define (clear-assert! v) (rosette:clear-asserts!) v)

(define (solve pc)
  (assert (empty? (rosette:asserts))
          #:msg "Rosette assertion store is not empty (pc attached)"
          (rosette:asserts) pc)
  (rosette:solve (rosette:assert (apply rosette:&& pc))))

(define-syntax-parameter threading
  (curry raise-syntax-error #f "wrong use outside of match+lift-rosette"))

(define-syntax-parser threading*
  #:datum-literals (<-)
  [(_ env:id st:id pc:id (_ (~seq id:id <- e:expr) ...
                            #:explicit st-final:id pc-final:id ret:expr))
   #'(let ([ST st] [PC pc])
       (match-let* ([(state id ST PC) (interp e env ST PC)] ...)
         (let ([st-final ST] [pc-final PC]) ret)))]
  [(_ env:id st:id pc:id (whatever ... ret:expr))
   #'(threading* env st pc (whatever ... #:explicit ST PC (state ret ST PC)))])

(define-syntax-parser match+lift-rosette
  [(~and expr (_ stx:id env:id st:id pc:id (sym:id ...) clauses ...))
   (with-syntax ([(rosette-sym ...) (map (curry format-id #'expr "rosette:~a")
                                         (syntax->list #'(sym ...)))])
     #`(syntax-parameterize ([threading (λ (stx*) #`(threading* env st pc #,stx*))])
         (match stx
           [`(sym ,e-left ,e-right) (threading val-left <- e-left
                                               val-right <- e-right
                                               (rosette-sym val-left val-right))] ...
           clauses ...)))])

(define (interp stx env st pc)
  (define return (curryr state st pc))
  (match+lift-rosette
   stx env st pc (= > < <= >= + - *)
   [(? number?) (return stx)]
   [(? boolean?) (return stx)]
   [(? string?) (return stx)]
   [`(void) (return (void))]
   [(? symbol?)
    (when (member stx reserved-id) (error "reserved identifier" stx))
    (return (hash-ref st (hash-ref env stx (thunk (error "unbound identifier" stx)))))]
   [`(/no-check ,e-left ,e-right)
    (threading val-left <- e-left
               val-right <- e-right
               (clear-assert! (rosette:quotient val-left val-right)))]
   [`(set! ,x ,e) (threading val <- e
                             #:explicit st pc
                             (state val (hash-set st (hash-ref env x) val) pc))]
   [`(lambda (,x) ,e) (state (closure x e env) st pc)]
   [`(displayln ,e)
    (threading val <- e
               (let ([model (solve pc)])
                 (printf "STDOUT: ~a\n" val)
                 (printf "PC: ~a\n" pc)
                 (printf "Example model: ~a\n" model)
                 (when (rosette:term? val)
                   (printf "Example value: ~a\n" (rosette:evaluate val model)))
                 (printf "\n")
                 val))]
   [`(raise) (error 'ERROR
                    (~a "assertion fails with path condition ~s "
                        "with example model ~s\n")
                    pc (solve pc))]
   [`(symbolic ,e ,type)
    (return (hash-ref! symbol-store (cons e type)
                       (thunk (rosette:constant (datum->syntax #f e)
                                                (match type
                                                  ['int rosette:integer?]
                                                  ['bool rosette:boolean?])))))]
   [`(if ,c ,t ,e)
    (match-define (state val-c st-c pc-c) (interp c env st pc))
    (match val-c
      [#f (interp e env st-c pc-c)]
      [(? (negate rosette:term?)) (interp t env st-c pc-c)]
      [_ (shift
          k
          (for ([condition (list (rosette:not (rosette:not val-c)) (rosette:not val-c))]
                [expr (list t e)])
            (define new-pc (cons condition pc-c))
            (when (rosette:sat? (solve new-pc))
              (enqueue! queue (thunk (k (interp expr env st-c new-pc)))))))])]

   ;; syntactic sugar
   [`(not ,e) (interp `(if ,e #f #t) env st pc)]
   [`(and ,e-left ,e-right) (interp `(if ,e-left ,e-right #f) env st pc)]
   [`(or ,e-left ,e-right) (interp `(if ,e-left #t ,e-right) env st pc)]
   [`(/ ,e-left ,e-right) (interp `(let ([$x ,e-left])
                                     (let ([$y ,e-right])
                                       (begin (assert (not (= $y 0)))
                                              (/no-check $x $y)))) env st pc)]
   [`(let ([,x ,v]) ,e) (interp `((lambda (,x) ,e) ,v) env st pc)]
   [`(when ,c ,e) (interp `(if ,c ,e (void)) env st pc)]
   [`(assert ,e) (interp `(when (not ,e) (raise)) env st pc)]
   [`(begin ,xs ... ,x) (interp (foldr (λ (e a) `(let ([$_ ,e]) ,a)) x xs) env st pc)]
   [`(letrec ([,x ,e]) ,body)
    (interp `(let ([,x (void)]) (begin (set! ,x ,e) ,body)) env st pc)]
   [`(while ,c ,body)
    (interp `(letrec ([$loop (lambda ($_) (when ,c (begin ,body ($loop (void)))))])
               ($loop (void))) env st pc)]

   ;; application must be the last one to prioritize primitive forms
   [`(,f ,a) (threading val-f <- f
                        val-a <- a
                        #:explicit st pc
                        (match val-f
                          [(closure x body env)
                           (set! location (add1 location))
                           (interp body
                                   (hash-set env x location)
                                   (hash-set st location val-a) pc)]
                          [_ (error "not a function" val-f)]))]))

(define-syntax-parser module-form
  [(_ (#:comment x ...)) #'(printf "~a\n~a~a\n\n" sep (~a (~a " " 'x "\n") ...) sep)]
  [(_ stx) #'(begin
               (enqueue! queue (thunk (interp (transform 'stx) (hash) (hash) '())))
               (main)
               (displayln "-----------------------------\n"))])

(define-syntax-rule (module-begin form ...) (#%module-begin (module-form form) ...))

;; make user-defined variables not conflict with generated ids
(define/match (transform stx)
  [((cons x y)) (cons (transform x) (transform y))]
  [((? (thunk* (and (symbol? stx) (string-prefix? (symbol->string stx) "$")))))
   (string->symbol (string-append "$" (symbol->string stx)))]
  [(_) stx])

;; the main loop
(define (main)
  (cond
    [(queue-empty? queue) (hash-clear! symbol-store) ; these are totally unnecessary
                          (rosette:clear-state!)
                          (set! location 0)]
    [else (match (reset ((dequeue! queue)))
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
