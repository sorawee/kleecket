#lang racket/base

(require racket/control
         racket/function
         racket/match
         racket/string
         racket/pretty
         racket/format
         racket/list
         racket/stxparam
         racket/exn
         syntax/parse/define
         data/queue
         (prefix-in rosette: rosette)
         (for-syntax racket/function
                     racket/base
                     syntax/stx))

(provide (rename-out [module-begin #%module-begin]))

(struct state (val st pc) #:transparent)
(struct closure (x body env))

(define queue (make-queue))
(define type-map (hash 'int rosette:integer? 'bool rosette:boolean?))
(define symbol-store (make-hash))
(define location 0)
(define reserved-id '(= > < <= >= + - * / set! /-no-check lambda displayln raise
                        symbolic if not and or let when begin assert letrec while
                        car cdr cons null? cons? null int bool))
(define sep (make-string 72 #\#))
(define error raise-user-error)

(define (assert x #:msg [msg #f] . xs)
  (when (not x) (apply error (or msg "INTERNAL ERROR:") xs)))

(define (solve pc)
  (assert (empty? (rosette:asserts))
          #:msg "INTERNAL ERROR: Rosette assertion store is not empty (pc attached)"
          (rosette:asserts) pc)
  (rosette:solve (rosette:assert (apply rosette:&& pc))))

(define (check-reserved! stx)
  (when (member stx reserved-id) (error 'ERROR "reserved: ~a" stx)))

(define-syntax-parameter threading
  (curry raise-syntax-error #f "wrong use outside of match+lift"))

(define-syntax-parser threading*
  #:datum-literals (<-)
  [(_ env:expr st:expr pc:expr (~seq id:id <- e:expr) ... #:ret st*:id pc*:id ret:expr)
   #'(let ([ST st] [PC pc] [ENV env])
       (match-let* ([(state id ST PC) (interp e ENV ST PC)] ...)
         (let ([st* ST] [pc* PC]) ret)))])

(define-simple-macro (app pc . xs)
  (let ([handler (λ (ex)
                   ;; Rosette asserts #f on exception, so clear it
                   (rosette:clear-asserts!)
                   (printf "EXCEPTION (see the ERROR after this for more info)\n")
                   (display (exn->string ex))
                   (interp '(raise) (hash) (hash) pc))])
    (with-handlers ([exn:fail? handler]) xs)))

(define-for-syntax (lift-clause stx)
  (define (arity->temporaries x)
    (generate-temporaries (build-list (syntax->datum x) identity)))
  (syntax-parse stx
    [(id:id (~optional f:id) arity:integer
            (~optional (~and #:clear (~bind [clear! #'(rosette:clear-asserts!)]))))
     (with-syntax ([(e ...) (arity->temporaries #'arity)]
                   [(val ...) (arity->temporaries #'arity)])
       #`[`(id ,e ...) (threading (~@ val <- e) ... #:ret st pc
                                  (begin0 (state (app pc (~? f id) val ...) st pc)
                                    (~? clear!)))])]))

(define-syntax-parser match+lift
  [(_ stx:expr env:expr st:expr pc:expr config . clauses)
   (with-syntax ([(lifted ...) (stx-map lift-clause #'config)]
                 [threader #'(syntax-parser [(_ . xs) #'(threading* env st pc . xs)])])
     #`(syntax-parameterize ([threading threader]) (match stx lifted ... . clauses)))])

(define (interp stx env st pc)
  (define return (curryr state st pc))
  (define desugar (curryr interp env st pc))
  (match+lift
   stx env st pc
   ([/-no-check rosette:quotient 2 #:clear]
    [+ rosette:+ 2] [- rosette:- 2] [* rosette:* 2]
    [= rosette:= 2] [> rosette:> 2] [< rosette:< 2] [<= rosette:<= 2] [>= rosette:>= 2]
    [car 1] [cdr 1] [cons 2] [null? 1] [cons? 1])
   [(? (disjoin number? boolean? string?)) (return stx)]
   [`(void) (return (void))]
   [`(null) (return null)]
   [(? symbol?)
    (check-reserved! stx)
    (return (hash-ref st (hash-ref env stx (thunk (error 'ERROR "unbound: ~a" stx)))))]
   [`(set! ,(? symbol? x) ,e)
    (check-reserved! x)
    (threading val <- e #:ret st pc (state val (hash-set st (hash-ref env x) val) pc))]
   [`(lambda (,x) ,e) (check-reserved! x)
                      (state (closure x e env) st pc)]
   [`(displayln ,e)
    (threading val <- e
               #:ret st pc
               (let ([model (solve pc)])
                 (printf "STDOUT: ~a\nPC: ~a\nExample model: ~a\n" val pc model)
                 (when (rosette:term? val)
                   (printf "Example value: ~a\n" (rosette:evaluate val model)))
                 (printf "\n")
                 (state val st pc)))]
   [`(raise) (error 'ERROR (~a "assertion fails with path condition ~s "
                               "with example model ~s\n") pc (solve pc))]
   [`(symbolic ,e ,type)
    (return (hash-ref! symbol-store (cons e type)
                       (thunk (rosette:constant (datum->syntax #f e)
                                                (hash-ref type-map type)))))]
   [`(symbolic* ,type) (rosette:define-symbolic* symbol (hash-ref type-map type))
                       (return symbol)]
   [`(if ,c ,t ,e)
    (match-define (state val-c st-c pc-c) (interp c env st pc))
    (match val-c
      [#f (interp e env st-c pc-c)]
      [(? (negate rosette:term?)) (interp t env st-c pc-c)]
      [_ (shift k (for ([condition (list (rosette:not (rosette:not val-c))
                                         (rosette:not val-c))]
                        [expr (list t e)])
                    (define new-pc (cons condition pc-c))
                    (when (rosette:sat? (solve new-pc))
                      (enqueue! queue (thunk (k (interp expr env st-c new-pc)))))))])]

   ;; syntactic sugar
   [`(not ,e) (desugar `(if ,e #f #t))]
   [`(and ,e-left ,e-right) (desugar `(if ,e-left ,e-right #f))]
   [`(or ,e-left ,e-right) (desugar `(if ,e-left #t ,e-right))]
   [`(/ ,e-left ,e-right) (desugar `(let ([$x ,e-left])
                                      (let ([$y ,e-right])
                                        (begin (assert (not (= $y 0)))
                                               (/-no-check $x $y)))))]
   [`(let ([,x ,v]) ,e) (desugar `((lambda (,x) ,e) ,v))]
   [`(when ,c ,e) (desugar `(if ,c ,e (void)))]
   [`(assert ,e) (desugar `(when (not ,e) (raise)))]
   [`(begin ,xs ... ,x) (desugar (foldr (λ (e a) `(let ([$_ ,e]) ,a)) x xs))]
   [`(letrec ([,x ,e]) ,body) (desugar `(let ([,x (void)]) (begin (set! ,x ,e) ,body)))]
   [`(while ,c ,body)
    (desugar `(letrec ([$loop (lambda ($_) (when ,c (begin ,body ($loop (void)))))])
                ($loop (void))))]

   ;; application must be the (almost) last one to prioritize primitive forms
   [`(,f ,a) (threading val-f <- f
                        val-a <- a
                        #:ret st pc
                        (match val-f
                          [(closure x body env)
                           (set! location (add1 location))
                           (interp body
                                   (hash-set env x location)
                                   (hash-set st location val-a) pc)]
                          [_ (error 'ERROR "applied to non-function: ~a" val-f)]))]
   [stx (error 'ERROR "unrecognized syntax: ~a" stx)]))

(define-syntax-parser module-form
  [(_ (#:comment x ...)) #'(displayln (~a sep "\n" (~a " " 'x "\n") ... sep "\n"))]
  [(_ stx) #'(let ([STX 'stx])
               (printf "~a\n\n" (pretty-format STX))
               (enqueue! queue (thunk (interp (transform STX) (hash) (hash) '())))
               (main)
               (displayln "-----------------------------\n"))])

(define-simple-macro (module-begin form ...) (#%module-begin (module-form form) ...))

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
