#lang racket

;; Exercises 4: Reducing (normalizing/simplifying) lambda calc terms by textual substitution
;;              using four different orders of evaluation (applicative, normal, CBV, CBN)
(provide collect-evaluation-trace
         applicative-order-reduce
         normal-order-reduce
         CBV-order-reduce
         CBN-order-reduce)

; A predicate for terms in the lambda calculus
(define (exp? e)
  (match e
         [(? symbol?) #t]
         [`(,(? exp?) ,(? exp?)) #t]
         [`(lambda (,(? symbol?)) ,(? exp?)) #t]
         [_ #f]))





; Free variables (may be useful for defining capt-avoid-subst)
;(define (free-vars exp)
;  'todo-or-from-e5)

(define (free-vars exp)
  (match exp
    [(? symbol?) (set exp)]
    [`(lambda (,x) ,body)
     (set-subtract (free-vars body) (set x))]
    [`(,f ,arg)
     (set-union (free-vars f) (free-vars arg))]))

; Capture avoiding substitution
;(define (capt-avoid-subst e0 x e1)
;  'todo-or-from-e5)

(define (capt-avoid-subst exp var new-exp)
  (match exp
    [(? symbol?)
     (if (eq? exp var)
       new-exp
       exp)]
    [`(lambda (,x) ,body)
      (if (eq? x var)
        exp ; If the lambda binds the variable, don't substitute.
        (let* ((fvs (free-vars new-exp))
               (new-x (if (set-member? fvs x)
                        (fresh-var x fvs)
                        x))
               (renamed-body (if (eq? x new-x) body (rename-var body x new-x))))
          `(lambda (,new-x) ,(capt-avoid-subst renamed-body var new-exp))))]
    [`(,f ,arg)
      `(,(capt-avoid-subst f var new-exp) ,(capt-avoid-subst arg var new-exp))]))

(define (rename-var exp old new)
  (match exp
    [(? symbol?) (if (eq? exp old) new exp)]
    [`(lambda (,x) ,body)
      `(lambda (,(if (eq? x old) new x)) ,(rename-var body old new))]
    [`(,f ,arg)
      `(,(rename-var f old new) ,(rename-var arg old new))]))

(define (fresh-var var fvs)
  (let loop ([new-var (string->symbol (string-append (symbol->string var) "'"))])
    (if (set-member? fvs new-var)
      (loop (string->symbol (string-append (symbol->string new-var) "'")))
      new-var)))

; Reduce the given expression by exactly one beta-reduction using
; applicative evaluation order. Return the simplified expression in a
; singleton set, or return (set) if there is no applicative order redex.
; Skip over any redexes that cannot be reduced using capture avoiding subst.
(define (applicative-order-reduce e)
  (match e
         [(? symbol? y) (set)]
         [`(lambda (,y) ,body)
          (define body-st (applicative-order-reduce body))
          (if (set-empty? body-st)
              ; No redex found
              (set)
              ; Derive a lambda with simplified body
              (set `(lambda (,y) ,(set-first body-st))))]
         [`((lambda (,y) ,body) ,ea)
          (let ([body-st (applicative-order-reduce body)]
		[ea-st (applicative-order-reduce ea)])
            (if (set-empty? ea-st)
		(if (set-empty? body-st)
		    ; this is the rightmost redex
                    (let ([body+ (capt-avoid-subst body y ea)])
                      (if (eq? body+ 'failed)
			  (set)
			  (set body+)))
                    ; evaluate under lambda
		    (set `((lambda (,y) ,(set-first body-st)) ,ea)))
		; A redex under the argument expression was found
                (set `((lambda (,y) ,body) ,(set-first ea-st)))))]
         [`(,ef ,ea)
	  (let ([ef-st (applicative-order-reduce ef)]
		[ea-st (applicative-order-reduce ea)])
            (if (set-empty? ea-st)
                ; No redex found
                (if (set-empty? ef-st)
		    (set)
		    (set `(,(set-first ef-st) ,ea)))
                ; Argument expression contained a redex
                (set `(,ef ,(set-first ea-st)))))]))


; Reduce the given expression by exactly one beta-reduction using
; normal evaluation order. Return the simplified expression in a
; singleton set, or return (set) if there is no normal-order redex.
; Skip over any redexes that cannot be reduced using capture avoiding subst.
;(define (normal-order-reduce e)
;  'todo)

(define (normal-order-reduce e)
  (match e
    [(? symbol?) (set)]
    [`((lambda (,x) ,body) ,arg)
     (set (capt-avoid-subst body x arg))]
    [`(lambda (,x) ,body)
     (let ([body-st (normal-order-reduce body)])
       (if (set-empty? body-st)
           (set)
           (set `(lambda (,x) ,(set-first body-st)))))]
    [`(,f ,arg)
     (let ([f-st (normal-order-reduce f)])
       (if (set-empty? f-st)
           (let ([arg-st (normal-order-reduce arg)])
             (if (set-empty? arg-st)
                 (set)
                 (set `(,f ,(set-first arg-st)))))
           (set `(,(set-first f-st) ,arg))))]))

; Reduce the given expression by exactly one beta-reduction using
; call-by-value evaluation order. Return the simplified expression in a
; singleton set, or return (set) if there is no CBV order redex.
;(define (CBV-order-reduce e)
;  'todo)

(define (CBV-order-reduce e)
  (match e
    ;; Direct application of a lambda expression to an argument
    [`((lambda (,x) ,body) ,arg)
     ;; Evaluate the argument first, if it's not already a value
     (if (value? arg)
         ;; If the argument is a value, proceed with substitution
         (let ([reduced-body (capt-avoid-subst body x arg)])
           (if (eq? reduced-body 'failed)
               (set) ;; Failed substitution, return empty set
               (set reduced-body))) ;; Successfully reduced
         ;; If the argument is not a value, attempt to reduce it
         (let ([reduced-arg (CBV-order-reduce arg)])
           (if (set-empty? reduced-arg)
               (set) ;; No reduction possible for the argument
               ;; Return with the reduced argument
               (set `((lambda (,x) ,body) ,(set-first reduced-arg))))))]
    ;; General function application
    [`(,f ,arg)
     ;; Try reducing the argument before the function part
     (let ([reduced-arg (CBV-order-reduce arg)])
       (if (set-empty? reduced-arg)
           ;; If the argument part cannot be reduced, then try reducing the function part
           (let ([reduced-f (CBV-order-reduce f)])
             (if (set-empty? reduced-f)
                 (set) ;; No reduction possible in the function part
                 ;; Return with the reduced function part
                 (set `(,(set-first reduced-f) ,arg))))
           ;; Return with the reduced argument
           (set `(,f ,(set-first reduced-arg)))))]
    ;; For expressions that are not directly reducible in this context
    [_ (set)]))

(define (value? e)
  (or (symbol? e)
      (and (pair? e) (eq? (car e) 'lambda))))

; Reduce the given expression by exactly one beta-reduction using
; call-by-name evaluation order. Return the simplified expression in a
; singleton set, or return (set) if there is no applicative order redex.
;(define (CBN-order-reduce e)
;  'todo)

(define (CBN-order-reduce e)
  (match e
    [`((lambda (,x) ,body) ,arg)
     ; Direct application of function to argument without evaluating the argument
     (set (capt-avoid-subst body x arg))]
    [`(,f ,arg)
     ; If the expression is a function application, try reducing the function part first
     (let ([f-st (CBN-order-reduce f)])
       (if (set-empty? f-st)
           ; If no reduction occurred in the function, there's nothing further to do
           (set)
           ; If reduction occurred in the function, return the new expression
           (set `(,(set-first f-st) ,arg))))]
    [_ ; For any other form (like variables or lambda abstractions), no reduction is possible
     (set)]))


; Takes one of the four step/reduce functions and an expression in the lambda calculus (satisfying exp?)
; Yields a list representing the full evaluation trace from e to a value
; Note, this function will non-terminate on programs like Omega that cannot be reduced to a value.
(define (collect-evaluation-trace step-f e)
  (let loop ([latest (set e)]
             [trace '()])
    (if (set-empty? latest)
        (reverse trace)
        (loop (step-f (set-first latest))
              (cons (set-first latest) trace)))))

