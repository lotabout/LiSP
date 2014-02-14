;======================================================================
; Documents

;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
; Special Forms
; Special forms are syntactic forms that are "untouchable": they
; cannot be redefined adequately, and they must not be tampered
; with. In Lisp, such form is known as a "special form". It is
; represented by a list where the first term is a particular symbol
; belonging to the set of "specify operators"

; Scheme has chosen to minimize the number of special operators:
; (quote, if, set!, and lambda).

;======================================================================
; Error Handling
(define wrong error)

;======================================================================
; Environment Handling

; Provide:
;  1. lookup -- (lookup var env)
;  2. update! -- (update! variable env value)
;  3. extend -- (extend env variables values)

;; We use associated list to represent environments
;; (('var1 . val1) ('var2 . 'val2) ...)

;;; lookup
;;; (lookup <variable> <environment>) -> value
(define (lookup var env)
  (if  (pair? env)
       (if (eq? (caar env) var)
	   (cddr env)
	   (lookup var (cdr env)))
       (wrong "No such binding" var)))

;; implement lookup using assoc
(define (lookup var env)
  (cond ((assoc var env) => cdr)
	(else (wrong "No such binding"))))

;;; update!
;;; (update! var env val) => update the corresponding 'var' with 'val'
(define (update! var env val)
  (if (pair? env)
      (if (eq? (caar env) var)
	  (set-cdr! (car env) val)
	  (update! var (cdr env) val))
      (wrong "No such binding" var)))

;;; implement update! using assoc
(define (update! var env value)
  (cond ((assoc var env) => (lambda (pair) (set-cdr! pair value)))
	(else (wrong "No such binding"))))

(define env.init '())

;;; extend
;;; extend an environment with a list of variables and a list of values.
(define (extend env variables values)
  (cond ((pair? variables)
	 (if (pair? values)
	     (cons (cons (car variables) (car values))
		   (extend env (cdr variables) (cdr values)))
	     (wrong "Too less values")))
	((null? variables)
	 (if (null? values)
	     env
	     (wrong "Too much values")))
	((symbol? variables) (cons (cons variables values) env))))

;;; Two macros for convenience
(define env.global env.init)
(define-syntax definitial
  (syntax-rules ()
    ((_ name)
     (begin (set! env.global (cons (cons 'name 'void) env.global))
	    'name))
    ((_ name value)
     (begin (set! env.global (cons (cons 'name value) env.global))
	    'name))))
(define-syntax defprimitive
  (syntax-rules ()
    ((_ name value arity)
     (definitial name
       (lambda (values)
	 (if (= arity (length values))
	     (apply value values) ; The real apply of scheme
	     (wrong "Incorrect arity" (list 'name values))))))))

;--------------------------------------------------
; Global Environment
(define the-false-value #f)
(definitial t #t)
(definitial f the-false-value)
(definitial nil '())
(definitial foo)
(definitial bar)
(definitial fib)
(definitial fact)
(defprimitive cons cons 2)
(defprimitive car car 1)
(defprimitive set-cdr! set-cdr! 2)
(defprimitive + + 2)
(defprimitive eq? eq? 2)
(defprimitive < < 2)

;======================================================================
; Implement the "eval" function

; Environment Handling
;;; atom?: determine if exp is an atom
(define (atom? exp)
  (not (pair? exp)))

;--------------------------------------------------
; Handle Sequences
(define (eprogn exps env)
  (if (pair? exps)
      (if (pair? (cdr exps))
	  (begin (evaluate (car exps) env)
		 (eprogn (cdr exps) env))
	  (evaluate (car exps) env))
      '()))

; add a layer which hide seqence details
(define seq? pair?)
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))
(define (last-exp? seq) (null? (cdr seq)))
(define (eprogn seqs env)
  (if (seq? seqs)
      (if (last-exp? seqs)
	  (evaluate (first-exp seqs) env)
	  (begin (evaluate (first-exp seqs) env)
		 (eprogn (rest-exps seqs) env)))
      '()))

;--------------------------------------------------
; Handle Function Application

;;; given a list of <parameters>, evaluate all of them
;;; i.e. map evaluate over (<arg1> <arg2> ...)
(define (evlis exps env)
  (if (pair? exps)
      (cons (evaluate (car exps) env)
	    (evlis (cdr exps) env))
      '()))

;;; Now we use scheme's function to represent the to-be-scheme's
;;; function.

;;; invoke
;;; (invoke fn args) => actually apply the function 'fn' to 'args'
(define (invoke fn args)
  (if (procedure? fn)
      (fn args)
      (wrong "Not a function" fn)))

;;; establish a function
(define (make-function variables body env)
  (lambda (values)
    (eprogn body (extend env variables values))))

;;; support modified version of "evaluate" for applying function
(define (d.invoke fn args env)
  (if (procedure? fn)
      (fn args env)
      (wrong "Not a function" fn)))

(define (d.make-function variables body def.env)
  (lambda (values current.env)
    (eprogn body (extend current.env variables values))))

(define (d.make-closure fun env)
  (lambda (values current.env)
    (fun values env)))

;--------------------------------------------------
; The "eval" function itself.

;;; Evaluates an expression with a given environment
;;; => return a scheme object
(define (evaluate e env)
  (if (atom? e)
      (cond ((symbol? e) (lookup e env))
	    ((or (number? e) (string? e) (char? e)
		 (boolean? e) (vector? e))
	     e)  ; objects that evaluate to themselves.
	    (else (wrong "Cannot evaluate" e)))
      (case (car e)  ; handling special forms
	; (quote <exp>)
	((quote) (cadr e))  
	; (if <test> <consequence> <alternate>)
	((if) (if (evaluate (cadr e) env)     
		  (evaluate (caddr e) env)
		  (evaluate (cadddr e) env)))
	; (begin <exp> ...>)
	((begin) (eprogn (cdr e) env))
	; (set! <var> <val>)
	((set!) (update! (cadr e) env (evaluate (caddr e) env)))
	; (lambda (<arg> ...) <exp> ...)
	((lambda) (make-function (cadr e) (cddr e) env))
	; (<fun> <parameters>)
	(else (invoke (evaluate (car e) env)
		      (evlis (cdr e) env))))))

;;; Modified version of "evaluate" for applying function
(define (d.evaluate e env)
  (if (atom? e)
      (cond ((symbol? e) (lookup e env))
	    ((or (number? e) (string? e) (char? e)
		 (boolean? e) (vector? e))
	     e)  ; objects that evaluate to themselves.
	    (else (wrong "Cannot evaluate" e)))
      (case (car e)  ; handling special forms
	; (quote <exp>)
	((quote) (cadr e))  
	; (if <test> <consequence> <alternate>)
	((if) (if (evaluate (cadr e) env)     
		  (evaluate (caddr e) env)
		  (evaluate (cadddr e) env)))
	; (begin <exp> ...>)
	((begin) (eprogn (cdr e) env))
	; (set! <var> <val>)
	((set!) (update! (cadr e) env (evaluate (caddr e) env)))
	; for section 1.6, introduce closure manually
	((function) ; syntax: (function (lambda <variables> <body>))
	 (let* ((f (cadr e))
		(fun (d.make-function (cadr f) (cddr f) env)))
	   (d.make-closure fun env)))
	; (lambda (<arg> ...) <exp> ...)
	((lambda) (d.make-function (cadr e) (cddr e) env))
	; (<fun> <parameters>)
	(else (d.invoke (d.evaluate (car e) env)
			(evlis (cdr e) env)
			env)))))

;======================================================================
; Starting the Interpreter

(define (chapter1-scheme)
  (define (toplevel)
    (display (evaluate (read) env.global))
    (newline)
    (toplevel))
  (toplevel))
