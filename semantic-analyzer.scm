

;;;;;;;;;;;;;;;;;;;;;; helper function ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;return arguments of lambda as a list
(define lambda-args->lst
  (lambda (el)
    (let (  (lambda-type (car el))
	  		(args (cadr el)))
    (cond 	((equal? lambda-type 'lambda-simple) args)
      		((equal? lambda-type 'lambda-opt) (append args (list (caddr el))))
      		(else (list args))))))


(define getLambdaArgs
  (lambda (el)
    (let ((lambda-type (car el))
	  (args (cadr el)))
    (cond
      ((lambdaWithoutArgs? el) `(() ,(caddr el)))
      ((null? args) '(()))  
      ((equal? lambda-type 'lambda-simple) `(,args))
      ((equal? lambda-type 'lambda-opt) `(,args ,(caddr el)))
      (else (list args))))))



;returns #t if lambda-simple or lambda-opt
(define lambda?
    (lambda (expr)
        (and (list? expr) (not (null? expr))
         (or 	(eq? (car expr) 'lambda-simple)
          		(eq? (car expr) 'lambda-opt))))) 

;returns body according to lambda type
(define getLambdaBody
    (lambda (expr)
    	(let ((lambdaType (car expr)))
	    	(if (equal? lambdaType 'lambda-simple) 
	    		(caddr expr)
	    		(cadddr expr)))))

(define setLambdaBody
    (lambda (orgLambda newBody)
        (cond ((eq? (car orgLambda) 'lambda-simple) `(lambda-simple ,(cadr orgLambda) ,newBody))
              ((eq? (car orgLambda) 'lambda-opt) `(lambda-opt ,(cadr orgLambda) ,(caddr orgLambda) ,newBody))
              (else #f))))


;returns args according to lambda type
(define getLambdaParameters
    (lambda (expr)
    	(let ((lambdaType (car expr)))
    		(if (eq? lambdaType 'lambda-simple)
    			(cadr expr)
    			(append (cadr expr) (list (caddr expr)))))))


(define var?
	(lambda (expr)
		(member (car expr) '(var fvar bvar pvar const))))

(define lambdaWithoutArgs?
	(lambda (expr)
		(and (equal? (car expr) 'lambda-opt) (null? (cadr expr)))))



;;;;;;;;;;;;;;;;;;;;;; applicLambdaSimpleNil ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define applicLambdaSimpleNil?
  (lambda (expr)
  	(if (and (> (length expr) 1) (list? expr) (eq? (car expr) 'applic) (list? (cadr expr))) ;if applic tag
  		(let ((expr (cadr expr)))
  			 (if (and (> (length expr) 2) (eq? (car expr) 'lambda-simple) (null? (cadr expr)))	 
  			 (caddr expr)
  			 '()))
  		'())))


(define removeApplicLambdaTag
	(lambda (expr)
  		(let ((body (applicLambdaSimpleNil? expr)))
  			(cond 	((null? body) expr)
  					((list? body) (remove-applic-lambda-nil body))
  					(else body)))))

(define remove-applic-lambda-nil
  (lambda (lst)
    (map (lambda (el) (if (list? el) ;lambda
    					(remove-applic-lambda-nil el)
    					el))
    (removeApplicLambdaTag lst)))) ;list

;;;;;;;;;;;;;;;;;;;;;;;;;; box-set ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
          

;eliminate-nested-defines-seq-pairs
; returns a list of defines, actualValues and the rest of the body
(define seqPairs
    (lambda (expr defines actualValues)
        (cond ((or (null? expr) (not (list? expr))) (list defines actualValues expr)) ; if expr isn't list nor null 
              ((equal? (caar expr) 'define) ;if define expression
                (seqPairs (cdr expr)
                             (append defines (list (cadar expr)))
                             (append actualValues (list (suffix (caddar expr))))))
              (else (list defines actualValues expr)))))


;called only with lambda body
(define suffixLambdaBody
    (lambda (expr)
    	(let ((tag (car expr)))
	        (cond ((or (not (list? expr)) (null? expr)) expr) ; (= (length expr) 1)
	              ((and (equal? tag 'seq) (not (equal? (length (car (seqPairs (cadr expr) '() '()))) 0)))  ;its a sequence, there aren't any nested defines
		               (let* ((esp (seqPairs (cadr expr) '() '())) ; esp[0]=defs, esp[1]=actualvalueues, esp[2]=rest
		               		  (args (car esp))) 
		                    `(applic (lambda-simple 
		                             ,(map cadr args)
		                             (seq ,(append (map (lambda (define value) `(set ,define ,value)) args (suffix (cadr esp))) (suffix (caddr esp)))))
		                            ,(map (lambda (x) '(const #f)) args))))
	              ((equal? tag 'define) ; tag is define
	                (let* ((esp (seqPairs (list expr) '() '()))) ; esp[0]=defs, esp[1]=actualvalueues, esp[2]=rest
	                    `(applic (lambda-simple 
	                                ,(map cadr (car esp))
	                                (seq ,(list (map (lambda (define value) `(set ,define ,value)) (car esp) (suffix (cadr esp)))
	                                            (suffix (caddr esp)))))
	                             ,(map (lambda (x) '(const #f)) (car esp)))))
	              (else (suffix expr))))))
        
              
;eliminate-nested-defines body
(define eliminate-nested-defines 
    (lambda (expr)
        (cond ((or (null? expr) (not (list? expr))) expr)
              ((equal? (car expr) 'define)
                `(define ,(cadr expr) ,(suffix (caddr expr))))
              (else (suffix expr)))))

(define suffix
    (lambda (expr) (if  (or (null? expr) (not (list? expr)))
    					expr
    					(if (lambda? expr)
    						(setLambdaBody expr (suffixLambdaBody (getLambdaBody expr)))
    						(map suffix expr)))))
 
 (define tagged?
    (lambda (expr)
        (and (list? expr)
             (not (null? expr)) 
             (eq? (car expr) 'set) 
             (list? (cadr expr)) 
             (= (length (cadr expr)) 2) 
             (eq? (caadr expr) 'var))))

(define prefixPush
    (lambda (expr toPush)
    	(if (or (null? expr) (not (list? expr)))
    		toPush
    		(if (eq? (car expr) 'seq)
    			`(seq ,(append (list toPush) (cadr expr)))
    			`(seq (,toPush ,expr))))))

(define equalVar?
    (lambda (el var)
        (and (list? el) (equal? (length el) 2) (equal? (car el) 'var) (equal? (cadr el) var))))
              
; var is '<char>
(define varInParams?
    (lambda (expr var)                                                         ;the list of parameters
        (and (lambda? expr) (not (< (length (filter (lambda (param) (equal? param var)) (getLambdaParameters expr))) 1)))))
            
; var is 'a or 'b or so..
(define varNotInParams?
    (lambda (expr var)                                                    ;the list of parameters
        (and (lambda? expr) (< (length (filter (lambda (param) (equal? param var)) (getLambdaParameters expr))) 1))))

; var is 'a or 'b or so..
(define hasParamsOrIsSet?
    (lambda (expr var)
        (or (varInParams? expr var) (tagged? expr))))

; is expr fulfilling f untill there is lambda with this var inside of it which it ignores it and continue
; var     is 'a or 'b or so..
; proc must receive an expr as a list and a value and checks if the list fullfills it needs
; suffixFunc must receive an expr as a list and a value and cut the search in that branch if it fullfills it needs
(define sameUntilSuffixFunc
    (lambda (proc var suffixFunc)
        (lambda (expr)
        	(if (or (not (list? expr)) (null? expr) (suffixFunc expr var))
        		#f
        		(if (proc expr var)
        			#t
        			(ormap (sameUntilSuffixFunc proc var suffixFunc) expr))))))
               
; find if under an expr tree there is a var with that name (until it get to a leaf or a lambda with redeclaration of that var)
(define appearsInExp?
    (lambda (expr var) ((sameUntilSuffixFunc equalVar? var varInParams?) expr)))
                
; checks if the variable is bounded
; if there is a lambda in the expr (flatly - not as tree search), it search this lambda fully to find if the variable is called there
(define Bounded?
    (lambda (expr var)
        (let ((NotInParamsAndAppearsInExp (lambda (nestedExp) (and (varNotInParams? nestedExp var) (appearsInExp? (getLambdaBody nestedExp) var)))))
             (or (NotInParamsAndAppearsInExp expr) (ormap NotInParamsAndAppearsInExp expr)))))
            
            
; checks flatly whether there is a set in the expr
(define taggedVar?
    (lambda (expr var) (and (tagged? expr) (equal? (cadadr expr) var))))

             
; find if under an expr tree there is a var with that name (untill it get to a leaf or a lambda with redeclaration of that var)
(define appearsInExp?
    (lambda (expr var)
        ((sameUntilSuffixFunc equalVar? var varInParams?)
         expr)))             
             
             
; checks if the variable is called (excluding (set var to something))
; if there is a set in the expr (flatly - not as tree search), it search this set fully by himself to find if the variable is called there
(define varCalled?
    (lambda (expr var)
        (let ((teggedAndsameUntilSuffixFunc (lambda (nestedExp)
                                				(and (tagged? nestedExp) ((sameUntilSuffixFunc varCalled? var hasParamsOrIsSet?) (caddr nestedExp))))))
          (or (equalVar? expr var) (ormap teggedAndsameUntilSuffixFunc expr)))))
                
; search if all three of the requirments are fulfilled in the expr
(define box-set?
    (lambda (expr var)
        (and ((sameUntilSuffixFunc Bounded? var varInParams?) expr)
             ((sameUntilSuffixFunc taggedVar? var varInParams?) expr)
             ((sameUntilSuffixFunc varCalled? var hasParamsOrIsSet?) expr))))
     
(define BoxSetGet
    (lambda (var)
        (lambda (expr)
            (cond ((or (null? expr) (not (list? expr)) (varInParams? expr var)) expr)
                ((equalVar? expr var) `(box-get (var ,var)))
                ((taggedVar? expr var) `(box-set (var ,var) ,((BoxSetGet var) (caddr expr))))
                (else (map (BoxSetGet var) expr))))))
                
; checks if a variable is need to be replaced and if so, replaces it.
(define lambdaBox
    (lambda (expr var)
    	(cond ((box-set? expr var) (prefixPush ((BoxSetGet var) expr) `(set (var ,var) (box (var ,var)))))
    	       (else expr))))

; replaces lst variables if needed inside expression
(define lambdaBoxList
    (lambda (expr lst)
    	(cond 	((null? lst) expr)
    			(else (lambdaBoxList (lambdaBox expr (car lst)) (cdr lst))))))

(define box-set
    (lambda (expr)
        (cond ((or (not (list? expr)) (null? expr)) expr)
              ((lambda? expr) (setLambdaBody expr 
                                            (box-set (lambdaBoxList (getLambdaBody expr)
                                                                            (reverse (getLambdaParameters expr))))))
              (else (map box-set expr)))))



;;;;;;;;;;;;;;;;;;;;;; pe->lex-pe ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define replaceBound
  (lambda (var major minor expr)
      (cond ((null? expr) expr)
			((list? expr) (cond ((and (eq? 2 (length expr)) (equal? (car expr) 'var) (equal? (cadr expr) var)) `(bvar ,var ,major ,minor))
	      						((and (lambda? expr) (not (member var (lambda-args->lst expr)))) `(,(car expr) ,@(getLambdaArgs expr) ,(replaceBound var (+ 1 major) minor (getLambdaBody expr))))
	      						((lambda? expr) expr)
	      						(else (map (lambda (x) (replaceBound var major minor x)) expr))))
	  (else expr))))	

(define replaceParam
  (lambda (var minor expr)
      	(cond ((null? expr) expr)
			((list? expr) (cond ((and (equal? 2 (length expr)) (equal? (car expr) 'var) (equal? (cadr expr) var)) `(pvar ,var ,minor))
	      						((and (lambda? expr) (not (member var (lambda-args->lst expr)))) `(,(car expr) ,@(getLambdaArgs expr) ,(replaceBound var 0 minor (getLambdaBody expr)))) ; if bounded
	      						((lambda? expr) expr)  	  
	      						(else (map (lambda (x) (replaceParam var minor x)) expr))))
		(else expr))))	

(define replaceParams
  (lambda (vars minor expr)
    (if (null? vars) 
    	expr
		(replaceParams (cdr vars) (+ minor 1) (replaceParam (car vars) (+ minor 1) expr)))))


(define SearchParamBoundedVars
    (lambda (expr)
    	(if (null? expr)
    		expr
    		(if (list? expr)
    			(if (and (not (null? expr)) (lambda?  expr))
    				`(,(car expr) ,@(getLambdaArgs expr),(SearchParamBoundedVars (replaceParams (lambda-args->lst expr) -1  (getLambdaBody expr))))
    				(map SearchParamBoundedVars expr))
    			expr))))

(define pe->lex-pe
    (lambda (expr)
      (letrec ( (ParamBoundedVars (SearchParamBoundedVars expr))
	       		(iter (lambda (ParamBoundedVars) 
	       			(cond 	((null? ParamBoundedVars) ParamBoundedVars) 
	       					((list? ParamBoundedVars) 
	       						(if (and (equal? (length ParamBoundedVars) 2) (equal? (car ParamBoundedVars) 'var))
	       							`(fvar ,(cadr ParamBoundedVars))
									 (map iter ParamBoundedVars)))
	       					(else ParamBoundedVars)))))
      	(iter ParamBoundedVars))))


;;;;;;;;;;;;;;;;;;;;;; annotate-tc ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define anotate-tc-run
  (lambda (expr in-tp)
      (cond ((null? expr) expr)
			((list? expr) (cond ((lambda? expr) `(,(car expr) ,@(getLambdaArgs expr) ,(anotate-tc-run (getLambdaBody expr) #t)))
	      						((equal? (car expr) 'applic) (if 	in-tp 
		  															`(tc-applic ,@(anotate-tc-run (cdr expr) #f))
		  															`(applic ,@(anotate-tc-run (cdr expr) #f))))	
	      						((equal? (car expr) 'if3) (let ((test (cadr expr))
	      		  												(dit (caddr expr))
	      		  												(dif (cadddr expr)))
															`(if3 ,(anotate-tc-run test #f) ,(anotate-tc-run dit in-tp) ,(anotate-tc-run dif in-tp))))
        						((member (car expr) '(set box-set)) `(,(car expr) ,(cadr expr) ,(anotate-tc-run (caddr expr) #f)))
        						((var? expr) expr)
	      						((or (equal? (car expr) 'seq) (equal? (car expr) 'or)) (let* ( (operator (car expr))
																							   (reversedList (reverse (cadr expr)))
																						       (last (car reversedList))
																						       (withoutLast (reverse (cdr reversedList))))
																						`(,operator (,@(map (lambda (subExp) (anotate-tc-run subExp #f)) withoutLast) ,(anotate-tc-run last in-tp)))))
	      						(else (map (lambda (subExp) (anotate-tc-run subExp in-tp)) expr))))
			(else expr))))

(define annotate-tc
  (lambda (expr)
    (anotate-tc-run expr #f)))
