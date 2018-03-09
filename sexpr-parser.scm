(load "project/pc.scm")

; ################## HELPER PARSERS

(define char->symbol
  (lambda (ch)
    (string->symbol (string ch))
))

(define <whitespace>
  (const
   (lambda (ch)
     (char<=? ch #\space))))

(define <lineComment>
  (let ((<CommentsAfterNewline>
   (new (*parser (char #\newline))
        (*parser <end-of-input>)
        (*disj 2)
        done)))
    (new (*parser (char #\;))
   
   (*parser <any-char>)
   (*parser <CommentsAfterNewline>)
   *diff *star

   (*parser <CommentsAfterNewline>)
   (*caten 3)
   done)))

(define <skip>
  (lambda (<parser>)
  (new (*parser (word "#;"))
       (*delayed <parser>)
       (*caten 2)
       done)))

(define <comment>
  (lambda (<parser>)
    (new
      (*parser (<skip> <parser>))
      (*parser <lineComment>)
      (*disj 2)
      done)))


(define <endWithWhitespace>
  (lambda (<parser>)
    (new
      (*parser (<comment> <parser>))
      (*parser <whitespace>)
      (*disj 2)
  done)))

(define <remSpacesCommentsinfix>
    (lambda (<p>)
      (new (*parser (star (<endWithWhitespace> (lambda () <InfixExpression>))))
     (*parser <p>)
     (*parser (star (<endWithWhitespace> (lambda () <InfixExpression>))))
     (*caten 3)
     (*pack-with
      (lambda (_left e _right) e))
     done)))

(define <remSpacesCommentsSexpr>
    (lambda (<p>)
      (new (*parser (star (<endWithWhitespace> (lambda () <Sexpr>))))
     (*parser <p>)
     (*parser (star (<endWithWhitespace> (lambda () <Sexpr>))))
     (*caten 3)
     (*pack-with
      (lambda (_left e _right) e))
     done)))
     
(define <removeSpaces>
    (lambda (<p>) ;gets parser and cleans all the whitespaces
      (new 
        (*parser (star <whitespace>))
        (*parser <p>)
        (*parser (star <whitespace>))
        (*caten 3)
        (*pack-with
         (lambda (_left e _right) e))
     done)))

(define <CleanSpaces>
  (lambda( <parser>)
    (new
      (*parser <whitespace>) *star
      (*parser <p>)
      (*parser <whitespace>) *star
      (*caten 3)
      *pack-with (lambda (leftSpace expression rightSpace) expression))
      ))



; Helper functions
; #####################################################################
(define <sexprWithSpace>                                                    
  (new

    (*delayed (lambda () <Sexpr>))
    (*parser (char #\space)) *star
    (*caten 2)
    (*pack-with (lambda (Sexpr space) Sexpr )) 

    (*parser (char #\space)) *star
    (*delayed (lambda () <Sexpr>)) 
    (*caten 2)
    (*pack-with (lambda (space Sexpr) Sexpr)) 

    (*delayed (lambda () <Sexpr>))

    (*disj 3)

    done))


(define <ParserWithSpaces>  
  (lambda(<parser>)                                                  
    (new

      (*delayed (lambda () <parser>))
      (*parser (char #\space)) *star
      (*caten 2)
      (*pack-with (lambda (Sexpr space) Sexpr )) 

      (*parser (char #\space)) *star
      (*delayed (lambda () <parser>))
      (*caten 2)
      (*pack-with (lambda (space Sexpr) Sexpr)) 

      (*delayed (lambda () <parser>))

      (*disj 3)

      done)))

(define is-unicode
  (lambda (num) 
    (and
  (or (= num #x0) (> num #x0)) 
  (or (= num #x10FFFF) (< num #x10FFFF)))
))

(define list->number
  (lambda (base)
    (lambda (lst)
      (string->number (list->string lst) base))
  ))

(define list->hex-number (list->number 16))

(define list->decimal-number (list->number 10))

(define list->symbol
  (lambda (lst)
    (string->symbol (list->string lst))
))


;######################### CHAR ##########################

(define <HexChar>
  (new
   (*parser (range #\0 #\9))
   (*parser (range-ci #\a #\f))
   (*disj 2)
  done))

(define <CharPrefix> (word "#\\"))

(define <NamedChar>
  (new
   (*parser (word-ci "lambda"))
   (*parser (word-ci "newline"))
   (*parser (word-ci "nul"))
   (*parser (word-ci "page"))
   (*parser (word-ci "return"))
   (*parser (word-ci "space"))
   (*parser (word-ci "tab"))
   (*disj 7)
   (*delayed (lambda () <Symbol>))
    *not-followed-by
   (*pack list->string)
done))

(define <VisibleSimpleChar>
 (const (lambda (ch) (char<=? (integer->char 33) ch))))


(define is-unicode
  (lambda (num) 
    (and
  (or (= num #x0) (> num #x0)) 
  (or (= num #x10FFFF) (< num #x10FFFF)))
))


(define <HexUnicodeChar> 
  (new
  (*parser (char-ci #\x))
  (*parser <HexChar>) *plus
  (*caten 2)

 (*pack-with (lambda (first rest)
   (list->hex-number `(,@rest))))
  (*only-if is-unicode)
  (*pack integer->char)  
done))


 (define <Char>
  (new
   (*parser <CharPrefix>)
   
   (*parser <VisibleSimpleChar>)
   (*parser <VisibleSimpleChar>)
   (*parser (char #\]))
   (*parser (char #\[))
   (*parser (char #\)))
   (*parser (char #\())
   (*disj 4)
   *diff
   *not-followed-by

   (*parser <NamedChar>)
   (*pack (lambda (namedChar) 
    ((lambda (str)
    (cond ((string-ci=? "lambda" str) (integer->char 955))
          ((string-ci=? "newline" str) #\newline)
          ((string-ci=? "nul" str) #\nul)
          ((string-ci=? "page" str) #\page)
          ((string-ci=? "return" str) #\return)
          ((string-ci=? "space" str) #\space)
          ((string-ci=? "tab" str) #\tab)
          (else #f))
    ) namedChar)))

   (*parser <HexUnicodeChar>)
   (*disj 3)

   (*caten 2)
   (*pack-with (lambda (prefix ch) ch))
  done)) 

; ##################### String #########################

(define <StringHexChar>
  (new
  (*parser (word-ci "\\x"))
  (*parser <HexChar>) *star
  (*parser (char #\;))
  (*caten 3)
  (*pack-with (lambda (x hexChar semicolon)
      (list->hex-number `(,@hexChar))))
  (*only-if is-unicode)
  (*pack integer->char)         
 done))

(define <StringMetaChar>
  (new
   (*parser (word-ci "\\\\")) ; \\
   (*parser (word-ci "\\\"")) ; \"
   (*parser (word-ci "\\t"))  ; \t
   (*parser (word-ci "\\f"))  ; \f
   (*parser (word-ci "\\n"))  ; \n
   (*parser (word-ci "\\r"))  ; \r
   (*disj 6)
   (*pack (lambda(meta-ch)
    (let ((str (list->string meta-ch)))
      (cond 
      ((string-ci=? "\\\\" str) #\\)
    ((string-ci=? "\\\"" str) #\")
    ((string-ci=? "\\t" str) #\tab)
    ((string-ci=? "\\f" str) #\page)
      ((string-ci=? "\\n" str) #\newline)
      ((string-ci=? "\\r" str) #\return)
      (else #f)))
    ))
done))


(define <StringLiteralChar>  
  (const (lambda(ch) (and (not(char=? #\\ ch)) (not(char=? #\" ch))))))

 (define <StringChar> 
  (new 
    (*parser <StringHexChar>)
    (*parser <StringMetaChar>)
    (*parser <StringLiteralChar>)
    (*disj 3)
  done))

(define <String>
  (new
   (*parser (char #\"))
   (*parser <StringChar>)
   (*parser (char #\"))
   *diff
   *star
   (*parser (char #\"))
   (*caten 3)
   (*pack-with (lambda (leftGershaym str rightGershaym)
(list->string str)))
done)) 



; ################## Symbol ##################
(define <SymbolChar>
  (new
   (*parser (range #\0 #\9))
   (*parser (range-ci #\a #\z))
   (*pack char-downcase)
   (*parser (char #\!))
   (*parser (char #\$))
   (*parser (char #\^))
   (*parser (char #\*))
   (*parser (char #\-))
   (*parser (char #\_))
   (*parser (char #\=))
   (*parser (char #\+))
   (*parser (char #\<))
   (*parser (char #\>))
   (*parser (char #\?))
   (*parser (char #\/))
   (*disj 14)
done))

(define <Symbol> 
  (new 
   (*parser <SymbolChar>) *plus
   (*pack (lambda (lst)
 (list->symbol lst))) 
done))

;############## Boolean ####################
(define <Boolean> 
  (new
   (*parser (word-ci "#t"))
   (*pack (lambda (bool) #t))

   (*parser (word-ci "#f"))
   (*pack (lambda (bool) #f))

   (*disj 2)
done))

;############## NUMBER ####################
(define <Natural>
  (new
   (*parser (range #\0 #\9)) *plus
   (*pack list->decimal-number)
done))


(define <Integer>
  (new
   (*parser (char #\+))
   (*parser <Natural>)
   (*caten 2)
   (*pack-with (lambda (plus number) number))

   (*parser (char #\-))
   (*parser <Natural>)
   (*caten 2)
   (*pack-with (lambda (minus num) (- num)))

   (*parser <Natural>)

   (*disj 3)
done))

(define <Fraction>
  (new
   (*parser <Integer>)
   (*parser (char #\/))
   (*parser <Natural>)
   (*caten 3)

   (*pack-with (lambda (int backSlash num) (/ int num)))
  done))


(define <Number>
  (new
    (*parser <Fraction>)
    (*parser <Integer>)
    (*disj 2)
  done))


(define <NumberNotFollowedBySymbol>
  (new
   (*parser <Number>)
   (*delayed (lambda () <Symbol>))
   (*parser (range #\0 #\9))
   (*parser (char #\/))
   (*disj 2)
   *diff
   *not-followed-by
  done))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; InfixExtension ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   
(define <InfixPrefixExtensionPrefix>
  (<removeSpaces> (disj (word "##") (word "#%"))))


(define <InfixSymbol>
  (new
   (*parser (range #\0 #\9))
   (*parser (range-ci #\a #\z))
   (*pack char-downcase)
   (*parser (char #\!))
   (*parser (char #\$))
   (*parser (char #\_))
   (*parser (char #\=))
   (*parser (char #\<))
   (*parser (char #\>))
   (*parser (char #\?))
   (*disj 9)
   *plus
   (*pack list->symbol)
   done)) 
   
(define <AtomicInfixValue>
    (new   
      (*parser <Number>)
      (*parser <InfixSymbol>)
      (*parser (range #\0 #\9))
      *diff
      *not-followed-by
      
      (*parser <InfixSymbol>)
      
      (*delayed (lambda ()  <InfixSexprEscape>)) 
      
      (*disj 3)
    done))
    
(define <PowerSymbol>
  (new
    (*parser (<remSpacesCommentsinfix> (char #\^)))
    (*parser (<remSpacesCommentsinfix> (word "**")))  
    (*disj 2)  
    (*pack (lambda (powSymbol) 'expt))
   done))
  
(define <InfixParen>
  (new 
    (*parser (char #\())
    (*delayed (lambda () (<remSpacesCommentsinfix> ^<InfixExpression>)))
    (*parser (char #\)))
    (*caten 3)
    (*pack-with (lambda (p1 exp p2) exp))   
            
    (*parser (<remSpacesCommentsinfix> <AtomicInfixValue>))
    (*disj 2)
  done)) 

(define <InfixArgList>
  (new
    (*delayed (lambda () <InfixExpression>))
    (*parser (char #\,))
    (*delayed (lambda () <InfixExpression>))   
    (*caten 2)
    (*pack-with (lambda (psik infixExpression) infixExpression))
    *star
    (*caten 2)
    (*pack-with (lambda (infixExpression rest) `(,infixExpression ,@rest)))
    
    (*parser <epsilon>)
    (*disj 2)
   done))  
     
(define <InfixArrayFuncall>
  (new           
    (*parser <InfixParen>)
    
    (*parser (<remSpacesCommentsinfix> (char #\[)))
    (*delayed (lambda () <InfixExpression>))
    (*parser (<remSpacesCommentsinfix> (char #\])))
    (*caten 3)
    (*pack-with (lambda (op1 exp op2) (cons 'array exp)))
    
    (*parser (<removeSpaces> (char #\()))
    (*parser <InfixArgList>)
    (*parser (<removeSpaces> (char #\))))
    (*caten 3)
    (*pack-with (lambda (op1 args op2) (cons 'funcall args))) 
    
    (*disj 2)
    *star
    
    (*caten 2)
    (*pack-with (lambda (first rest)
    (if (null? rest)
    first
        `,(fold-left (lambda (x y) 
        (if (equal? (car y) 'funcall)
        `(,x ,@(cdr y))
        `(vector-ref ,x ,(cdr y)))) first rest))))
        
    (*parser <InfixParen>)
    (*disj 2)
  done))      

(define <InfixNeg>
    (new
      (*parser (<removeSpaces> <InfixArrayFuncall>))
      
      (*parser (char #\-))
      (*parser (<removeSpaces> <InfixArrayFuncall>))
      (*caten 2)
      (*pack-with (lambda (Minus expr) `(- ,expr)))
      
      (*disj 2)
    done))
  

   

  (define <InfixPow>
    (new                                        
      (*parser (<removeSpaces> <InfixNeg>))
      (*parser (<removeSpaces> <PowerSymbol>))
      (*caten 2)
      (*pack-with cons)
      *star
      
      (*parser (<removeSpaces> <InfixNeg>))       
      (*caten 2)

      (*pack-with (lambda (rest last) 
        (if (null? rest)
          last
          (if (equal? (length rest) 1) `(,(cdar rest) ,(caar rest) ,last)
        `,(fold-left (lambda (x y) `(,(cdr y) ,(car y) ,x)) last (reverse rest))))))
     done)) 

(define <AddSub>
  (new
    (*parser (<remSpacesCommentsinfix> (char #\+)))
    (*parser (<remSpacesCommentsinfix> (char #\-)))
    (*disj 2)
    (*pack char->symbol)    
   done))
   
(define <MultDiv>
  (new
    (*parser (<remSpacesCommentsinfix> (char #\*)))
    (*parser (<remSpacesCommentsinfix> (char #\/)))
    (*disj 2)
    (*pack char->symbol)
   done))  


(define <InfixMultDiv>
    (new
      (*parser (<removeSpaces> <InfixPow>))
      (*parser (<removeSpaces> <MultDiv>))
      (*parser (<removeSpaces> <InfixPow>))
      (*caten 3)
      (*pack-with (lambda (left sign right) `(,sign ,left ,right)))
        
      (*parser (<removeSpaces> <MultDiv>))      
      (*parser (<removeSpaces> <InfixPow>))
      (*caten 2)
      (*pack-with cons)
      *star
      
      (*caten 2)
      (*pack-with (lambda (first rest) 
      (if (null? rest)
      first
    `,(fold-left (lambda (x y) `(,(car y) ,x ,(cdr y))) first rest))))
      
      (*parser (<removeSpaces> <InfixPow>))
      (*disj 2)  
done))
  
  
(define <InfixAddSub>
    (new
      (*parser (<removeSpaces> <InfixMultDiv>))
      (*parser (<removeSpaces> <AddSub>))
      (*parser (<removeSpaces> <InfixMultDiv>))
      (*caten 3)
      (*pack-with (lambda (n1 sign n2) `(,sign ,n1 ,n2)))
        
      (*parser (<removeSpaces> <AddSub>))      
      (*parser (<removeSpaces> <InfixMultDiv>))
      (*caten 2)
      (*pack-with cons)
      *star
      
      (*caten 2)
      (*pack-with (lambda (n1 n2) 
  (if (null? n2)
    n1
  `,(fold-left (lambda (x y) `(,(car y) ,x ,(cdr y))) n1 n2))))
      
      (*parser (<removeSpaces> <InfixMultDiv>))
      (*disj 2)  
done))
     
  

(define ^<InfixExpression>
  (new
    (*parser (<removeSpaces> <InfixAddSub>))
  done))
  
  
(define <InfixSexprEscape>
  (new
    (*parser (<removeSpaces> <InfixPrefixExtensionPrefix>))
    (*delayed (lambda () (<remSpacesCommentsSexpr> <Sexpr>)))
    (*caten 2)
    (*pack-with (lambda (_ sexp) sexp))
  done))
    
(define <InfixExpression> (<remSpacesCommentsinfix> ^<InfixExpression>))
   
   
(define <InfixExtension>
  (new 
    (*parser <InfixPrefixExtensionPrefix>)  
    (*parser <InfixExpression>)
    (*caten 2)
    (*pack-with (lambda (prefix exp) exp))    
done))
     ;######## end of infix ###############################################
 

  (define <ProperList>
  (new
    (*parser (word "("))
    (*parser <sexprWithSpace>) *star
    (*parser (word ")"))
    (*caten 3)
    (*pack-with (lambda(left_br Sexpr right_br) Sexpr ))
    done)) 

     
(define <ImproperList>
  (new
    (*parser (word "("))
    (*parser <sexprWithSpace>) *plus
    (*parser (word ".") )
    (*delayed (lambda () <sexprWithSpace>))
    (*parser (word ")"))
    (*caten 5)
    (*pack-with (lambda(left_br sexpr1 dot sexpr2 right_br ) `(,@sexpr1 . ,sexpr2)))
    done)) 
  
     
(define <Vector>
  
  (new
   (*parser (word "#("))
   (*delayed (lambda () <sexpr>))
   *star
   (*parser (char #\)))   
   (*caten 3)
   (*pack-with (lambda (p1 expr p2)
     `#(,@expr)))
   done))

     
(define <Quoted>
  (new
    (*parser (word "'"))
    (*delayed (lambda () <Sexpr>))
    (*caten 2)
    (*pack-with (lambda(quot Sexpr) `'(,@Sexpr) ))
      done))
  
     
(define <QuasiQuoted>
  (new
    (*parser (word "`"))
    (*delayed (lambda () <Sexpr>))
    (*caten 2)
    (*pack-with (lambda(qq Sexpr)  (list 'quasiquote Sexpr)))
      done))

     
(define <Unquoted>
  (new
    (*parser (word ","))
    (*parser (word "@"))
    *not-followed-by
    (*delayed (lambda () <Sexpr>)) 
    (*caten 2)
    (*pack-with (lambda(unquot Sexpr) (list 'unquote Sexpr) ))
      done))
 
     
(define <UnquoteAndSpliced>
  (new
    (*parser (word ",@"))
    (*delayed (lambda () <Sexpr>)) 
    (*caten 2)
    (*pack-with (lambda(unquot Sexpr) (list 'unquote-splicing Sexpr)) )
      done)) 
     
     
(define <CBNameSyntax1>
  (new
    (*parser (word "@"))
    (*delayed (lambda () <Sexpr>))
    (*caten 2)
    (*pack-with (lambda(shtrudel Sexpr) (list 'cbname Sexpr)  ))
      done)) 
     
     
  (define <CBNameSyntax2>
  (new
    (*parser (word "{"))
    (*delayed (lambda () <Sexpr>))
    (*parser (word "}"))
    (*caten 3)
    (*pack-with (lambda(left_br Sexpr right_br) (list 'cbname Sexpr) ))
    done))  

     
(define <CBName>
  (disj <CBNameSyntax1> <CBNameSyntax2>))


(define <Sexpr> 
  (<remSpacesCommentsSexpr>
    (disj <Boolean>
          <Char>
          <NumberNotFollowedBySymbol>
          <String>
          <Symbol>
          <ProperList>
          <ImproperList>
          <Vector>
          <Quoted>
          <QuasiQuoted>
          <Unquoted>
          <UnquoteAndSpliced>
          <CBName>
          <InfixExtension>)))

(define <remSpacesCommentsSexpr> <remSpacesCommentsSexpr>)
(define <sexpr> <Sexpr>)




