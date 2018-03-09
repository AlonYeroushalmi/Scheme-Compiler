(load "project/pc.scm")
(load "project/qq.scm")
(load "project/pattern-matcher.scm")
(load "project/semantic-analyzer.scm")
(load "project/sexpr-parser.scm")
(load "project/tag-parser.scm")

(define (display-all . vs)
  (for-each display vs))

(define fraction? (lambda(x) (and (number? x) (not (integer? x)))))

(define next-free-ind-in-mem 1)

;------------------------ PRIMITIVE FUNCTIONS  ---------------------

(define primitive-eq
  (lambda (fvars)
    (string-append 
    "jmp LmakeEqClos
     LEqBody: 
      push rbp
      mov rbp,rsp

      mov rcx,qword [rbp + 3*8]
      cmp rcx,3
      jne L_cannot_apply_non_closure
       
      mov rcx,qword [rbp + 4*8]  
      mov rbx,qword [rbp + 5*8] 
      TYPE rcx
      TYPE rbx
      cmp rcx,rbx
      jne L_eq_not_equal

      cmp rcx,T_VOID
      je L_eq_cmp_addr

      cmp rcx,T_NIL
      je L_eq_cmp_addr

      cmp rcx,T_BOOL
      je L_eq_cmp_addr

      cmp rcx,T_STRING
      je L_eq_cmp_addr

      cmp rcx,T_VECTOR
      je L_eq_cmp_addr

      cmp rcx,T_PAIR
      je L_eq_cmp_addr

      cmp rcx,T_CLOSURE
      je L_eq_cmp_addr

      cmp rcx,T_INTEGER
      je L_eq_cmp_single_value

      cmp rcx,T_SYMBOL
      je L_eq_cmp_single_value

      cmp rcx,T_FRACTION
      je L_eq_cmp_fraction

      
      L_eq_cmp_addr:
      mov rcx,qword [rbp + 4*8]  
      mov rbx,qword [rbp + 5*8] 
      cmp rcx,rbx
      jne L_eq_not_equal
      jmp L_eq_equal 
      
      L_eq_cmp_fraction:
      mov rcx,qword [rbp + 4*8]  
      mov rbx,qword [rbp + 5*8]

      NUMERATOR rcx
      NUMERATOR rbx
      cmp rcx,rbx
      jne L_eq_not_equal

      mov rcx,qword [rbp + 4*8]  
      mov rbx,qword [rbp + 5*8]

      DENOMINATOR rcx
      DENOMINATOR rbx
      cmp rcx,rbx
      jne L_eq_not_equal
      jmp L_eq_equal
      
      L_eq_cmp_single_value:
      mov rcx,qword [rbp + 4*8]  
      mov rbx,qword [rbp + 5*8]
      DATA rcx
      DATA rbx
      cmp rcx,rbx
      jne L_eq_not_equal
      jmp L_eq_equal
      
      L_eq_equal:
      mov rax, SOB_TRUE
      jmp L_eq_exit
      
      L_eq_not_equal:
      mov rax,SOB_FALSE
      
      L_eq_exit:
      leave
      ret
     
      LmakeEqClos: 
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LEqBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'eq? fvars) "],rax
      \n\n"

)))

(define primitive-symbol-pred
  (lambda (fvars)
    (string-append 
    "jmp LmakeSymbolPredClos
     LSymbolPredBody: 
      push rbp
      mov rbp,rsp

      mov rcx,qword [rbp + 3*8]
      cmp rcx,2
      jne L_cannot_apply_non_closure
      
      mov rcx,qword [rbp + 4*8]    
      TYPE rcx
      cmp rcx, T_SYMBOL
      jne L_not_symbol_symbol_pred_body
      
      mov rax,SOB_TRUE
      jmp L_symbol_pred_exit;
      
      L_not_symbol_symbol_pred_body:
      mov rax,SOB_FALSE
      
      L_symbol_pred_exit:
      leave
      ret
      
      LmakeSymbolPredClos: 
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LSymbolPredBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'symbol? fvars) "],rax
      \n\n"
)))

(define primitive-string-to-symbol
  (lambda (fvars)
    (string-append 
    "jmp LmakeStringToSymbolClos
     LStringToSymbolBody: 
      push rbp
      mov rbp,rsp

      mov rcx,qword [rbp + 3*8]
      cmp rcx,2
      jne L_cannot_apply_non_closure
      
      mov rcx,qword [rbp + 4*8]    
      TYPE rcx
      cmp rcx, T_STRING
      jne L_cannot_apply_non_closure

      mov r11,qword [rbp + 4*8]  
      STRING_ELEMENTS r11
      mov r8,qword [rbp + 4*8]
      STRING_LENGTH r8 

      mov rbx, qword [L_SYMBOL_TABLE]
      mov rbx,qword [rbx]


      L_string_to_symbol_loop:
      mov rax,rbx
      cmp rax,SOB_NIL
      je L_not_found_string_to_symbol
      mov rax,rbx
      GET_CAR_ADDR rax
      mov rdx,qword [rax]
      mov r9,rdx
      STRING_LENGTH r9
      CDR rbx
      cmp r8,r9
      jne L_string_to_symbol_loop    
      STRING_ELEMENTS rdx
      mov rsi,0

      L_compare_strings:
      cmp rsi,r8
      je l_found_string_to_symbol
      mov cl, byte [r11+rsi]
      cmp cl,byte[rdx+rsi]
      jne L_string_to_symbol_loop
      inc rsi
      jmp L_compare_strings

      L_not_found_string_to_symbol:
      mov rax, qword [rbp + 4*8] 
      mov rbx,rax
      STRING_ELEMENTS rbx
      sub rbx,start_of_data
      mov rcx,rax
      STRING_LENGTH rcx
      mov rdi,8
      call my_malloc
      mov qword [rax],rcx
      shl qword [rax],30
      or qword [rax],rbx
      shl qword [rax],4
      or qword [rax],T_STRING

      mov rcx,qword [L_SYMBOL_TABLE]
      mov rbx,rax
      mov rdi,8
      call my_malloc
      MAKE_MALLOC_LITERAL_PAIR rax,rbx,rcx
      mov qword [L_SYMBOL_TABLE],rax
      mov rax,qword [rax]
      GET_CAR_ADDR rax

      l_found_string_to_symbol:
      MAKE_RT_SYMBOL rax
      leave
      ret

      LmakeStringToSymbolClos: 
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LStringToSymbolBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'string->symbol fvars) "],rax
      \n\n"
      )
))


(define primitive-symbol-to-string
  (lambda (fvars)
    (string-append 
    " jmp LmakeSymbolToStringClos
      LSymbolToStringBody:
      push rbp
      mov rbp,rsp

      mov rcx,qword [rbp + 3*8]
      cmp rcx,2
      jne L_cannot_apply_non_closure

      mov rcx,qword [rbp + 4*8]    
      mov rax,rcx
      TYPE rcx
      cmp rcx, T_SYMBOL
      jne L_cannot_apply_non_closure

      DATA rax 
      mov rcx,rax
      add rcx, start_of_data
      mov rax, qword [rcx]

      leave
      ret

      LmakeSymbolToStringClos:
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LSymbolToStringBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'symbol->string fvars) "],rax
      \n\n"
)))

(define primitive-apply
  (lambda (fvars)
     (string-append
     "jmp L_apply_make_clos
      L_apply_body:     

      push rbp
      mov rbp, rsp
      mov r8,qword [rbp] ; // old rbp
      mov r9,qword [rbp+8] ;// ret addr
      mov rax,qword [rbp+4*8];closure
      mov rdx,rbp
      add rdx,6*8 ;address of nil of apply
      
      mov rbx,rax 
      TYPE rbx
      cmp rbx,T_CLOSURE
      jne L_cannot_apply_non_closure

      mov rcx, qword [rbp+5*8]
      mov rbx, rcx
      TYPE rbx
      cmp rbx,T_PAIR
      je L_apply_body_valid_args

      cmp rbx, T_NIL
      jne L_error_invalid_arguments

      L_apply_body_valid_args:
      mov rsi,0
      L_count_list:
      cmp rcx,SOB_NIL
      je L_count_list_exit

      CDR rcx
      inc rsi
      jmp L_count_list

      L_count_list_exit:
      shl rsi,3
      sub rdx,rsi
      shr rsi,3
      mov rdi,0
      mov rcx,qword [rbp+5*8]

      L_update_frame_loop:
      cmp rdi,rsi
      je L_update_frame_loop_exit
      mov rbx,rcx
      CAR rbx
      mov qword [rdx + 8*rdi],rbx
      CDR rcx
      inc rdi
      jmp L_update_frame_loop
      

      L_update_frame_loop_exit:
      inc rsi
      sub rdx,8
      mov qword [rdx],rsi
      sub rdx,8
      mov rbx,rax
      CLOSURE_ENV rbx
      mov qword [rdx],rbx
      sub rdx,8
      mov qword [rdx],r9
      mov rsp, rdx
      mov rbp,r8
      mov rbx,rax
      TYPE rbx
      cmp rbx,T_CLOSURE
      jne L_cannot_apply_non_closure
      CLOSURE_CODE rax
      jmp rax
       
      L_apply_make_clos:

        mov rdi,8*2
        call my_malloc
        MAKE_LITERAL_CLOSURE rax, rcx, L_apply_body
        mov rax, qword [rax]
        mov qword ["(search-addr 'apply fvars) "],rax
        \n\n"
)))

(define primitive-zero-pred
  (lambda (fvars)
    (string-append 
    "\njmp LmakeZeroPredClos
     LZeroPredBody: 
      
      push rbp
      mov rbp, rsp
      
      mov rcx,qword [rbp + 3*8]
      cmp rcx,2
      jne L_cannot_apply_non_closure

      mov rax,qword [rbp + 4*8]    
      mov rcx,rax
      TYPE rcx
      cmp rcx, T_FRACTION
      je L_not_zero_zero_pred_body

      mov rcx,rax     
      TYPE rcx
      cmp rcx, T_INTEGER
      jne L_cannot_apply_non_closure 
      
      cmp rax,MAKE_LITERAL(T_INTEGER,0)
      jne L_not_zero_zero_pred_body
      
      mov rax,SOB_TRUE
      jmp L_zero_pred_exit
      
      L_not_zero_zero_pred_body:
      mov rax,SOB_FALSE
      
      L_zero_pred_exit:
      leave
      ret
            
      LmakeZeroPredClos: 
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LZeroPredBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'zero? fvars) "],rax
      \n\n"
)))

(define primitive-null-pred
  (lambda (fvars)
    (string-append 
      "jmp LmakeNullPredClos
      LNullPredBody:

      push rbp
      mov rbp, rsp

      mov rcx,qword [rbp + 3*8]
      cmp rcx,2
      jne L_error_lambda_args_count

      ;check if rax is null type
      mov rcx,qword [rbp + 4*8]    
      mov rax,rcx
      TYPE rcx
      cmp rcx, T_NIL
      jne L_not_null_null_pred_body

      mov rax,SOB_TRUE
      jmp L_null_pred_exit

      L_not_null_null_pred_body:
      mov rax,SOB_FALSE

      L_null_pred_exit:
      leave
      ret

      LmakeNullPredClos:
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx, LNullPredBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'null? fvars) "],rax
      \n\n"
)))

(define primitive-boolean-pred
  (lambda (fvars)
    (string-append 
      "jmp LmakeBooleanPredClos
      LBooleanPredBody:

      push rbp
      mov rbp, rsp

      ;arg_count check
      mov rcx,qword [rbp + 3*8]
      cmp rcx,2
      jne L_error_lambda_args_count

      mov rcx,qword [rbp + 4*8]    
      mov rax,rcx
      TYPE rcx
      cmp rcx, T_BOOL
      jne L_not_boolean_boolean_pred_body
      
      mov rax,SOB_TRUE
      jmp L_boolean_pred_exit
      
      L_not_boolean_boolean_pred_body:
      mov rax,SOB_FALSE
      
      L_boolean_pred_exit:
      leave
      ret
      
      LmakeBooleanPredClos:
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx, LBooleanPredBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'boolean? fvars) "],rax
      \n\n"
)))

(define primitive-char-pred
  (lambda (fvars)
    (string-append 
      "jmp LmakeCharPredClos
      LCharPredBody: 
      push rbp
      mov rbp, rsp
      
      mov rcx,qword [rbp + 3*8]
      cmp rcx,2
      jne L_error_lambda_args_count
      
      mov rcx,qword [rbp + 4*8]    
      mov rax,rcx
      TYPE rcx
      cmp rcx, T_CHAR
      jne L_not_char_char_pred_body
      
      mov rax,SOB_TRUE
      jmp L_char_pred_exit
      
      L_not_char_char_pred_body:
      mov rax,SOB_FALSE
      
      L_char_pred_exit:
      leave
      ret
      
      LmakeCharPredClos:
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx, LCharPredBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'char? fvars) "],rax
      \n\n"
)))

(define primitive-integer-pred
  (lambda (fvars)
    (string-append 
      "jmp LmakeIntegerPredClos
      LIntegerPredBody: 
      
      push rbp
      mov rbp, rsp

      mov rcx,qword [rbp + 3*8]
      cmp rcx,2
      jne L_error_lambda_args_count
      
      mov rcx,qword [rbp + 4*8]    
      mov rax,rcx
      TYPE rcx
      cmp rcx, T_INTEGER
      jne L_not_integer_integer_pred_body
      
      mov rax,SOB_TRUE
      jmp L_integer_pred_exit
      
      L_not_integer_integer_pred_body:
      mov rax,SOB_FALSE
      
      L_integer_pred_exit:
      leave
      ret
      
      LmakeIntegerPredClos:
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx, LIntegerPredBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'integer? fvars) "],rax
      \n\n"
)))

(define primitive-pair-pred
  (lambda (fvars)
    (string-append 
      "jmp LmakePairPredClos
      LPairPredBody: 
      push rbp
      mov rbp, rsp
      ;arg_count check
      mov rcx,qword [rbp + 3*8]
      cmp rcx,2
      jne L_error_lambda_args_count
      ;check if rax is pair type
      mov rcx,qword [rbp + 4*8]    
      mov rax,rcx
      TYPE rcx
      cmp rcx, T_PAIR
      jne L_not_pair_pair_pred_body
      mov rax,SOB_TRUE
      jmp L_pair_pred_exit
      L_not_pair_pair_pred_body:
      mov rax,SOB_FALSE
      L_pair_pred_exit:
      leave
      ret
      LmakePairPredClos:
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx, LPairPredBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'pair? fvars) "],rax
      \n\n"
)))

(define primitive-number-pred
  (lambda (fvars)
    (string-append 
      "jmp LmakeNumberPredClos
      LNumberPredBody: 
      push rbp
      mov rbp, rsp
      ;arg_count check
      mov rcx,qword [rbp + 3*8]
      cmp rcx,2
      jne L_error_lambda_args_count
      ;get the type
      mov rcx,qword [rbp + 4*8]    
      mov rax,rcx
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_true_number_pred_body
      cmp rcx, T_FRACTION
      je L_true_number_pred_body
      L_not_number_pred_body:
      mov rax,SOB_FALSE
      jmp L_number_pred_exit
      L_true_number_pred_body:
      mov rax,SOB_TRUE
      L_number_pred_exit:
      leave
      ret
      LmakeNumberPredClos:
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx, LNumberPredBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'number? fvars) "],rax
      \n\n"
)))

(define primitive-rational-pred
  (lambda (fvars)
    (string-append 
      "jmp LmakeRationalPredClos
      LRationalPredBody: 

      push rbp
      mov rbp, rsp

      ;arg_count check
      mov rcx,qword [rbp + 3*8]
      cmp rcx,2
      jne L_error_lambda_args_count

      ;get the type
      mov rcx,qword [rbp + 4*8]    
      mov rax,rcx
      TYPE rcx

      cmp rcx, T_INTEGER
      je L_rational_pred_body_true

      cmp rcx, T_FRACTION
      je L_rational_pred_body_true

      L_rational_pred_body_false:
      mov rax,SOB_FALSE
      jmp L_rational_pred_exit

      L_rational_pred_body_true:
      mov rax,SOB_TRUE

      L_rational_pred_exit:
      leave
      ret

      LmakeRationalPredClos:
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx, LRationalPredBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'rational? fvars) "],rax
      \n\n"
)))

(define primitive-procedure-pred
  (lambda (fvars)
    (string-append 
      "jmp LmakeProcedurePredClos
      LProcedurePredBody: 
      push rbp
      mov rbp, rsp
      ;arg_count check
      mov rcx,qword [rbp + 3*8]
      cmp rcx,2
      jne L_error_lambda_args_count
      ;check if rax is procedure type
      mov rcx,qword [rbp + 4*8]    
      mov rax,rcx
      TYPE rcx
      cmp rcx, T_CLOSURE
      jne L_not_procedure_procedure_pred_body
      mov rax,SOB_TRUE
      jmp L_procedure_pred_exit
      L_not_procedure_procedure_pred_body:
      mov rax,SOB_FALSE
      L_procedure_pred_exit:
      leave
      ret
      LmakeProcedurePredClos:
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx, LProcedurePredBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'procedure? fvars) "],rax
      \n\n"
)))

(define primitive-string-pred
  (lambda (fvars)
    (string-append 
      "jmp LmakeStringPredClos
      LStringPredBody: 
      push rbp
      mov rbp, rsp
      ;arg_count check
      mov rcx,qword [rbp + 3*8]
      cmp rcx,2
      jne L_error_lambda_args_count
      ;check if rax is string type
      mov rcx,qword [rbp + 4*8]    
      mov rax,rcx
      TYPE rcx
      cmp rcx, T_STRING
      jne L_not_string_string_pred_body
      mov rax,SOB_TRUE
      jmp L_string_pred_exit
      L_not_string_string_pred_body:
      mov rax,SOB_FALSE
      L_string_pred_exit:
      leave
      ret
      LmakeStringPredClos:
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx, LStringPredBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'string? fvars) "],rax
      \n\n"
)))

(define primitive-vector-pred
  (lambda (fvars)
    (string-append 
      "jmp LmakeVectorPredClos
      LVectorPredBody: 
      push rbp
      mov rbp, rsp
      ;arg_count check
      mov rcx,qword [rbp + 3*8]
      cmp rcx,2
      jne L_error_lambda_args_count
      ;check if rax is vector type
      mov rcx,qword [rbp + 4*8]    
      mov rax,rcx
      TYPE rcx
      cmp rcx, T_VECTOR
      jne L_not_vector_vector_pred_body
      mov rax,SOB_TRUE
      jmp L_vector_pred_exit
      L_not_vector_vector_pred_body:
      mov rax,SOB_FALSE
      L_vector_pred_exit:
      leave
      ret
      LmakeVectorPredClos:
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx, LVectorPredBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'vector? fvars) "],rax
      \n\n"
)))


(define primitive-cdr
  (lambda(fvars)
    (string-append
      "\njmp LmakeCdrClos
      LCdrClosBody:

      push rbp
      mov rbp, rsp
      
      mov rcx, qword [rbp + 3*8];     number of arguments
      cmp rcx, 2
      jne L_error_lambda_args_count

      mov rax, qword [rbp + 4*8];     get the first argument(the list in this case)
      mov rcx, rax;                   save the value of rax
      TYPE rcx;                       get the type of the argument
      cmp rcx, T_PAIR;                check if the type is pair
      jne L_error_invalid_arguments

      CDR rax

      L_cdr_exit:
      leave
      ret

      LmakeCdrClos:
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LCdrClosBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'cdr fvars) "],rax
      \n\n"
)))

(define primitive-car
  (lambda(fvars)
    (string-append
      "\njmp LmakeCarClos
      LCarClosBody:
      push rbp
      mov rbp, rsp
      
      mov rcx, qword [rbp + 3*8];     number of arguments
      cmp rcx, 2
      jne L_error_lambda_args_count
      
      mov rax, qword [rbp + 4*8];     get the first argument(the list in this case)
      mov rbx, rax;                   save the value of rax
      TYPE rbx;                       get the type of the argument
      cmp rbx, T_PAIR;                check if the type is pair
      jne L_error_invalid_arguments
      
      CAR rax;
      
      L_car_exit:
      leave
      ret
      
      LmakeCarClos:
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rdx, LCarClosBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'car fvars) "],rax
      \n\n"
)))

(define primitive-set-car
  (lambda(fvars)
    (string-append
      "\njmp LmakeSetCarClos
      LSetCarClosBody:
      
      push rbp
      mov rbp, rsp
      
      ;check number of arguments
      mov rcx, qword [rbp + 3*8];     number of arguments
      cmp rcx, 3
      jne L_error_lambda_args_count
      
      ;check type of the argument
      mov r8, qword [rbp + 4*8];     get the first argument
      mov rcx, r8;                   save the value of rax
      TYPE rcx;                       get the type of the argument
      cmp rcx, T_PAIR;                check if the type is pair
      jne L_error_invalid_arguments

      ;get second argument to rdx
      mov rdx, qword [rbp + 5*8];     rdx holds data structure. car will be changed to DATA r8
      
      GET_CAR_ADDR r8
      mov qword [r8],rdx
      mov rax,SOB_VOID
      
      L_set_car_exit:
      leave
      ret
      
      LmakeSetCarClos:
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LSetCarClosBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'set-car! fvars) "],rax
      \n\n"
)))

(define primitive-set-cdr
  (lambda(fvars)
    (string-append
      "\njmp LmakeSetCdrClos
      LSetCdrClosBody:
      
      push rbp
      mov rbp, rsp
      
      ;check number of arguments

    ;check number of arguments
      mov rcx, qword [rbp + 3*8];     number of arguments
      cmp rcx, 3
      jne L_error_lambda_args_count
      
      ;check type of the argument
      mov r8, qword [rbp + 4*8];     get the first argument
      mov rcx, r8;                   save the value of rax
      TYPE rcx;                       get the type of the argument
      cmp rcx, T_PAIR;                check if the type is pair
      jne L_error_invalid_arguments

      ;get second argument to rdx
      mov rdx, qword [rbp + 5*8];     rdx holds data structure. car will be changed to DATA r8
      
      GET_CDR_ADDR r8
      mov qword [r8],rdx
      mov rax,SOB_VOID
      
      L_set_cdr_exit:
      leave
      ret
      
      LmakeSetCdrClos:
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LSetCdrClosBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'set-cdr! fvars) "],rax
      \n\n"
)))
      
(define primitive-cons
  (lambda(fvars)
    (string-append
    "\njmp LmakeConsClos
    LConsClosBody:

    push rbp
    mov rbp, rsp

    ;check number of arguments
    mov rcx, qword [rbp + 3*8];     number of arguments
    cmp rcx, 3
    jne L_error_lambda_args_count

    mov rdx, qword [rbp + 4*8];     rdx holds first argument
    mov r8,  qword [rbp + 5*8];     r8 holds second argument
    
    ;create new pair
    mov rdi, 16
    call my_malloc
    test rax, rax
    mov qword[rax], rdx
    mov qword[rax+8],r8
    mov rsi,rax
    add rsi,8
    mov r8, rsi
    MAKE_PAIR rax, r8
    
    L_primitive_cons_end_of_loop:
    leave
    ret
    
    LmakeConsClos:
    mov rdi,8*2
    call my_malloc
    MAKE_LITERAL_CLOSURE rax, rcx,LConsClosBody\n\n
    mov rax, qword [rax]
      mov qword ["(search-addr 'cons fvars) "],rax
      \n\n"
)))



(define primitive-greater-than
  (lambda (fvars)
    (string-append 
      "\njmp LmakeGreaterThanClos
      LGreaterThanBody:
      
      push rbp
      mov rbp, rsp
      
      mov r12,MAKE_LITERAL(T_INTEGER,INFINITY);  create accumulator r12
      mov r11 ,qword [rbp + 3*8];         number of arguments
      mov r10, 4;               r10 holds current arg offset

      L_greater_than_loop:
      mov rcx, r11
      cmp rcx, 2
      jb L_greater_than_exit

      L_greater_than_acc_type:
      ;check accumulator argument type
      mov rax, r12; use accumulator r12
      mov rcx, rax
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_greater_than_first_int_check_sec
      
      L_greater_than_first_frac_check_sec:
      mov rbx, qword [rbp + r10*8]
      mov r12, rbx;   update accumulator
      mov rcx, rbx
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_greater_than_first_frac_sec_int
      
      ;-----First Frac, Second Frac-----
      L_greater_than_first_frac_sec_frac:
      mov rcx, rax;       we will put in rcx first_numerator
      NUMERATOR rcx
      DATA rcx
      mov rdx, rax;       we will put in rdx first_denominator
      DENOMINATOR rdx
      DATA rdx
      
      mov rsi, rbx;       we will put in rsi second_numerator
      NUMERATOR rsi
      DATA rsi
      mov rdi, rbx;       we will put in rdi second_denominator
      DENOMINATOR rdi
      DATA rdi
      MULTIPLY rcx, rdi;  now rcx holds first_numerator*second_denominator
      MULTIPLY rsi, rdx;   now rsi holds second_numerator*first_denominator
      jmp L_greater_than_compare
      
      ;-----First Int, Check Second-----
      L_greater_than_first_int_check_sec:
      mov rcx,qword [rbp + r10*8]
      mov r12, rcx;   update accumulator    
      mov rbx, rcx
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_greater_than_first_int_sec_int
      
      ;-----First Int, Sec Frac-----
      L_greater_than_first_int_sec_frac:
      mov rsi, rbx;       we will put in rsi second_numerator
      NUMERATOR rsi
      DATA rsi
      mov rcx, rbx;       we will put in rcx second_denominator
      DENOMINATOR rcx
      DATA rcx
      DATA rax
      mov r15,rax
      MULTIPLY rcx, r15
      jmp L_greater_than_compare
      
      ;-----First Frac, Sec Int-----
      L_greater_than_first_frac_sec_int:
      mov rcx, rax;       we will put in rcx first_numerator
      NUMERATOR rcx
      DATA rcx
      mov rsi, rax;       we will put in rsi first_denominator
      DENOMINATOR rsi
      DATA rsi
      DATA rbx
      MULTIPLY rsi, rbx
      jmp L_greater_than_compare
      
      ;-----First Int, Sec Int-----
      L_greater_than_first_int_sec_int:
      mov rcx,rax
      mov rsi,rbx
      DATA rcx
      DATA rsi
      
      L_greater_than_compare:
      cmp rcx,rsi
      jle L_greater_than_not_greater
      
      L_greater_than_greater:
      mov rax, SOB_TRUE

      L_greater_than_update_vars:
      inc r10;  increase offset
      dec r11;  decrease number of argument left
      jmp L_greater_than_loop
      
      L_greater_than_not_greater:
      mov rax, SOB_FALSE
      jmp L_greater_than_exit
     
      L_greater_than_exit:
      leave
      ret
      
      LmakeGreaterThanClos:
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LGreaterThanBody
      mov rax, qword [rax]
      mov qword ["(search-addr '> fvars) "],rax
      \n\n"
)))


(define primitive-variadic-equal
  (lambda (fvars)
    (string-append 
      "\njmp LmakeVariadicEqualClos
      LVariadicEqualBody:
      
      push rbp
      mov rbp, rsp
      
      mov r10, 4;                         r10 holds current arg offset
      mov r11 ,qword [rbp + 3*8];         number of arguments
      mov r12, qword [rbp + 4*8];         create accumulator r12

      L_variadic_equal_loop:
      mov rcx, r11
      cmp rcx, 2
      jb L_variadic_equal_exit

      L_variadic_equal_acc_type:
      ;check accumulator argument type
      mov rax, r12; use accumulator r12
      mov rcx, rax
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_variadic_equal_first_int_check_sec
      
      L_variadic_equal_first_frac_check_sec:
      mov rbx, qword [rbp + r10*8]
      mov r12, rbx;                       update accumulator
      mov rcx, rbx
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_variadic_equal_first_frac_sec_int
      
      ;-----First Frac, Second Frac-----
      L_variadic_equal_first_frac_sec_frac:
      mov rcx, rax;                       we will put in rcx first_numerator
      NUMERATOR rcx
      DATA rcx
      mov rdx, rax;                       we will put in rdx first_denominator
      DENOMINATOR rdx
      DATA rdx
      
      mov rsi, rbx;                       we will put in rsi second_numerator
      NUMERATOR rsi
      DATA rsi
      mov rdi, rbx;                       we will put in rdi second_denominator
      DENOMINATOR rdi
      DATA rdi
      MULTIPLY rcx, rdi;                  now rcx holds first_numerator*second_denominator
      MULTIPLY rsi, rdx;                  now rsi holds second_numerator*first_denominator
      jmp L_variadic_equal_compare
      
      ;-----First Int, Check Second-----
      L_variadic_equal_first_int_check_sec:
      mov rcx,qword [rbp + r10*8]
      mov r12, rcx;   update accumulator    
      mov rbx, rcx
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_variadic_equal_first_int_sec_int
      
      ;-----First Int, Sec Frac-----
      L_variadic_equal_first_int_sec_frac:
      mov rsi, rbx;       we will put in rsi second_numerator
      NUMERATOR rsi
      DATA rsi
      mov rcx, rbx;       we will put in rcx second_denominator
      DENOMINATOR rcx
      DATA rcx
      DATA rax
      mov r15,rax
      MULTIPLY rcx, r15
      jmp L_variadic_equal_compare
      
      ;-----First Frac, Sec Int-----
      L_variadic_equal_first_frac_sec_int:
      mov rcx, rax;       we will put in rcx first_numerator
      NUMERATOR rcx
      DATA rcx
      mov rsi, rax;       we will put in rsi first_denominator
      DENOMINATOR rsi
      DATA rsi
      DATA rbx
      MULTIPLY rsi, rbx
      jmp L_variadic_equal_compare
      
      ;-----First Int, Sec Int-----
      L_variadic_equal_first_int_sec_int:
      mov rcx,rax
      mov rsi,rbx
      DATA rcx
      DATA rsi
      
      L_variadic_equal_compare:
      cmp rcx,rsi
      jne L_variadic_equal_not_equal
      
      L_variadic_equal_equal:
      mov rax, SOB_TRUE

      L_variadic_equal_update_vars:
      inc r10;  increase offset
      dec r11;  decrease number of argument left
      jmp L_variadic_equal_loop
      
      L_variadic_equal_not_equal:
      mov rax, SOB_FALSE
      jmp L_variadic_equal_exit
     
      L_variadic_equal_exit:
      leave
      ret
      
      LmakeVariadicEqualClos:
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LVariadicEqualBody
      mov rax, qword [rax]
      mov qword ["(search-addr '= fvars) "],rax
      \n\n"
)))

(define primitive-smaller-than
  (lambda (fvars)
    (string-append 
      "\njmp LmakeSmallerThanClos
      LSmallerThanBody:
      
      push rbp
      mov rbp, rsp
      
      mov r12,MAKE_LITERAL(T_INTEGER,-INFINITY);  create accumulator r12
      mov r11 ,qword [rbp + 3*8];         number of arguments
      mov r10, 4;               r10 holds current arg offset

      L_smaller_than_loop:
      mov rcx, r11
      cmp rcx, 2
      jb L_smaller_than_exit

      L_smaller_than_acc_type:
      ;check accumulator argument type
      mov rax, r12; use accumulator r12
      mov rcx, rax
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_smaller_than_first_int_check_sec
      
      L_smaller_than_first_frac_check_sec:
      mov rbx, qword [rbp + r10*8]
      mov r12, rbx;   update accumulator
      mov rcx, rbx
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_smaller_than_first_frac_sec_int
      
      ;-----First Frac, Second Frac-----
      L_smaller_than_first_frac_sec_frac:
      mov rcx, rax;       we will put in rcx first_numerator
      NUMERATOR rcx
      DATA rcx
      mov rdx, rax;       we will put in rdx first_denominator
      DENOMINATOR rdx
      DATA rdx
      
      mov rsi, rbx;       we will put in rsi second_numerator
      NUMERATOR rsi
      DATA rsi
      mov rdi, rbx;       we will put in rdi second_denominator
      DENOMINATOR rdi
      DATA rdi
      MULTIPLY rcx, rdi;  now rcx holds first_numerator*second_denominator
      MULTIPLY rsi, rdx;   now rsi holds second_numerator*first_denominator
      jmp L_smaller_than_compare
      
      ;-----First Int, Check Second-----
      L_smaller_than_first_int_check_sec:
      mov rcx,qword [rbp + r10*8]
      mov r12, rcx;   update accumulator    
      mov rbx, rcx
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_smaller_than_first_int_sec_int
      
      ;-----First Int, Sec Frac-----
      L_smaller_than_first_int_sec_frac:
      mov rsi, rbx;       we will put in rsi second_numerator
      NUMERATOR rsi
      DATA rsi
      mov rcx, rbx;       we will put in rcx second_denominator
      DENOMINATOR rcx
      DATA rcx
      DATA rax
      mov r15,rax
      MULTIPLY rcx, r15
      jmp L_smaller_than_compare
      
      ;-----First Frac, Sec Int-----
      L_smaller_than_first_frac_sec_int:
      mov rcx, rax;       we will put in rcx first_numerator
      NUMERATOR rcx
      DATA rcx
      mov rsi, rax;       we will put in rsi first_denominator
      DENOMINATOR rsi
      DATA rsi
      DATA rbx
      MULTIPLY rsi, rbx
      jmp L_smaller_than_compare
      
      ;-----First Int, Sec Int-----
      L_smaller_than_first_int_sec_int:
      mov rcx,rax
      mov rsi,rbx
      DATA rcx
      DATA rsi
      
      L_smaller_than_compare:
      cmp rcx, rsi
      jge L_smaller_than_not_smaller
      
      L_smaller_than_smaller:
      mov rax, SOB_TRUE

      L_smaller_than_update_vars:
      inc r10;  increase offset
      dec r11;  decrease number of argument left
      jmp L_smaller_than_loop
      
      L_smaller_than_not_smaller:
      mov rax, SOB_FALSE
      jmp L_smaller_than_exit
     
      L_smaller_than_exit:
      leave
      ret
      
      LmakeSmallerThanClos:
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LSmallerThanBody
      mov rax, qword [rax]
      mov qword ["(search-addr '< fvars) "],rax
      \n\n"
)))

            
(define primitive-numerator
  (lambda(fvars)
    (string-append
      "\njmp LmakeNumeratorClos
      LNumeratorClosBody:
      push rbp
      mov rbp, rsp
      
      ;check number of arguments
      mov rcx, qword [rbp + 3*8];     number of arguments
      cmp rcx, 2
      jne L_error_lambda_args_count
      
      ;check type of the argument
      mov rax, qword [rbp + 4*8];     get the first argument(the list in this case)
      mov rbx, rax;                   save the value of rax
      TYPE rbx;                       get the type of the argument
      cmp rbx, T_INTEGER;             check if the type is integer
      je L_numerator_exit
      LNumeratorClosBody_Frac:
      NUMERATOR rax
      
      L_numerator_exit:
      leave
      ret
      
      LmakeNumeratorClos:
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LNumeratorClosBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'numerator fvars) "],rax
      \n\n"
)))

(define primitive-denominator
  (lambda(fvars)
    (string-append
      "\njmp LmakeDenominatorClos
      LDenominatorClosBody:

      push rbp
      mov rbp, rsp

      ;check number of arguments
      mov rcx, qword [rbp + 3*8];     number of arguments
      cmp rcx, 2
      jne L_error_lambda_args_count
      
      ;check type of the argument
      mov rax, qword [rbp + 4*8];     get the first argument(the list in this case)
      mov rbx, rax;                   save the value of rax
      TYPE rbx;                       get the type of the argument
      cmp rbx, T_INTEGER;             check if the type is integer
      je L_denominator_int
      
      L_denominator_frac:
      DENOMINATOR rax
      jmp L_denominator_exit
      
      L_denominator_int:
      mov rax, 1
      MAKE_INT rax
      
      L_denominator_exit:
      leave
      ret
      
      LmakeDenominatorClos:
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LDenominatorClosBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'denominator fvars) "],rax
      \n\n")))

(define primitive-char-to-integer
  (lambda (fvars)
    (string-append 
    "\nJMP LmakeCharToIntegerClos;
     LcharToIntegerBody: 
     push rbp
     mov rbp, rsp
      ;check number of arguments
      mov rcx, qword [rbp + 3*8]
      cmp rcx, 2
      jne L_error_lambda_args_count
      ;get first argument to rax
      mov rax, qword [rbp + 4*8];     
      mov rcx, rax;                   save the value of rax
      TYPE rcx;                       get the type of the argument
      cmp rcx, T_CHAR;                check if the type is integer
      jne L_cannot_apply_non_closure
      
      L_char_to_int_exit:
      DATA rax
      MAKE_INT rax
      leave
      ret
      LmakeCharToIntegerClos:
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx,LcharToIntegerBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'char->integer fvars) "],rax
      \n\n")))

(define primitive-integer-to-char
  (lambda (fvars)
    (string-append 
    "\nJMP LmakeIntegerToCharClos;
     LintegerToCharBody: 
     push rbp
     mov rbp, rsp
      ;check number of arguments
      mov rcx, qword [rbp + 3*8]
      cmp rcx, 2
      jne L_error_lambda_args_count
      ;get first argument to rax
      mov rax, qword [rbp + 4*8];     
      mov rcx, rax;                   save the value of rax
      TYPE rcx;                       get the type of the argument
      cmp rcx, T_INTEGER;                check if the type is integer
      jne L_cannot_apply_non_closure
      
      L_int_to_char_exit:
      DATA rax
      MAKE_CHAR rax
      leave
      ret
      LmakeIntegerToCharClos:
      mov rdi,8*2
      call my_malloc 
      
      MAKE_LITERAL_CLOSURE rax, rcx,LintegerToCharBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'integer->char fvars) "],rax
      \n\n")))

 (define primitive-vector-set
  (lambda (fvars)
    (string-append 
    "jmp LmakeVectorSetClos
     LVectorSetBody:     
     push rbp
     mov rbp, rsp
      
      ;check number of arguments
      mov rcx, qword [rbp + 3*8]
      cmp rcx, 4
      jne L_error_lambda_args_count
      
      ;get first argument to rax 
      mov rbx, qword [rbp + 4*8]
      mov rax,rbx
      TYPE rax;                      
      cmp rax, T_VECTOR;                
      jne L_cannot_apply_non_closure
      ;get second argument to rbx
      mov rcx, qword [rbp + 5*8]
      mov rax,rcx
      TYPE rax;                      
      cmp rax, T_INTEGER;                
      jne L_cannot_apply_non_closure

      mov rdx, qword [rbp + 6*8]
      mov rdi,8
      call my_malloc
      mov qword [rax],rdx
      VECTOR_ELEMENTS rbx
      DATA rcx
      mov qword [rbx+8*rcx],rax
      mov rax,SOB_VOID

      leave
      ret
      
      LmakeVectorSetClos: 
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx,LVectorSetBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'vector-set!  fvars) "],rax
      \n\n" 
)))     

 (define primitive-vector-ref
  (lambda (fvars)
    (string-append 
    "jmp LmakeVectorRefClos
     LVectorRefBody: 
      push rbp
      mov rbp, rsp
      
      ;check number of arguments
      mov rcx, qword [rbp + 3*8]
      cmp rcx, 3
      jne L_error_lambda_args_count
      
      ;get string to rdx
      mov rdx, qword [rbp + 4*8];     
      mov rcx, rdx;                       save the value of rdx
      TYPE rcx;                           get the type of the argument
      cmp rcx, T_VECTOR;                  check if the type is string
      jne L_error_lambda_args_count
      
      ;get position of char to rbx
      mov rbx, qword [rbp + 5*8];     
      mov rcx, rbx;                       save the value of rbx
      TYPE rcx;                           get the type of the argument
      cmp rcx, T_INTEGER;                 check if the type is string
      jne L_cannot_apply_non_closure

      VECTOR_ELEMENTS rdx
      DATA rbx
      mov rax,qword [rdx + 8*rbx]
      mov rax,qword [rax]
      
      leave
      ret
      
      LmakeVectorRefClos: 
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx,LVectorRefBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'vector-ref  fvars) "],rax
      \n\n" 
)))     

(define primitive-make-vector
  (lambda (fvars)
    (string-append 
    "jmp LmakeMakeVectorClos
     LmakeVectorBody: 

      push rbp
      mov rbp, rsp
      
      ;check number of arguments
      mov rcx, qword [rbp + 3*8]
      cmp rcx, 3
      jne L_make_vector_not_two_args
      
      ;get first argument to rax
      mov rax, qword [rbp + 4*8];     
      mov rcx, rax;                   save the value of rax
      TYPE rcx;                       get the type of the argument
      cmp rcx, T_INTEGER;                check if the type is integer
      jne L_cannot_apply_non_closure
      ;get second argument to rbx

      mov rdx,qword [rbp + 5*8];
      mov rdi,8
      call my_malloc
      mov qword [rax],rdx
      mov rdx,rax
      jmp L_make_vector_create_vector

      L_make_vector_not_two_args: 
      mov rcx, qword [rbp + 3*8]
      cmp rcx, 2
      jne L_cannot_apply_non_closure
      mov rdx,0
      MAKE_INT rdx
      mov rdi,8
      call my_malloc
      mov qword [rax],rdx
      mov rdx,rax

      L_make_vector_create_vector:
      mov rsi, qword [rbp + 4*8]
      DATA rsi
      mov rdi,rsi
      shl rdi,3
      call my_malloc
      mov rdi,0

      
      L_make_vector_loop:
      cmp rsi,rdi
      je L_make_vector_loop_exit
      mov qword [rax+rdi*8],rdx
      inc rdi
      jmp L_make_vector_loop


      
      L_make_vector_loop_exit:
      mov rcx,rax
      sub rcx,start_of_data
      mov rdi,8
      call my_malloc
      mov qword [rax],rsi
      shl qword [rax],30
      or qword [rax],rcx
      shl qword [rax],4
      or qword [rax],T_VECTOR

      mov rax,qword [rax]
      leave
      ret
      
  
      
      LmakeMakeVectorClos: 
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx,LmakeVectorBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'make-vector  fvars) "],rax
      \n\n" 
)))

(define primitive-vector-length
  (lambda (fvars)
    (string-append 
    "jmp LmakeVectorLengthClos
     LvectorLengthBody: 
      push rbp
      mov rbp, rsp


      mov rcx, qword [rbp + 3*8]
      cmp rcx, 2
      jne L_cannot_apply_non_closure
      
      mov rbx, qword [rbp + 4*8]
      mov rax,rbx
      TYPE rax                     
      cmp rax, T_VECTOR
      mov rsi,0    
      jne L_cannot_apply_non_closure

      
      VECTOR_LENGTH rbx
      MAKE_INT rbx
      mov rax,rbx
      
      leave
      ret
      
      LmakeVectorLengthClos: 
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx,LvectorLengthBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'vector-length  fvars) "],rax
      \n\n" 
)))

(define primitive-list-to-vector
  (lambda (fvars)
    (string-append 
    "jmp LmakeListToVectorClos
     LlistToVectorBody:
     push rbp
      mov rbp, rsp


      mov rcx, qword [rbp + 3*8]
      cmp rcx, 2
      jne L_cannot_apply_non_closure

      ;get first argument to rax 
      mov rbx, qword [rbp + 4*8]
      mov rax,rbx
      TYPE rax;                      
      cmp rax, T_PAIR
      mov rsi,0               
      je L_list_to_vector_count_loop

      end:
      cmp rax, SOB_NIL
      mov rsi,0
      mov rdx,SOB_NIL
      je L_list_to_vector_loop_exit_exit

      


      L_list_to_vector_count_loop:
      cmp rbx,SOB_NIL
      je L_list_to_vector_malloc
      CDR rbx
      inc rsi
      jmp L_list_to_vector_count_loop

      L_list_to_vector_malloc:
      mov rdi,rsi
      shl rdi,3
      call my_malloc
      mov r9,0
      mov rbx, qword [rbp + 4*8]
 

      L_list_to_vector_loop:
      cmp rbx,SOB_NIL
      je L_list_to_vector_loop_exit
      mov rcx,rbx
      GET_CAR_ADDR rcx
      mov qword [rax+8*r9],rcx
      CDR rbx
      inc r9
      jmp L_list_to_vector_loop

      L_list_to_vector_loop_exit:
      mov rdx,rax
      sub rdx,start_of_data


      L_list_to_vector_loop_exit_exit:
      mov rdi,8
      call my_malloc
      mov qword [rax],rsi
      shl qword [rax],30
      or qword [rax],rdx
      shl qword [rax],4
      or qword [rax],T_VECTOR

      mov rax, qword [rax]
      leave
      ret
      
      LmakeListToVectorClos: 
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx,LlistToVectorBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'asaf-lior-list-to-vector fvars) "],rax
      \n\n"
)))

(define primitive-string-set
  (lambda (fvars)
    (string-append 
    "jmp LmakeStringSetClos
     LStringSetBody: 
     push rbp
     mov rbp, rsp
      
      ;check number of arguments
      mov rcx, qword [rbp + 3*8]
      cmp rcx, 4
      jne L_cannot_apply_non_closure
      
      ;get first argument to rax 
      mov rbx, qword [rbp + 4*8]
      mov rax,rbx
      TYPE rax;                      
      cmp rax, T_STRING;                
      jne L_cannot_apply_non_closure
      ;get second argument to rbx
      mov rcx, qword [rbp + 5*8]
      mov rax,rcx
      TYPE rax;                      
      cmp rax, T_INTEGER;                
      jne L_cannot_apply_non_closure

      mov rdx, qword [rbp + 6*8]
      mov rax,rdx
      TYPE rax;                      
      cmp rax, T_CHAR;                
      jne L_cannot_apply_non_closure

      STRING_ELEMENTS rbx
      DATA rcx
      DATA rdx
      mov byte [rbx+rcx],dl
      mov rax,SOB_VOID

      leave
      ret
      
       
      LmakeStringSetClos:
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx,LStringSetBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'string-set! fvars) "],rax
      \n\n"
)))

(define primitive-make-string
  (lambda (fvars)
    (string-append 
    "jmp LmakeMakeStringClos
     LMakeStringBody: 
     push rbp
     mov rbp, rsp
      
      ;check number of arguments
      mov rcx, qword [rbp + 3*8]
      cmp rcx, 3
      jne L_make_string_not_two_args
      
      ;get first argument to rax
      mov rax, qword [rbp + 4*8];     
      mov rcx, rax;                   save the value of rax
      TYPE rcx;                       get the type of the argument
      cmp rcx, T_INTEGER;                check if the type is integer
      jne L_cannot_apply_non_closure
      ;get second argument to rbx
      mov rcx, qword [rbp + 5*8];     
      TYPE rcx;                       get the type of the argument
      cmp rcx, T_CHAR;                check if the type is char
      jne L_cannot_apply_non_closure
      mov rdx,qword [rbp + 5*8];
      DATA rdx
      jmp L_make_string_create_string

      L_make_string_not_two_args: 
      mov rcx, qword [rbp + 3*8]
      cmp rcx, 2
      jne L_cannot_apply_non_closure
      mov rdx,0

      L_make_string_create_string:
      mov rsi, qword [rbp + 4*8]
      DATA rsi
      mov rdi,rsi
      call my_malloc
      mov rdi,0

      
      L_make_string_loop:
      cmp rsi,rdi
      je L_make_string_exit
      mov byte [rax+rdi],dl
      inc rdi
      jmp L_make_string_loop


      
      L_make_string_exit:
      mov rcx,rax
      sub rcx,start_of_data
      mov rdi,8
      call my_malloc
      mov qword [rax],rsi
      shl qword [rax],30
      or qword [rax],rcx
      shl qword [rax],4
      or qword [rax],T_STRING

      mov rax,qword [rax]
      leave
      ret

      LmakeMakeStringClos:
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx,LMakeStringBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'make-string fvars) "],rax
      \n\n"
      )))


(define primitive-string-length
  (lambda (fvars)
    (string-append 
    "\nJMP LmakeStringLengthClos;
     LstringlengthBody: 
     push rbp
     mov rbp, rsp
      
      ;check number of arguments
      mov rcx, qword [rbp + 3*8]
      cmp rcx, 2
      jne L_error_lambda_args_count
      
      ;get first argument to rax
      mov rax, qword [rbp + 4*8];     
      mov rcx, rax;                   save the value of rax
      TYPE rcx;                       get the type of the argument
      cmp rcx, T_STRING;                check if the type is string
      jne L_cannot_apply_non_closure
      
      STRING_LENGTH rax
      MAKE_INT rax
      
      L_tring_length_exit:
      leave
      ret
      
      LmakeStringLengthClos:
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx,LstringlengthBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'string-length fvars) "],rax
      \n\n")))

(define primitive-string-ref
  (lambda (fvars)
    (string-append 
    "\nJMP LmakeStringRefClos;
     LstringRefBody: 
     push rbp
     mov rbp, rsp
      
      ;check number of arguments
      mov rcx, qword [rbp + 3*8]
      cmp rcx, 3
      jne L_error_lambda_args_count
      
      ;get string to rdx
      mov rdx, qword [rbp + 4*8];     
      mov rcx, rdx;                       save the value of rdx
      TYPE rcx;                           get the type of the argument
      cmp rcx, T_STRING;                  check if the type is string
      jne L_cannot_apply_non_closure
      
      ;get position of char to rbx
      mov rbx, qword [rbp + 5*8];     
      mov rcx, rbx;                       save the value of rbx
      TYPE rcx;                           get the type of the argument
      cmp rcx, T_INTEGER;                 check if the type is string
      jne L_cannot_apply_non_closure
      
      xor rsi,rsi
      DATA rbx
      STRING_REF sil,rdx,rbx; now sil contains char!
      mov rax, rsi
      MAKE_CHAR rax
      
      L_string_ref_exit:
      leave
      ret
      LmakeStringRefClos:
      mov rdi,8*2
      call my_malloc 
      MAKE_LITERAL_CLOSURE rax, rcx,LstringRefBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'string-ref fvars) "],rax
      \n\n")))



(define primitive-plus
  (lambda(fvars)
    (string-append
      "\njmp LmakePlusClos
      LPlusBody:
      push rbp
      mov rbp, rsp
      
      mov r12, MAKE_LITERAL(T_INTEGER,0);  create accumulator r12
      mov r11 ,qword [rbp + 3*8];         number of arguments
      mov r10, 4;               r10 holds current arg offset

      L_plus_start:
      mov rcx, r11
      cmp rcx, 1
      jne L_plus_loop

      L_plus_no_args:
      mov rax, r12
      jmp L_plus_exit

      L_plus_loop:
      mov rcx, r11
      cmp rcx, 2
      jl L_plus_exit
     
      L_plus_acc_type:
      ;check accumulator argument type
      mov rax, r12; use accumulator r12
      mov rcx, rax
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_plus_first_int_check_sec
      
      L_plus_first_frac_check_sec:
      mov rbx, qword [rbp + r10*8]; we will put in rbx second number
      mov rcx, rbx
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_plus_first_frac_sec_int; 
      
      ;--------First Frac, Second Frac ------
      L_plus_first_frac_sec_frac:
      mov rcx, rax;       we will put in rcx first_numerator
      NUMERATOR rcx
      DATA rcx
      mov rdx, rax;       we will put in rdx first_denominator
      DENOMINATOR rdx
      DATA rdx
      
      mov rsi, rbx;       we will put in rsi second_numerator
      NUMERATOR rsi
      DATA rsi
      mov rdi, rbx;       we will put in rdi second_denominator
      DENOMINATOR rdi
      DATA rdi
      mov r8, rdx;        backup first denominator

      MULTIPLY rdx, rdi;  now rdx holds first denominator * second denominator
      MULTIPLY rcx, rdi;  now rcx holds first numerator * second denominator
      MULTIPLY rsi, r8;   now rsi holds second numerator * first_denominator
      add rcx,rsi
      
      L_plus_plus_create_fraction:
      ;rcx holds numerator DATA
      ;rdx holds denominator DATA

      mov r9, rcx; rcx holds numerator DATA
      mov r8, rdx; r8  holds denominator DATA
      call reduce_fraction
      jmp L_plus_create_new_fraction

      ;------ First Frac, Sec Int ----------
      L_plus_first_frac_sec_int:
      ;rax holds fraction
      ;rbx holds integer

      mov rsi, rax; we will put in rsi first numerator
      NUMERATOR rsi
      DATA rsi
      mov rdi, rax;  we will put in rdi first denominator
      DENOMINATOR rdi
      DATA rdi

      DATA rbx
      mov r8,rbx
      MULTIPLY r8, rdi;  now r8 holds integer*second_denominator
      mov rbx,r8

      add rbx, rsi

      ;rbx holds numerator
      ;rdi holds denominator
      mov rdx, rbx; rdx holds numerator DATA
      mov r9, rdx
      mov r8,  rdi; r8  holds denominator DATA
      call reduce_fraction
      jmp L_plus_create_new_fraction

      L_plus_first_int_check_sec:
      mov rbx, qword [rbp + r10*8]
      mov rdx, rbx
      TYPE rdx
      cmp rdx, T_INTEGER
      je L_plus_first_int_sec_int

      ;------ First Int, Sec Frac ----------
      L_plus_first_int_sec_frac:
      ;rax contains first integer
      ;rbx contains second fraction
      mov rsi, rbx; we will put in rsi second_numerator
      NUMERATOR rsi
      DATA rsi
      mov rdi, rbx;           we will put in rdi second_denominator
      DENOMINATOR rdi
      DATA rdi
      DATA rax
      mov r8,rax
      MULTIPLY r8, rdi;       now rax holds first_numerator*second_denominator
      mov rax,r8
      add rax, rsi

      ;rax holds numerator
      ;rdi holds denominator
      mov r8,  rdi;          r8  holds denominator DATA
      mov rdx, rax;          rcx holds numerator DATA
      mov r9, rdx
      call reduce_fraction
      jmp L_plus_create_new_fraction
      
      ;------ First Int, Sec Int ----------
      L_plus_first_int_sec_int:
      DATA rbx 
      DATA rax    
      add rax,rbx
      MAKE_INT rax
      mov r12, rax ;           update the accumulator
      jmp L_plus_update_vars

      ;----- Create New Fraction -------
      L_plus_create_new_fraction:
      cmp r8, 1
      je L_plus_no_remainder

      L_plus_remainder_exist:
      MAKE_INT r9; r9 holds numerator in data structure
      MAKE_INT r8;  r8  holds denominator in data structure

      mov rdi, 16
      call my_malloc
      test rax, rax
      mov qword[rax], r9
      mov qword[rax+8], r8
      mov rsi, rax
      add rsi, 8
      mov r8, rsi
      MAKE_FRACTION rax, r8
      mov r12, rax ; update the accumulator
      jmp L_plus_update_vars

      L_plus_no_remainder:
      mov rax, r9
      MAKE_INT rax
      mov r12, rax ; update the accumulator
      jmp L_plus_update_vars

      L_plus_update_vars:
      inc r10;               increase offset
      dec r11;               decrease number of argument left
      jmp L_plus_loop
      
      L_plus_exit:
      leave
      ret

      LmakePlusClos:
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LPlusBody
      mov rax, qword [rax]
      mov qword ["(search-addr '+ fvars) "],rax
      \n\n"
)))

(define primitive-multiply
  (lambda(fvars)
    (string-append
      "\njmp LmakeMultiplyClos
      LMultiplyBody:
      push rbp
      mov rbp, rsp
      
      mov r12,MAKE_LITERAL(T_INTEGER,1);  create accumulator r12
      mov r11 ,qword [rbp + 3*8];         number of arguments
      mov r10, 4;               r10 holds current arg offset

      L_multiply_loop:
      mov rcx,r11
      cmp rcx, 1
      jg L_multiply_acc_type

      L_multiply_return_one:
      mov rax, r12
      jmp L_multiply_exit
     
      L_multiply_acc_type:
      ;check accumulator argument type
      mov rax, r12; use accumulator r12
      mov rcx, rax
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_multiply_first_int_check_sec
      
      L_multiply_first_frac_check_sec:
      mov rbx, qword [rbp + r10*8]; we will put in rbx second number
      mov rcx, rbx
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_multiply_first_frac_sec_int; 
      
      ;--------First Frac, Second Frac ------
      L_multiply_first_frac_sec_frac:
      mov rcx, rax;       we will put in rcx first_numerator
      NUMERATOR rcx
      DATA rcx
      mov rdx, rax;       we will put in rdx first_denominator
      DENOMINATOR rdx
      DATA rdx
      
      mov rsi, rbx;       we will put in rsi second_numerator
      NUMERATOR rsi
      DATA rsi
      mov r9, rbx;       we will put in r9 second_denominator
      DENOMINATOR r9
      DATA r9
      
      MULTIPLY rcx, rsi;  rcx holds numerator*numerator
      MULTIPLY rdx, r9;    now rdx holds denominator*denominator

      L_multiply_create_fraction:
      ;rcx holds numerator DATA
      ;rdx holds denominator DATA

      mov r8,  rdx; r8  holds denominator DATA
      mov r9, rcx; r9 holds numerator DATA
      call reduce_fraction

      MAKE_INT r9; r9 holds numerator in data structure
      MAKE_INT r8;  r8  holds denominator in data structure

      ;create new fraction
      mov rdi, 16
      call my_malloc
      test rax, rax
      mov qword[rax], r9
      mov qword[rax+8],r8
      mov rsi,rax
      add rsi,8
      mov r8, rsi
      MAKE_FRACTION rax, r8;  rax holds the fraction with its data structure 
      mov r12,rax ; update the accumulator
      jmp L_multiply_update_vars

      ;------ First Frac, Sec Int ----------
      L_multiply_first_frac_sec_int:
      ;rax holds fraction
      ;rbx holds integer

      mov rsi, rax; we will put in rsi first numerator
      NUMERATOR rsi
      DATA rsi
      mov rdi, rax;  we will put in rdi first denominator
      DENOMINATOR rdi
      DATA rdi

      DATA rbx
      mov r8,rbx
      MULTIPLY r8, rsi;  now r8 holds integer*first numerator
      mov rbx,r8

      ;rbx holds numerator
      ;rdi holds denominator
      mov r9, rbx; rdx holds numerator DATA
      mov r8,  rdi; r8  holds denominator DATA
      call reduce_fraction

      MAKE_INT r9; rdx holds numerator in data structure
      MAKE_INT r8;  r8  holds denominator in data structure

      ;create new fraction
      mov rdi, 16
      call my_malloc
      test rax, rax
      mov qword[rax], r9
      mov qword[rax+8],r8
      mov rsi,rax
      add rsi,8
      mov r8, rsi
      MAKE_FRACTION rax, r8
      mov r12,rax ; update the accumulator
      jmp L_multiply_update_vars

      L_multiply_first_int_check_sec:
      mov rbx, qword [rbp + r10*8]
      mov rdx, rbx
      TYPE rdx
      cmp rdx, T_INTEGER
      je L_multiply_first_int_sec_int

      ;------ First Int, Sec Frac ----------
      L_multiply_first_int_sec_frac:
      ;rax contains first integer
      ;rbx contains second fraction
      mov rsi, rbx; we will put in rsi second_numerator
      NUMERATOR rsi
      DATA rsi
      mov rdi, rbx;  we will put in rdi second_denominator
      DENOMINATOR rdi
      DATA rdi
      DATA rax
      mov r8,rax
      MULTIPLY r8, rsi;  now rax holds first_numerator*integer
      mov rax,r8

      ;rax holds numerator
      ;rdi holds denominator
      mov r8,  rdi; r8  holds denominator DATA
      mov r9, rax; rcx holds numerator DATA
      call reduce_fraction
      MAKE_INT r9; r9 holds numerator in data structure
      MAKE_INT r8;  r8  holds denominator in data structure

      ;create new fraction
      mov rdi, 16
      call my_malloc
      test rax, rax
      mov qword[rax], r9
      mov qword[rax+8],r8
      mov rsi,rax
      add rsi,8
      mov r8, rsi
      MAKE_FRACTION rax, r8
      mov r12,rax ; update the accumulator
      jmp L_multiply_update_vars
      
      ;------ First Int, Sec Int ----------
      L_multiply_first_int_sec_int:
      DATA rbx 
      DATA rax   
      mov r8,rax    
      MULTIPLY r8,rbx
      mov rax, r8
      MAKE_INT rax
      mov r12,rax ; update the accumulator
      jmp L_multiply_update_vars

      L_multiply_update_vars:
      inc r10;  increase offset
      dec r11;  decrease number of argument left
      jmp L_multiply_loop
      
      L_multiply_exit:
      leave
      ret

      LmakeMultiplyClos:
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LMultiplyBody
      mov rax, qword [rax]
      mov qword ["(search-addr '* fvars) "],rax
      \n\n"
)))

(define primitive-division
  (lambda(fvars)
    (string-append
      "\njmp LmakeDivisionClos
      LDivisionBody:
      push rbp
      mov rbp, rsp
      
      mov r12, qword [rbp + 4*8];         create accumulator r12
      mov r11, qword [rbp + 3*8];         number of arguments
      mov r10, 5;                         r10 holds current arg offset

      L_division_start:
      mov rcx, r11
      cmp rcx, 2
      ja L_division_loop

      L_division_one_argument:
      mov r12, MAKE_LITERAL(T_INTEGER,1)
      mov r10, 4
      jmp L_division_acc_type
      
      L_division_loop:
      mov rcx, r11
      cmp rcx, 3
      jb L_division_exit
     
      L_division_acc_type:
      ;check accumulator argument type
      mov rax, r12; use accumulator r12
      mov rcx, rax
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_division_first_int_check_sec
      
      L_division_first_frac_check_sec:
      mov rbx, qword [rbp + r10*8]; we will put in rbx second number
      mov rcx, rbx
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_division_first_frac_sec_int; 
      
      ;--------First Frac, Second Frac ------
      L_division_first_frac_sec_frac:
      mov rcx, rax;       we will put in rcx first_numerator
      NUMERATOR rcx
      DATA rcx
      mov rdx, rax;       we will put in rdx first_denominator
      DENOMINATOR rdx
      DATA rdx
      
      mov rsi, rbx;       we will put in rsi second_numerator
      NUMERATOR rsi
      DATA rsi
      mov r9, rbx;       we will put in r9 second_denominator
      DENOMINATOR r9
      DATA r9
      
      MULTIPLY rcx, r9;  rcx holds numerator*numerator
      MULTIPLY rdx, rsi;    now rdx holds denominator*denominator

      L_division_create_fraction:
      ;rcx holds numerator DATA
      ;rdx holds denominator DATA
      mov r8,  rdx; r8  holds denominator DATA
      mov r9, rcx; r9 holds numerator DATA
      call reduce_fraction
      jmp L_division_create_new_fraction

      ;------ First Frac, Sec Int ----------
      L_division_first_frac_sec_int:
      ;rax holds fraction
      ;rbx holds integer

      mov rsi, rax; we will put in rsi first numerator
      NUMERATOR rsi
      DATA rsi
      mov rdi, rax;  we will put in rdi first denominator
      DENOMINATOR rdi
      DATA rdi

      DATA rbx
      mov r8, rbx
      MULTIPLY r8, rdi;  now r8 holds integer*first denominator
      mov rbx, r8

      ;rbx holds numerator
      ;rdi holds denominator
      mov r9, rsi; rdx holds numerator DATA
      mov r8, rbx; r8  holds denominator DATA
      call reduce_fraction
      jmp L_division_create_new_fraction

      L_division_first_int_check_sec:
      mov rbx, qword [rbp + r10*8]
      mov rdx, rbx
      TYPE rdx
      cmp rdx, T_INTEGER
      je L_division_first_int_sec_int

      ;------ First Int, Sec Frac ----------
      L_division_first_int_sec_frac:
      ;rax contains first integer
      ;rbx contains second fraction
      mov rsi, rbx; we will put in rsi second_numerator
      NUMERATOR rsi
      DATA rsi
      mov rdi, rbx;  we will put in rdi second_denominator
      DENOMINATOR rdi
      DATA rdi
      DATA rax
      mov r8,rax
      MULTIPLY r8, rdi;  now rax holds integer * second denominator
      mov rax,r8

      ;rax holds numerator
      ;rdi holds denominator
      mov r9, rax; rcx holds numerator DATA
      mov r8, rsi; r8  holds denominator DATA
      call reduce_fraction
      jmp L_division_create_new_fraction

      
      ;------ First Int, Sec Int ----------
      L_division_first_int_sec_int:
      DATA rax
      DATA rbx
      mov r9, rax; r9 holds numerator DATA
      mov r8,  rbx; r8  holds denominator DATA
      call reduce_fraction
      jmp L_division_create_new_fraction

      ;----- Create New Fraction ---------
      L_division_create_new_fraction:
      cmp r8, 1
      je L_division_no_remainder

      cmp r8, -1
      jne L_division_remainder_exist

      L_division_change_numerator_sign:
      neg r9
      jmp L_division_no_remainder


      L_division_remainder_exist:
      MAKE_INT r9; r9 holds numerator in data structure
      MAKE_INT r8;  r8  holds denominator in data structure

      mov rdi, 16
      call my_malloc
      test rax, rax
      mov qword[rax], r9
      mov qword[rax+8], r8
      mov rsi, rax
      add rsi, 8
      mov r8, rsi
      MAKE_FRACTION rax, r8
      mov r12, rax ; update the accumulator
      jmp L_division_update_vars

      L_division_no_remainder:
      mov rax, r9
      MAKE_INT rax
      mov r12, rax ; update the accumulator
      jmp L_division_update_vars

      L_division_update_vars:
      inc r10;  increase offset
      dec r11;  decrease number of argument left
      jmp L_division_loop
      
      L_division_exit:
      leave
      ret

      LmakeDivisionClos:
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LDivisionBody
      mov rax, qword [rax]
      mov qword ["(search-addr '/ fvars) "],rax
      \n\n"
)))

(define primitive-minus
  (lambda(fvars)
    (string-append
      "\njmp LmakeMinusClos
      LMinusBody:
      push rbp
      mov rbp, rsp
      
      mov r12, qword [rbp + 4*8];         create accumulator r12
      mov r11, qword [rbp + 3*8];         number of arguments
      mov r10, 5;                         r10 holds current arg offset

      L_minus_start:
      mov rcx, r11
      cmp rcx, 2
      jne L_minus_loop

      L_minus_one_argument:
      mov rcx, r12
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_minus_one_argument_integer

      L_minus_one_argument_fraction:
      mov r9, r12 ; r9 holds numerator
      NUMERATOR r9
      DATA r9
      neg r9
      mov r8, r12
      DENOMINATOR r8; r8 holds denominator
      DATA r8

      MAKE_INT r9;  r9 holds numerator in data structure
      MAKE_INT r8;  r8  holds denominator in data structure

      ;create new fraction
      mov rdi, 16
      call my_malloc
      test rax, rax
      mov qword[rax], r9
      mov qword[rax+8],r8
      mov rsi,rax
      add rsi,8
      mov r8, rsi
      MAKE_FRACTION rax, r8
      jmp L_minus_exit

      L_minus_one_argument_integer:
      DATA r12
      neg r12
      mov rax, r12
      MAKE_INT rax
      jmp L_minus_exit

      L_minus_loop:
      mov rcx, r11
      cmp rcx, 3
      jl L_minus_exit
     
      L_minus_acc_type:
      ;check accumulator argument type
      mov rax, r12; use accumulator r12
      mov rcx, rax
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_minus_first_int_check_sec
      
      L_minus_first_frac_check_sec:
      mov rbx, qword [rbp + r10*8]; we will put in rbx second number
      mov rcx, rbx
      TYPE rcx
      cmp rcx, T_INTEGER
      je L_minus_first_frac_sec_int; 
      
      ;--------First Frac, Second Frac ------
      ;rax holds first fraction
      ;rbx holds second fraction
      L_minus_first_frac_sec_frac:
      mov rcx, rax;       we will put in rcx first_numerator
      NUMERATOR rcx
      DATA rcx
      mov rdx, rax;       we will put in rdx first_denominator
      DENOMINATOR rdx
      DATA rdx
      
      mov rsi, rbx;       we will put in rsi second_numerator
      NUMERATOR rsi
      DATA rsi
      mov r15, rbx;       we will put in r15 second_denominator
      DENOMINATOR r15
      DATA r15
      mov r8, rdx;        backup first denominator
      mov r12,r15;        backup second denominator

      ;evaluate new fraction
      MULTIPLY rdx, r15;  now rdx holds denominator*denominator
      MULTIPLY rcx, r12;  now rcx holds first_numerator*second_denominator
      MULTIPLY rsi, r8;   now rsi holds second_numerator*first_denominator
      sub rcx,rsi
      
      ;rcx holds numerator DATA
      ;rdx holds denominator DATA
      mov r9, rcx; rcx holds numerator DATA
      mov r8, rdx; r8  holds denominator DATA   
      call reduce_fraction
      jmp L_minus_create_new_fraction

      ;------ First Frac, Sec Int ----------
      L_minus_first_frac_sec_int:
      ;rax holds fraction
      ;rbx holds integer

      mov rsi, rax;       we will put in rsi first numerator
      NUMERATOR rsi
      DATA rsi
      mov rdi, rax;       we will put in rdi first denominator
      DENOMINATOR rdi
      DATA rdi

      DATA rbx;           rbx holds integer   
      mov r8, rbx
      MULTIPLY r8, rdi;   now r8 holds integer * first denominator
      sub rsi, r8;        r8 = first numerator - (integer * first denominator)

      ;rsi holds numerator
      ;rdi holds denominator
      mov r9, rsi;        rsi holds numerator DATA
      mov r8, rdi;        rdi holds denominator DATA
      call reduce_fraction
      jmp L_minus_create_new_fraction

      L_minus_first_int_check_sec:
      mov rbx, qword [rbp + r10*8]
      mov rdx, rbx
      TYPE rdx
      cmp rdx, T_INTEGER
      je L_minus_first_int_sec_int

      ;------ First Int, Sec Frac ----------
      L_minus_first_int_sec_frac:
      ;rax contains first integer
      ;rbx contains second fraction
      mov rsi, rbx; we will put in rsi second_numerator
      NUMERATOR rsi
      DATA rsi
      mov rdi, rbx;  we will put in rdi second_denominator
      DENOMINATOR rdi
      DATA rdi
      DATA rax
      mov r8,rax
      MULTIPLY r8, rdi;  now rax holds first_numerator*second_denominator
      mov rax,r8
      sub rax, rsi

      ;rax holds numerator
      ;rdi holds denominator
      mov r8,  rdi; r8  holds denominator DATA
      mov rdx, rax; rcx holds numerator DATA
      mov r9, rdx
      call reduce_fraction
      jmp L_minus_create_new_fraction
      
      ;------ First Int, Sec Int ----------
      L_minus_first_int_sec_int:
      DATA rbx 
      DATA rax    
      sub rax,rbx
      MAKE_INT rax
      mov r12,rax ; update the accumulator
      jmp L_minus_update_vars

      L_minus_update_vars:
      inc r10;  increase offset
      dec r11;  decrease number of argument left
      jmp L_minus_loop

      ;----- Create New Fraction ---------
      L_minus_create_new_fraction:
      cmp r8, 1
      je L_minus_no_remainder

      L_minus_remainder_exist:
      MAKE_INT r9; r9 holds numerator in data structure
      MAKE_INT r8;  r8  holds denominator in data structure

      mov rdi, 16
      call my_malloc
      test rax, rax
      mov qword[rax], r9
      mov qword[rax+8], r8
      mov rsi, rax
      add rsi, 8
      mov r8, rsi
      MAKE_FRACTION rax, r8
      mov r12, rax ; update the accumulator
      jmp L_minus_update_vars

      L_minus_no_remainder:
      mov rax, r9
      MAKE_INT rax
      mov r12, rax ; update the accumulator
      jmp L_minus_update_vars
      
      L_minus_exit:
      leave
      ret
      
      LmakeMinusClos:
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LMinusBody
      mov rax, qword [rax]
      mov qword ["(search-addr '- fvars) "],rax
      \n\n"
)))

(define primitive-remainder
  (lambda(fvars)
    (string-append
      "\njmp LmakeRemainderClos
      LRemainderBody:
      push rbp
      mov rbp, rsp

      mov rcx, qword [rbp + 3 * 8]
      cmp rcx, 3
      jne L_error_lambda_args_count
      
      mov rax, qword [rbp + 4 * 8]
      mov rcx, rax    
      TYPE rcx
      cmp rcx, T_INTEGER
      jne L_error_invalid_arguments

      mov rbx, qword [rbp + 5 * 8]
      mov rcx, rbx    
      TYPE rcx
      cmp rcx, T_INTEGER
      jne L_error_invalid_arguments

      L_remainder_check_first:
      cmp rax, 0
      jl L_remainder_first_negative

      L_remainder_first_positive:
      ;rax holds left arg
      ;rbx holds right arg
      DATA rax
      DATA rbx
      xor rdx, rdx
      idiv rbx;       rax = rax / rbx, rdx holds remainder
      mov rax, rdx
      MAKE_INT rax
      jmp L_remainder_exit

      L_remainder_first_negative:
      DATA rax
      neg rax
      DATA rbx
      xor rdx, rdx
      idiv rbx;       rax = rax / rbx, rdx holds remainder
      neg rdx
      mov rax, rdx
      MAKE_INT rax
      jmp L_remainder_exit

      L_remainder_exit:
      leave
      ret

      LmakeRemainderClos:
      mov rdi,8*2
      call my_malloc
      MAKE_LITERAL_CLOSURE rax, rcx, LRemainderBody
      mov rax, qword [rax]
      mov qword ["(search-addr 'remainder fvars) "],rax
      \n\n"
)))
;------------------------END OF PRIMITIVE FUNCTIONS  ---------------------


(define primitive-functions-list
  '(cdr car apply cons 
    null? boolean? char? integer? pair? number? zero? procedure? vector? rational?
    symbol? 
    char->integer integer->char
    string-length vector-length make-string string? string-ref string-set!
    make-vector vector-ref vector-set!
    denominator numerator remainder
    set-car! set-cdr!
    symbol->string string->symbol
    eq?
    +
    >
    <
    =
    -
    *
    /
    asaf-lior-list-to-vector 
    asaf-lior-reduce-num
    asaf-lior-opposite-num
    asaf-lior-inverse-num

    asaf-lior-binary-int-int-plus
    asaf-lior-binary-int-frac-plus
    asaf-lior-binary-frac-frac-plus

    asaf-lior-binary-int-int-mul
    asaf-lior-binary-int-frac-mul
    asaf-lior-binary-frac-frac-mul
    asaf-lior-greater-than-int-int)
)



(define remove-duplicates
  (lambda (lst)
    (if (null? lst) lst 
    (cons (car lst) 
    (remove-duplicates 
      (filter (lambda (y) (not (equal? (car lst) y))) lst))))
))


(define constant-symbols->assembly
  (lambda (lst ct)
    (if (null? lst) ""
      (string-append

"
  mov rdi,8
  call my_malloc
  MAKE_MALLOC_LITERAL_PAIR rax,"
  (cadar lst) 
  "," 
  (search-addr '() ct)
  "\n"
  (apply string-append (map 
    (lambda (x)
      (string-append

        " 
          mov rbx,rax
          mov rdi,8
          call my_malloc
          MAKE_MALLOC_LITERAL_PAIR rax,"
          (cadr x)
          ",rbx\n"
         )) (cdr lst)))
  "mov qword [L_SYMBOL_TABLE],rax\n\n"))
))

(define fvar-addr
  (lambda (lst addr)
    (if (null? lst)
      (begin (set! next-free-ind-in-mem addr) lst)
      `((,(car lst) ,(string-append "LGLOB" (number->string addr))) ,@(fvar-addr (cdr lst) (+ addr 1))))
))

(define ct-addr
  (lambda (lst counter)
    (let ((label-name (string-append "LCONST" (number->string counter))))
      (cond
        ((null? lst) (begin (set! next-free-ind-in-mem counter) '()))
        ((list? lst)
          (cond 
            ((equal? (car lst) (void)) `((,(car lst) ,label-name) ,@(ct-addr (cdr lst) (+ 1 counter))))
            ((null? (car lst)) `((,(car lst) ,label-name) ,@(ct-addr (cdr lst) (+ 1 counter))))
            ((equal? #t (car lst)) `((,(car lst) ,label-name) ,@(ct-addr (cdr lst) (+ 2 counter))))
            ((boolean? (car lst)) `((,(car lst) ,label-name) ,@(ct-addr (cdr lst) (+ 2 counter))))
            ((number? (car lst)) 
              (if (integer? (car lst))
                `((,(car lst) ,label-name) ,@(ct-addr (cdr lst) (+ 2 counter))) 
                `((,(car lst) ,label-name) ,@(ct-addr (cdr lst) (+ 3 counter))))) ; fraction
            ((pair? (car lst)) `((,(car lst) ,label-name) ,@(ct-addr (cdr lst) (+ 3 counter))))
            ((char? (car lst)) `((,(car lst) ,label-name) ,@(ct-addr (cdr lst) (+ 2 counter))))
            ((vector? (car lst)) `((,(car lst) ,label-name) ,@(ct-addr (cdr lst) 
                (+ 2 (length (vector->list (car lst))) counter))))
            ((string? (car lst)) `((,(car lst) ,label-name) 
                  ,@(ct-addr (cdr lst) (+ 2 (string-length (car lst)) counter))))
            ((symbol? (car lst)) `((,(car lst) ,label-name) 
                  ,@(ct-addr (cdr lst) 
                  (+ 2 counter))))          
            (else (error 'ct-addr "PANIC"))))
      (else (error 'ct-addr "PANIC"))))))

(define create-fvar-table
  (lambda (exps start-addr)
   (letrec ((iter (lambda (exps) 
    (cond ((null? exps) '())
    ((list? exps)
      (cond
        ((equal? 'fvar (car exps))
    (list (cadr exps)))
        (else (append (iter (car exps))
          (iter (cdr exps))))))
    (else '())))))
    (fvar-addr (remove-duplicates `(,@primitive-functions-list ,@(iter exps))) start-addr)
)))

(define create-sub-constants
  (lambda (e)
    (cond ((pair? e)
            `(,@(create-sub-constants (car e))
              ,@(create-sub-constants (cdr e))
              ,e))
          ((fraction? e)
            `(,@(create-sub-constants (numerator e))
              ,@(create-sub-constants (denominator e))
              ,e))
    ((symbol? e)
      `(,@(create-sub-constants (symbol->string e)) ,e))
    ((vector? e)
      `(,@(apply append (map create-sub-constants (vector->list e))) ,e))
    (else `(,e)))
))

(define create-constants-table
  (lambda (exps)
    (letrec ((iter (lambda (exps) 
              (cond ((null? exps) '())
                    ((list? exps)
                      (if (equal? 'const (car exps))
                          (list (cadr exps))
                          (append (iter (car exps)) (iter (cdr exps)))))
                    (else '())))))
      (ct-addr 
        `(,(void) () #t #f
          ,@(filter 
            (lambda (x) 
              (not (or (null? x) (boolean? x) (equal? x (void)))))
          (remove-duplicates (apply append (map create-sub-constants
            (remove-duplicates (iter exps)))))))
        1))))

(define file->string
  (lambda (in-file)
    (let ((in-port (open-input-file in-file)))
      (letrec ((run
        (lambda ()
          (let ((ch (read-char in-port)))
            (if (eof-object? ch)
                (begin
                  (close-input-port in-port) '())
                (cons ch (run)))))))
          (list->string (run))))))

(define file->list
  (lambda (filename)
    (let ((input (open-input-file filename)))
      (letrec ((run
        (lambda ()
          (let ((e (read input)))
            (if (eof-object? e)
              (begin (close-input-port input) '())
              (cons e (run)))))))
        (run)))))


(define list->sexprs
  (lambda (lst)
    (if (null? lst)
      lst
      (<sexpr> lst
        (lambda (x y) `(,x ,@(list->sexprs y)))
        (lambda (x) `(Failed to parse sexpr ,x))))))

(define search-pair
  (lambda (el lst)
    (if (null? lst) 
        (error 'search-pair "PANIC")
        (if (equal? el (caar lst))
          (car lst)
            (search-pair el (cdr lst))))))

(define search-fraction
  (lambda (el lst)
    (if (null? lst) 
        (error 'search-pair "PANIC")
        (if (equal? el (caar lst))
            (car lst)
            (search-pair el (cdr lst))))))

(define constant-symbols 
  (lambda (lst orig-lst)
      (if (null? lst) 
        lst
        (if (symbol? (caar lst))  
          `(,(search-pair (symbol->string (caar lst)) orig-lst) ,@(constant-symbols (cdr lst) orig-lst))
          `(,@(constant-symbols (cdr lst) orig-lst))))))

(define fvar-table->assembly
  (lambda (lst)
    (if (null? lst) 
      ""
      (apply string-append (map 
        (lambda (x)
          (string-append
            (cadr x)
            ":\n dq SOB_UNDEFINED\n")) lst)))))


(define list-of-exps->str
  (lambda (exps)
    (if (null? exps) 
        ""
        (string-append 
          (if (list? (car exps)) 
              (list-of-exps->str (car exps))
              (cond ((number? (car exps)) (number->string (car exps)))
                    ((symbol? (car exps)) (symbol->string (car exps)))
                   ;((boolean? (car exps)) (car exps))
                    (else (car exps))))
      ; (format "\n")
    (list-of-exps->str (cdr exps))))))

;gets an element(integer/char/etc.) and lst(const/fvar table) 
;returns the address of this element in this list
(define search-addr
  (lambda (el lst)
    (if (null? lst) 
      (error 'search-addr "PANIC")
              (if (equal? el (caar lst))
          (cadar lst)
          (search-addr el (cdr lst))))))

(define make-const-label
  (lambda (name value)
    (string-append name ":\ndq " value)))

(define get-ascii
  (lambda (c)
    (number->string (char->integer c))
))

 (define constants-table->assembly
   (lambda (lst)
     (list-of-exps->str (map (lambda (x)
       (cond 
  ((null? (car x)) (make-const-label (cadr x) "SOB_NIL\n"))
  ((equal? (car x) (void)) (make-const-label (cadr x) "SOB_VOID\n"))
  ((boolean? (car x))
    (make-const-label (cadr x) (if (equal? (car x) #f) "SOB_FALSE\n" "SOB_TRUE\n")))
  ((number? (car x))
    (if (integer? (car x))
    (make-const-label (cadr x) (string-append "MAKE_LITERAL(T_INTEGER," (number->string (car x)) ")\n"))
    (make-const-label (cadr x) ;fraction 
      (string-append
       "MAKE_LITERAL_FRACTION(" (search-addr  (numerator(car x)) lst) 
                                "," 
                                (search-addr  (denominator (car x) ) lst) 
                                ")\n" ))))
  ((pair? (car x))
      (make-const-label (cadr x) (string-append
       "MAKE_LITERAL_PAIR(" (search-addr (caar x) lst) "," (search-addr (cdar x) lst) ")\n" )))

  ((char? (car x))
    (make-const-label (cadr x) (string-append "MAKE_LITERAL(T_CHAR,"
     (number->string (char->integer (car x))) ")\n")))

  ; ##########################((symbol? (car x))######################### 
    ((symbol? (car x))
        (make-const-label (cadr x) (string-append "MAKE_SYMBOL("(search-addr (symbol->string (car x)) lst) ")\n")))
     
  ;   (string-append
  ;     "PUSH(IMM(" (number->string (search-addr (symbol->string (car x)) lst)) "));
  ;      CALL(MAKE_SOB_SYMBOL);
  ;      DROP(1);\n"))       
    ((string? (car x))
    (if (null? (string->list (car x))) (string-append (cadr x) ":\n" "MAKE_LITERAL_STRING \"\" \n")
         (let* ((chars-list (string->list (car x)))
                (first-param (get-ascii (car chars-list)))
                (other-params
              (list-of-exps->str
                (map 
                (lambda (x)
                   (string-append  "," (get-ascii x) )) (cdr chars-list))))) 
            (string-append (cadr x) ":\n" (string-append "MAKE_LITERAL_STRING " first-param other-params "\n")))))
   ((vector? (car x))
      (let ((v-l (vector->list (car x))))
        (if (null? v-l)
        (string-append (cadr x) ":\n" (string-append "MAKE_LITERAL_VECTOR \"\" \n"))
        (string-append (cadr x) ":\n" (string-append "MAKE_LITERAL_VECTOR "
            (string-append (search-addr (car v-l) lst)
              (list-of-exps->str 
            (map 
              (lambda (x)
               (string-append "," (search-addr x lst))) (cdr v-l))))
            "\n")))))

   (else (error 'constants-table->assembly "PANIC")))) lst))))


(define pe?
  (lambda (type)
    (lambda (pe)
      (equal? type (car pe)))))

(define pe-const? (pe? 'const))
(define pe-pvar? (pe? 'pvar))
(define pe-bvar? (pe? 'bvar))
(define pe-fvar? (pe? 'fvar))
(define pe-def? (pe? 'define))
(define pe-if3? (pe? 'if3))
(define pe-or? (pe? 'or))
(define pe-seq? (pe? 'seq))
(define pe-set? (pe? 'set))
(define pe-box? (pe? 'box))
(define pe-box-set? (pe? 'box-set))
(define pe-box-get? (pe? 'box-get))
(define pe-applic? (pe? 'applic))
(define pe-tc-applic? (pe? 'tc-applic))
(define pe-lambda-simple? (pe? 'lambda-simple))
(define pe-lambda-var? (pe? 'lambda-opt))
(define pe-lambda-opt? (pe? 'lambda-opt))


(define label-counter 0)

 (define create-label
  (lambda (str)
    (lambda ()
      (let ((counter (number->string label-counter)))
  (set! label-counter (+ 1 label-counter))
  (string-append str "_" counter)))
))

(define label-if3-else (create-label "L_if3_else"))
(define label-if3-exit (create-label "L_if3_exit"))
(define label-or (create-label "L_or"))
(define label-or-exit (create-label "L_or_exit"))
(define label-closure-body (create-label "L_clos_body"))
(define label-closure-exit (create-label "L_clos_exit"))
(define label-copy-params-loop (create-label "L_copy_params_loop"))
(define label-copy-params-exit (create-label "L_copy_params_exit"))
(define label-copy-prev-env-loop (create-label "L_copy_prev_env_loop"))
(define label-copy-prev-env-exit (create-label "L_copy_prev_env_exit"))
(define label-fix-stack-loop (create-label "L_fix_stack_loop"))
(define label-fix-stack-exit (create-label "L_fix_stack_exit"))
(define label-copy-frame-loop (create-label "L_copy_frame_loop"))
(define label-copy-frame-exit (create-label "L_copy_frame_exit"))
(define label-write-sob-exit (create-label "L_write_sob_exit"))

(define cg-if3
  (lambda (pe ct fvars depth)
    (let ((if3-label (label-if3-else))
    (if3-exit-label (label-if3-exit)))
      (string-append
       ";;;;START OF IF \n\n"
    (code-gen (car pe) ct fvars depth)
    "cmp rax,SOB_FALSE\n"
    "je " if3-label "\n"
    (code-gen (cadr pe) ct fvars depth)
    "jmp " if3-exit-label "\n"
    if3-label ":\n"
    (code-gen (caddr pe) ct fvars depth)
    if3-exit-label ":"
    "\n;;;;END OF IF\n\n"

    ))
))

(define cg-or
  (lambda (pe ct fvars depth)
    (let (
    (or-exit-label (label-or-exit)))
      (string-append
        ";;;;START OF OR \n\n"
    (list-of-exps->str (map 
      (lambda (x)
        (string-append
    (code-gen x ct fvars depth)
    "cmp rax,SOB_FALSE \n"
    "jne " or-exit-label "\n"))
    pe))
    or-exit-label ":"
     "\n;;;;END OF OR\n\n"
))
))

(define cg-fvar
  (lambda (pe ct fvars depth)
    (string-append
      "mov rax, qword [" (search-addr (cadr pe) fvars) "]\n")
))

(define cg-pvar
  (lambda (pe ct fvars depth)
    (string-append
      "mov rcx," (number->string (caddr pe))
      "\nadd rcx,4\n"
      "mov rax, qword [rbp + rcx*8]\n" 
      )

))

(define cg-bvar
  (lambda (pe ct fvars depth)
    (string-append
      "mov rax,qword [rbp+2*8]"
      "\nmov rax,qword [rax + "(number->string (caddr pe))"*8]"
      "\nmov rax,qword [rax + "(number->string (cadddr pe))"*8]\n" 
      )

))

(define cg-def
  (lambda (pe ct fvars depth)
    (string-append
      ";;;;START OF DEFINE \n\n"
      (code-gen (caddr pe) ct fvars depth)
      ";;;;END OF DEFINE \n\n"
      "mov qword [" (search-addr (cadr (cadr pe)) fvars) "] ,rax\n"
      "mov rax, SOB_VOID \n"
)))

(define cg-lambda-var
    (lambda (pe ct fvars depth)
    (let ((label-body (label-closure-body))
    (label-exit (label-closure-exit))
    (label-copy-params-loop (label-copy-params-loop))
    (label-copy-params-exit (label-copy-params-exit))
    (label-copy-prev-env-loop (label-copy-prev-env-loop))
    (label-copy-prev-env-exit (label-copy-prev-env-exit))
    (label-fix-stack-loop (label-fix-stack-loop))
    (label-fix-stack-exit (label-fix-stack-exit)))
    (string-append
      ";;;;START BUILD CLOSURE \n\n"
      "
      mov rdi,8
      call my_malloc
      mov rbx,rax
      mov rdi,8*2
      call my_malloc
      "
      (if (> depth 0)
      (string-append 
      "
      mov rsi,rax
      mov rdi,8*" (number->string (+ 1 depth)) "
      call my_malloc
      mov rbx,rax
      mov rdi,qword [rbp+3*8]
      shl rdi,3
      call my_malloc
      mov rcx,rax
      mov rax,rsi"

      "
      mov r8,0        
      " label-copy-params-loop ":
      cmp r8,qword [rbp+3*8]
      jge " label-copy-params-exit "
      mov rdx,qword [rbp+4*8+8*r8]
      mov qword [rcx + 8*r8],rdx
      inc r8
      jmp " label-copy-params-loop "\n"

      label-copy-params-exit ":\n
      mov qword [rbx],rcx
      mov r8,0
      mov r9,1
      mov rdx,qword [rbp +2*8]
      "
      label-copy-prev-env-loop ":
      cmp r8, " (number->string depth) "
      jge " label-copy-prev-env-exit
      "
      mov rsi,qword [rdx + 8*r8]
      mov qword [rbx +8*r9],rsi
      inc r8
      inc r9
      jmp "  label-copy-prev-env-loop "\n"
      label-copy-prev-env-exit ":\n\n"
) "")
      "
      MAKE_LITERAL_CLOSURE rax,rbx," label-body
      "\nmov rax,qword [rax]
      \njmp " label-exit "\n"

      label-body ":
      push rbp
      mov rbp, rsp \n"
      
      ";;;;START FIX STACK 
      mov rbx," (search-addr '() ct) "
      mov rsi,qword [rbp + 3*8]
      " label-fix-stack-loop ":
      cmp rsi,1
      je " label-fix-stack-exit " 
      dec rsi
      mov rdi,8
      call my_malloc
      mov rcx,rax
      mov rdx,rbp
      add rdx,3*8
      shl rsi,3
      add rdx,rsi
      shr rsi,3
      mov rdx,qword [rdx]
      mov qword [rcx],rdx
      mov rdi,8
      call my_malloc
      MAKE_MALLOC_LITERAL_PAIR rax,rcx,rbx
      mov rbx,rax
      jmp " label-fix-stack-loop "\n\n" 
      label-fix-stack-exit ":
      mov rbx,qword [rbx]
      mov qword [rbp + 4*8],rbx "
      "\n\n ;;;;END FIX STACK \n\n"

      (code-gen (getLambdaBody pe) ct fvars depth)
      "leave
      ret\n"
      label-exit ":\n"
      ";;;;END BUILD CLOSURE \n\n"
))))

(define cg-lambda-opt
    (lambda (pe ct fvars depth)
    (let ((label-body (label-closure-body))
    (label-exit (label-closure-exit))
    (label-copy-params-loop (label-copy-params-loop))
    (label-copy-params-exit (label-copy-params-exit))
    (label-copy-prev-env-loop (label-copy-prev-env-loop))
    (label-copy-prev-env-exit (label-copy-prev-env-exit))
    (label-fix-stack-loop (label-fix-stack-loop))
    (label-fix-stack-exit (label-fix-stack-exit)))
    (string-append
      ";;;;START BUILD CLOSURE \n\n"
      "
      mov rdi,8
      call my_malloc
      mov rbx,rax
      mov rdi,8*2
      call my_malloc
      "
      (if (> depth 0)
      (string-append 
      "
      mov rsi,rax
      mov rdi,8*" (number->string (+ 1 depth)) "
      call my_malloc
      mov rbx,rax
      mov rdi,qword [rbp+3*8]
      shl rdi,3
      call my_malloc
      mov rcx,rax
      mov rax,rsi"

      "
      mov r8,0        
      " label-copy-params-loop ":
      cmp r8,qword [rbp+3*8]
      jge " label-copy-params-exit "
      mov rdx,qword [rbp+4*8+8*r8]
      mov qword [rcx + 8*r8],rdx
      inc r8
      jmp " label-copy-params-loop "\n"

      label-copy-params-exit ":\n
      mov qword [rbx],rcx
      mov r8,0
      mov r9,1
      mov rdx,qword [rbp +2*8]
      "
      label-copy-prev-env-loop ":
      cmp r8, " (number->string depth) "
      jge " label-copy-prev-env-exit
      "
      mov rsi,qword [rdx + 8*r8]
      mov qword [rbx +8*r9],rsi
      inc r8
      inc r9
      jmp "  label-copy-prev-env-loop "\n"
      label-copy-prev-env-exit ":\n\n"
) "")
      "
      MAKE_LITERAL_CLOSURE rax,rbx," label-body
      "\nmov rax,qword [rax]
      \njmp " label-exit "\n"

      label-body ":
      push rbp
      mov rbp, rsp
      cmp qword [rbp +3*8]," (number->string (+ 1 (length (cadr pe)))) "\n
      jl L_error_lambda_args_count"
      
      ";;;;START FIX STACK 
      mov rbx," (search-addr '() ct) "
      mov rsi,qword [rbp + 3*8]
      mov r9, " (number->string (+ 1 (length (cadr pe)))) "
      " label-fix-stack-loop ":
      cmp rsi,r9
      jle " label-fix-stack-exit " 
      dec rsi
      mov rdi,8
      call my_malloc
      mov rcx,rax
      mov rdx,rbp
      add rdx,3*8
      shl rsi,3
      add rdx,rsi
      shr rsi,3
      mov rdx,qword [rdx]
      mov qword [rcx],rdx
      mov rdi,8
      call my_malloc
      MAKE_MALLOC_LITERAL_PAIR rax,rcx,rbx
      mov rbx,rax
      jmp " label-fix-stack-loop "\n\n" 
      label-fix-stack-exit ":
      mov rbx,qword [rbx]
      mov qword [rbp+3*8 +r9*8],rbx"
      "\n\n ;;;;END FIX STACK \n\n"

      (code-gen (getLambdaBody pe) ct fvars depth)
      "leave
      ret\n"
      label-exit ":\n"
      ";;;;END BUILD CLOSURE \n\n"
))))

(define cg-lambda-simple
  (lambda (pe ct fvars depth)
    (let ((label-body (label-closure-body))
    (label-exit (label-closure-exit))
    (label-copy-params-loop (label-copy-params-loop))
    (label-copy-params-exit (label-copy-params-exit))
    (label-copy-prev-env-loop (label-copy-prev-env-loop))
    (label-copy-prev-env-exit (label-copy-prev-env-exit)))
    (string-append
      ";;;;START BUILD CLOSURE \n\n"
      "
      mov rdi,8
      call my_malloc
      mov rbx,rax
      mov rdi,8*2
      call my_malloc
      "
      (if (> depth 0)
      (string-append 
      "
      mov rsi,rax
      mov rdi,8*" (number->string (+ 1 depth)) "
      call my_malloc
      mov rbx,rax
      mov rdi,qword [rbp+3*8]
      shl rdi,3
      call my_malloc
      mov rcx,rax
      mov rax,rsi"

      "
      mov r8,0        
      " label-copy-params-loop ":
      cmp r8,qword [rbp+3*8]
      jge " label-copy-params-exit "
      mov rdx,qword [rbp+4*8+8*r8]
      mov qword [rcx + 8*r8],rdx
      inc r8
      jmp " label-copy-params-loop "\n"

      label-copy-params-exit ":\n
      mov qword [rbx],rcx
      mov r8,0
      mov r9,1
      mov rdx,qword [rbp +2*8]
      "
      label-copy-prev-env-loop ":
      cmp r8, " (number->string depth) "
      jge " label-copy-prev-env-exit
      "
      mov rsi,qword [rdx + 8*r8]
      mov qword [rbx +8*r9],rsi
      inc r8
      inc r9
      jmp "  label-copy-prev-env-loop "\n"
      label-copy-prev-env-exit ":\n\n"
) "")
      "
      MAKE_LITERAL_CLOSURE rax,rbx," label-body
      "\nmov rax,qword [rax]
      \njmp " label-exit "\n"

      label-body ":
      push rbp
      mov rbp, rsp
        "  (code-gen (getLambdaBody pe) ct fvars depth)
      "leave
      ret\n"
      label-exit ":\n"
      ";;;;END BUILD CLOSURE \n\n"
 ))))


(define cg-tc-applic
  (lambda (pe ct fvars depth)
    (let ((label-copy-frame-loop (label-copy-frame-loop))
          (label-copy-frame-exit (label-copy-frame-exit)))
      (string-append
        "\n;;;;;;;; START TC-APPLIC\n"
        (apply string-append
      "push SOB_NIL\n"
    (map
      (lambda (x)
        (string-append
    (code-gen x ct fvars depth)
    "push rax\n"))
      (reverse (caddr pe))))
      "mov rcx, "(number->string (+ 1 (length (caddr pe))))
      "\npush rcx\n"
      (code-gen (cadr pe) ct fvars depth)
      "
      mov rcx,rax
      TYPE rcx
      cmp rcx,T_CLOSURE
      jne L_cannot_apply_non_closure
      mov rbx,rax
      CLOSURE_ENV rbx
      push rbx
      mov r8,rbp
      mov r10, qword [rbp+8*3]
      shl r10,3
      add r10,3*8
      add r10,r8
      push qword [rbp+8]
      mov rbp,qword [rbp]
      mov r9,qword [rsp+2*8]
      add r9,3
      mov rsi,0
       " 
       label-copy-frame-loop 
       ":\n
       cmp rsi,r9
       je " label-copy-frame-exit "\n
       mov rcx,r8
       shl rsi,3
       sub rcx, rsi
       sub rcx,8
       mov rcx,qword [rcx]
       mov rdx,r10
       sub rdx,rsi
       mov qword [rdx],rcx
       shr rsi,3
       inc rsi
       jmp "label-copy-frame-loop "\n
        " label-copy-frame-exit ":\n
        sub rsi,1
  shl rsi,3
  sub r10,rsi
  mov rsp,r10
          CLOSURE_CODE rax
          jmp rax "
         "\n ;;;;;;;; END TC-APPLIC   \n"  

))))

(define cg-applic
  (lambda (pe ct fvars depth)
    (string-append
      "\n;;;;;;;; START - APPLIC\n"
      (apply string-append
    "push SOB_NIL\n"
    (map
      (lambda (x)
        (string-append
          (code-gen x ct fvars depth)
      "push rax\n"))
      (reverse (caddr pe))))
      "mov rcx, "(number->string (+ 1 (length (caddr pe))))
      "\npush rcx\n"
      (code-gen (cadr pe) ct fvars depth)
      "
      mov rcx,rax
      TYPE rcx
      cmp rcx,T_CLOSURE
      jne L_cannot_apply_non_closure
      mov rbx,rax
      CLOSURE_ENV rbx
      push rbx
      CLOSURE_CODE rax
      call rax
      mov rbx,qword [rsp + 8]
      shl rbx,3
      add rbx,2*8
      add rsp,rbx"
      "\n ;;;;;;;; END - APPLIC   \n"
)))

;=========================================  SET  ===================================
 (define cg-set-pvar
  (lambda (pe ct fvars depth) ; get the parsed expression, constant table, free-vars table and lambda-depth
    (let ((minor (number->string (caddr (cadr pe)))))
    (string-append
      (code-gen (caddr pe) ct fvars depth) ; get the value to be set and put it in RAX
      "mov rbx, " minor "\n"
      "add rbx, 4 
      mov qword [rbp + rbx*8], rax
      mov rax, SOB_VOID\n"
          ))))

(define cg-set-bvar
  (lambda (pe ct fvars depth)
    (let ((major (number->string (caddr (cadr pe))))
          (minor (number->string (cadddr (cadr pe)))))
        (string-append
          (code-gen (caddr pe) ct fvars depth)
          "mov rbx, qword [rbp + 2*8];    get the env
           mov rbx, qword [rbx + "major"*8];  get the bounded var?
           mov qword [rbx + "minor"*8], rax;  update the env
           mov rax, SOB_VOID;         return void
          " ))))
;==================================== END OF SET  ==================================

;======================================  BOX  ======================================
(define cg-box
  (lambda (pe ct fvars depth)               
    (string-append
      (code-gen (cadr pe) ct fvars depth)
    "
          mov rbx,rax ;save rax
          mov rdi,8
          call my_malloc ; now rax = my_malloc(8), create a pointer
          mov qword[rax], rbx ; wrap the rax in the pointer
    "
       )))

; same as bvar
(define cg-box-set-pvar
  (lambda (pe ct fvars depth)  
    (string-append
     (code-gen (caddr pe) ct fvars depth) ; get value
     "\nMOV RBX, RAX ; save RAX\n"
     (code-gen (cadr pe) ct fvars depth) ; get the box
     "\nMOV [RAX], RBX; change the content of the box 
     MOV RAX, SOB_VOID ; return void
     \n
     "
    )))

(define cg-box-set-bvar
  (lambda (pe ct fvars depth)  
    (string-append
     (code-gen (caddr pe) ct fvars depth) ; get value
      "\nMOV RBX, RAX ; save RAX\n"
     (code-gen (cadr pe) ct fvars depth) ; get the box
     "\n MOV [RAX], RBX; change the content of the box 
     MOV RAX, SOB_VOID ; return void
     \n
     "
    )))

; same as bvar
(define cg-box-get-pvar
  (lambda (pe ct fvars depth)
    (string-append
      (code-gen (cadr pe) ct fvars depth)
      "MOV RAX,[RAX]; unbox\n")))

(define cg-box-get-bvar
  (lambda (pe ct fvars depth)
    (string-append
      (code-gen (cadr pe) ct fvars depth)
      "MOV RAX,[RAX]; unbox\n"
    )))
;===================================  END OF BOX  ==================================
 (define code-gen
  (lambda (pe ct fvars depth-count)
    (cond
      ((pe-seq? pe) 
      (apply string-append (map (lambda (x) (code-gen x ct fvars depth-count)) (cadr pe))))
      ((pe-if3? pe) (cg-if3 (cdr pe) ct fvars depth-count))
      ((pe-or? pe) (cg-or (cadr pe) ct fvars depth-count))
      ((pe-lambda-simple? pe)
      (string-append 
      ";;;;START - LAMBDA-SIMPLE \n\n"
            (cg-lambda-simple pe ct fvars (+ 1 depth-count))
       ";;;;END - LAMBDA-SIMPLE \n\n"))
       ((and (pe-lambda-opt? pe) (not (null? (cadr pe))))
       (string-append
        ";;;;START - LAMBDA-OPT \n\n"
        (cg-lambda-opt pe ct fvars (+ 1 depth-count))
        ";;;;END - LAMBDA-OPT \n\n"))
      ((and (pe-lambda-var? pe) (null? (cadr pe)))
       (string-append
        ";;;;START - LAMBDA-VAR \n\n"
        (cg-lambda-var pe ct fvars (+ 1 depth-count))
        ";;;;END - LAMBDA-VAR \n\n"))
      ((pe-tc-applic? pe) (cg-tc-applic pe ct fvars depth-count))
      ((pe-applic? pe) (cg-applic pe ct fvars depth-count))
      ((pe-pvar? pe) (cg-pvar pe ct fvars depth-count))
      ((pe-bvar? pe) (cg-bvar pe ct fvars depth-count))
      ((pe-fvar? pe) (cg-fvar pe ct fvars depth-count))
      ((pe-def? pe) (cg-def pe ct fvars depth-count))
      ((pe-const? pe) 
       (string-append
      "mov rax, qword [" (search-addr (cadr pe) ct) "]\n" ))
      ((pe-set? pe) ;right now, all cg-set-SOMETHING are the same. maybe need to merge
        (cond
          ((equal? (caadr pe) 'pvar)      
            (cg-set-pvar pe ct fvars depth-count))
          ((equal? (caadr pe) 'bvar) 
            (cg-set-bvar pe ct fvars depth-count))
          ((equal? (caadr pe) 'fvar)
            (cg-def pe ct fvars depth-count))
          (else (error 'code-gen "SET ELSE"))))
      ((pe-box? pe) (cg-box pe ct fvars depth-count))
      ((pe-box-set? pe)
        (cond
          ((equal? (caadr pe) 'pvar)
            (cg-box-set-pvar pe ct fvars depth-count))
          ((equal? (caadr pe) 'bvar) 
           (cg-box-set-bvar pe ct fvars depth-count))
          ((equal? (caadr pe) 'fvar) "ERROR box-set fvar")
          (else (error 'code-gen "ERROR box-set else"))))
      ((pe-box-get? pe)
        (cond
          ((equal? (caadr pe) 'pvar)
            (cg-box-get-pvar pe ct fvars depth-count))
          ((equal? (caadr pe) 'bvar) 
            (cg-box-get-bvar pe ct fvars depth-count))
          ((equal? (caadr pe) 'fvar) "ERROR box-get fvar")
          (else (error 'code-gen "ERROR box-get else"))))
      (else (error 'code-gen "ERROR code-gen else\n")))))

 (define print-value
  (lambda ()
    (let ((label-exit (label-write-sob-exit)))
      (string-append 
  "push rax\n";
  "call write_sob_if_not_void \n"
  "add rsp, 1*8 \n"))
))


 (define primitive-car-cdr
  (lambda (lst)
    (let ((proc-name (string-append "c" (apply string-append (map (lambda (x) x) lst)) "r ")))
  (string-append "(define " proc-name 
    "(lambda (x) "
      (fold-right string-append "x " (map (lambda (x)
      (if (equal? x "a") "(car " "(cdr ")) lst)) 
      (apply string-append (map (lambda (x) ")") lst)) "))\n"))
))

(define flatmap 
  (lambda (f lst)
    (apply append (map f lst))
))

(define permutations 
  (lambda (size elements)
  (if (zero? size)
      '(())
      (flatmap (lambda (p)            
                 (map (lambda (e)     
                        (cons e p))   
                      elements))
               (permutations (- size 1) elements)))
))

(define all-primitive-car-cdr
  (lambda ()
    (apply string-append `(,@(map primitive-car-cdr (permutations 2 (list "a" "d")))
      ,@(map primitive-car-cdr (permutations 3 (list "a" "d")))
      ,@(map primitive-car-cdr (permutations 4 (list "a" "d")))))
))



 (define scheme-primitive-functions
  (lambda ()  
     (string-append
     "
     (define list (lambda lst lst))
     
     (define not (lambda (x) (if x #f #t)))

     (define vector (lambda x (asaf-lior-list-to-vector x)))
     
     
      (define asaf-lior-one-list-map
       (lambda (f s)
   (if (null? s) '()
       (let ((x (f (car s))))
     (cons x (asaf-lior-one-list-map f (cdr s)))))))
    
      (define map
   (lambda (f x . y)
     (if (null? y) 
         (asaf-lior-one-list-map f x)
         (letrec ((iter
       (lambda (lst)
         (if (null? (car lst)) '()
           (cons (apply f (asaf-lior-one-list-map car lst))
           (iter (asaf-lior-one-list-map cdr lst)))))))
       (iter (append (list x) y))))))"
    
   "(define append
     (lambda args
       (letrec 
         ((f (lambda (ls args)
            (if (null? args)
                 ls
         (letrec ((g (lambda (ls)
           (if (null? ls)
               (f (car args) (cdr args))
               (cons (car ls) (g (cdr ls)))))))
       (g ls))))))
       (f '() args))))"

       "\n(define asaf-lior-binary-sub
     (lambda (x y)
       (+ x (asaf-lior-opposite-num y))))"
      
      "(define void (lambda() (if #f #f)))"

  )))

(define compile-scheme-file
  (lambda (scheme-file target-file)
    (let* ((scheme-file-content (list->sexprs (string->list (string-append (scheme-primitive-functions)
                (file->string scheme-file)))))
            (parsed-exps  
              (map 
                  (lambda (x)
                    (annotate-tc 
                        (pe->lex-pe
                          (box-set
                              (remove-applic-lambda-nil
                                (parse x))))))
                  scheme-file-content))
            (fvar-table (create-fvar-table parsed-exps next-free-ind-in-mem))
            (constants-table (create-constants-table parsed-exps))
            (constant-symbols (constant-symbols constants-table constants-table))
            (symbol-table-addr next-free-ind-in-mem)
            (out (open-output-file target-file)))

      (begin (display  
        (string-append 

          " %include \"project/mayer/scheme.s\" \n\n "
          (constants-table->assembly constants-table)
          (fvar-table->assembly fvar-table)
          (string-append "L_SYMBOL_TABLE" ":\n dq "(search-addr '() constants-table)"\n")
          "
            L_error_lambda_args_count:
              call exit
            L_cannot_apply_non_closure:
              call exit
            L_error_invalid_arguments:
              call exit
              "

          "section .text
           main:\n\n
           mov rax, malloc_pointer
           mov qword [rax], start_of_memory
           "

; ------------ OUR PRIMITIVE FUNCTIONS ---------------
(primitive-vector-set fvar-table)
(primitive-vector-ref fvar-table)
(primitive-make-vector fvar-table)
(primitive-vector-length fvar-table)
(primitive-list-to-vector fvar-table)
(primitive-eq fvar-table)
(primitive-symbol-pred fvar-table)
(constant-symbols->assembly constant-symbols constants-table)
(primitive-symbol-to-string fvar-table)
(primitive-string-to-symbol fvar-table)
(primitive-apply fvar-table)
(primitive-null-pred fvar-table)
(primitive-boolean-pred fvar-table)
(primitive-char-pred fvar-table)
(primitive-integer-pred fvar-table)
(primitive-pair-pred fvar-table)
(primitive-number-pred fvar-table)
(primitive-procedure-pred fvar-table)
(primitive-vector-pred fvar-table) 
(primitive-numerator fvar-table) 
(primitive-denominator fvar-table) 
(primitive-greater-than fvar-table)
(primitive-smaller-than fvar-table) 
(primitive-variadic-equal fvar-table)
(primitive-string-pred fvar-table) 
(primitive-char-to-integer fvar-table)
(primitive-integer-to-char fvar-table) 
(primitive-car fvar-table)
(primitive-cdr fvar-table) 
(primitive-string-length fvar-table)
(primitive-rational-pred fvar-table)
(primitive-cons fvar-table)
(primitive-string-ref fvar-table)
(primitive-make-string fvar-table)
(primitive-string-set fvar-table)
(primitive-set-cdr fvar-table)
(primitive-set-car fvar-table)
(primitive-zero-pred fvar-table)
(primitive-minus fvar-table)
(primitive-multiply fvar-table)
(primitive-remainder fvar-table)
(primitive-division fvar-table) 
(primitive-plus fvar-table)
;------- ----- END OF OUR PRIMITIVE FUNCTIONS -------

(list-of-exps->str 
   (map (lambda (x) (string-append 
    (code-gen x constants-table fvar-table -1) (print-value))) parsed-exps))

"\n\nret")

     out) (close-output-port out)))))