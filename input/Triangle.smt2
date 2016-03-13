(set-option :smt.arith.random_initial_value true)
(declare-datatypes () ((TType EQUI ISO SCA NOT)))
(declare-fun x () TType)
(declare-const a Int) 
(declare-const b Int) 
(declare-const c Int) 
(define-fun eq_ab () Bool  (= a b))
(define-fun eq_bc () Bool  (= b c))
(define-fun eq_ca () Bool  (= c a))
(define-fun tri1 () Bool  (> (+ a b) c ))
(define-fun tri2 () Bool  (> (+ b c) a ))
(define-fun tri3 () Bool  (> (+ a c) b ))
(define-fun tri () Bool  (and tri1 tri2 tri3 ))
;check TType
(assert (= x 
    (if (not tri)
      NOT
      (if (and tri eq_ab eq_bc)
        EQUI
        (if (or (and tri eq_ab (not eq_bc)) 
(and tri eq_bc (not eq_ca)) 
(and tri eq_ca (not eq_ab)))
       	ISO
       	SCA )))))
;can add more constraints to check in partially    
   
;(assert (or  
	;(and tri eq_ab eq_bc)
;	(and tri (> a 0) (> b 0) (> c 0))
;	(and (> a 0) (> b 0) (> c 0) (not tri))
;	(not tri)
;	))
;(check-sat)
;(get-model)
