;CanMarry - pre: 0<=age<=150; return value
(set-option :smt.arith.random_initial_value true)
(declare-const age Int)
(declare-const isMale Bool)
(declare-const result Bool)
(declare-fun f (Int Bool) Bool)
(assert (and (<= 0 age) (<= age 150)))
;(assert (or isMale (not isMale)))
(assert (= result 
	(ite (or (>= age 18) (and (>= age 16) (= isMale false)))
		true
		false)))
   
(assert (= (f age isMale) result))
;(check-sat)
;(get-model)
