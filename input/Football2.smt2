;@mannd an example of Football team - valid case
(set-option :smt.arith.random_initial_value true)
(declare-fun win () Int)
(declare-fun draw () Int)
(declare-fun lose () Int)
(declare-fun point () Int)

(assert (> win 0)) ;inv win>0
(assert (> draw 0)) ;inv draw >0
(assert (> lose 0)) ; inv lose >0
(assert (= point (+ (* 3 win) draw))) ;inv point
(assert (and (> win 0) (> draw 0)))
(assert (<= (+ (+ win draw) lose) 12))
