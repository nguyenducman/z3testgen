;@mannd an example of Football team - invalid case
(set-option :smt.arith.random_initial_value true)
(declare-fun win () Int)
(declare-fun draw () Int)
(declare-fun lose () Int)
(declare-fun point () Int)

(assert (or (<= win 0) (<= draw 0) (<= lose 0))) ;inv win>0
(assert (= point (+ (* 3 win) draw))) ;inv point
(assert (<= (+ (+ win draw) lose) 12))
