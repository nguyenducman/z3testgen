;@mannd an example of pairwise 
(set-option :smt.arith.random_initial_value true)

(declare-datatypes () ((Type1 Val1A Val1B Val1C)))
(declare-datatypes () ((Type2 Val2A Val2B Val2C Val2D)))
(declare-datatypes () ((Type3 Val3A Val3B Val3C )))

(declare-fun v1 () Type1)
(declare-fun v2 () Type2)
(declare-fun v3 () Type3)

(assert (or
  (and (= v1 Val1A ) (= v2 Val2A))
  (and (= v1 Val1A ) (= v2 Val2B))
  (and (= v1 Val1B ) (= v2 Val2A))
  (and (= v1 Val1B ) (= v2 Val2B))
  (and (= v1 Val1C ) (= v2 Val2A))
  (and (= v1 Val1C ) (= v2 Val2B))

 (and (= v2 Val2A ) (= v3 Val3A))
 (and (= v2 Val2A ) (= v3 Val3B))
 (and (= v2 Val2A ) (= v3 Val3C))
 (and (= v2 Val2B ) (= v3 Val3A))
 (and (= v2 Val2B ) (= v3 Val3B))
 (and (= v2 Val2B ) (= v3 Val3C))

 (and (= v3 Val3A ) (= v1 Val1A))
 (and (= v3 Val3A ) (= v1 Val1B))
 (and (= v3 Val3A ) (= v1 Val1C))
 (and (= v3 Val3B ) (= v1 Val1A))
 (and (= v3 Val3B ) (= v1 Val1B))
 (and (= v3 Val3B ) (= v1 Val1C))
 (and (= v3 Val3C ) (= v1 Val1A))
 (and (= v3 Val3C ) (= v1 Val1B))
 (and (= v3 Val3C ) (= v1 Val1C))
))
