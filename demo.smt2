(declare-rel start ((Array Int Int))) 
;
(assert (forall ((a (Array Int Int))) (start a)))
(assert (forall ((a (Array Int Int)) (v Int) (v2 Int)) (=> (and (start a) (= v (select a 0)) (= v2 (select a 0))) (= v v2))))
(check-sat)
