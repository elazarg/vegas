(declare-const action_A_0_done Bool)
(assert (=> action_A_0_done (and true true)))

(declare-const A_outcome Int)
(assert (= A_outcome 0))

(check-sat)
(get-model)
