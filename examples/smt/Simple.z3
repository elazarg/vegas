(declare-const A_c Bool)
(declare-const A_c_done Bool)

(declare-const B_c Bool)
(declare-const B_c_done Bool)

(declare-const action_A_0_done Bool)
(assert (=> action_A_0_done (and true true)))

(declare-const action_B_1_done Bool)
(assert (=> action_B_1_done (and (and true action_A_0_done) true)))

(declare-const action_A_2_done Bool)
(assert (=> action_A_2_done (and (and true action_B_1_done) true)))
(assert (=> action_A_2_done A_c_done))

(declare-const action_B_3_done Bool)
(assert (=> action_B_3_done (and (and true action_A_2_done) true)))
(assert (=> action_B_3_done B_c_done))

(declare-const action_A_4_done Bool)
(assert (=> action_A_4_done (and (and (and true action_B_3_done) action_A_2_done) true)))
(assert (=> action_A_4_done A_c_done))

(declare-const A_outcome Int)
(assert (= A_outcome (ite (or (not (= A_c B_c)) (not B_c_done)) 1 (- 1))))

(declare-const B_outcome Int)
(assert (= B_outcome (ite (or (= A_c B_c) (not A_c_done)) 1 (- 1))))

(check-sat)
(get-model)
