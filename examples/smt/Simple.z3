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
(assert (= A_outcome (ite (and (not A_c_done) (not B_c_done)) 1 (ite (not A_c_done) 0 (ite (not B_c_done) 2 (ite (not (= A_c B_c)) 2 0))))))

(declare-const B_outcome Int)
(assert (= B_outcome (ite (and (not A_c_done) (not B_c_done)) 1 (ite (not A_c_done) 2 (ite (not B_c_done) 0 (ite (= A_c B_c) 2 0))))))

(check-sat)
(get-model)
