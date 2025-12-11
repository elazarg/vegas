(declare-const A_c Bool)
(declare-const A_c_done Bool)

(declare-const B_c Bool)
(declare-const B_c_done Bool)

(declare-const action_A_0_done Bool)
(assert (=> action_A_0_done (and true true)))

(declare-const action_B_1_done Bool)
(assert (=> action_B_1_done (and (and true action_A_0_done) true)))

(declare-const action_A_3_done Bool)
(assert (=> action_A_3_done (and (and true action_B_1_done) true)))
(assert (=> action_A_3_done A_c_done))

(declare-const action_A_4_done Bool)
(assert (=> action_A_4_done (and (and (and (and true action_B_1_done) action_A_3_done) action_B_5_done) true)))
(assert (=> action_A_4_done A_c_done))

(declare-const action_B_5_done Bool)
(assert (=> action_B_5_done (and (and true action_B_1_done) true)))
(assert (=> action_B_5_done B_c_done))

(declare-const action_B_6_done Bool)
(assert (=> action_B_6_done (and (and (and (and true action_B_1_done) action_B_5_done) action_A_3_done) true)))
(assert (=> action_B_6_done B_c_done))

(declare-const A_outcome Int)
(assert (= A_outcome (ite (and A_c_done B_c_done) (ite (and A_c B_c) 100 (ite (and A_c (not B_c)) 0 (ite (and (not A_c) B_c) 200 90))) (ite (not A_c_done) 0 200))))

(declare-const B_outcome Int)
(assert (= B_outcome (ite (and A_c_done B_c_done) (ite (and A_c B_c) 100 (ite (and A_c (not B_c)) 200 (ite (and (not A_c) B_c) 0 110))) (ite (not A_c_done) 200 0))))

(check-sat)
(get-model)
