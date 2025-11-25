(declare-const Even_c Bool)
(declare-const Even_c_done Bool)

(declare-const Odd_c Bool)
(declare-const Odd_c_done Bool)

(declare-const action_Even_0_done Bool)
(assert (=> action_Even_0_done (and true true)))

(declare-const action_Odd_0_done Bool)
(assert (=> action_Odd_0_done (and true true)))

(declare-const action_Odd_2_done Bool)
(assert (=> action_Odd_2_done (and (and (and true action_Odd_0_done) action_Even_0_done) true)))
(assert (=> action_Odd_2_done Odd_c_done))

(declare-const action_Odd_3_done Bool)
(assert (=> action_Odd_3_done (and (and (and (and (and true action_Odd_0_done) action_Even_0_done) action_Odd_2_done) action_Even_4_done) true)))
(assert (=> action_Odd_3_done Odd_c_done))

(declare-const action_Even_4_done Bool)
(assert (=> action_Even_4_done (and (and (and true action_Odd_0_done) action_Even_0_done) true)))
(assert (=> action_Even_4_done Even_c_done))

(declare-const action_Even_5_done Bool)
(assert (=> action_Even_5_done (and (and (and (and (and true action_Odd_0_done) action_Even_0_done) action_Even_4_done) action_Odd_2_done) true)))
(assert (=> action_Even_5_done Even_c_done))

(declare-const Even_outcome Int)
(assert (= Even_outcome (ite (and Even_c_done Odd_c_done) (ite (= Even_c Odd_c) 10 (- 10)) (ite (and (not Even_c_done) Odd_c_done) (- 100) (- 100)))))

(declare-const Odd_outcome Int)
(assert (= Odd_outcome (ite (and Even_c_done Odd_c_done) (ite (= Even_c Odd_c) (- 10) 10) (ite (and (not Even_c_done) Odd_c_done) 10 (- 100)))))

(check-sat)
(get-model)
