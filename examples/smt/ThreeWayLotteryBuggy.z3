(declare-const Alice_c Int)
(declare-const Alice_c_done Bool)
(assert (or (= Alice_c 1) (= Alice_c 2) (= Alice_c 3)))

(declare-const Bob_c Int)
(declare-const Bob_c_done Bool)
(assert (or (= Bob_c 1) (= Bob_c 2) (= Bob_c 3)))

(declare-const Issuer_c Int)
(declare-const Issuer_c_done Bool)
(assert (or (= Issuer_c 1) (= Issuer_c 2) (= Issuer_c 3)))

(declare-const action_Issuer_0_done Bool)
(assert (=> action_Issuer_0_done (and true true)))

(declare-const action_Alice_1_done Bool)
(assert (=> action_Alice_1_done (and (and true action_Issuer_0_done) true)))

(declare-const action_Bob_2_done Bool)
(assert (=> action_Bob_2_done (and (and true action_Alice_1_done) true)))

(declare-const action_Issuer_4_done Bool)
(assert (=> action_Issuer_4_done (and (and true action_Bob_2_done) true)))
(assert (=> action_Issuer_4_done Issuer_c_done))

(declare-const action_Issuer_5_done Bool)
(assert (=> action_Issuer_5_done (and (and (and (and (and true action_Bob_2_done) action_Issuer_4_done) action_Alice_6_done) action_Bob_8_done) true)))
(assert (=> action_Issuer_5_done Issuer_c_done))

(declare-const action_Alice_6_done Bool)
(assert (=> action_Alice_6_done (and (and true action_Bob_2_done) true)))
(assert (=> action_Alice_6_done Alice_c_done))

(declare-const action_Alice_7_done Bool)
(assert (=> action_Alice_7_done (and (and (and (and (and true action_Bob_2_done) action_Alice_6_done) action_Issuer_4_done) action_Bob_8_done) true)))
(assert (=> action_Alice_7_done Alice_c_done))

(declare-const action_Bob_8_done Bool)
(assert (=> action_Bob_8_done (and (and true action_Bob_2_done) true)))
(assert (=> action_Bob_8_done Bob_c_done))

(declare-const action_Bob_9_done Bool)
(assert (=> action_Bob_9_done (and (and (and (and (and true action_Bob_2_done) action_Bob_8_done) action_Issuer_4_done) action_Alice_6_done) true)))
(assert (=> action_Bob_9_done Bob_c_done))

(declare-const Bob_outcome Int)
(assert (= Bob_outcome (ite (or (not Alice_c_done) (not Bob_c_done)) (- 10) (ite (not Issuer_c_done) (- 10) (ite (= Alice_c Bob_c) (- 10) (ite (= (* (div (+ (+ Alice_c Bob_c) Issuer_c) 2) 2) (+ (+ Alice_c Bob_c) Issuer_c)) (- 10) 20))))))

(declare-const Issuer_outcome Int)
(assert (= Issuer_outcome (ite (or (not Alice_c_done) (not Bob_c_done)) 20 (ite (not Issuer_c_done) (- 10) (ite (= Alice_c Bob_c) 20 (ite (= (* (div (+ (+ Alice_c Bob_c) Issuer_c) 2) 2) (+ (+ Alice_c Bob_c) Issuer_c)) (- 10) (- 10)))))))

(declare-const Alice_outcome Int)
(assert (= Alice_outcome (ite (or (not Alice_c_done) (not Bob_c_done)) (- 10) (ite (not Issuer_c_done) 20 (ite (= Alice_c Bob_c) (- 10) (ite (= (* (div (+ (+ Alice_c Bob_c) Issuer_c) 2) 2) (+ (+ Alice_c Bob_c) Issuer_c)) 20 (- 10)))))))

(check-sat)
(get-model)
