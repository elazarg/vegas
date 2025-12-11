(declare-const Alice_c Int)
(declare-const Alice_c_done Bool)
(assert (or (= Alice_c 1) (= Alice_c 2) (= Alice_c 3)))

(declare-const Bob_c Int)
(declare-const Bob_c_done Bool)
(assert (or (= Bob_c 1) (= Bob_c 2) (= Bob_c 3)))

(declare-const Issuer_c Int)
(declare-const Issuer_c_done Bool)
(assert (or (= Issuer_c 1) (= Issuer_c 2) (= Issuer_c 3)))

(declare-const action_Issuer_1_done Bool)
(assert (=> action_Issuer_1_done (and true true)))
(assert (=> action_Issuer_1_done Issuer_c_done))

(declare-const action_Issuer_2_done Bool)
(assert (=> action_Issuer_2_done (and (and (and (and true action_Issuer_1_done) action_Alice_3_done) action_Bob_5_done) true)))
(assert (=> action_Issuer_2_done Issuer_c_done))

(declare-const action_Alice_3_done Bool)
(assert (=> action_Alice_3_done (and true true)))
(assert (=> action_Alice_3_done Alice_c_done))

(declare-const action_Alice_4_done Bool)
(assert (=> action_Alice_4_done (and (and (and (and true action_Alice_3_done) action_Issuer_1_done) action_Bob_5_done) true)))
(assert (=> action_Alice_4_done Alice_c_done))

(declare-const action_Bob_5_done Bool)
(assert (=> action_Bob_5_done (and true true)))
(assert (=> action_Bob_5_done Bob_c_done))

(declare-const action_Bob_6_done Bool)
(assert (=> action_Bob_6_done (and (and (and (and true action_Bob_5_done) action_Issuer_1_done) action_Alice_3_done) true)))
(assert (=> action_Bob_6_done Bob_c_done))

(declare-const Bob_outcome Int)
(assert (= Bob_outcome (ite (or (not Alice_c_done) (not Bob_c_done)) 0 (ite (not Issuer_c_done) 0 (ite (= (* (div (+ (+ Issuer_c Alice_c) Bob_c) 3) 3) (+ (+ Issuer_c Alice_c) Bob_c)) 0 (ite (= (* (div (+ (+ Issuer_c Alice_c) Bob_c) 3) 3) (- (+ (+ Issuer_c Alice_c) Bob_c) 1)) 30 0))))))

(declare-const Issuer_outcome Int)
(assert (= Issuer_outcome (ite (or (not Alice_c_done) (not Bob_c_done)) 30 (ite (not Issuer_c_done) 0 (ite (= (* (div (+ (+ Issuer_c Alice_c) Bob_c) 3) 3) (+ (+ Issuer_c Alice_c) Bob_c)) 0 (ite (= (* (div (+ (+ Issuer_c Alice_c) Bob_c) 3) 3) (- (+ (+ Issuer_c Alice_c) Bob_c) 1)) 0 30))))))

(declare-const Alice_outcome Int)
(assert (= Alice_outcome (ite (or (not Alice_c_done) (not Bob_c_done)) 0 (ite (not Issuer_c_done) 30 (ite (= (* (div (+ (+ Issuer_c Alice_c) Bob_c) 3) 3) (+ (+ Issuer_c Alice_c) Bob_c)) 30 (ite (= (* (div (+ (+ Issuer_c Alice_c) Bob_c) 3) 3) (- (+ (+ Issuer_c Alice_c) Bob_c) 1)) 0 0))))))

(check-sat)
(get-model)
