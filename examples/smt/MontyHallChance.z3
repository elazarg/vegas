(declare-const Host_goat Int)
(declare-const Host_goat_done Bool)
(assert (or (= Host_goat 0) (= Host_goat 1) (= Host_goat 2)))

(declare-const Guest_d Int)
(declare-const Guest_d_done Bool)
(assert (or (= Guest_d 0) (= Guest_d 1) (= Guest_d 2)))

(declare-const Host_car Int)
(declare-const Host_car_done Bool)
(assert (or (= Host_car 0) (= Host_car 1) (= Host_car 2)))

(declare-const Guest_switch Bool)
(declare-const Guest_switch_done Bool)

(declare-const action_Host_0_done Bool)
(assert (=> action_Host_0_done (and true true)))

(declare-const action_Guest_1_done Bool)
(assert (=> action_Guest_1_done (and (and true action_Host_0_done) true)))

(declare-const action_Host_2_done Bool)
(assert (=> action_Host_2_done (and (and true action_Guest_1_done) true)))
(assert (=> action_Host_2_done Host_car_done))

(declare-const action_Guest_3_done Bool)
(assert (=> action_Guest_3_done (and (and true action_Host_2_done) true)))
(assert (=> action_Guest_3_done Guest_d_done))

(declare-const action_Host_4_done Bool)
(assert (=> action_Host_4_done (and (and (and true action_Guest_3_done) action_Host_2_done) (and (not (= Host_goat Guest_d)) (not (= Host_goat Host_car))))))
(assert (=> action_Host_4_done Host_goat_done))

(declare-const action_Guest_5_done Bool)
(assert (=> action_Guest_5_done (and (and true action_Host_4_done) true)))
(assert (=> action_Guest_5_done Guest_switch_done))

(declare-const action_Host_6_done Bool)
(assert (=> action_Host_6_done (and (and (and true action_Guest_5_done) action_Host_2_done) true)))
(assert (=> action_Host_6_done Host_car_done))

(declare-const Guest_outcome Int)
(assert (= Guest_outcome (ite (and (and Host_car_done Host_goat_done) Guest_switch_done) (ite (= (not (= Guest_d Host_car)) Guest_switch) 20 (- 20)) (ite (or (not Host_car_done) (not Host_goat_done)) 20 (- 100)))))

(declare-const Host_outcome Int)
(assert (= Host_outcome (ite (and (and Host_car_done Host_goat_done) Guest_switch_done) 0 (ite (or (not Host_car_done) (not Host_goat_done)) (- 100) 0))))

(check-sat)
(get-model)
