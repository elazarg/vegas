(declare-const Race_winner Int)
(declare-const Race_winner_done Bool)
(assert (or (= Race_winner 1) (= Race_winner 2) (= Race_winner 3)))

(declare-const Gambler_bet Int)
(declare-const Gambler_bet_done Bool)
(assert (or (= Gambler_bet 1) (= Gambler_bet 2) (= Gambler_bet 3)))

(declare-const action_Race_0_done Bool)
(assert (=> action_Race_0_done (and true true)))

(declare-const action_Gambler_1_done Bool)
(assert (=> action_Gambler_1_done (and (and true action_Race_0_done) true)))
(assert (=> action_Gambler_1_done Gambler_bet_done))

(declare-const action_Race_2_done Bool)
(assert (=> action_Race_2_done (and (and true action_Gambler_1_done) true)))
(assert (=> action_Race_2_done Race_winner_done))

(declare-const Gambler_outcome Int)
(assert (= Gambler_outcome (ite (or (not Race_winner_done) (= Race_winner Gambler_bet)) 20 0)))

(declare-const Race_outcome Int)
(assert (= Race_outcome (ite (or (not Race_winner_done) (= Race_winner Gambler_bet)) 0 20)))

(check-sat)
(get-model)
