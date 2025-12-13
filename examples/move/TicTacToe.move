module tictactoe::tictactoe {
    use sui::balance;
    use std::bcs;
    use sui::clock;
    use sui::coin;
    use sui::event;
    use sui::hash;
    use sui::object;
    use sui::transfer;
    use sui::tx_context;
    use std::vector;

    public struct Instance<phantom Asset> has key {
        id: object::UID,
        role_X: address,
        role_O: address,
        joined_X: bool,
        joined_O: bool,
        timeout_ms: u64,
        last_ts_ms: u64,
        bailed_X: bool,
        bailed_O: bool,
        pot: balance::Balance<Asset>,
        finalized: bool,
        claim_amount_X: u64,
        claimed_X: bool,
        claim_amount_O: u64,
        claimed_O: bool,
        X_c1: u64,
        done_X_c1: bool,
        O_c1: u64,
        done_O_c1: bool,
        X_c2: u64,
        done_X_c2: bool,
        O_c2: u64,
        done_O_c2: bool,
        X_c3: u64,
        done_X_c3: bool,
        O_c3: u64,
        done_O_c3: bool,
        X_c4: u64,
        done_X_c4: bool,
        O_c4: u64,
        done_O_c4: bool,
        action_X_0_done: bool,
        action_O_1_done: bool,
        action_X_2_done: bool,
        action_O_3_done: bool,
        action_X_4_done: bool,
        action_O_5_done: bool,
        action_X_6_done: bool,
        action_O_7_done: bool,
        action_X_8_done: bool,
        action_O_9_done: bool,
    }

    fun init(ctx: &mut tx_context::TxContext) {
    }

    public entry fun create_game<Asset>(timeout_ms: u64, ctx: &mut tx_context::TxContext) {
        let instance = Instance<Asset> { id: object::new(ctx), role_X: 0x0, role_O: 0x0, joined_X: false, joined_O: false, timeout_ms: timeout_ms, last_ts_ms: 0, bailed_X: false, bailed_O: false, pot: balance::zero<Asset>(), finalized: false, claim_amount_X: 0, claimed_X: false, claim_amount_O: 0, claimed_O: false, X_c1: 0, done_X_c1: false, O_c1: 0, done_O_c1: false, X_c2: 0, done_X_c2: false, O_c2: 0, done_O_c2: false, X_c3: 0, done_X_c3: false, O_c3: 0, done_O_c3: false, X_c4: 0, done_X_c4: false, O_c4: 0, done_O_c4: false, action_X_0_done: false, action_O_1_done: false, action_X_2_done: false, action_O_3_done: false, action_X_4_done: false, action_O_5_done: false, action_X_6_done: false, action_O_7_done: false, action_X_8_done: false, action_O_9_done: false };
        transfer::share_object<Asset>(instance);
    }

    public entry fun join_X<Asset>(instance: &mut Instance<Asset>, payment: coin::Coin<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(!instance.joined_X, 100);
        instance.role_X = tx_context::sender(ctx);
        instance.joined_X = true;
        balance::join<Asset>(&mut instance.pot, coin::into_balance<Asset>(payment));
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun join_O<Asset>(instance: &mut Instance<Asset>, payment: coin::Coin<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(!instance.joined_O, 100);
        instance.role_O = tx_context::sender(ctx);
        instance.joined_O = true;
        balance::join<Asset>(&mut instance.pot, coin::into_balance<Asset>(payment));
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_X_0<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!((tx_context::sender(ctx) == instance.role_X), 101);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_X = true;
        };
        assert!(!instance.action_X_0_done, 102);
        instance.action_X_0_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_O_1<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!((tx_context::sender(ctx) == instance.role_O), 101);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_O = true;
        };
        assert!(!instance.action_O_1_done, 102);
        assert!(instance.action_X_0_done, 103);
        instance.action_O_1_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_X_2<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, c1: u64) {
        assert!((tx_context::sender(ctx) == instance.role_X), 101);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_X = true;
        };
        assert!(!instance.action_X_2_done, 102);
        assert!(instance.action_O_1_done, 103);
        assert!((((c1 == 0) || (c1 == 1)) || (c1 == 4)), 104);
        instance.X_c1 = c1;
        instance.done_X_c1 = true;
        instance.action_X_2_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_O_3<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, c1: u64) {
        assert!((tx_context::sender(ctx) == instance.role_O), 101);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_O = true;
        };
        assert!(!instance.action_O_3_done, 102);
        assert!(instance.action_X_2_done, 103);
        assert!((((((c1 == 1) || (c1 == 3)) || (c1 == 4)) || (c1 == 5)) || (c1 == 9)), 104);
        assert!((instance.X_c1 != c1), 105);
        instance.O_c1 = c1;
        instance.done_O_c1 = true;
        instance.action_O_3_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_X_4<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, c2: u64) {
        assert!((tx_context::sender(ctx) == instance.role_X), 101);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_X = true;
        };
        assert!(!instance.action_X_4_done, 102);
        assert!(instance.action_O_3_done, 103);
        assert!(instance.action_X_2_done, 103);
        assert!((((((((((c2 == 0) || (c2 == 1)) || (c2 == 2)) || (c2 == 3)) || (c2 == 4)) || (c2 == 5)) || (c2 == 6)) || (c2 == 7)) || (c2 == 8)), 104);
        assert!((((instance.X_c1 != instance.O_c1) && (instance.X_c1 != c2)) && (instance.O_c1 != c2)), 105);
        instance.X_c2 = c2;
        instance.done_X_c2 = true;
        instance.action_X_4_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_O_5<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, c2: u64) {
        assert!((tx_context::sender(ctx) == instance.role_O), 101);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_O = true;
        };
        assert!(!instance.action_O_5_done, 102);
        assert!(instance.action_X_4_done, 103);
        assert!(instance.action_X_2_done, 103);
        assert!(instance.action_O_3_done, 103);
        assert!((((((((((c2 == 0) || (c2 == 1)) || (c2 == 2)) || (c2 == 3)) || (c2 == 4)) || (c2 == 5)) || (c2 == 6)) || (c2 == 7)) || (c2 == 8)), 104);
        assert!(((((((instance.X_c1 != instance.O_c1) && (instance.X_c1 != instance.X_c2)) && (instance.X_c1 != c2)) && (instance.O_c1 != instance.X_c2)) && (instance.O_c1 != c2)) && (instance.X_c2 != c2)), 105);
        instance.O_c2 = c2;
        instance.done_O_c2 = true;
        instance.action_O_5_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_X_6<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, c3: u64) {
        assert!((tx_context::sender(ctx) == instance.role_X), 101);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_X = true;
        };
        assert!(!instance.action_X_6_done, 102);
        assert!(instance.action_O_5_done, 103);
        assert!(instance.action_X_2_done, 103);
        assert!(instance.action_O_3_done, 103);
        assert!(instance.action_X_4_done, 103);
        assert!((((((((((c3 == 0) || (c3 == 1)) || (c3 == 2)) || (c3 == 3)) || (c3 == 4)) || (c3 == 5)) || (c3 == 6)) || (c3 == 7)) || (c3 == 8)), 104);
        assert!(((((((((((instance.X_c1 != instance.O_c1) && (instance.X_c1 != instance.X_c2)) && (instance.X_c1 != instance.O_c2)) && (instance.X_c1 != c3)) && (instance.O_c1 != instance.X_c2)) && (instance.O_c1 != instance.O_c2)) && (instance.O_c1 != c3)) && (instance.X_c2 != instance.O_c2)) && (instance.X_c2 != c3)) && (instance.O_c2 != c3)), 105);
        instance.X_c3 = c3;
        instance.done_X_c3 = true;
        instance.action_X_6_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_O_7<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, c3: u64) {
        assert!((tx_context::sender(ctx) == instance.role_O), 101);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_O = true;
        };
        assert!(!instance.action_O_7_done, 102);
        assert!(instance.action_X_6_done, 103);
        assert!(instance.action_X_2_done, 103);
        assert!(instance.action_O_3_done, 103);
        assert!(instance.action_X_4_done, 103);
        assert!(instance.action_O_5_done, 103);
        assert!((((((((((c3 == 0) || (c3 == 1)) || (c3 == 2)) || (c3 == 3)) || (c3 == 4)) || (c3 == 5)) || (c3 == 6)) || (c3 == 7)) || (c3 == 8)), 104);
        assert!((((((((((((((((instance.X_c1 != instance.O_c1) && (instance.X_c1 != instance.X_c2)) && (instance.X_c1 != instance.O_c2)) && (instance.X_c1 != instance.X_c3)) && (instance.X_c1 != c3)) && (instance.O_c1 != instance.X_c2)) && (instance.O_c1 != instance.O_c2)) && (instance.O_c1 != instance.X_c3)) && (instance.O_c1 != c3)) && (instance.X_c2 != instance.O_c2)) && (instance.X_c2 != instance.X_c3)) && (instance.X_c2 != c3)) && (instance.O_c2 != instance.X_c3)) && (instance.O_c2 != c3)) && (instance.X_c3 != c3)), 105);
        instance.O_c3 = c3;
        instance.done_O_c3 = true;
        instance.action_O_7_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_X_8<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, c4: u64) {
        assert!((tx_context::sender(ctx) == instance.role_X), 101);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_X = true;
        };
        assert!(!instance.action_X_8_done, 102);
        assert!(instance.action_O_7_done, 103);
        assert!(instance.action_X_2_done, 103);
        assert!(instance.action_O_3_done, 103);
        assert!(instance.action_X_4_done, 103);
        assert!(instance.action_O_5_done, 103);
        assert!(instance.action_X_6_done, 103);
        assert!((((((((((c4 == 0) || (c4 == 1)) || (c4 == 2)) || (c4 == 3)) || (c4 == 4)) || (c4 == 5)) || (c4 == 6)) || (c4 == 7)) || (c4 == 8)), 104);
        assert!((((((((((((((((((((((instance.X_c1 != instance.O_c1) && (instance.X_c1 != instance.X_c2)) && (instance.X_c1 != instance.O_c2)) && (instance.X_c1 != instance.X_c3)) && (instance.X_c1 != instance.O_c3)) && (instance.X_c1 != c4)) && (instance.O_c1 != instance.X_c2)) && (instance.O_c1 != instance.O_c2)) && (instance.O_c1 != instance.X_c3)) && (instance.O_c1 != instance.O_c3)) && (instance.O_c1 != c4)) && (instance.X_c2 != instance.O_c2)) && (instance.X_c2 != instance.X_c3)) && (instance.X_c2 != instance.O_c3)) && (instance.X_c2 != c4)) && (instance.O_c2 != instance.X_c3)) && (instance.O_c2 != instance.O_c3)) && (instance.O_c2 != c4)) && (instance.X_c3 != instance.O_c3)) && (instance.X_c3 != c4)) && (instance.O_c3 != c4)), 105);
        instance.X_c4 = c4;
        instance.done_X_c4 = true;
        instance.action_X_8_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_O_9<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, c4: u64) {
        assert!((tx_context::sender(ctx) == instance.role_O), 101);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_O = true;
        };
        assert!(!instance.action_O_9_done, 102);
        assert!(instance.action_X_8_done, 103);
        assert!(instance.action_X_2_done, 103);
        assert!(instance.action_O_3_done, 103);
        assert!(instance.action_X_4_done, 103);
        assert!(instance.action_O_5_done, 103);
        assert!(instance.action_X_6_done, 103);
        assert!(instance.action_O_7_done, 103);
        assert!((((((((((c4 == 0) || (c4 == 1)) || (c4 == 2)) || (c4 == 3)) || (c4 == 4)) || (c4 == 5)) || (c4 == 6)) || (c4 == 7)) || (c4 == 8)), 104);
        assert!(((((((((((((((((((((((((((((instance.X_c1 != instance.O_c1) && (instance.X_c1 != instance.X_c2)) && (instance.X_c1 != instance.O_c2)) && (instance.X_c1 != instance.X_c3)) && (instance.X_c1 != instance.O_c3)) && (instance.X_c1 != instance.X_c4)) && (instance.X_c1 != c4)) && (instance.O_c1 != instance.X_c2)) && (instance.O_c1 != instance.O_c2)) && (instance.O_c1 != instance.X_c3)) && (instance.O_c1 != instance.O_c3)) && (instance.O_c1 != instance.X_c4)) && (instance.O_c1 != c4)) && (instance.X_c2 != instance.O_c2)) && (instance.X_c2 != instance.X_c3)) && (instance.X_c2 != instance.O_c3)) && (instance.X_c2 != instance.X_c4)) && (instance.X_c2 != c4)) && (instance.O_c2 != instance.X_c3)) && (instance.O_c2 != instance.O_c3)) && (instance.O_c2 != instance.X_c4)) && (instance.O_c2 != c4)) && (instance.X_c3 != instance.O_c3)) && (instance.X_c3 != instance.X_c4)) && (instance.X_c3 != c4)) && (instance.O_c3 != instance.X_c4)) && (instance.O_c3 != c4)) && (instance.X_c4 != c4)), 105);
        instance.O_c4 = c4;
        instance.done_O_c4 = true;
        instance.action_O_9_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun finalize<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.action_O_9_done, 107);
        assert!(!instance.finalized, 108);
        let total_payout: u64 = 0;
        instance.claim_amount_X = 100;
        total_payout = (total_payout + 100);
        instance.claim_amount_O = 100;
        total_payout = (total_payout + 100);
        assert!((total_payout <= balance::value<Asset>(&instance.pot)), 109);
        instance.finalized = true;
    }

    public entry fun claim_X<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.finalized, 110);
        assert!(!instance.claimed_X, 111);
        instance.claimed_X = true;
        let amount: u64 = instance.claim_amount_X;
        if ((amount > 0)) {
            let payout_coin = coin::take<Asset>(&mut instance.pot, amount, ctx);
            transfer::public_transfer<Asset>(payout_coin, tx_context::sender(ctx));
        };
    }

    public entry fun claim_O<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.finalized, 110);
        assert!(!instance.claimed_O, 111);
        instance.claimed_O = true;
        let amount: u64 = instance.claim_amount_O;
        if ((amount > 0)) {
            let payout_coin = coin::take<Asset>(&mut instance.pot, amount, ctx);
            transfer::public_transfer<Asset>(payout_coin, tx_context::sender(ctx));
        };
    }

}
