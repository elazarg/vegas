module puzzle::puzzle {
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
        id: sui::object::UID,
        role_Q: address,
        role_A: address,
        joined_Q: bool,
        joined_A: bool,
        timeout_ms: u64,
        last_ts_ms: u64,
        bailed_Q: bool,
        bailed_A: bool,
        pot: sui::balance::Balance<Asset>,
        finalized: bool,
        claim_amount_Q: u64,
        claimed_Q: bool,
        claim_amount_A: u64,
        claimed_A: bool,
        Q_x: u64,
        done_Q_x: bool,
        A_p: u64,
        done_A_p: bool,
        A_q: u64,
        done_A_q: bool,
        action_Q_0_done: bool,
        action_A_1_done: bool,
    }

    fun init(ctx: &mut sui::tx_context::TxContext) {
    }

    public entry fun create_game<Asset>(timeout_ms: u64, ctx: &mut sui::tx_context::TxContext) {
        let instance = Instance<Asset> { id: sui::object::new(ctx), role_Q: 0x0, role_A: 0x0, joined_Q: false, joined_A: false, timeout_ms: timeout_ms, last_ts_ms: 0, bailed_Q: false, bailed_A: false, pot: sui::balance::zero<Asset>(), finalized: false, claim_amount_Q: 0, claimed_Q: false, claim_amount_A: 0, claimed_A: false, Q_x: 0, done_Q_x: false, A_p: 0, done_A_p: false, A_q: 0, done_A_q: false, action_Q_0_done: false, action_A_1_done: false };
        sui::transfer::share_object<Asset>(instance);
    }

    public entry fun join_Q<Asset>(instance: &mut Instance<Asset>, payment: sui::coin::Coin<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext) {
        assert!(!instance.joined_Q, 100);
        instance.role_Q = sui::tx_context::sender(ctx);
        instance.joined_Q = true;
        sui::balance::join<Asset>(&mut instance.pot, sui::coin::into_balance<Asset>(payment));
        instance.last_ts_ms = sui::clock::timestamp_ms(clock);
    }

    public entry fun join_A<Asset>(instance: &mut Instance<Asset>, payment: sui::coin::Coin<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext) {
        assert!(!instance.joined_A, 100);
        instance.role_A = sui::tx_context::sender(ctx);
        instance.joined_A = true;
        sui::balance::join<Asset>(&mut instance.pot, sui::coin::into_balance<Asset>(payment));
        instance.last_ts_ms = sui::clock::timestamp_ms(clock);
    }

    public entry fun move_Q_0<Asset>(instance: &mut Instance<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext, x: u64) {
        assert!((sui::tx_context::sender(ctx) == instance.role_Q), 101);
        if ((sui::clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Q = true;
        };
        assert!(!instance.action_Q_0_done, 102);
        instance.Q_x = x;
        instance.done_Q_x = true;
        instance.action_Q_0_done = true;
        instance.last_ts_ms = sui::clock::timestamp_ms(clock);
    }

    public entry fun move_A_1<Asset>(instance: &mut Instance<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext, p: u64, q: u64) {
        assert!((sui::tx_context::sender(ctx) == instance.role_A), 101);
        if ((sui::clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_A = true;
        };
        assert!(!instance.action_A_1_done, 102);
        assert!(instance.action_Q_0_done, 103);
        assert!(((((p * q) == instance.Q_x) && (p != 1)) && (q != 1)), 105);
        instance.A_p = p;
        instance.done_A_p = true;
        instance.A_q = q;
        instance.done_A_q = true;
        instance.action_A_1_done = true;
        instance.last_ts_ms = sui::clock::timestamp_ms(clock);
    }

    public entry fun finalize<Asset>(instance: &mut Instance<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext) {
        assert!(instance.action_A_1_done, 107);
        assert!(!instance.finalized, 108);
        let total_payout: u64 = 0;
        instance.claim_amount_Q = 0;
        total_payout = (total_payout + 0);
        instance.claim_amount_A = 100;
        total_payout = (total_payout + 100);
        assert!((total_payout <= sui::balance::value<Asset>(&instance.pot)), 109);
        instance.finalized = true;
    }

    public entry fun claim_Q<Asset>(instance: &mut Instance<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext) {
        assert!(instance.finalized, 110);
        assert!(!instance.claimed_Q, 111);
        instance.claimed_Q = true;
        let amount: u64 = instance.claim_amount_Q;
        if ((amount > 0)) {
            let payout_coin = sui::coin::take<Asset>(&mut instance.pot, amount, ctx);
            sui::transfer::public_transfer<Asset>(payout_coin, sui::tx_context::sender(ctx));
        };
    }

    public entry fun claim_A<Asset>(instance: &mut Instance<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext) {
        assert!(instance.finalized, 110);
        assert!(!instance.claimed_A, 111);
        instance.claimed_A = true;
        let amount: u64 = instance.claim_amount_A;
        if ((amount > 0)) {
            let payout_coin = sui::coin::take<Asset>(&mut instance.pot, amount, ctx);
            sui::transfer::public_transfer<Asset>(payout_coin, sui::tx_context::sender(ctx));
        };
    }

}
