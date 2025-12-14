module trivial1::trivial1 {
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
        role_A: address,
        joined_A: bool,
        timeout_ms: u64,
        last_ts_ms: u64,
        bailed_A: bool,
        pot: balance::Balance<Asset>,
        finalized: bool,
        claim_amount_A: u64,
        claimed_A: bool,
        action_A_0_done: bool,
    }

    fun init(ctx: &mut tx_context::TxContext) {
    }

    public entry fun create_game<Asset>(timeout_ms: u64, ctx: &mut tx_context::TxContext) {
        let instance = Instance<Asset> { id: object::new(ctx), role_A: 0x0, joined_A: false, timeout_ms: timeout_ms, last_ts_ms: 0, bailed_A: false, pot: balance::zero<Asset>(), finalized: false, claim_amount_A: 0, claimed_A: false, action_A_0_done: false };
        transfer::share_object(instance);
    }

    public entry fun join_A<Asset>(instance: &mut Instance<Asset>, payment: coin::Coin<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(!instance.joined_A, 100);
        assert!((coin::value<Asset>(&payment) == 10), 112);
        instance.role_A = tx_context::sender(ctx);
        instance.joined_A = true;
        balance::join<Asset>(&mut instance.pot, coin::into_balance<Asset>(payment));
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun timeout_A<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_A = true;
        };
    }

    public entry fun move_A_0<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!((tx_context::sender(ctx) == instance.role_A), 101);
        assert!(instance.joined_A, 113);
        assert!(!instance.bailed_A, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_A = true;
            return
        };
        assert!(!instance.action_A_0_done, 102);
        instance.action_A_0_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun finalize<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!((instance.action_A_0_done || (clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))), 107);
        assert!(!instance.finalized, 108);
        let mut total_payout: u64 = 0;
        if (instance.joined_A) {
            instance.claim_amount_A = 10;
            total_payout = (total_payout + 10);
        } else {
            if (instance.joined_A) {
                instance.claim_amount_A = 10;
                total_payout = (total_payout + 10);
            };
        }
        assert!((total_payout <= balance::value<Asset>(&instance.pot)), 109);
        instance.finalized = true;
    }

    public entry fun claim_A<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.finalized, 110);
        assert!(!instance.claimed_A, 111);
        instance.claimed_A = true;
        let amount: u64 = instance.claim_amount_A;
        if ((amount > 0)) {
            let payout_coin = coin::take<Asset>(&mut instance.pot, amount, ctx);
            transfer::public_transfer<Asset>(payout_coin, instance.role_A);
        };
    }

    public entry fun sweep<Asset>(instance: &mut Instance<Asset>, ctx: &mut tx_context::TxContext) {
        assert!(instance.finalized, 116);
        let val: u64 = balance::value<Asset>(&instance.pot);
        if ((val > 0)) {
            let payout_coin = coin::take<Asset>(&mut instance.pot, val, ctx);
            transfer::public_transfer<Asset>(payout_coin, tx_context::sender(ctx));
        };
    }

}
