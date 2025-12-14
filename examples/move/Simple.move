module simple::simple {
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
        role_B: address,
        joined_A: bool,
        joined_B: bool,
        timeout_ms: u64,
        last_ts_ms: u64,
        bailed_A: bool,
        bailed_B: bool,
        pot: balance::Balance<Asset>,
        finalized: bool,
        claim_amount_A: u64,
        claimed_A: bool,
        claim_amount_B: u64,
        claimed_B: bool,
        A_c: bool,
        done_A_c: bool,
        A_c_hidden: vector<u8>,
        done_A_c_hidden: bool,
        B_c: bool,
        done_B_c: bool,
        action_A_0_done: bool,
        action_B_1_done: bool,
        action_A_2_done: bool,
        action_B_3_done: bool,
        action_A_4_done: bool,
    }

    fun init(ctx: &mut tx_context::TxContext) {
    }

    public entry fun create_game<Asset>(timeout_ms: u64, ctx: &mut tx_context::TxContext) {
        let instance = Instance<Asset> { id: object::new(ctx), role_A: @0x0, role_B: @0x0, joined_A: false, joined_B: false, timeout_ms: timeout_ms, last_ts_ms: 0, bailed_A: false, bailed_B: false, pot: balance::zero<Asset>(), finalized: false, claim_amount_A: 0, claimed_A: false, claim_amount_B: 0, claimed_B: false, A_c: false, done_A_c: false, A_c_hidden: vector::empty<u8>(), done_A_c_hidden: false, B_c: false, done_B_c: false, action_A_0_done: false, action_B_1_done: false, action_A_2_done: false, action_B_3_done: false, action_A_4_done: false };
        transfer::share_object(instance);
    }

    public entry fun join_A<Asset>(instance: &mut Instance<Asset>, payment: coin::Coin<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(!instance.joined_A, 100);
        assert!(!instance.finalized, 117);
        assert!((coin::value<Asset>(&payment) == 6), 112);
        instance.role_A = tx_context::sender(ctx);
        instance.joined_A = true;
        balance::join<Asset>(&mut instance.pot, coin::into_balance<Asset>(payment));
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun join_B<Asset>(instance: &mut Instance<Asset>, payment: coin::Coin<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(!instance.joined_B, 100);
        assert!(!instance.finalized, 117);
        assert!((coin::value<Asset>(&payment) == 6), 112);
        instance.role_B = tx_context::sender(ctx);
        instance.joined_B = true;
        balance::join<Asset>(&mut instance.pot, coin::into_balance<Asset>(payment));
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun timeout_A<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.joined_A, 113);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_A = true;
        };
    }

    public entry fun timeout_B<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.joined_B, 113);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_B = true;
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

    public entry fun move_B_1<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!((tx_context::sender(ctx) == instance.role_B), 101);
        assert!(instance.joined_B, 113);
        assert!(!instance.bailed_B, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_B = true;
            return
        };
        assert!(!instance.action_B_1_done, 102);
        assert!((instance.action_A_0_done || instance.bailed_A), 103);
        instance.action_B_1_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_A_2<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, hidden_c: vector<u8>) {
        assert!((tx_context::sender(ctx) == instance.role_A), 101);
        assert!(instance.joined_A, 113);
        assert!(!instance.bailed_A, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_A = true;
            return
        };
        assert!(!instance.action_A_2_done, 102);
        assert!((instance.action_B_1_done || instance.bailed_B), 103);
        assert!((vector::length<u8>(&hidden_c) == 32), 115);
        instance.A_c_hidden = hidden_c;
        instance.done_A_c_hidden = true;
        instance.action_A_2_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_B_3<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, c: bool) {
        assert!((tx_context::sender(ctx) == instance.role_B), 101);
        assert!(instance.joined_B, 113);
        assert!(!instance.bailed_B, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_B = true;
            return
        };
        assert!(!instance.action_B_3_done, 102);
        assert!((instance.action_A_2_done || instance.bailed_A), 103);
        instance.B_c = c;
        instance.done_B_c = true;
        instance.action_B_3_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_A_4<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, c: bool, salt: u64) {
        assert!((tx_context::sender(ctx) == instance.role_A), 101);
        assert!(instance.joined_A, 113);
        assert!(!instance.bailed_A, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_A = true;
            return
        };
        assert!(!instance.action_A_4_done, 102);
        assert!((instance.action_B_3_done || instance.bailed_B), 103);
        assert!(instance.action_A_2_done, 103);
        let mut data_c = bcs::to_bytes<bool>(&c);
        let salt_bytes_c = bcs::to_bytes<u64>(&salt);
        vector::append<u8>(&mut data_c, salt_bytes_c);
        assert!((hash::keccak256(&data_c) == instance.A_c_hidden), 106);
        instance.A_c = c;
        instance.done_A_c = true;
        instance.action_A_4_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun finalize<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!((instance.action_A_4_done || (clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))), 107);
        assert!(!instance.finalized, 108);
        let mut total_payout: u64 = 0;
        if ((instance.joined_A && instance.joined_B)) {
            instance.claim_amount_A = if ((!instance.done_A_c && !instance.done_B_c)) { 6 } else { if (!instance.done_A_c) { 1 } else { if (!instance.done_B_c) { 11 } else { if ((instance.A_c != instance.B_c)) { 9 } else { 3 } } } };
            total_payout = (total_payout + if ((!instance.done_A_c && !instance.done_B_c)) { 6 } else { if (!instance.done_A_c) { 1 } else { if (!instance.done_B_c) { 11 } else { if ((instance.A_c != instance.B_c)) { 9 } else { 3 } } } });
            instance.claim_amount_B = if ((!instance.done_A_c && !instance.done_B_c)) { 6 } else { if (!instance.done_A_c) { 11 } else { if (!instance.done_B_c) { 1 } else { if ((instance.A_c == instance.B_c)) { 9 } else { 3 } } } };
            total_payout = (total_payout + if ((!instance.done_A_c && !instance.done_B_c)) { 6 } else { if (!instance.done_A_c) { 11 } else { if (!instance.done_B_c) { 1 } else { if ((instance.A_c == instance.B_c)) { 9 } else { 3 } } } });
        } else {
            if (instance.joined_A) {
                instance.claim_amount_A = 6;
                total_payout = (total_payout + 6);
            };
            if (instance.joined_B) {
                instance.claim_amount_B = 6;
                total_payout = (total_payout + 6);
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

    public entry fun claim_B<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.finalized, 110);
        assert!(!instance.claimed_B, 111);
        instance.claimed_B = true;
        let amount: u64 = instance.claim_amount_B;
        if ((amount > 0)) {
            let payout_coin = coin::take<Asset>(&mut instance.pot, amount, ctx);
            transfer::public_transfer<Asset>(payout_coin, instance.role_B);
        };
    }

    public entry fun sweep<Asset>(instance: &mut Instance<Asset>, ctx: &mut tx_context::TxContext) {
        assert!(instance.finalized, 116);
        assert!((instance.claimed_A && instance.claimed_B), 118);
        let val: u64 = balance::value<Asset>(&instance.pot);
        if ((val > 0)) {
            let payout_coin = coin::take<Asset>(&mut instance.pot, val, ctx);
            transfer::public_transfer<Asset>(payout_coin, tx_context::sender(ctx));
        };
    }

}
