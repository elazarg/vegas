module prisoners::prisoners {
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
        role_A: address,
        role_B: address,
        joined_A: bool,
        joined_B: bool,
        timeout_ms: u64,
        last_ts_ms: u64,
        bailed_A: bool,
        bailed_B: bool,
        pot: sui::balance::Balance<Asset>,
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
        B_c_hidden: vector<u8>,
        done_B_c_hidden: bool,
        action_A_0_done: bool,
        action_B_1_done: bool,
        action_A_3_done: bool,
        action_B_5_done: bool,
        action_A_4_done: bool,
        action_B_6_done: bool,
    }

    fun init(ctx: &mut sui::tx_context::TxContext) {
    }

    public entry fun create_game<Asset>(timeout_ms: u64, ctx: &mut sui::tx_context::TxContext) {
        let instance = Instance<Asset> { id: sui::object::new(ctx), role_A: 0x0, role_B: 0x0, joined_A: false, joined_B: false, timeout_ms: timeout_ms, last_ts_ms: 0, bailed_A: false, bailed_B: false, pot: sui::balance::zero<Asset>(), finalized: false, claim_amount_A: 0, claimed_A: false, claim_amount_B: 0, claimed_B: false, A_c: false, done_A_c: false, A_c_hidden: std::vector::empty<u8>(), done_A_c_hidden: false, B_c: false, done_B_c: false, B_c_hidden: std::vector::empty<u8>(), done_B_c_hidden: false, action_A_0_done: false, action_B_1_done: false, action_A_3_done: false, action_B_5_done: false, action_A_4_done: false, action_B_6_done: false };
        sui::transfer::share_object<Asset>(instance);
    }

    public entry fun join_A<Asset>(instance: &mut Instance<Asset>, payment: sui::coin::Coin<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext) {
        assert!(!instance.joined_A, 100);
        instance.role_A = sui::tx_context::sender(ctx);
        instance.joined_A = true;
        sui::balance::join<Asset>(&mut instance.pot, sui::coin::into_balance<Asset>(payment));
        instance.last_ts_ms = sui::clock::timestamp_ms(clock);
    }

    public entry fun join_B<Asset>(instance: &mut Instance<Asset>, payment: sui::coin::Coin<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext) {
        assert!(!instance.joined_B, 100);
        instance.role_B = sui::tx_context::sender(ctx);
        instance.joined_B = true;
        sui::balance::join<Asset>(&mut instance.pot, sui::coin::into_balance<Asset>(payment));
        instance.last_ts_ms = sui::clock::timestamp_ms(clock);
    }

    public entry fun move_A_0<Asset>(instance: &mut Instance<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext) {
        assert!((sui::tx_context::sender(ctx) == instance.role_A), 101);
        if ((sui::clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_A = true;
        };
        assert!(!instance.action_A_0_done, 102);
        instance.action_A_0_done = true;
        instance.last_ts_ms = sui::clock::timestamp_ms(clock);
    }

    public entry fun move_B_1<Asset>(instance: &mut Instance<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext) {
        assert!((sui::tx_context::sender(ctx) == instance.role_B), 101);
        if ((sui::clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_B = true;
        };
        assert!(!instance.action_B_1_done, 102);
        assert!(instance.action_A_0_done, 103);
        instance.action_B_1_done = true;
        instance.last_ts_ms = sui::clock::timestamp_ms(clock);
    }

    public entry fun move_A_2<Asset>(instance: &mut Instance<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext, hidden_c: vector<u8>) {
        assert!((sui::tx_context::sender(ctx) == instance.role_A), 101);
        if ((sui::clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_A = true;
        };
        assert!(!instance.action_A_3_done, 102);
        assert!(instance.action_B_1_done, 103);
        instance.A_c_hidden = hidden_c;
        instance.done_A_c_hidden = true;
        instance.action_A_3_done = true;
        instance.last_ts_ms = sui::clock::timestamp_ms(clock);
    }

    public entry fun move_B_4<Asset>(instance: &mut Instance<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext, hidden_c: vector<u8>) {
        assert!((sui::tx_context::sender(ctx) == instance.role_B), 101);
        if ((sui::clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_B = true;
        };
        assert!(!instance.action_B_5_done, 102);
        assert!(instance.action_B_1_done, 103);
        instance.B_c_hidden = hidden_c;
        instance.done_B_c_hidden = true;
        instance.action_B_5_done = true;
        instance.last_ts_ms = sui::clock::timestamp_ms(clock);
    }

    public entry fun move_A_3<Asset>(instance: &mut Instance<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext, c: bool, salt: u64) {
        assert!((sui::tx_context::sender(ctx) == instance.role_A), 101);
        if ((sui::clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_A = true;
        };
        assert!(!instance.action_A_4_done, 102);
        assert!(instance.action_B_1_done, 103);
        assert!(instance.action_A_3_done, 103);
        assert!(instance.action_B_5_done, 103);
        let data_c = std::bcs::to_bytes<bool>(&c);
        std::vector::append<u8>(&mut data_c, std::bcs::to_bytes<u64>(&salt));
        assert!((sui::hash::keccak256(&data_c) == instance.A_c_hidden), 106);
        instance.A_c = c;
        instance.done_A_c = true;
        instance.action_A_4_done = true;
        instance.last_ts_ms = sui::clock::timestamp_ms(clock);
    }

    public entry fun move_B_5<Asset>(instance: &mut Instance<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext, c: bool, salt: u64) {
        assert!((sui::tx_context::sender(ctx) == instance.role_B), 101);
        if ((sui::clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_B = true;
        };
        assert!(!instance.action_B_6_done, 102);
        assert!(instance.action_B_1_done, 103);
        assert!(instance.action_B_5_done, 103);
        assert!(instance.action_A_3_done, 103);
        let data_c = std::bcs::to_bytes<bool>(&c);
        std::vector::append<u8>(&mut data_c, std::bcs::to_bytes<u64>(&salt));
        assert!((sui::hash::keccak256(&data_c) == instance.B_c_hidden), 106);
        instance.B_c = c;
        instance.done_B_c = true;
        instance.action_B_6_done = true;
        instance.last_ts_ms = sui::clock::timestamp_ms(clock);
    }

    public entry fun finalize<Asset>(instance: &mut Instance<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext) {
        assert!(instance.action_A_4_done, 107);
        assert!(instance.action_B_6_done, 107);
        assert!(!instance.finalized, 108);
        let total_payout: u64 = 0;
        instance.claim_amount_A = if ((instance.done_A_c && instance.done_B_c)) if ((instance.A_c && instance.B_c)) 100 else if ((instance.A_c && !instance.B_c)) 0 else if ((!instance.A_c && instance.B_c)) 200 else 90 else if (!instance.done_A_c) 0 else 200;
        total_payout = (total_payout + if ((instance.done_A_c && instance.done_B_c)) if ((instance.A_c && instance.B_c)) 100 else if ((instance.A_c && !instance.B_c)) 0 else if ((!instance.A_c && instance.B_c)) 200 else 90 else if (!instance.done_A_c) 0 else 200);
        instance.claim_amount_B = if ((instance.done_A_c && instance.done_B_c)) if ((instance.A_c && instance.B_c)) 100 else if ((instance.A_c && !instance.B_c)) 200 else if ((!instance.A_c && instance.B_c)) 0 else 110 else if (!instance.done_A_c) 200 else 0;
        total_payout = (total_payout + if ((instance.done_A_c && instance.done_B_c)) if ((instance.A_c && instance.B_c)) 100 else if ((instance.A_c && !instance.B_c)) 200 else if ((!instance.A_c && instance.B_c)) 0 else 110 else if (!instance.done_A_c) 200 else 0);
        assert!((total_payout <= sui::balance::value<Asset>(&instance.pot)), 109);
        instance.finalized = true;
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

    public entry fun claim_B<Asset>(instance: &mut Instance<Asset>, clock: &sui::clock::Clock, ctx: &mut sui::tx_context::TxContext) {
        assert!(instance.finalized, 110);
        assert!(!instance.claimed_B, 111);
        instance.claimed_B = true;
        let amount: u64 = instance.claim_amount_B;
        if ((amount > 0)) {
            let payout_coin = sui::coin::take<Asset>(&mut instance.pot, amount, ctx);
            sui::transfer::public_transfer<Asset>(payout_coin, sui::tx_context::sender(ctx));
        };
    }

}
