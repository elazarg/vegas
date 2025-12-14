module oddsevensshort::oddsevensshort {
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
        role_Odd: address,
        role_Even: address,
        joined_Odd: bool,
        joined_Even: bool,
        timeout_ms: u64,
        last_ts_ms: u64,
        bailed_Odd: bool,
        bailed_Even: bool,
        pot: balance::Balance<Asset>,
        finalized: bool,
        claim_amount_Odd: u64,
        claimed_Odd: bool,
        claim_amount_Even: u64,
        claimed_Even: bool,
        Odd_c: bool,
        done_Odd_c: bool,
        Odd_c_hidden: vector<u8>,
        done_Odd_c_hidden: bool,
        Even_c: bool,
        done_Even_c: bool,
        Even_c_hidden: vector<u8>,
        done_Even_c_hidden: bool,
        action_Odd_1_done: bool,
        action_Even_3_done: bool,
        action_Odd_2_done: bool,
        action_Even_4_done: bool,
    }

    fun init(ctx: &mut tx_context::TxContext) {
    }

    public entry fun create_game<Asset>(timeout_ms: u64, ctx: &mut tx_context::TxContext) {
        let instance = Instance<Asset> { id: object::new(ctx), role_Odd: @0x0, role_Even: @0x0, joined_Odd: false, joined_Even: false, timeout_ms: timeout_ms, last_ts_ms: 0, bailed_Odd: false, bailed_Even: false, pot: balance::zero<Asset>(), finalized: false, claim_amount_Odd: 0, claimed_Odd: false, claim_amount_Even: 0, claimed_Even: false, Odd_c: false, done_Odd_c: false, Odd_c_hidden: vector::empty<u8>(), done_Odd_c_hidden: false, Even_c: false, done_Even_c: false, Even_c_hidden: vector::empty<u8>(), done_Even_c_hidden: false, action_Odd_1_done: false, action_Even_3_done: false, action_Odd_2_done: false, action_Even_4_done: false };
        transfer::share_object(instance);
    }

    public entry fun join_Odd<Asset>(instance: &mut Instance<Asset>, payment: coin::Coin<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(!instance.joined_Odd, 100);
        assert!(!instance.finalized, 117);
        assert!((coin::value<Asset>(&payment) == 100), 112);
        instance.role_Odd = tx_context::sender(ctx);
        instance.joined_Odd = true;
        balance::join<Asset>(&mut instance.pot, coin::into_balance<Asset>(payment));
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun join_Even<Asset>(instance: &mut Instance<Asset>, payment: coin::Coin<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(!instance.joined_Even, 100);
        assert!(!instance.finalized, 117);
        assert!((coin::value<Asset>(&payment) == 100), 112);
        instance.role_Even = tx_context::sender(ctx);
        instance.joined_Even = true;
        balance::join<Asset>(&mut instance.pot, coin::into_balance<Asset>(payment));
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun timeout_Odd<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.joined_Odd, 113);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Odd = true;
        };
    }

    public entry fun timeout_Even<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.joined_Even, 113);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Even = true;
        };
    }

    public entry fun move_Odd_0<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, hidden_c: vector<u8>) {
        assert!((tx_context::sender(ctx) == instance.role_Odd), 101);
        assert!(instance.joined_Odd, 113);
        assert!(!instance.bailed_Odd, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Odd = true;
            return
        };
        assert!(!instance.action_Odd_1_done, 102);
        assert!((vector::length<u8>(&hidden_c) == 32), 115);
        instance.Odd_c_hidden = hidden_c;
        instance.done_Odd_c_hidden = true;
        instance.action_Odd_1_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Even_2<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, hidden_c: vector<u8>) {
        assert!((tx_context::sender(ctx) == instance.role_Even), 101);
        assert!(instance.joined_Even, 113);
        assert!(!instance.bailed_Even, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Even = true;
            return
        };
        assert!(!instance.action_Even_3_done, 102);
        assert!((vector::length<u8>(&hidden_c) == 32), 115);
        instance.Even_c_hidden = hidden_c;
        instance.done_Even_c_hidden = true;
        instance.action_Even_3_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Odd_1<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, c: bool, salt: u64) {
        assert!((tx_context::sender(ctx) == instance.role_Odd), 101);
        assert!(instance.joined_Odd, 113);
        assert!(!instance.bailed_Odd, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Odd = true;
            return
        };
        assert!(!instance.action_Odd_2_done, 102);
        assert!(instance.action_Odd_1_done, 103);
        assert!((instance.action_Even_3_done || instance.bailed_Even), 103);
        let mut data_c = bcs::to_bytes<bool>(&c);
        let salt_bytes_c = bcs::to_bytes<u64>(&salt);
        vector::append<u8>(&mut data_c, salt_bytes_c);
        assert!((hash::keccak256(&data_c) == instance.Odd_c_hidden), 106);
        instance.Odd_c = c;
        instance.done_Odd_c = true;
        instance.action_Odd_2_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Even_3<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, c: bool, salt: u64) {
        assert!((tx_context::sender(ctx) == instance.role_Even), 101);
        assert!(instance.joined_Even, 113);
        assert!(!instance.bailed_Even, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Even = true;
            return
        };
        assert!(!instance.action_Even_4_done, 102);
        assert!(instance.action_Even_3_done, 103);
        assert!((instance.action_Odd_1_done || instance.bailed_Odd), 103);
        let mut data_c = bcs::to_bytes<bool>(&c);
        let salt_bytes_c = bcs::to_bytes<u64>(&salt);
        vector::append<u8>(&mut data_c, salt_bytes_c);
        assert!((hash::keccak256(&data_c) == instance.Even_c_hidden), 106);
        instance.Even_c = c;
        instance.done_Even_c = true;
        instance.action_Even_4_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun finalize<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(((instance.action_Odd_2_done && instance.action_Even_4_done) || (clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))), 107);
        assert!(!instance.finalized, 108);
        let mut total_payout: u64 = 0;
        if ((instance.joined_Odd && instance.joined_Even)) {
            if ((instance.action_Odd_2_done && instance.action_Even_4_done)) {
                instance.claim_amount_Even = if ((instance.done_Even_c && instance.done_Odd_c)) { if ((instance.Even_c == instance.Odd_c)) { 126 } else { 74 } } else { if ((!instance.done_Even_c && instance.done_Odd_c)) { 20 } else { if ((instance.done_Even_c && !instance.done_Odd_c)) { 180 } else { 100 } } };
                total_payout = (total_payout + if ((instance.done_Even_c && instance.done_Odd_c)) { if ((instance.Even_c == instance.Odd_c)) { 126 } else { 74 } } else { if ((!instance.done_Even_c && instance.done_Odd_c)) { 20 } else { if ((instance.done_Even_c && !instance.done_Odd_c)) { 180 } else { 100 } } });
                instance.claim_amount_Odd = if ((instance.done_Even_c && instance.done_Odd_c)) { if ((instance.Even_c == instance.Odd_c)) { 74 } else { 126 } } else { if ((!instance.done_Even_c && instance.done_Odd_c)) { 180 } else { if ((instance.done_Even_c && !instance.done_Odd_c)) { 20 } else { 100 } } };
                total_payout = (total_payout + if ((instance.done_Even_c && instance.done_Odd_c)) { if ((instance.Even_c == instance.Odd_c)) { 74 } else { 126 } } else { if ((!instance.done_Even_c && instance.done_Odd_c)) { 180 } else { if ((instance.done_Even_c && !instance.done_Odd_c)) { 20 } else { 100 } } });
            } else {
                if (!instance.action_Odd_1_done) {
                    instance.claim_amount_Odd = 0;
                    instance.claim_amount_Even = (balance::value<Asset>(&instance.pot) / 1);
                    total_payout = ((balance::value<Asset>(&instance.pot) / 1) * 1);
                } else {
                    if (!instance.action_Odd_2_done) {
                        instance.claim_amount_Odd = 0;
                        instance.claim_amount_Even = (balance::value<Asset>(&instance.pot) / 1);
                        total_payout = ((balance::value<Asset>(&instance.pot) / 1) * 1);
                    } else {
                        if (!instance.action_Even_3_done) {
                            instance.claim_amount_Even = 0;
                            instance.claim_amount_Odd = (balance::value<Asset>(&instance.pot) / 1);
                            total_payout = ((balance::value<Asset>(&instance.pot) / 1) * 1);
                        } else {
                            if (!instance.action_Even_4_done) {
                                instance.claim_amount_Even = 0;
                                instance.claim_amount_Odd = (balance::value<Asset>(&instance.pot) / 1);
                                total_payout = ((balance::value<Asset>(&instance.pot) / 1) * 1);
                            } else {
                            }
                        }
                    }
                }
            }
        } else {
            if (instance.joined_Odd) {
                instance.claim_amount_Odd = 100;
                total_payout = (total_payout + 100);
            };
            if (instance.joined_Even) {
                instance.claim_amount_Even = 100;
                total_payout = (total_payout + 100);
            };
        }
        assert!((total_payout <= balance::value<Asset>(&instance.pot)), 109);
        instance.finalized = true;
    }

    public entry fun claim_Odd<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.finalized, 110);
        assert!(!instance.claimed_Odd, 111);
        instance.claimed_Odd = true;
        let amount: u64 = instance.claim_amount_Odd;
        if ((amount > 0)) {
            let payout_coin = coin::take<Asset>(&mut instance.pot, amount, ctx);
            transfer::public_transfer<Asset>(payout_coin, instance.role_Odd);
        };
    }

    public entry fun claim_Even<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.finalized, 110);
        assert!(!instance.claimed_Even, 111);
        instance.claimed_Even = true;
        let amount: u64 = instance.claim_amount_Even;
        if ((amount > 0)) {
            let payout_coin = coin::take<Asset>(&mut instance.pot, amount, ctx);
            transfer::public_transfer<Asset>(payout_coin, instance.role_Even);
        };
    }

    public entry fun sweep<Asset>(instance: &mut Instance<Asset>, ctx: &mut tx_context::TxContext) {
        assert!(instance.finalized, 116);
        assert!((instance.claimed_Odd && instance.claimed_Even), 118);
        let val: u64 = balance::value<Asset>(&instance.pot);
        if ((val > 0)) {
            let payout_coin = coin::take<Asset>(&mut instance.pot, val, ctx);
            transfer::public_transfer<Asset>(payout_coin, tx_context::sender(ctx));
        };
    }

}
