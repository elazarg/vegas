module threewaylottery::threewaylottery {
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
        role_Issuer: address,
        role_Alice: address,
        role_Bob: address,
        joined_Issuer: bool,
        joined_Alice: bool,
        joined_Bob: bool,
        timeout_ms: u64,
        last_ts_ms: u64,
        bailed_Issuer: bool,
        bailed_Alice: bool,
        bailed_Bob: bool,
        pot: balance::Balance<Asset>,
        finalized: bool,
        claim_amount_Issuer: u64,
        claimed_Issuer: bool,
        claim_amount_Alice: u64,
        claimed_Alice: bool,
        claim_amount_Bob: u64,
        claimed_Bob: bool,
        Issuer_c: u64,
        done_Issuer_c: bool,
        Issuer_c_hidden: vector<u8>,
        done_Issuer_c_hidden: bool,
        Alice_c: u64,
        done_Alice_c: bool,
        Alice_c_hidden: vector<u8>,
        done_Alice_c_hidden: bool,
        Bob_c: u64,
        done_Bob_c: bool,
        Bob_c_hidden: vector<u8>,
        done_Bob_c_hidden: bool,
        action_Issuer_0_done: bool,
        action_Alice_1_done: bool,
        action_Bob_2_done: bool,
        action_Issuer_4_done: bool,
        action_Alice_6_done: bool,
        action_Bob_8_done: bool,
        action_Issuer_5_done: bool,
        action_Alice_7_done: bool,
        action_Bob_9_done: bool,
    }

    fun init(ctx: &mut tx_context::TxContext) {
    }

    public entry fun create_game<Asset>(timeout_ms: u64, ctx: &mut tx_context::TxContext) {
        let instance = Instance<Asset> { id: object::new(ctx), role_Issuer: @0x0, role_Alice: @0x0, role_Bob: @0x0, joined_Issuer: false, joined_Alice: false, joined_Bob: false, timeout_ms: timeout_ms, last_ts_ms: 0, bailed_Issuer: false, bailed_Alice: false, bailed_Bob: false, pot: balance::zero<Asset>(), finalized: false, claim_amount_Issuer: 0, claimed_Issuer: false, claim_amount_Alice: 0, claimed_Alice: false, claim_amount_Bob: 0, claimed_Bob: false, Issuer_c: 0, done_Issuer_c: false, Issuer_c_hidden: vector::empty<u8>(), done_Issuer_c_hidden: false, Alice_c: 0, done_Alice_c: false, Alice_c_hidden: vector::empty<u8>(), done_Alice_c_hidden: false, Bob_c: 0, done_Bob_c: false, Bob_c_hidden: vector::empty<u8>(), done_Bob_c_hidden: false, action_Issuer_0_done: false, action_Alice_1_done: false, action_Bob_2_done: false, action_Issuer_4_done: false, action_Alice_6_done: false, action_Bob_8_done: false, action_Issuer_5_done: false, action_Alice_7_done: false, action_Bob_9_done: false };
        transfer::share_object(instance);
    }

    public entry fun join_Issuer<Asset>(instance: &mut Instance<Asset>, payment: coin::Coin<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(!instance.joined_Issuer, 100);
        assert!(!instance.finalized, 117);
        assert!((coin::value<Asset>(&payment) == 12), 112);
        instance.role_Issuer = tx_context::sender(ctx);
        instance.joined_Issuer = true;
        balance::join<Asset>(&mut instance.pot, coin::into_balance<Asset>(payment));
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun join_Alice<Asset>(instance: &mut Instance<Asset>, payment: coin::Coin<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(!instance.joined_Alice, 100);
        assert!(!instance.finalized, 117);
        assert!((coin::value<Asset>(&payment) == 12), 112);
        instance.role_Alice = tx_context::sender(ctx);
        instance.joined_Alice = true;
        balance::join<Asset>(&mut instance.pot, coin::into_balance<Asset>(payment));
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun join_Bob<Asset>(instance: &mut Instance<Asset>, payment: coin::Coin<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(!instance.joined_Bob, 100);
        assert!(!instance.finalized, 117);
        assert!((coin::value<Asset>(&payment) == 12), 112);
        instance.role_Bob = tx_context::sender(ctx);
        instance.joined_Bob = true;
        balance::join<Asset>(&mut instance.pot, coin::into_balance<Asset>(payment));
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun timeout_Issuer<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.joined_Issuer, 113);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Issuer = true;
        };
    }

    public entry fun timeout_Alice<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.joined_Alice, 113);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Alice = true;
        };
    }

    public entry fun timeout_Bob<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.joined_Bob, 113);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Bob = true;
        };
    }

    public entry fun move_Issuer_0<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!((tx_context::sender(ctx) == instance.role_Issuer), 101);
        assert!(instance.joined_Issuer, 113);
        assert!(!instance.bailed_Issuer, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Issuer = true;
            return
        };
        assert!(!instance.action_Issuer_0_done, 102);
        instance.action_Issuer_0_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Alice_1<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!((tx_context::sender(ctx) == instance.role_Alice), 101);
        assert!(instance.joined_Alice, 113);
        assert!(!instance.bailed_Alice, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Alice = true;
            return
        };
        assert!(!instance.action_Alice_1_done, 102);
        assert!((instance.action_Issuer_0_done || instance.bailed_Issuer), 103);
        instance.action_Alice_1_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Bob_2<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!((tx_context::sender(ctx) == instance.role_Bob), 101);
        assert!(instance.joined_Bob, 113);
        assert!(!instance.bailed_Bob, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Bob = true;
            return
        };
        assert!(!instance.action_Bob_2_done, 102);
        assert!((instance.action_Alice_1_done || instance.bailed_Alice), 103);
        instance.action_Bob_2_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Issuer_3<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, hidden_c: vector<u8>) {
        assert!((tx_context::sender(ctx) == instance.role_Issuer), 101);
        assert!(instance.joined_Issuer, 113);
        assert!(!instance.bailed_Issuer, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Issuer = true;
            return
        };
        assert!(!instance.action_Issuer_4_done, 102);
        assert!((instance.action_Bob_2_done || instance.bailed_Bob), 103);
        assert!((vector::length<u8>(&hidden_c) == 32), 115);
        instance.Issuer_c_hidden = hidden_c;
        instance.done_Issuer_c_hidden = true;
        instance.action_Issuer_4_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Alice_5<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, hidden_c: vector<u8>) {
        assert!((tx_context::sender(ctx) == instance.role_Alice), 101);
        assert!(instance.joined_Alice, 113);
        assert!(!instance.bailed_Alice, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Alice = true;
            return
        };
        assert!(!instance.action_Alice_6_done, 102);
        assert!((instance.action_Bob_2_done || instance.bailed_Bob), 103);
        assert!((vector::length<u8>(&hidden_c) == 32), 115);
        instance.Alice_c_hidden = hidden_c;
        instance.done_Alice_c_hidden = true;
        instance.action_Alice_6_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Bob_7<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, hidden_c: vector<u8>) {
        assert!((tx_context::sender(ctx) == instance.role_Bob), 101);
        assert!(instance.joined_Bob, 113);
        assert!(!instance.bailed_Bob, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Bob = true;
            return
        };
        assert!(!instance.action_Bob_8_done, 102);
        assert!(instance.action_Bob_2_done, 103);
        assert!((vector::length<u8>(&hidden_c) == 32), 115);
        instance.Bob_c_hidden = hidden_c;
        instance.done_Bob_c_hidden = true;
        instance.action_Bob_8_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Issuer_4<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, c: u64, salt: u64) {
        assert!((tx_context::sender(ctx) == instance.role_Issuer), 101);
        assert!(instance.joined_Issuer, 113);
        assert!(!instance.bailed_Issuer, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Issuer = true;
            return
        };
        assert!(!instance.action_Issuer_5_done, 102);
        assert!((instance.action_Bob_2_done || instance.bailed_Bob), 103);
        assert!(instance.action_Issuer_4_done, 103);
        assert!((instance.action_Alice_6_done || instance.bailed_Alice), 103);
        assert!((instance.action_Bob_8_done || instance.bailed_Bob), 103);
        assert!((((c == 1) || (c == 2)) || (c == 3)), 104);
        let mut data_c = bcs::to_bytes<u64>(&c);
        let salt_bytes_c = bcs::to_bytes<u64>(&salt);
        vector::append<u8>(&mut data_c, salt_bytes_c);
        assert!((hash::keccak256(&data_c) == instance.Issuer_c_hidden), 106);
        instance.Issuer_c = c;
        instance.done_Issuer_c = true;
        instance.action_Issuer_5_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Alice_6<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, c: u64, salt: u64) {
        assert!((tx_context::sender(ctx) == instance.role_Alice), 101);
        assert!(instance.joined_Alice, 113);
        assert!(!instance.bailed_Alice, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Alice = true;
            return
        };
        assert!(!instance.action_Alice_7_done, 102);
        assert!((instance.action_Bob_2_done || instance.bailed_Bob), 103);
        assert!(instance.action_Alice_6_done, 103);
        assert!((instance.action_Issuer_4_done || instance.bailed_Issuer), 103);
        assert!((instance.action_Bob_8_done || instance.bailed_Bob), 103);
        assert!((((c == 1) || (c == 2)) || (c == 3)), 104);
        let mut data_c = bcs::to_bytes<u64>(&c);
        let salt_bytes_c = bcs::to_bytes<u64>(&salt);
        vector::append<u8>(&mut data_c, salt_bytes_c);
        assert!((hash::keccak256(&data_c) == instance.Alice_c_hidden), 106);
        instance.Alice_c = c;
        instance.done_Alice_c = true;
        instance.action_Alice_7_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Bob_8<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, c: u64, salt: u64) {
        assert!((tx_context::sender(ctx) == instance.role_Bob), 101);
        assert!(instance.joined_Bob, 113);
        assert!(!instance.bailed_Bob, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Bob = true;
            return
        };
        assert!(!instance.action_Bob_9_done, 102);
        assert!(instance.action_Bob_2_done, 103);
        assert!(instance.action_Bob_8_done, 103);
        assert!((instance.action_Issuer_4_done || instance.bailed_Issuer), 103);
        assert!((instance.action_Alice_6_done || instance.bailed_Alice), 103);
        assert!((((c == 1) || (c == 2)) || (c == 3)), 104);
        let mut data_c = bcs::to_bytes<u64>(&c);
        let salt_bytes_c = bcs::to_bytes<u64>(&salt);
        vector::append<u8>(&mut data_c, salt_bytes_c);
        assert!((hash::keccak256(&data_c) == instance.Bob_c_hidden), 106);
        instance.Bob_c = c;
        instance.done_Bob_c = true;
        instance.action_Bob_9_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun finalize<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!((((instance.action_Issuer_5_done && instance.action_Alice_7_done) && instance.action_Bob_9_done) || (clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))), 107);
        assert!(!instance.finalized, 108);
        let mut total_payout: u64 = 0;
        if (((instance.joined_Issuer && instance.joined_Alice) && instance.joined_Bob)) {
            if (((instance.action_Issuer_5_done && instance.action_Alice_7_done) && instance.action_Bob_9_done)) {
                instance.claim_amount_Bob = if (((instance.done_Alice_c && instance.done_Bob_c) && instance.done_Issuer_c)) { if (((((instance.Issuer_c + instance.Alice_c) + instance.Bob_c) % 3) == 0)) { 6 } else { if (((((instance.Issuer_c + instance.Alice_c) + instance.Bob_c) % 3) == 1)) { 24 } else { 6 } } } else { if ((!instance.done_Alice_c && !instance.done_Bob_c)) { 1 } else { if ((!instance.done_Alice_c && !instance.done_Issuer_c)) { 34 } else { if ((!instance.done_Bob_c && !instance.done_Issuer_c)) { 1 } else { if (!instance.done_Alice_c) { 17 } else { if (!instance.done_Bob_c) { 2 } else { if (!instance.done_Issuer_c) { 17 } else { 12 } } } } } } };
                total_payout = (total_payout + if (((instance.done_Alice_c && instance.done_Bob_c) && instance.done_Issuer_c)) { if (((((instance.Issuer_c + instance.Alice_c) + instance.Bob_c) % 3) == 0)) { 6 } else { if (((((instance.Issuer_c + instance.Alice_c) + instance.Bob_c) % 3) == 1)) { 24 } else { 6 } } } else { if ((!instance.done_Alice_c && !instance.done_Bob_c)) { 1 } else { if ((!instance.done_Alice_c && !instance.done_Issuer_c)) { 34 } else { if ((!instance.done_Bob_c && !instance.done_Issuer_c)) { 1 } else { if (!instance.done_Alice_c) { 17 } else { if (!instance.done_Bob_c) { 2 } else { if (!instance.done_Issuer_c) { 17 } else { 12 } } } } } } });
                instance.claim_amount_Issuer = if (((instance.done_Alice_c && instance.done_Bob_c) && instance.done_Issuer_c)) { if (((((instance.Issuer_c + instance.Alice_c) + instance.Bob_c) % 3) == 0)) { 6 } else { if (((((instance.Issuer_c + instance.Alice_c) + instance.Bob_c) % 3) == 1)) { 6 } else { 24 } } } else { if ((!instance.done_Alice_c && !instance.done_Bob_c)) { 34 } else { if ((!instance.done_Alice_c && !instance.done_Issuer_c)) { 1 } else { if ((!instance.done_Bob_c && !instance.done_Issuer_c)) { 1 } else { if (!instance.done_Alice_c) { 17 } else { if (!instance.done_Bob_c) { 17 } else { if (!instance.done_Issuer_c) { 2 } else { 12 } } } } } } };
                total_payout = (total_payout + if (((instance.done_Alice_c && instance.done_Bob_c) && instance.done_Issuer_c)) { if (((((instance.Issuer_c + instance.Alice_c) + instance.Bob_c) % 3) == 0)) { 6 } else { if (((((instance.Issuer_c + instance.Alice_c) + instance.Bob_c) % 3) == 1)) { 6 } else { 24 } } } else { if ((!instance.done_Alice_c && !instance.done_Bob_c)) { 34 } else { if ((!instance.done_Alice_c && !instance.done_Issuer_c)) { 1 } else { if ((!instance.done_Bob_c && !instance.done_Issuer_c)) { 1 } else { if (!instance.done_Alice_c) { 17 } else { if (!instance.done_Bob_c) { 17 } else { if (!instance.done_Issuer_c) { 2 } else { 12 } } } } } } });
                instance.claim_amount_Alice = if (((instance.done_Alice_c && instance.done_Bob_c) && instance.done_Issuer_c)) { if (((((instance.Issuer_c + instance.Alice_c) + instance.Bob_c) % 3) == 0)) { 24 } else { if (((((instance.Issuer_c + instance.Alice_c) + instance.Bob_c) % 3) == 1)) { 6 } else { 6 } } } else { if ((!instance.done_Alice_c && !instance.done_Bob_c)) { 1 } else { if ((!instance.done_Alice_c && !instance.done_Issuer_c)) { 1 } else { if ((!instance.done_Bob_c && !instance.done_Issuer_c)) { 34 } else { if (!instance.done_Alice_c) { 2 } else { if (!instance.done_Bob_c) { 17 } else { if (!instance.done_Issuer_c) { 17 } else { 12 } } } } } } };
                total_payout = (total_payout + if (((instance.done_Alice_c && instance.done_Bob_c) && instance.done_Issuer_c)) { if (((((instance.Issuer_c + instance.Alice_c) + instance.Bob_c) % 3) == 0)) { 24 } else { if (((((instance.Issuer_c + instance.Alice_c) + instance.Bob_c) % 3) == 1)) { 6 } else { 6 } } } else { if ((!instance.done_Alice_c && !instance.done_Bob_c)) { 1 } else { if ((!instance.done_Alice_c && !instance.done_Issuer_c)) { 1 } else { if ((!instance.done_Bob_c && !instance.done_Issuer_c)) { 34 } else { if (!instance.done_Alice_c) { 2 } else { if (!instance.done_Bob_c) { 17 } else { if (!instance.done_Issuer_c) { 17 } else { 12 } } } } } } });
            } else {
                if (!instance.action_Issuer_0_done) {
                    instance.claim_amount_Issuer = 0;
                    instance.claim_amount_Alice = (balance::value<Asset>(&instance.pot) / 2);
                    instance.claim_amount_Bob = (balance::value<Asset>(&instance.pot) / 2);
                    total_payout = ((balance::value<Asset>(&instance.pot) / 2) * 2);
                } else {
                    if (!instance.action_Alice_1_done) {
                        instance.claim_amount_Alice = 0;
                        instance.claim_amount_Issuer = (balance::value<Asset>(&instance.pot) / 2);
                        instance.claim_amount_Bob = (balance::value<Asset>(&instance.pot) / 2);
                        total_payout = ((balance::value<Asset>(&instance.pot) / 2) * 2);
                    } else {
                        if (!instance.action_Bob_2_done) {
                            instance.claim_amount_Bob = 0;
                            instance.claim_amount_Issuer = (balance::value<Asset>(&instance.pot) / 2);
                            instance.claim_amount_Alice = (balance::value<Asset>(&instance.pot) / 2);
                            total_payout = ((balance::value<Asset>(&instance.pot) / 2) * 2);
                        } else {
                            if (!instance.action_Issuer_4_done) {
                                instance.claim_amount_Issuer = 0;
                                instance.claim_amount_Alice = (balance::value<Asset>(&instance.pot) / 2);
                                instance.claim_amount_Bob = (balance::value<Asset>(&instance.pot) / 2);
                                total_payout = ((balance::value<Asset>(&instance.pot) / 2) * 2);
                            } else {
                                if (!instance.action_Issuer_5_done) {
                                    instance.claim_amount_Issuer = 0;
                                    instance.claim_amount_Alice = (balance::value<Asset>(&instance.pot) / 2);
                                    instance.claim_amount_Bob = (balance::value<Asset>(&instance.pot) / 2);
                                    total_payout = ((balance::value<Asset>(&instance.pot) / 2) * 2);
                                } else {
                                    if (!instance.action_Alice_6_done) {
                                        instance.claim_amount_Alice = 0;
                                        instance.claim_amount_Issuer = (balance::value<Asset>(&instance.pot) / 2);
                                        instance.claim_amount_Bob = (balance::value<Asset>(&instance.pot) / 2);
                                        total_payout = ((balance::value<Asset>(&instance.pot) / 2) * 2);
                                    } else {
                                        if (!instance.action_Alice_7_done) {
                                            instance.claim_amount_Alice = 0;
                                            instance.claim_amount_Issuer = (balance::value<Asset>(&instance.pot) / 2);
                                            instance.claim_amount_Bob = (balance::value<Asset>(&instance.pot) / 2);
                                            total_payout = ((balance::value<Asset>(&instance.pot) / 2) * 2);
                                        } else {
                                            if (!instance.action_Bob_8_done) {
                                                instance.claim_amount_Bob = 0;
                                                instance.claim_amount_Issuer = (balance::value<Asset>(&instance.pot) / 2);
                                                instance.claim_amount_Alice = (balance::value<Asset>(&instance.pot) / 2);
                                                total_payout = ((balance::value<Asset>(&instance.pot) / 2) * 2);
                                            } else {
                                                if (!instance.action_Bob_9_done) {
                                                    instance.claim_amount_Bob = 0;
                                                    instance.claim_amount_Issuer = (balance::value<Asset>(&instance.pot) / 2);
                                                    instance.claim_amount_Alice = (balance::value<Asset>(&instance.pot) / 2);
                                                    total_payout = ((balance::value<Asset>(&instance.pot) / 2) * 2);
                                                } else {
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        } else {
            if (instance.joined_Issuer) {
                instance.claim_amount_Issuer = 12;
                total_payout = (total_payout + 12);
            };
            if (instance.joined_Alice) {
                instance.claim_amount_Alice = 12;
                total_payout = (total_payout + 12);
            };
            if (instance.joined_Bob) {
                instance.claim_amount_Bob = 12;
                total_payout = (total_payout + 12);
            };
        }
        assert!((total_payout <= balance::value<Asset>(&instance.pot)), 109);
        instance.finalized = true;
    }

    public entry fun claim_Issuer<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.finalized, 110);
        assert!(!instance.claimed_Issuer, 111);
        instance.claimed_Issuer = true;
        let amount: u64 = instance.claim_amount_Issuer;
        if ((amount > 0)) {
            let payout_coin = coin::take<Asset>(&mut instance.pot, amount, ctx);
            transfer::public_transfer<Asset>(payout_coin, instance.role_Issuer);
        };
    }

    public entry fun claim_Alice<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.finalized, 110);
        assert!(!instance.claimed_Alice, 111);
        instance.claimed_Alice = true;
        let amount: u64 = instance.claim_amount_Alice;
        if ((amount > 0)) {
            let payout_coin = coin::take<Asset>(&mut instance.pot, amount, ctx);
            transfer::public_transfer<Asset>(payout_coin, instance.role_Alice);
        };
    }

    public entry fun claim_Bob<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.finalized, 110);
        assert!(!instance.claimed_Bob, 111);
        instance.claimed_Bob = true;
        let amount: u64 = instance.claim_amount_Bob;
        if ((amount > 0)) {
            let payout_coin = coin::take<Asset>(&mut instance.pot, amount, ctx);
            transfer::public_transfer<Asset>(payout_coin, instance.role_Bob);
        };
    }

    public entry fun sweep<Asset>(instance: &mut Instance<Asset>, ctx: &mut tx_context::TxContext) {
        assert!(instance.finalized, 116);
        assert!(((instance.claimed_Issuer && instance.claimed_Alice) && instance.claimed_Bob), 118);
        let val: u64 = balance::value<Asset>(&instance.pot);
        if ((val > 0)) {
            let payout_coin = coin::take<Asset>(&mut instance.pot, val, ctx);
            transfer::public_transfer<Asset>(payout_coin, tx_context::sender(ctx));
        };
    }

}
