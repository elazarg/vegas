module montyhallchance::montyhallchance {
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
        role_Guest: address,
        joined_Guest: bool,
        timeout_ms: u64,
        last_ts_ms: u64,
        bailed_Guest: bool,
        pot: balance::Balance<Asset>,
        finalized: bool,
        claim_amount_Guest: u64,
        claimed_Guest: bool,
        Host_car: u64,
        done_Host_car: bool,
        Host_car_hidden: vector<u8>,
        done_Host_car_hidden: bool,
        Guest_d: u64,
        done_Guest_d: bool,
        Host_goat: u64,
        done_Host_goat: bool,
        Guest_switch: bool,
        done_Guest_switch: bool,
        action_Host_0_done: bool,
        action_Guest_1_done: bool,
        action_Host_2_done: bool,
        action_Guest_3_done: bool,
        action_Host_4_done: bool,
        action_Guest_5_done: bool,
        action_Host_6_done: bool,
    }

    fun init(ctx: &mut tx_context::TxContext) {
    }

    public entry fun create_game<Asset>(timeout_ms: u64, ctx: &mut tx_context::TxContext) {
        let instance = Instance<Asset> { id: object::new(ctx), role_Guest: 0x0, joined_Guest: false, timeout_ms: timeout_ms, last_ts_ms: 0, bailed_Guest: false, pot: balance::zero<Asset>(), finalized: false, claim_amount_Guest: 0, claimed_Guest: false, Host_car: 0, done_Host_car: false, Host_car_hidden: vector::empty<u8>(), done_Host_car_hidden: false, Guest_d: 0, done_Guest_d: false, Host_goat: 0, done_Host_goat: false, Guest_switch: false, done_Guest_switch: false, action_Host_0_done: false, action_Guest_1_done: false, action_Host_2_done: false, action_Guest_3_done: false, action_Host_4_done: false, action_Guest_5_done: false, action_Host_6_done: false };
        transfer::share_object(instance);
    }

    public entry fun join_Guest<Asset>(instance: &mut Instance<Asset>, payment: coin::Coin<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(!instance.joined_Guest, 100);
        assert!((coin::value<Asset>(&payment) == 100), 112);
        instance.role_Guest = tx_context::sender(ctx);
        instance.joined_Guest = true;
        balance::join<Asset>(&mut instance.pot, coin::into_balance<Asset>(payment));
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun timeout_Guest<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Guest = true;
        };
    }

    public entry fun move_Host_0<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!((tx_context::sender(ctx) == instance.role_Host), 101);
        assert!(instance.joined_Host, 113);
        assert!(!instance.bailed_Host, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Host = true;
            return
        };
        assert!(!instance.action_Host_0_done, 102);
        instance.action_Host_0_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Guest_1<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!((tx_context::sender(ctx) == instance.role_Guest), 101);
        assert!(instance.joined_Guest, 113);
        assert!(!instance.bailed_Guest, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Guest = true;
            return
        };
        assert!(!instance.action_Guest_1_done, 102);
        assert!((instance.action_Host_0_done || instance.bailed_Host), 103);
        instance.action_Guest_1_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Host_2<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, hidden_car: vector<u8>) {
        assert!((tx_context::sender(ctx) == instance.role_Host), 101);
        assert!(instance.joined_Host, 113);
        assert!(!instance.bailed_Host, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Host = true;
            return
        };
        assert!(!instance.action_Host_2_done, 102);
        assert!((instance.action_Guest_1_done || instance.bailed_Guest), 103);
        assert!((vector::length<u8>(&hidden_car) == 32), 115);
        instance.Host_car_hidden = hidden_car;
        instance.done_Host_car_hidden = true;
        instance.action_Host_2_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Guest_3<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, d: u64) {
        assert!((tx_context::sender(ctx) == instance.role_Guest), 101);
        assert!(instance.joined_Guest, 113);
        assert!(!instance.bailed_Guest, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Guest = true;
            return
        };
        assert!(!instance.action_Guest_3_done, 102);
        assert!((instance.action_Host_2_done || instance.bailed_Host), 103);
        assert!((((d == 0) || (d == 1)) || (d == 2)), 104);
        instance.Guest_d = d;
        instance.done_Guest_d = true;
        instance.action_Guest_3_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Host_4<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, goat: u64) {
        assert!((tx_context::sender(ctx) == instance.role_Host), 101);
        assert!(instance.joined_Host, 113);
        assert!(!instance.bailed_Host, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Host = true;
            return
        };
        assert!(!instance.action_Host_4_done, 102);
        assert!((instance.action_Guest_3_done || instance.bailed_Guest), 103);
        assert!((instance.action_Host_2_done || instance.bailed_Host), 103);
        assert!((((goat == 0) || (goat == 1)) || (goat == 2)), 104);
        assert!(((goat != instance.Guest_d) && (goat != instance.Host_car)), 105);
        instance.Host_goat = goat;
        instance.done_Host_goat = true;
        instance.action_Host_4_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Guest_5<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, switch: bool) {
        assert!((tx_context::sender(ctx) == instance.role_Guest), 101);
        assert!(instance.joined_Guest, 113);
        assert!(!instance.bailed_Guest, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Guest = true;
            return
        };
        assert!(!instance.action_Guest_5_done, 102);
        assert!((instance.action_Host_4_done || instance.bailed_Host), 103);
        instance.Guest_switch = switch;
        instance.done_Guest_switch = true;
        instance.action_Guest_5_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Host_6<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, car: u64, salt: u64) {
        assert!((tx_context::sender(ctx) == instance.role_Host), 101);
        assert!(instance.joined_Host, 113);
        assert!(!instance.bailed_Host, 114);
        assert!(!instance.finalized, 117);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Host = true;
            return
        };
        assert!(!instance.action_Host_6_done, 102);
        assert!((instance.action_Guest_5_done || instance.bailed_Guest), 103);
        assert!((instance.action_Host_2_done || instance.bailed_Host), 103);
        assert!((((car == 0) || (car == 1)) || (car == 2)), 104);
        let mut data_car = bcs::to_bytes<u64>(&car);
        vector::append<u8>(&mut data_car, bcs::to_bytes<u64>(&salt));
        assert!((hash::keccak256(&data_car) == instance.Host_car_hidden), 106);
        instance.Host_car = car;
        instance.done_Host_car = true;
        instance.action_Host_6_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun finalize<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!((instance.action_Host_6_done || (clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))), 107);
        assert!(!instance.finalized, 108);
        let mut total_payout: u64 = 0;
        if (instance.joined_Guest) {
            instance.claim_amount_Guest = if (((instance.done_Host_car && instance.done_Host_goat) && instance.done_Guest_switch)) if (((instance.Guest_d != instance.Host_car) == instance.Guest_switch)) 120 else 80 else if ((!instance.done_Host_car || !instance.done_Host_goat)) 200 else 0;
            total_payout = (total_payout + if (((instance.done_Host_car && instance.done_Host_goat) && instance.done_Guest_switch)) if (((instance.Guest_d != instance.Host_car) == instance.Guest_switch)) 120 else 80 else if ((!instance.done_Host_car || !instance.done_Host_goat)) 200 else 0);
            instance.claim_amount_Host = if (((instance.done_Host_car && instance.done_Host_goat) && instance.done_Guest_switch)) if (((instance.Guest_d != instance.Host_car) == instance.Guest_switch)) 80 else 120 else if ((!instance.done_Host_car || !instance.done_Host_goat)) 0 else 200;
            total_payout = (total_payout + if (((instance.done_Host_car && instance.done_Host_goat) && instance.done_Guest_switch)) if (((instance.Guest_d != instance.Host_car) == instance.Guest_switch)) 80 else 120 else if ((!instance.done_Host_car || !instance.done_Host_goat)) 0 else 200);
        } else {
            if (instance.joined_Guest) {
                instance.claim_amount_Guest = 100;
                total_payout = (total_payout + 100);
            };
        }
        assert!((total_payout <= balance::value<Asset>(&instance.pot)), 109);
        instance.finalized = true;
    }

    public entry fun claim_Guest<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.finalized, 110);
        assert!(!instance.claimed_Guest, 111);
        instance.claimed_Guest = true;
        let amount: u64 = instance.claim_amount_Guest;
        if ((amount > 0)) {
            let payout_coin = coin::take<Asset>(&mut instance.pot, amount, ctx);
            transfer::public_transfer<Asset>(payout_coin, instance.role_Guest);
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
