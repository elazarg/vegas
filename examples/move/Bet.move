module bet::bet {
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
        role_Gambler: address,
        joined_Gambler: bool,
        timeout_ms: u64,
        last_ts_ms: u64,
        bailed_Gambler: bool,
        pot: balance::Balance<Asset>,
        finalized: bool,
        claim_amount_Gambler: u64,
        claimed_Gambler: bool,
        Gambler_bet: u64,
        done_Gambler_bet: bool,
        Race_winner: u64,
        done_Race_winner: bool,
        action_Race_0_done: bool,
        action_Gambler_1_done: bool,
        action_Race_2_done: bool,
    }

    fun init(ctx: &mut tx_context::TxContext) {
    }

    public entry fun create_game<Asset>(timeout_ms: u64, ctx: &mut tx_context::TxContext) {
        let instance = Instance<Asset> { id: object::new(ctx), role_Gambler: 0x0, joined_Gambler: false, timeout_ms: timeout_ms, last_ts_ms: 0, bailed_Gambler: false, pot: balance::zero<Asset>(), finalized: false, claim_amount_Gambler: 0, claimed_Gambler: false, Gambler_bet: 0, done_Gambler_bet: false, Race_winner: 0, done_Race_winner: false, action_Race_0_done: false, action_Gambler_1_done: false, action_Race_2_done: false };
        transfer::share_object<Asset>(instance);
    }

    public entry fun join_Gambler<Asset>(instance: &mut Instance<Asset>, payment: coin::Coin<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(!instance.joined_Gambler, 100);
        assert!((coin::value<Asset>(&payment) == 10), 112);
        instance.role_Gambler = tx_context::sender(ctx);
        instance.joined_Gambler = true;
        balance::join<Asset>(&mut instance.pot, coin::into_balance<Asset>(payment));
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Race_0<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!((tx_context::sender(ctx) == instance.role_Race), 101);
        assert!(instance.joined_Race, 113);
        assert!(!instance.bailed_Race, 114);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Race = true;
            return
        };
        assert!(!instance.action_Race_0_done, 102);
        instance.action_Race_0_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Gambler_1<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, bet: u64) {
        assert!((tx_context::sender(ctx) == instance.role_Gambler), 101);
        assert!(instance.joined_Gambler, 113);
        assert!(!instance.bailed_Gambler, 114);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Gambler = true;
            return
        };
        assert!(!instance.action_Gambler_1_done, 102);
        assert!((instance.action_Race_0_done || instance.bailed_Race), 103);
        assert!((((bet == 1) || (bet == 2)) || (bet == 3)), 104);
        instance.Gambler_bet = bet;
        instance.done_Gambler_bet = true;
        instance.action_Gambler_1_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun move_Race_2<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext, winner: u64) {
        assert!((tx_context::sender(ctx) == instance.role_Race), 101);
        assert!(instance.joined_Race, 113);
        assert!(!instance.bailed_Race, 114);
        if ((clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))) {
            instance.bailed_Race = true;
            return
        };
        assert!(!instance.action_Race_2_done, 102);
        assert!((instance.action_Gambler_1_done || instance.bailed_Gambler), 103);
        assert!((((winner == 1) || (winner == 2)) || (winner == 3)), 104);
        instance.Race_winner = winner;
        instance.done_Race_winner = true;
        instance.action_Race_2_done = true;
        instance.last_ts_ms = clock::timestamp_ms(clock);
    }

    public entry fun finalize<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!((instance.action_Race_2_done || (clock::timestamp_ms(clock) > (instance.last_ts_ms + instance.timeout_ms))), 107);
        assert!(!instance.finalized, 108);
        let mut total_payout: u64 = 0;
        instance.claim_amount_Gambler = if ((!instance.done_Race_winner || (instance.Race_winner == instance.Gambler_bet))) 20 else 0;
        total_payout = (total_payout + if ((!instance.done_Race_winner || (instance.Race_winner == instance.Gambler_bet))) 20 else 0);
        instance.claim_amount_Race = if ((!instance.done_Race_winner || (instance.Race_winner == instance.Gambler_bet))) 0 else 20;
        total_payout = (total_payout + if ((!instance.done_Race_winner || (instance.Race_winner == instance.Gambler_bet))) 0 else 20);
        assert!((total_payout <= balance::value<Asset>(&instance.pot)), 109);
        instance.finalized = true;
    }

    public entry fun claim_Gambler<Asset>(instance: &mut Instance<Asset>, clock: &clock::Clock, ctx: &mut tx_context::TxContext) {
        assert!(instance.finalized, 110);
        assert!(!instance.claimed_Gambler, 111);
        instance.claimed_Gambler = true;
        let amount: u64 = instance.claim_amount_Gambler;
        if ((amount > 0)) {
            let payout_coin = coin::take<Asset>(&mut instance.pot, amount, ctx);
            transfer::public_transfer<Asset>(payout_coin, tx_context::sender(ctx));
        };
    }

}
