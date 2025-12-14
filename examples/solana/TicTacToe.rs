use anchor_lang::prelude::*;

declare_id!("Fg6PaFpoGXkYsidMpWTK6W2BeZ7FEfcYkg476zPFsLnS"); // Placeholder ID

#[program]
pub mod tictactoe {
    use super::*;

    pub fn init_instance(ctx: Context<Init_instance>, game_id: u64, timeout: i64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let vault = &mut ctx.accounts.vault;
        let signer = &mut ctx.accounts.signer;
         game.game_id = game_id;
         game.timeout = timeout;
         game.last_ts = Clock::get()?.unix_timestamp;
         game.pot_total = 0;
        Ok(())
    }

    pub fn move_X_0(ctx: Context<Move_X_0>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
        let vault = &mut ctx.accounts.vault;
         require!(!(game.is_finalized), ErrorCode::AlreadyDone);
         require!(!(game.joined[1 as usize]), ErrorCode::AlreadyJoined);
         game.roles[1 as usize] = signer.key();
         game.joined[1 as usize] = true;
         // Deposit 100 lamports
         anchor_lang::system_program::transfer(
            anchor_lang::context::CpiContext::new(
                ctx.accounts.system_program.to_account_info(),
                anchor_lang::system_program::Transfer {
                    from: ctx.accounts.signer.to_account_info(),
                    to: ctx.accounts.vault.to_account_info(),
                },
            ),
            100,
         )?;
         game.pot_total = (game.pot_total + 100);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[0 as usize]), ErrorCode::AlreadyDone);
         game.action_done[0 as usize] = true;
         game.action_ts[0 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_O_1(ctx: Context<Move_O_1>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
        let vault = &mut ctx.accounts.vault;
         require!(!(game.is_finalized), ErrorCode::AlreadyDone);
         require!(!(game.joined[0 as usize]), ErrorCode::AlreadyJoined);
         game.roles[0 as usize] = signer.key();
         game.joined[0 as usize] = true;
         // Deposit 100 lamports
         anchor_lang::system_program::transfer(
            anchor_lang::context::CpiContext::new(
                ctx.accounts.system_program.to_account_info(),
                anchor_lang::system_program::Transfer {
                    from: ctx.accounts.signer.to_account_info(),
                    to: ctx.accounts.vault.to_account_info(),
                },
            ),
            100,
         )?;
         game.pot_total = (game.pot_total + 100);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[1 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[0 as usize], ErrorCode::DependencyNotMet);
         }
         game.action_done[1 as usize] = true;
         game.action_ts[1 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_X_2(ctx: Context<Move_X_2>, c1: i64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::AlreadyDone);
         require!((game.roles[1 as usize] == signer.key()), ErrorCode::Unauthorized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[2 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[1 as usize], ErrorCode::DependencyNotMet);
         }
         require!((((c1 == 0) || (c1 == 1)) || (c1 == 4)), ErrorCode::GuardFailed);
         game.X_c1 = c1;
         game.done_X_c1 = true;
         game.action_done[2 as usize] = true;
         game.action_ts[2 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_O_3(ctx: Context<Move_O_3>, c1: i64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::AlreadyDone);
         require!((game.roles[0 as usize] == signer.key()), ErrorCode::Unauthorized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[3 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         }
         require!(((((((c1 == 1) || (c1 == 3)) || (c1 == 4)) || (c1 == 5)) || (c1 == 9)) && (game.X_c1 != c1)), ErrorCode::GuardFailed);
         game.O_c1 = c1;
         game.done_O_c1 = true;
         game.action_done[3 as usize] = true;
         game.action_ts[3 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_X_4(ctx: Context<Move_X_4>, c2: i64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::AlreadyDone);
         require!((game.roles[1 as usize] == signer.key()), ErrorCode::Unauthorized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[4 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[3 as usize], ErrorCode::DependencyNotMet);
         }
         require!(((((((((((c2 == 0) || (c2 == 1)) || (c2 == 2)) || (c2 == 3)) || (c2 == 4)) || (c2 == 5)) || (c2 == 6)) || (c2 == 7)) || (c2 == 8)) && (((game.X_c1 != game.O_c1) && (game.X_c1 != c2)) && (game.O_c1 != c2))), ErrorCode::GuardFailed);
         game.X_c2 = c2;
         game.done_X_c2 = true;
         game.action_done[4 as usize] = true;
         game.action_ts[4 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_O_5(ctx: Context<Move_O_5>, c2: i64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::AlreadyDone);
         require!((game.roles[0 as usize] == signer.key()), ErrorCode::Unauthorized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[5 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[3 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[4 as usize], ErrorCode::DependencyNotMet);
         }
         require!(((((((((((c2 == 0) || (c2 == 1)) || (c2 == 2)) || (c2 == 3)) || (c2 == 4)) || (c2 == 5)) || (c2 == 6)) || (c2 == 7)) || (c2 == 8)) && ((((((game.X_c1 != game.O_c1) && (game.X_c1 != game.X_c2)) && (game.X_c1 != c2)) && (game.O_c1 != game.X_c2)) && (game.O_c1 != c2)) && (game.X_c2 != c2))), ErrorCode::GuardFailed);
         game.O_c2 = c2;
         game.done_O_c2 = true;
         game.action_done[5 as usize] = true;
         game.action_ts[5 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_X_6(ctx: Context<Move_X_6>, c3: i64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::AlreadyDone);
         require!((game.roles[1 as usize] == signer.key()), ErrorCode::Unauthorized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[6 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[3 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[4 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[5 as usize], ErrorCode::DependencyNotMet);
         }
         require!(((((((((((c3 == 0) || (c3 == 1)) || (c3 == 2)) || (c3 == 3)) || (c3 == 4)) || (c3 == 5)) || (c3 == 6)) || (c3 == 7)) || (c3 == 8)) && ((((((((((game.X_c1 != game.O_c1) && (game.X_c1 != game.X_c2)) && (game.X_c1 != game.O_c2)) && (game.X_c1 != c3)) && (game.O_c1 != game.X_c2)) && (game.O_c1 != game.O_c2)) && (game.O_c1 != c3)) && (game.X_c2 != game.O_c2)) && (game.X_c2 != c3)) && (game.O_c2 != c3))), ErrorCode::GuardFailed);
         game.X_c3 = c3;
         game.done_X_c3 = true;
         game.action_done[6 as usize] = true;
         game.action_ts[6 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_O_7(ctx: Context<Move_O_7>, c3: i64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::AlreadyDone);
         require!((game.roles[0 as usize] == signer.key()), ErrorCode::Unauthorized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[7 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[3 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[4 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[5 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[6 as usize], ErrorCode::DependencyNotMet);
         }
         require!(((((((((((c3 == 0) || (c3 == 1)) || (c3 == 2)) || (c3 == 3)) || (c3 == 4)) || (c3 == 5)) || (c3 == 6)) || (c3 == 7)) || (c3 == 8)) && (((((((((((((((game.X_c1 != game.O_c1) && (game.X_c1 != game.X_c2)) && (game.X_c1 != game.O_c2)) && (game.X_c1 != game.X_c3)) && (game.X_c1 != c3)) && (game.O_c1 != game.X_c2)) && (game.O_c1 != game.O_c2)) && (game.O_c1 != game.X_c3)) && (game.O_c1 != c3)) && (game.X_c2 != game.O_c2)) && (game.X_c2 != game.X_c3)) && (game.X_c2 != c3)) && (game.O_c2 != game.X_c3)) && (game.O_c2 != c3)) && (game.X_c3 != c3))), ErrorCode::GuardFailed);
         game.O_c3 = c3;
         game.done_O_c3 = true;
         game.action_done[7 as usize] = true;
         game.action_ts[7 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_X_8(ctx: Context<Move_X_8>, c4: i64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::AlreadyDone);
         require!((game.roles[1 as usize] == signer.key()), ErrorCode::Unauthorized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[8 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[3 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[4 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[5 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[6 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[7 as usize], ErrorCode::DependencyNotMet);
         }
         require!(((((((((((c4 == 0) || (c4 == 1)) || (c4 == 2)) || (c4 == 3)) || (c4 == 4)) || (c4 == 5)) || (c4 == 6)) || (c4 == 7)) || (c4 == 8)) && (((((((((((((((((((((game.X_c1 != game.O_c1) && (game.X_c1 != game.X_c2)) && (game.X_c1 != game.O_c2)) && (game.X_c1 != game.X_c3)) && (game.X_c1 != game.O_c3)) && (game.X_c1 != c4)) && (game.O_c1 != game.X_c2)) && (game.O_c1 != game.O_c2)) && (game.O_c1 != game.X_c3)) && (game.O_c1 != game.O_c3)) && (game.O_c1 != c4)) && (game.X_c2 != game.O_c2)) && (game.X_c2 != game.X_c3)) && (game.X_c2 != game.O_c3)) && (game.X_c2 != c4)) && (game.O_c2 != game.X_c3)) && (game.O_c2 != game.O_c3)) && (game.O_c2 != c4)) && (game.X_c3 != game.O_c3)) && (game.X_c3 != c4)) && (game.O_c3 != c4))), ErrorCode::GuardFailed);
         game.X_c4 = c4;
         game.done_X_c4 = true;
         game.action_done[8 as usize] = true;
         game.action_ts[8 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_O_9(ctx: Context<Move_O_9>, c4: i64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::AlreadyDone);
         require!((game.roles[0 as usize] == signer.key()), ErrorCode::Unauthorized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[9 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[3 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[4 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[5 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[6 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[7 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[8 as usize], ErrorCode::DependencyNotMet);
         }
         require!(((((((((((c4 == 0) || (c4 == 1)) || (c4 == 2)) || (c4 == 3)) || (c4 == 4)) || (c4 == 5)) || (c4 == 6)) || (c4 == 7)) || (c4 == 8)) && ((((((((((((((((((((((((((((game.X_c1 != game.O_c1) && (game.X_c1 != game.X_c2)) && (game.X_c1 != game.O_c2)) && (game.X_c1 != game.X_c3)) && (game.X_c1 != game.O_c3)) && (game.X_c1 != game.X_c4)) && (game.X_c1 != c4)) && (game.O_c1 != game.X_c2)) && (game.O_c1 != game.O_c2)) && (game.O_c1 != game.X_c3)) && (game.O_c1 != game.O_c3)) && (game.O_c1 != game.X_c4)) && (game.O_c1 != c4)) && (game.X_c2 != game.O_c2)) && (game.X_c2 != game.X_c3)) && (game.X_c2 != game.O_c3)) && (game.X_c2 != game.X_c4)) && (game.X_c2 != c4)) && (game.O_c2 != game.X_c3)) && (game.O_c2 != game.O_c3)) && (game.O_c2 != game.X_c4)) && (game.O_c2 != c4)) && (game.X_c3 != game.O_c3)) && (game.X_c3 != game.X_c4)) && (game.X_c3 != c4)) && (game.O_c3 != game.X_c4)) && (game.O_c3 != c4)) && (game.X_c4 != c4))), ErrorCode::GuardFailed);
         game.O_c4 = c4;
         game.done_O_c4 = true;
         game.action_done[9 as usize] = true;
         game.action_ts[9 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn finalize(ctx: Context<Finalize>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
         require!(!(game.is_finalized), ErrorCode::AlreadyDone);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         require!((game.action_done[9 as usize] || game.bailed[0 as usize]), ErrorCode::NotFinalized);
         let p_X: u64 = (std::cmp::max(0, 100)) as u64;
         let p_O: u64 = (std::cmp::max(0, 100)) as u64;
         if (((0 + p_X) + p_O) > game.pot_total) {
             game.claim_amount[0 as usize] = 100;
             game.claim_amount[1 as usize] = 100;
         } else {
             game.claim_amount[0 as usize] = p_O;
             game.claim_amount[1 as usize] = p_X;
         }
         game.is_finalized = true;
        Ok(())
    }

    pub fn claim_O(ctx: Context<Claim_O>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let vault = &mut ctx.accounts.vault;
        let signer = &mut ctx.accounts.signer;
         require!(game.is_finalized, ErrorCode::NotFinalized);
         require!(!(game.claimed[0 as usize]), ErrorCode::AlreadyClaimed);
         game.claimed[0 as usize] = true;
         {
    let amount = game.claim_amount[0];
    if amount > 0 {
        let seeds = &[
            b"vault",
            game.to_account_info().key.as_ref(),
            &[ctx.bumps.vault],
        ];
        let signer_seeds = &[&seeds[..]];
        anchor_lang::system_program::transfer(
            anchor_lang::context::CpiContext::new_with_signer(
                ctx.accounts.system_program.to_account_info(),
                anchor_lang::system_program::Transfer {
                    from: ctx.accounts.vault.to_account_info(),
                    to: ctx.accounts.signer.to_account_info(),
                },
                signer_seeds
            ),
            amount,
        )?;
    }
}
        Ok(())
    }

    pub fn claim_X(ctx: Context<Claim_X>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let vault = &mut ctx.accounts.vault;
        let signer = &mut ctx.accounts.signer;
         require!(game.is_finalized, ErrorCode::NotFinalized);
         require!(!(game.claimed[1 as usize]), ErrorCode::AlreadyClaimed);
         game.claimed[1 as usize] = true;
         {
    let amount = game.claim_amount[1];
    if amount > 0 {
        let seeds = &[
            b"vault",
            game.to_account_info().key.as_ref(),
            &[ctx.bumps.vault],
        ];
        let signer_seeds = &[&seeds[..]];
        anchor_lang::system_program::transfer(
            anchor_lang::context::CpiContext::new_with_signer(
                ctx.accounts.system_program.to_account_info(),
                anchor_lang::system_program::Transfer {
                    from: ctx.accounts.vault.to_account_info(),
                    to: ctx.accounts.signer.to_account_info(),
                },
                signer_seeds
            ),
            amount,
        )?;
    }
}
        Ok(())
    }

}

#[derive(Accounts)]
#[instruction(game_id: u64, timeout: i64)]
pub struct Init_instance<'info> {
    #[account(mut)]
    #[account(init, payer = signer, space = 289, seeds = [b"game", game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    #[account(init, payer = signer, space = 0, seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    #[account(mut)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Move_X_0<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
    #[account(mut)]
    #[account(seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Move_O_1<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
    #[account(mut)]
    #[account(seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
#[instruction(c1: i64)]
pub struct Move_X_2<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(c1: i64)]
pub struct Move_O_3<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(c2: i64)]
pub struct Move_X_4<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(c2: i64)]
pub struct Move_O_5<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(c3: i64)]
pub struct Move_X_6<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(c3: i64)]
pub struct Move_O_7<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(c4: i64)]
pub struct Move_X_8<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(c4: i64)]
pub struct Move_O_9<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
pub struct Finalize<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
}

#[derive(Accounts)]
pub struct Claim_O<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    #[account(seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    #[account(mut)]
    #[account(constraint = signer.key() == game.roles[0] @ ErrorCode::Unauthorized)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Claim_X<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    #[account(seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    #[account(mut)]
    #[account(constraint = signer.key() == game.roles[1] @ ErrorCode::Unauthorized)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[account]
pub struct GameState {
    pub game_id: u64,
    pub roles: [Pubkey; 2],
    pub joined: [bool; 2],
    pub last_ts: i64,
    pub bailed: [bool; 2],
    pub action_done: [bool; 10],
    pub action_ts: [i64; 10],
    pub timeout: i64,
    pub pot_total: u64,
    pub is_finalized: bool,
    pub claimed: [bool; 2],
    pub claim_amount: [u64; 2],
    pub X_c1: i64,
    pub done_X_c1: bool,
    pub O_c1: i64,
    pub done_O_c1: bool,
    pub X_c2: i64,
    pub done_X_c2: bool,
    pub O_c2: i64,
    pub done_O_c2: bool,
    pub X_c3: i64,
    pub done_X_c3: bool,
    pub O_c3: i64,
    pub done_O_c3: bool,
    pub X_c4: i64,
    pub done_X_c4: bool,
    pub O_c4: i64,
    pub done_O_c4: bool,
}

#[error_code]
pub enum ErrorCode {
    #[msg("Player has not joined")]
    NotJoined,
    #[msg("Player already joined")]
    AlreadyJoined,
    #[msg("Signer is not the authorized player")]
    Unauthorized,
    #[msg("Action timed out")]
    Timeout,
    #[msg("Action dependency not met")]
    DependencyNotMet,
    #[msg("Reveal hash mismatch")]
    InvalidReveal,
    #[msg("Action already performed")]
    AlreadyDone,
    #[msg("Funds already claimed")]
    AlreadyClaimed,
    #[msg("Game not finalized")]
    NotFinalized,
    #[msg("Invalid amount")]
    BadAmount,
    #[msg("Guard condition failed")]
    GuardFailed,
}
