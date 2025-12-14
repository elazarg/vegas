use anchor_lang::prelude::*;

declare_id!("Fg6PaFpoGXkYsidMpWTK6W2BeZ7FEfcYkg476zPFsLnS"); // Placeholder ID

#[program]
pub mod prisoners {
    use super::*;

    pub fn init_instance(ctx: Context<Init_instance>, game_id: u64, timeout: i64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         game.game_id = game_id;
         game.timeout = timeout;
         game.last_ts = Clock::get()?.unix_timestamp;
         game.pot_total = 0;
        Ok(())
    }

    pub fn timeout_A(ctx: Context<Timeout_A>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let _signer = &mut ctx.accounts._signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!(!(game.bailed[0 as usize]), ErrorCode::AlreadyDone);
         require!((Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)), ErrorCode::NotTimedOut);
         game.bailed[0 as usize] = true;
        Ok(())
    }

    pub fn timeout_B(ctx: Context<Timeout_B>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let _signer = &mut ctx.accounts._signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!(!(game.bailed[1 as usize]), ErrorCode::AlreadyDone);
         require!((Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)), ErrorCode::NotTimedOut);
         game.bailed[1 as usize] = true;
        Ok(())
    }

    pub fn move_A_0(ctx: Context<Move_A_0>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!(!(game.joined[0 as usize]), ErrorCode::AlreadyJoined);
         game.roles[0 as usize] = signer.key();
         game.joined[0 as usize] = true;
         // Deposit 100 lamports
         anchor_lang::system_program::transfer(
            anchor_lang::context::CpiContext::new(
                ctx.accounts.system_program.to_account_info(),
                anchor_lang::system_program::Transfer {
                    from: ctx.accounts.signer.to_account_info(),
                    to: ctx.accounts.game.to_account_info(),
                },
            ),
            100,
         )?;
         game.pot_total = (game.pot_total + 100);
         game.deposited[0 as usize] = (game.deposited[0 as usize] + 100);
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[0 as usize]), ErrorCode::AlreadyDone);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         game.action_done[0 as usize] = true;
         game.action_ts[0 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_B_1(ctx: Context<Move_B_1>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!(!(game.joined[1 as usize]), ErrorCode::AlreadyJoined);
         game.roles[1 as usize] = signer.key();
         game.joined[1 as usize] = true;
         // Deposit 100 lamports
         anchor_lang::system_program::transfer(
            anchor_lang::context::CpiContext::new(
                ctx.accounts.system_program.to_account_info(),
                anchor_lang::system_program::Transfer {
                    from: ctx.accounts.signer.to_account_info(),
                    to: ctx.accounts.game.to_account_info(),
                },
            ),
            100,
         )?;
         game.pot_total = (game.pot_total + 100);
         game.deposited[1 as usize] = (game.deposited[1 as usize] + 100);
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[1 as usize]), ErrorCode::AlreadyDone);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[0 as usize], ErrorCode::DependencyNotMet);
         }
         game.action_done[1 as usize] = true;
         game.action_ts[1 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_A_2(ctx: Context<Move_A_2>, hidden_c: [u8; 32]) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!((game.roles[0 as usize] == signer.key()), ErrorCode::Unauthorized);
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[2 as usize]), ErrorCode::AlreadyDone);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[1 as usize], ErrorCode::DependencyNotMet);
         }
         game.A_c_hidden = hidden_c;
         game.done_A_c_hidden = true;
         game.action_done[2 as usize] = true;
         game.action_ts[2 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_B_4(ctx: Context<Move_B_4>, hidden_c: [u8; 32]) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!((game.roles[1 as usize] == signer.key()), ErrorCode::Unauthorized);
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[4 as usize]), ErrorCode::AlreadyDone);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[1 as usize], ErrorCode::DependencyNotMet);
         }
         game.B_c_hidden = hidden_c;
         game.done_B_c_hidden = true;
         game.action_done[4 as usize] = true;
         game.action_ts[4 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_A_3(ctx: Context<Move_A_3>, c: bool, salt: u64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!((game.roles[0 as usize] == signer.key()), ErrorCode::Unauthorized);
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[3 as usize]), ErrorCode::AlreadyDone);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[1 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[4 as usize], ErrorCode::DependencyNotMet);
         }
         {
             let val_bytes = (c as u8).to_be_bytes();
             let salt_bytes = salt.to_be_bytes();
             let hash = anchor_lang::solana_program::keccak::hashv(&[&val_bytes, &salt_bytes]).0;
             require!(hash == game.A_c_hidden, ErrorCode::InvalidReveal);
         }
         game.A_c = c;
         game.done_A_c = true;
         game.action_done[3 as usize] = true;
         game.action_ts[3 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_B_5(ctx: Context<Move_B_5>, c: bool, salt: u64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!((game.roles[1 as usize] == signer.key()), ErrorCode::Unauthorized);
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[5 as usize]), ErrorCode::AlreadyDone);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[1 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[4 as usize], ErrorCode::DependencyNotMet);
         }
         {
             let val_bytes = (c as u8).to_be_bytes();
             let salt_bytes = salt.to_be_bytes();
             let hash = anchor_lang::solana_program::keccak::hashv(&[&val_bytes, &salt_bytes]).0;
             require!(hash == game.B_c_hidden, ErrorCode::InvalidReveal);
         }
         game.B_c = c;
         game.done_B_c = true;
         game.action_done[5 as usize] = true;
         game.action_ts[5 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn finalize(ctx: Context<Finalize>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         let spendable_pot: u64 = {
    let rent = Rent::get()?.minimum_balance(8 + GameState::INIT_SPACE);
    let lamports = **game.to_account_info().lamports.borrow();
    lamports.saturating_sub(rent)
};
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         }
         require!((game.action_done[3 as usize] || game.bailed[0 as usize]), ErrorCode::NotFinalized);
         require!((game.action_done[5 as usize] || game.bailed[1 as usize]), ErrorCode::NotFinalized);
         let p_A: u64 = (std::cmp::max(0, if (game.done_A_c && game.done_B_c) { if (game.A_c && game.B_c) { 100 } else { if (game.A_c && !(game.B_c)) { 0 } else { if (!(game.A_c) && game.B_c) { 200 } else { 90 } } } } else { if !(game.done_A_c) { 0 } else { 200 } })) as u64;
         let p_B: u64 = (std::cmp::max(0, if (game.done_A_c && game.done_B_c) { if (game.A_c && game.B_c) { 100 } else { if (game.A_c && !(game.B_c)) { 200 } else { if (!(game.A_c) && game.B_c) { 0 } else { 110 } } } } else { if !(game.done_A_c) { 200 } else { 0 } })) as u64;
         if (((0 + p_A) + p_B) > spendable_pot) {
             game.claim_amount[0 as usize] = game.deposited[0 as usize];
             game.claim_amount[1 as usize] = game.deposited[1 as usize];
         } else {
             game.claim_amount[0 as usize] = p_A;
             game.claim_amount[1 as usize] = p_B;
         }
         game.is_finalized = true;
        Ok(())
    }

    pub fn claim_A(ctx: Context<Claim_A>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(game.is_finalized, ErrorCode::NotFinalized);
         require!(!(game.claimed[0 as usize]), ErrorCode::AlreadyClaimed);
         game.claimed[0 as usize] = true;
         {
             let amount = game.claim_amount[0];
             if amount > 0 {
                 let rent_balance = Rent::get()?.minimum_balance(8 + GameState::INIT_SPACE);
                 let game_lamports = **game.to_account_info().lamports.borrow();
                 let spendable = game_lamports.checked_sub(rent_balance).ok_or(ErrorCode::InsufficientFunds)?;
                 if amount > spendable {
                      return err!(ErrorCode::InsufficientFunds);
                 }
                 **game.to_account_info().try_borrow_mut_lamports()? -= amount;
                 **signer.to_account_info().try_borrow_mut_lamports()? += amount;
             }
         }
        Ok(())
    }

    pub fn claim_B(ctx: Context<Claim_B>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(game.is_finalized, ErrorCode::NotFinalized);
         require!(!(game.claimed[1 as usize]), ErrorCode::AlreadyClaimed);
         game.claimed[1 as usize] = true;
         {
             let amount = game.claim_amount[1];
             if amount > 0 {
                 let rent_balance = Rent::get()?.minimum_balance(8 + GameState::INIT_SPACE);
                 let game_lamports = **game.to_account_info().lamports.borrow();
                 let spendable = game_lamports.checked_sub(rent_balance).ok_or(ErrorCode::InsufficientFunds)?;
                 if amount > spendable {
                      return err!(ErrorCode::InsufficientFunds);
                 }
                 **game.to_account_info().try_borrow_mut_lamports()? -= amount;
                 **signer.to_account_info().try_borrow_mut_lamports()? += amount;
             }
         }
        Ok(())
    }

}

#[derive(Accounts)]
#[instruction(game_id: u64, timeout: i64)]
pub struct Init_instance<'info> {
    #[account(mut)]
    #[account(init, payer = signer, space = 8 + GameState::INIT_SPACE, seeds = [b"game", game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Timeout_A<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub _signer: Signer<'info>,
}

#[derive(Accounts)]
pub struct Timeout_B<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub _signer: Signer<'info>,
}

#[derive(Accounts)]
pub struct Move_A_0<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Move_B_1<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
#[instruction(hidden_c: [u8; 32])]
pub struct Move_A_2<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(hidden_c: [u8; 32])]
pub struct Move_B_4<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(c: bool, salt: u64)]
pub struct Move_A_3<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(c: bool, salt: u64)]
pub struct Move_B_5<'info> {
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
pub struct Claim_A<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    #[account(constraint = signer.key() == game.roles[0] @ ErrorCode::Unauthorized)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Claim_B<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    #[account(constraint = signer.key() == game.roles[1] @ ErrorCode::Unauthorized)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[account]
#[derive(InitSpace)]
pub struct GameState {
    pub game_id: u64,
    pub roles: [Pubkey; 2],
    pub joined: [bool; 2],
    pub deposited: [u64; 2],
    pub last_ts: i64,
    pub bailed: [bool; 2],
    pub action_done: [bool; 6],
    pub action_ts: [i64; 6],
    pub timeout: i64,
    pub pot_total: u64,
    pub is_finalized: bool,
    pub claimed: [bool; 2],
    pub claim_amount: [u64; 2],
    pub A_c: bool,
    pub done_A_c: bool,
    pub A_c_hidden: [u8; 32],
    pub done_A_c_hidden: bool,
    pub B_c: bool,
    pub done_B_c: bool,
    pub B_c_hidden: [u8; 32],
    pub done_B_c_hidden: bool,
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
    #[msg("Action not yet timed out")]
    NotTimedOut,
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
    #[msg("Game already finalized")]
    GameFinalized,
    #[msg("Invalid amount")]
    BadAmount,
    #[msg("Insufficient funds including rent")]
    InsufficientFunds,
    #[msg("Guard condition failed")]
    GuardFailed,
}
