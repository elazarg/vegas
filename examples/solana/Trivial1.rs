use anchor_lang::prelude::*;

declare_id!("Fg6PaFpoGXkYsidMpWTK6W2BeZ7FEfcYkg476zPFsLnS"); // Placeholder ID

#[program]
pub mod trivial1 {
    use super::*;

    pub fn init_instance(ctx: Context<Init_instance>, game_id: u64, timeout: i64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         game.creator = signer.key();
         game.game_id = game_id;
         game.timeout = timeout;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn close_game(ctx: Context<Close_game>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let _creator = &mut ctx.accounts._creator;
         let now: i64 = Clock::get()?.unix_timestamp;
         require!((((now > (game.last_ts + game.timeout)) && !(game.joined[0 as usize])) || (game.is_finalized && game.claimed[0 as usize])), ErrorCode::CannotClose);
        Ok(())
    }

    pub fn timeout_A(ctx: Context<Timeout_A>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
         let now: i64 = Clock::get()?.unix_timestamp;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!(!(game.bailed[0 as usize]), ErrorCode::AlreadyDone);
         require!((now > (game.last_ts + game.timeout)), ErrorCode::NotTimedOut);
         game.bailed[0 as usize] = true;
        Ok(())
    }

    pub fn move_A_0(ctx: Context<Move_A_0>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         let now: i64 = Clock::get()?.unix_timestamp;
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!((now <= (game.last_ts + game.timeout)), ErrorCode::Timeout);
         require!(!(game.action_done[0 as usize]), ErrorCode::AlreadyDone);
         require!(!(game.joined[0 as usize]), ErrorCode::AlreadyJoined);
         game.roles[0 as usize] = signer.key();
         game.joined[0 as usize] = true;
         // Deposit 10 lamports
         anchor_lang::system_program::transfer(
            anchor_lang::context::CpiContext::new(
                ctx.accounts.system_program.to_account_info(),
                anchor_lang::system_program::Transfer {
                    from: ctx.accounts.signer.to_account_info(),
                    to: ctx.accounts.game.to_account_info(),
                },
            ),
            10,
         )?;
         game.deposited[0 as usize] = (game.deposited[0 as usize] + 10);
         game.action_done[0 as usize] = true;
         game.action_ts[0 as usize] = now;
         game.last_ts = now;
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
         require!((game.action_done[0 as usize] || game.bailed[0 as usize]), ErrorCode::NotFinalized);
         let p_A: u64 = (std::cmp::max(0, 10)) as u64;
         if ((0 + p_A) > spendable_pot) {
             game.claim_amount[0 as usize] = game.deposited[0 as usize];
         } else {
             game.claim_amount[0 as usize] = p_A;
         }
         if (game.claim_amount[0 as usize] == 0) {
             game.claimed[0 as usize] = true;
         }
         game.is_finalized = true;
        Ok(())
    }

    pub fn claim_A(ctx: Context<Claim_A>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let recipient = &mut ctx.accounts.recipient;
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
                 **recipient.to_account_info().try_borrow_mut_lamports()? += amount;
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
pub struct Close_game<'info> {
    #[account(mut, close = _creator, seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    #[account(address = game.creator)]
    pub _creator: SystemAccount<'info>,
}

#[derive(Accounts)]
pub struct Timeout_A<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
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
    #[account(address = game.roles[0] @ ErrorCode::Unauthorized)]
    pub recipient: SystemAccount<'info>,
    pub system_program: Program<'info, System>,
}

#[account]
#[derive(InitSpace)]
pub struct GameState {
    pub creator: Pubkey,
    pub game_id: u64,
    pub roles: [Pubkey; 1],
    pub joined: [bool; 1],
    pub deposited: [u64; 1],
    pub last_ts: i64,
    pub bailed: [bool; 1],
    pub action_done: [bool; 1],
    pub action_ts: [i64; 1],
    pub timeout: i64,
    pub is_finalized: bool,
    pub claimed: [bool; 1],
    pub claim_amount: [u64; 1],
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
    #[msg("Cannot close game yet")]
    CannotClose,
    #[msg("Guard condition failed")]
    GuardFailed,
}
