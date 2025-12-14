use anchor_lang::prelude::*;

declare_id!("Fg6PaFpoGXkYsidMpWTK6W2BeZ7FEfcYkg476zPFsLnS"); // Placeholder ID

#[program]
pub mod trivial1 {
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

    pub fn move_A_0(ctx: Context<Move_A_0>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
        let vault = &mut ctx.accounts.vault;
         require!(!(game.joined[0 as usize]), ErrorCode::AlreadyJoined);
         game.roles[0 as usize] = signer.key();
         game.joined[0 as usize] = true;
         // Deposit 10 lamports
         anchor_lang::system_program::transfer(
            anchor_lang::context::CpiContext::new(
                ctx.accounts.system_program.to_account_info(),
                anchor_lang::system_program::Transfer {
                    from: ctx.accounts.signer.to_account_info(),
                    to: ctx.accounts.vault.to_account_info(),
                },
            ),
            10,
         )?;
         game.pot_total = (game.pot_total + 10);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
         }
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[0 as usize]), ErrorCode::AlreadyDone);
         game.action_done[0 as usize] = true;
         game.action_ts[0 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn finalize(ctx: Context<Finalize>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
         }
         require!((game.action_done[0 as usize] || game.bailed[0 as usize]), ErrorCode::NotFinalized);
         let p_A: u64 = (std::cmp::max(0, 10)) as u64;
         if ((0 + p_A) > game.pot_total) {
             game.claim_amount[0 as usize] = 10;
         } else {
             game.claim_amount[0 as usize] = p_A;
         }
         game.is_finalized = true;
        Ok(())
    }

    pub fn claim_A(ctx: Context<Claim_A>, ) -> Result<()> {
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

}

#[derive(Accounts)]
#[instruction(game_id: u64, timeout: i64)]
pub struct Init_instance<'info> {
    #[account(mut)]
    #[account(init, payer = signer, space = 93, seeds = [b"game", game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    #[account(init, payer = signer, space = 0, seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    #[account(mut)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Move_A_0<'info> {
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
    #[account(seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    #[account(mut)]
    #[account(constraint = signer.key() == game.roles[0] @ ErrorCode::Unauthorized)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[account]
pub struct GameState {
    pub game_id: u64,
    pub roles: [Pubkey; 1],
    pub joined: [bool; 1],
    pub last_ts: i64,
    pub bailed: [bool; 1],
    pub action_done: [bool; 1],
    pub action_ts: [i64; 1],
    pub timeout: i64,
    pub pot_total: u64,
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
