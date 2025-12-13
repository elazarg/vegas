use anchor_lang::prelude::*;

declare_id!("Fg6PaFpoGXkYsidMpWTK6W2BeZ7FEfcYkg476zPFsLnS"); // Placeholder ID

#[program]
pub mod bet {
    use super::*;

    pub fn init_instance(ctx: Context<Init_instance>, game_id: u64, timeout: i64) -> Result<()> {
         game.game_id = game_id;
         game.timeout = timeout;
         game.last_ts = Clock::get()?.unix_timestamp;
         game.pot_total = 0;
        Ok(())
    }

    pub fn move_Race_0(ctx: Context<Move_Race_0>, ) -> Result<()> {
         require!(!(game.joined[1 as usize]), ErrorCode::AlreadyJoined);
         game.roles[1 as usize] = signer.key();
         game.joined[1 as usize] = true;
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
             game.bailed[1 as usize] = true;
         }
         game.action_done[0 as usize] = true;
         game.action_ts[0 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_Gambler_1(ctx: Context<Move_Gambler_1>, bet: i64) -> Result<()> {
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
         if !(game.bailed[0 as usize]) {
             require!((game.action_done[0 as usize] || game.bailed[1 as usize]), ErrorCode::DependencyNotMet);
         }
         require!((((bet == 1) || (bet == 2)) || (bet == 3)), ErrorCode::GuardFailed);
         game.Gambler_bet = bet;
         game.done_Gambler_bet = true;
         game.action_done[1 as usize] = true;
         game.action_ts[1 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_Race_2(ctx: Context<Move_Race_2>, winner: i64) -> Result<()> {
         require!((game.roles[1 as usize] == signer.key()), ErrorCode::Unauthorized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
         }
         if !(game.bailed[1 as usize]) {
             require!((game.action_done[1 as usize] || game.bailed[0 as usize]), ErrorCode::DependencyNotMet);
         }
         require!((((winner == 1) || (winner == 2)) || (winner == 3)), ErrorCode::GuardFailed);
         game.Race_winner = winner;
         game.done_Race_winner = true;
         game.action_done[2 as usize] = true;
         game.action_ts[2 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn finalize(ctx: Context<Finalize>, ) -> Result<()> {
         require!((game.action_done[2 as usize] || game.bailed[1 as usize]), ErrorCode::NotFinalized);
         let p_Gambler: u64 = (std::cmp::max(0, if (!(game.done_Race_winner) || (game.Race_winner == game.Gambler_bet)) { 20 } else { 0 })) as u64;
         let p_Race: u64 = (std::cmp::max(0, if (!(game.done_Race_winner) || (game.Race_winner == game.Gambler_bet)) { 0 } else { 20 })) as u64;
         if (((0 + p_Gambler) + p_Race) > game.pot_total) {
             game.claim_amount[0 as usize] = 10;
             game.claim_amount[1 as usize] = 10;
         } else {
             game.claim_amount[0 as usize] = p_Gambler;
             game.claim_amount[1 as usize] = p_Race;
         }
         game.is_finalized = true;
        Ok(())
    }

    pub fn claim_Gambler(ctx: Context<Claim_Gambler>, ) -> Result<()> {
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

    pub fn claim_Race(ctx: Context<Claim_Race>, ) -> Result<()> {
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
    #[account(init, payer = signer, space = 8 + 10240, seeds = [b"game", game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Move_Race_0<'info> {
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    pub signer: Signer<'info>,
    #[account(seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
#[instruction(bet: i64)]
pub struct Move_Gambler_1<'info> {
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    pub signer: Signer<'info>,
    #[account(seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
#[instruction(winner: i64)]
pub struct Move_Race_2<'info> {
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
pub struct Finalize<'info> {
    pub game: Account<'info, GameState>,
}

#[derive(Accounts)]
pub struct Claim_Gambler<'info> {
    pub game: Account<'info, GameState>,
    #[account(seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    #[account(address = game.roles[0])]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Claim_Race<'info> {
    pub game: Account<'info, GameState>,
    #[account(seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    #[account(address = game.roles[1])]
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
    pub action_done: [bool; 3],
    pub action_ts: [i64; 3],
    pub timeout: i64,
    pub pot_total: u64,
    pub is_finalized: bool,
    pub claimed: [bool; 2],
    pub claim_amount: [u64; 2],
    pub Gambler_bet: i64,
    pub done_Gambler_bet: bool,
    pub Race_winner: i64,
    pub done_Race_winner: bool,
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
