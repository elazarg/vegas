use anchor_lang::prelude::*;

declare_id!("Fg6PaFpoGXkYsidMpWTK6W2BeZ7FEfcYkg476zPFsLnS"); // Placeholder ID

#[program]
pub mod simple {
    use super::*;

    pub fn init_instance(ctx: Context<Init_instance>, game_id: u64, timeout: i64) -> Result<()> {
         game.game_id = game_id;
         game.timeout = timeout;
         game.last_ts = Clock::get()?.unix_timestamp;
         game.pot_total = 0;
        Ok(())
    }

    pub fn move_A_0(ctx: Context<Move_A_0>, ) -> Result<()> {
         require!(!(game.joined[0 as usize]), ErrorCode::AlreadyJoined);
         game.roles[0 as usize] = signer.key();
         game.joined[0 as usize] = true;
         // Deposit 6 lamports
         anchor_lang::system_program::transfer(
            anchor_lang::context::CpiContext::new(
                ctx.accounts.system_program.to_account_info(),
                anchor_lang::system_program::Transfer {
                    from: ctx.accounts.signer.to_account_info(),
                    to: ctx.accounts.vault.to_account_info(),
                },
            ),
            6,
         )?;
         game.pot_total = (game.pot_total + 6);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
         }
         game.action_done[0 as usize] = true;
         game.action_ts[0 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_B_1(ctx: Context<Move_B_1>, ) -> Result<()> {
         require!(!(game.joined[1 as usize]), ErrorCode::AlreadyJoined);
         game.roles[1 as usize] = signer.key();
         game.joined[1 as usize] = true;
         // Deposit 6 lamports
         anchor_lang::system_program::transfer(
            anchor_lang::context::CpiContext::new(
                ctx.accounts.system_program.to_account_info(),
                anchor_lang::system_program::Transfer {
                    from: ctx.accounts.signer.to_account_info(),
                    to: ctx.accounts.vault.to_account_info(),
                },
            ),
            6,
         )?;
         game.pot_total = (game.pot_total + 6);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
         }
         if !(game.bailed[1 as usize]) {
             require!((game.action_done[0 as usize] || game.bailed[0 as usize]), ErrorCode::DependencyNotMet);
         }
         game.action_done[1 as usize] = true;
         game.action_ts[1 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_A_2(ctx: Context<Move_A_2>, hidden_c: [u8; 32]) -> Result<()> {
         require!((game.roles[0 as usize] == signer.key()), ErrorCode::Unauthorized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
         }
         if !(game.bailed[0 as usize]) {
             require!((game.action_done[1 as usize] || game.bailed[1 as usize]), ErrorCode::DependencyNotMet);
         }
         game.A_c_hidden = hidden_c;
         game.done_A_c_hidden = true;
         game.action_done[2 as usize] = true;
         game.action_ts[2 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_B_3(ctx: Context<Move_B_3>, c: bool) -> Result<()> {
         require!((game.roles[1 as usize] == signer.key()), ErrorCode::Unauthorized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
         }
         if !(game.bailed[1 as usize]) {
             require!((game.action_done[2 as usize] || game.bailed[0 as usize]), ErrorCode::DependencyNotMet);
         }
         game.B_c = c;
         game.done_B_c = true;
         game.action_done[3 as usize] = true;
         game.action_ts[3 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_A_4(ctx: Context<Move_A_4>, c: bool, salt: u64) -> Result<()> {
         require!((game.roles[0 as usize] == signer.key()), ErrorCode::Unauthorized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
         }
         if !(game.bailed[0 as usize]) {
             require!((game.action_done[3 as usize] || game.bailed[1 as usize]), ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!((game.action_done[2 as usize] || game.bailed[0 as usize]), ErrorCode::DependencyNotMet);
         }
         {
    let val_bytes = (c as u8).to_le_bytes();
    let salt_bytes = salt.to_le_bytes();
    let hash = anchor_lang::solana_program::keccak::hashv(&[&val_bytes, &salt_bytes]).0;
    require!(hash == game.A_c_hidden, ErrorCode::InvalidReveal);
}
         game.A_c = c;
         game.done_A_c = true;
         game.action_done[4 as usize] = true;
         game.action_ts[4 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn finalize(ctx: Context<Finalize>, ) -> Result<()> {
         require!((game.action_done[4 as usize] || game.bailed[0 as usize]), ErrorCode::NotFinalized);
         let p_A: u64 = (std::cmp::max(0, if (!(game.done_A_c) && !(game.done_B_c)) { 6 } else { if !(game.done_A_c) { 1 } else { if !(game.done_B_c) { 11 } else { if (game.A_c != game.B_c) { 9 } else { 3 } } } })) as u64;
         let p_B: u64 = (std::cmp::max(0, if (!(game.done_A_c) && !(game.done_B_c)) { 6 } else { if !(game.done_A_c) { 11 } else { if !(game.done_B_c) { 1 } else { if (game.A_c == game.B_c) { 9 } else { 3 } } } })) as u64;
         if (((0 + p_A) + p_B) > game.pot_total) {
             game.claim_amount[0 as usize] = 6;
             game.claim_amount[1 as usize] = 6;
         } else {
             game.claim_amount[0 as usize] = p_A;
             game.claim_amount[1 as usize] = p_B;
         }
         game.is_finalized = true;
        Ok(())
    }

    pub fn claim_A(ctx: Context<Claim_A>, ) -> Result<()> {
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

    pub fn claim_B(ctx: Context<Claim_B>, ) -> Result<()> {
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
pub struct Move_A_0<'info> {
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    pub signer: Signer<'info>,
    #[account(seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Move_B_1<'info> {
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    pub signer: Signer<'info>,
    #[account(seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
#[instruction(hidden_c: [u8; 32])]
pub struct Move_A_2<'info> {
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(c: bool)]
pub struct Move_B_3<'info> {
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(c: bool, salt: u64)]
pub struct Move_A_4<'info> {
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
pub struct Finalize<'info> {
    pub game: Account<'info, GameState>,
}

#[derive(Accounts)]
pub struct Claim_A<'info> {
    pub game: Account<'info, GameState>,
    #[account(seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    #[account(address = game.roles[0])]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Claim_B<'info> {
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
    pub action_done: [bool; 5],
    pub action_ts: [i64; 5],
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
