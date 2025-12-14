use anchor_lang::prelude::*;

declare_id!("Fg6PaFpoGXkYsidMpWTK6W2BeZ7FEfcYkg476zPFsLnS"); // Placeholder ID

#[program]
pub mod oddsevensshort {
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

    pub fn move_Odd_0(ctx: Context<Move_Odd_0>, hidden_c: [u8; 32]) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
        let vault = &mut ctx.accounts.vault;
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
         }
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[0 as usize]), ErrorCode::AlreadyDone);
         game.Odd_c_hidden = hidden_c;
         game.done_Odd_c_hidden = true;
         game.action_done[0 as usize] = true;
         game.action_ts[0 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_Even_2(ctx: Context<Move_Even_2>, hidden_c: [u8; 32]) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
        let vault = &mut ctx.accounts.vault;
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
         }
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[2 as usize]), ErrorCode::AlreadyDone);
         game.Even_c_hidden = hidden_c;
         game.done_Even_c_hidden = true;
         game.action_done[2 as usize] = true;
         game.action_ts[2 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_Odd_1(ctx: Context<Move_Odd_1>, c: bool, salt: u64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!((game.roles[1 as usize] == signer.key()), ErrorCode::Unauthorized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
         }
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[1 as usize]), ErrorCode::AlreadyDone);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[0 as usize], ErrorCode::DependencyNotMet);
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         }
         {
    let val_bytes = (c as u8).to_le_bytes();
    let salt_bytes = salt.to_le_bytes();
    let hash = anchor_lang::solana_program::keccak::hashv(&[&val_bytes, &salt_bytes]).0;
    require!(hash == game.Odd_c_hidden, ErrorCode::InvalidReveal);
}
         game.Odd_c = c;
         game.done_Odd_c = true;
         game.action_done[1 as usize] = true;
         game.action_ts[1 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_Even_3(ctx: Context<Move_Even_3>, c: bool, salt: u64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!((game.roles[0 as usize] == signer.key()), ErrorCode::Unauthorized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
         }
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[3 as usize]), ErrorCode::AlreadyDone);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[0 as usize], ErrorCode::DependencyNotMet);
         }
         {
    let val_bytes = (c as u8).to_le_bytes();
    let salt_bytes = salt.to_le_bytes();
    let hash = anchor_lang::solana_program::keccak::hashv(&[&val_bytes, &salt_bytes]).0;
    require!(hash == game.Even_c_hidden, ErrorCode::InvalidReveal);
}
         game.Even_c = c;
         game.done_Even_c = true;
         game.action_done[3 as usize] = true;
         game.action_ts[3 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn finalize(ctx: Context<Finalize>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
         }
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
         }
         require!((game.action_done[1 as usize] || game.bailed[1 as usize]), ErrorCode::NotFinalized);
         require!((game.action_done[3 as usize] || game.bailed[0 as usize]), ErrorCode::NotFinalized);
         let p_Even: u64 = (std::cmp::max(0, if (game.done_Even_c && game.done_Odd_c) { if (game.Even_c == game.Odd_c) { 126 } else { 74 } } else { if (!(game.done_Even_c) && game.done_Odd_c) { 20 } else { if (game.done_Even_c && !(game.done_Odd_c)) { 180 } else { 100 } } })) as u64;
         let p_Odd: u64 = (std::cmp::max(0, if (game.done_Even_c && game.done_Odd_c) { if (game.Even_c == game.Odd_c) { 74 } else { 126 } } else { if (!(game.done_Even_c) && game.done_Odd_c) { 180 } else { if (game.done_Even_c && !(game.done_Odd_c)) { 20 } else { 100 } } })) as u64;
         if (((0 + p_Even) + p_Odd) > game.pot_total) {
             game.claim_amount[0 as usize] = 100;
             game.claim_amount[1 as usize] = 100;
         } else {
             game.claim_amount[0 as usize] = p_Even;
             game.claim_amount[1 as usize] = p_Odd;
         }
         game.is_finalized = true;
        Ok(())
    }

    pub fn claim_Even(ctx: Context<Claim_Even>, ) -> Result<()> {
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

    pub fn claim_Odd(ctx: Context<Claim_Odd>, ) -> Result<()> {
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
    #[account(init, payer = signer, space = 233, seeds = [b"game", game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    #[account(init, payer = signer, space = 0, seeds = [b"vault", game.key().as_ref()], bump)]
    pub vault: SystemAccount<'info>,
    #[account(mut)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
#[instruction(hidden_c: [u8; 32])]
pub struct Move_Odd_0<'info> {
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
#[instruction(hidden_c: [u8; 32])]
pub struct Move_Even_2<'info> {
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
#[instruction(c: bool, salt: u64)]
pub struct Move_Odd_1<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(c: bool, salt: u64)]
pub struct Move_Even_3<'info> {
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
pub struct Claim_Even<'info> {
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
pub struct Claim_Odd<'info> {
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
    pub action_done: [bool; 4],
    pub action_ts: [i64; 4],
    pub timeout: i64,
    pub pot_total: u64,
    pub is_finalized: bool,
    pub claimed: [bool; 2],
    pub claim_amount: [u64; 2],
    pub Odd_c: bool,
    pub done_Odd_c: bool,
    pub Odd_c_hidden: [u8; 32],
    pub done_Odd_c_hidden: bool,
    pub Even_c: bool,
    pub done_Even_c: bool,
    pub Even_c_hidden: [u8; 32],
    pub done_Even_c_hidden: bool,
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
