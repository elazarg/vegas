use anchor_lang::prelude::*;

declare_id!("Fg6PaFpoGXkYsidMpWTK6W2BeZ7FEfcYkg476zPFsLnS"); // Placeholder ID

#[program]
pub mod montyhall {
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

    pub fn timeout_Guest(ctx: Context<Timeout_Guest>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[0 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         } else {
             require!(false, ErrorCode::NotTimedOut);
         }
        Ok(())
    }

    pub fn timeout_Host(ctx: Context<Timeout_Host>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         if (Clock::get()?.unix_timestamp > (game.last_ts + game.timeout)) {
             game.bailed[1 as usize] = true;
             game.last_ts = Clock::get()?.unix_timestamp;
         } else {
             require!(false, ErrorCode::NotTimedOut);
         }
        Ok(())
    }

    pub fn move_Host_0(ctx: Context<Move_Host_0>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!(!(game.joined[1 as usize]), ErrorCode::AlreadyJoined);
         game.roles[1 as usize] = signer.key();
         game.joined[1 as usize] = true;
         // Deposit 20 lamports
         anchor_lang::system_program::transfer(
            anchor_lang::context::CpiContext::new(
                ctx.accounts.system_program.to_account_info(),
                anchor_lang::system_program::Transfer {
                    from: ctx.accounts.signer.to_account_info(),
                    to: ctx.accounts.game.to_account_info(),
                },
            ),
            20,
         )?;
         game.pot_total = (game.pot_total + 20);
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[0 as usize]), ErrorCode::AlreadyDone);
         game.action_done[0 as usize] = true;
         game.action_ts[0 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_Guest_1(ctx: Context<Move_Guest_1>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!(!(game.joined[0 as usize]), ErrorCode::AlreadyJoined);
         game.roles[0 as usize] = signer.key();
         game.joined[0 as usize] = true;
         // Deposit 20 lamports
         anchor_lang::system_program::transfer(
            anchor_lang::context::CpiContext::new(
                ctx.accounts.system_program.to_account_info(),
                anchor_lang::system_program::Transfer {
                    from: ctx.accounts.signer.to_account_info(),
                    to: ctx.accounts.game.to_account_info(),
                },
            ),
            20,
         )?;
         game.pot_total = (game.pot_total + 20);
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

    pub fn move_Host_2(ctx: Context<Move_Host_2>, hidden_car: [u8; 32]) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!((game.roles[1 as usize] == signer.key()), ErrorCode::Unauthorized);
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[2 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[1 as usize], ErrorCode::DependencyNotMet);
         }
         game.Host_car_hidden = hidden_car;
         game.done_Host_car_hidden = true;
         game.action_done[2 as usize] = true;
         game.action_ts[2 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_Guest_3(ctx: Context<Move_Guest_3>, d: i64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!((game.roles[0 as usize] == signer.key()), ErrorCode::Unauthorized);
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[3 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         }
         require!((((d == 0) || (d == 1)) || (d == 2)), ErrorCode::GuardFailed);
         game.Guest_d = d;
         game.done_Guest_d = true;
         game.action_done[3 as usize] = true;
         game.action_ts[3 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_Host_4(ctx: Context<Move_Host_4>, goat: i64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!((game.roles[1 as usize] == signer.key()), ErrorCode::Unauthorized);
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[4 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[3 as usize], ErrorCode::DependencyNotMet);
         }
         require!(((((goat == 0) || (goat == 1)) || (goat == 2)) && (goat != game.Guest_d)), ErrorCode::GuardFailed);
         game.Host_goat = goat;
         game.done_Host_goat = true;
         game.action_done[4 as usize] = true;
         game.action_ts[4 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_Guest_5(ctx: Context<Move_Guest_5>, switch: bool) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!((game.roles[0 as usize] == signer.key()), ErrorCode::Unauthorized);
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[5 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[4 as usize], ErrorCode::DependencyNotMet);
         }
         game.Guest_switch = switch;
         game.done_Guest_switch = true;
         game.action_done[5 as usize] = true;
         game.action_ts[5 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn move_Host_6(ctx: Context<Move_Host_6>, car: i64, salt: u64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!((game.roles[1 as usize] == signer.key()), ErrorCode::Unauthorized);
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!(!(game.action_done[6 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[5 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[4 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         }
         require!(((((car == 0) || (car == 1)) || (car == 2)) && (game.Host_goat != car)), ErrorCode::GuardFailed);
         {
             let val_bytes = (car).to_be_bytes();
             let salt_bytes = salt.to_be_bytes();
             let hash = anchor_lang::solana_program::keccak::hashv(&[&val_bytes, &salt_bytes]).0;
             require!(hash == game.Host_car_hidden, ErrorCode::InvalidReveal);
         }
         game.Host_car = car;
         game.done_Host_car = true;
         game.action_done[6 as usize] = true;
         game.action_ts[6 as usize] = Clock::get()?.unix_timestamp;
         game.last_ts = Clock::get()?.unix_timestamp;
        Ok(())
    }

    pub fn finalize(ctx: Context<Finalize>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!((game.action_done[6 as usize] || game.bailed[1 as usize]), ErrorCode::NotFinalized);
         let p_Guest: u64 = (std::cmp::max(0, if (game.done_Host_car && game.done_Guest_switch) { if ((game.Guest_d != game.Host_car) == game.Guest_switch) { 40 } else { 0 } } else { if !(game.done_Host_car) { 40 } else { 0 } })) as u64;
         let p_Host: u64 = (std::cmp::max(0, if (game.done_Host_car && game.done_Guest_switch) { if ((game.Guest_d != game.Host_car) == game.Guest_switch) { 0 } else { 40 } } else { if !(game.done_Host_car) { 0 } else { 40 } })) as u64;
         if (((0 + p_Guest) + p_Host) > game.pot_total) {
             game.claim_amount[0 as usize] = 20;
             game.claim_amount[1 as usize] = 20;
         } else {
             game.claim_amount[0 as usize] = p_Guest;
             game.claim_amount[1 as usize] = p_Host;
         }
         game.is_finalized = true;
        Ok(())
    }

    pub fn claim_Guest(ctx: Context<Claim_Guest>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(game.is_finalized, ErrorCode::NotFinalized);
         require!(!(game.claimed[0 as usize]), ErrorCode::AlreadyClaimed);
         game.claimed[0 as usize] = true;
         {
             let amount = game.claim_amount[0];
             if amount > 0 {
                 **game.to_account_info().try_borrow_mut_lamports()? -= amount;
                 **signer.to_account_info().try_borrow_mut_lamports()? += amount;
             }
         }
        Ok(())
    }

    pub fn claim_Host(ctx: Context<Claim_Host>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(game.is_finalized, ErrorCode::NotFinalized);
         require!(!(game.claimed[1 as usize]), ErrorCode::AlreadyClaimed);
         game.claimed[1 as usize] = true;
         {
             let amount = game.claim_amount[1];
             if amount > 0 {
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
pub struct Timeout_Guest<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
pub struct Timeout_Host<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
pub struct Move_Host_0<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Move_Guest_1<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
#[instruction(hidden_car: [u8; 32])]
pub struct Move_Host_2<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(d: i64)]
pub struct Move_Guest_3<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(goat: i64)]
pub struct Move_Host_4<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(switch: bool)]
pub struct Move_Guest_5<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(car: i64, salt: u64)]
pub struct Move_Host_6<'info> {
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
pub struct Claim_Guest<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    #[account(constraint = signer.key() == game.roles[0] @ ErrorCode::Unauthorized)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Claim_Host<'info> {
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
    pub last_ts: i64,
    pub bailed: [bool; 2],
    pub action_done: [bool; 7],
    pub action_ts: [i64; 7],
    pub timeout: i64,
    pub pot_total: u64,
    pub is_finalized: bool,
    pub claimed: [bool; 2],
    pub claim_amount: [u64; 2],
    pub Host_car: i64,
    pub done_Host_car: bool,
    pub Host_car_hidden: [u8; 32],
    pub done_Host_car_hidden: bool,
    pub Guest_d: i64,
    pub done_Guest_d: bool,
    pub Host_goat: i64,
    pub done_Host_goat: bool,
    pub Guest_switch: bool,
    pub done_Guest_switch: bool,
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
    #[msg("Guard condition failed")]
    GuardFailed,
}
