use anchor_lang::prelude::*;

declare_id!("Fg6PaFpoGXkYsidMpWTK6W2BeZ7FEfcYkg476zPFsLnS"); // Placeholder ID

#[program]
pub mod threewaylotteryshort {
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
         require!((((now > (game.last_ts + game.timeout)) && !(((game.joined[0 as usize] || game.joined[1 as usize]) || game.joined[2 as usize]))) || (game.is_finalized && ((game.claimed[0 as usize] && game.claimed[1 as usize]) && game.claimed[2 as usize]))), ErrorCode::CannotClose);
        Ok(())
    }

    pub fn timeout_Alice(ctx: Context<Timeout_Alice>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
         let now: i64 = Clock::get()?.unix_timestamp;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!(!(game.bailed[0 as usize]), ErrorCode::AlreadyDone);
         require!((now > (game.last_ts + game.timeout)), ErrorCode::NotTimedOut);
         game.bailed[0 as usize] = true;
        Ok(())
    }

    pub fn timeout_Bob(ctx: Context<Timeout_Bob>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
         let now: i64 = Clock::get()?.unix_timestamp;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!(!(game.bailed[1 as usize]), ErrorCode::AlreadyDone);
         require!((now > (game.last_ts + game.timeout)), ErrorCode::NotTimedOut);
         game.bailed[1 as usize] = true;
        Ok(())
    }

    pub fn timeout_Issuer(ctx: Context<Timeout_Issuer>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
         let now: i64 = Clock::get()?.unix_timestamp;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         require!(!(game.bailed[2 as usize]), ErrorCode::AlreadyDone);
         require!((now > (game.last_ts + game.timeout)), ErrorCode::NotTimedOut);
         game.bailed[2 as usize] = true;
        Ok(())
    }

    pub fn move_Issuer_0(ctx: Context<Move_Issuer_0>, hidden_c: [u8; 32]) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         let now: i64 = Clock::get()?.unix_timestamp;
         require!(!(game.bailed[2 as usize]), ErrorCode::Timeout);
         require!((now <= (game.last_ts + game.timeout)), ErrorCode::Timeout);
         require!(!(game.action_done[0 as usize]), ErrorCode::AlreadyDone);
         require!(!(game.joined[2 as usize]), ErrorCode::AlreadyJoined);
         game.roles[2 as usize] = signer.key();
         game.joined[2 as usize] = true;
         // Deposit 12 lamports
         anchor_lang::system_program::transfer(
            anchor_lang::context::CpiContext::new(
                ctx.accounts.system_program.to_account_info(),
                anchor_lang::system_program::Transfer {
                    from: ctx.accounts.signer.to_account_info(),
                    to: ctx.accounts.game.to_account_info(),
                },
            ),
            12,
         )?;
         game.deposited[2 as usize] = (game.deposited[2 as usize] + 12);
         game.Issuer_c_hidden = hidden_c;
         game.done_Issuer_c_hidden = true;
         game.action_done[0 as usize] = true;
         game.action_ts[0 as usize] = now;
         game.last_ts = now;
        Ok(())
    }

    pub fn move_Alice_2(ctx: Context<Move_Alice_2>, hidden_c: [u8; 32]) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         let now: i64 = Clock::get()?.unix_timestamp;
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!((now <= (game.last_ts + game.timeout)), ErrorCode::Timeout);
         require!(!(game.action_done[2 as usize]), ErrorCode::AlreadyDone);
         require!(!(game.joined[0 as usize]), ErrorCode::AlreadyJoined);
         game.roles[0 as usize] = signer.key();
         game.joined[0 as usize] = true;
         // Deposit 12 lamports
         anchor_lang::system_program::transfer(
            anchor_lang::context::CpiContext::new(
                ctx.accounts.system_program.to_account_info(),
                anchor_lang::system_program::Transfer {
                    from: ctx.accounts.signer.to_account_info(),
                    to: ctx.accounts.game.to_account_info(),
                },
            ),
            12,
         )?;
         game.deposited[0 as usize] = (game.deposited[0 as usize] + 12);
         game.Alice_c_hidden = hidden_c;
         game.done_Alice_c_hidden = true;
         game.action_done[2 as usize] = true;
         game.action_ts[2 as usize] = now;
         game.last_ts = now;
        Ok(())
    }

    pub fn move_Bob_4(ctx: Context<Move_Bob_4>, hidden_c: [u8; 32]) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         let now: i64 = Clock::get()?.unix_timestamp;
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!((now <= (game.last_ts + game.timeout)), ErrorCode::Timeout);
         require!(!(game.action_done[4 as usize]), ErrorCode::AlreadyDone);
         require!(!(game.joined[1 as usize]), ErrorCode::AlreadyJoined);
         game.roles[1 as usize] = signer.key();
         game.joined[1 as usize] = true;
         // Deposit 12 lamports
         anchor_lang::system_program::transfer(
            anchor_lang::context::CpiContext::new(
                ctx.accounts.system_program.to_account_info(),
                anchor_lang::system_program::Transfer {
                    from: ctx.accounts.signer.to_account_info(),
                    to: ctx.accounts.game.to_account_info(),
                },
            ),
            12,
         )?;
         game.deposited[1 as usize] = (game.deposited[1 as usize] + 12);
         game.Bob_c_hidden = hidden_c;
         game.done_Bob_c_hidden = true;
         game.action_done[4 as usize] = true;
         game.action_ts[4 as usize] = now;
         game.last_ts = now;
        Ok(())
    }

    pub fn move_Issuer_1(ctx: Context<Move_Issuer_1>, c: u8, salt: u64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         let now: i64 = Clock::get()?.unix_timestamp;
         require!(!(game.bailed[2 as usize]), ErrorCode::Timeout);
         require!((now <= (game.last_ts + game.timeout)), ErrorCode::Timeout);
         require!(!(game.action_done[1 as usize]), ErrorCode::AlreadyDone);
         require!(game.action_done[0 as usize], ErrorCode::DependencyNotMet);
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[4 as usize], ErrorCode::DependencyNotMet);
         }
         require!((((c == 1) || (c == 2)) || (c == 3)), ErrorCode::GuardFailed);
         require!((game.roles[2 as usize] == signer.key()), ErrorCode::Unauthorized);
         {
             let val_bytes = (c).to_be_bytes();
             let salt_bytes = salt.to_be_bytes();
             let hash = anchor_lang::solana_program::keccak::hashv(&[&val_bytes, &salt_bytes]).0;
             require!(hash == game.Issuer_c_hidden, ErrorCode::InvalidReveal);
         }
         game.Issuer_c = c;
         game.done_Issuer_c = true;
         game.action_done[1 as usize] = true;
         game.action_ts[1 as usize] = now;
         game.last_ts = now;
        Ok(())
    }

    pub fn move_Alice_3(ctx: Context<Move_Alice_3>, c: u8, salt: u64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         let now: i64 = Clock::get()?.unix_timestamp;
         require!(!(game.bailed[0 as usize]), ErrorCode::Timeout);
         require!((now <= (game.last_ts + game.timeout)), ErrorCode::Timeout);
         require!(!(game.action_done[3 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[2 as usize]) {
             require!(game.action_done[0 as usize], ErrorCode::DependencyNotMet);
         }
         require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         if !(game.bailed[1 as usize]) {
             require!(game.action_done[4 as usize], ErrorCode::DependencyNotMet);
         }
         require!((((c == 1) || (c == 2)) || (c == 3)), ErrorCode::GuardFailed);
         require!((game.roles[0 as usize] == signer.key()), ErrorCode::Unauthorized);
         {
             let val_bytes = (c).to_be_bytes();
             let salt_bytes = salt.to_be_bytes();
             let hash = anchor_lang::solana_program::keccak::hashv(&[&val_bytes, &salt_bytes]).0;
             require!(hash == game.Alice_c_hidden, ErrorCode::InvalidReveal);
         }
         game.Alice_c = c;
         game.done_Alice_c = true;
         game.action_done[3 as usize] = true;
         game.action_ts[3 as usize] = now;
         game.last_ts = now;
        Ok(())
    }

    pub fn move_Bob_5(ctx: Context<Move_Bob_5>, c: u8, salt: u64) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let signer = &mut ctx.accounts.signer;
         require!(!(game.is_finalized), ErrorCode::GameFinalized);
         let now: i64 = Clock::get()?.unix_timestamp;
         require!(!(game.bailed[1 as usize]), ErrorCode::Timeout);
         require!((now <= (game.last_ts + game.timeout)), ErrorCode::Timeout);
         require!(!(game.action_done[5 as usize]), ErrorCode::AlreadyDone);
         if !(game.bailed[2 as usize]) {
             require!(game.action_done[0 as usize], ErrorCode::DependencyNotMet);
         }
         if !(game.bailed[0 as usize]) {
             require!(game.action_done[2 as usize], ErrorCode::DependencyNotMet);
         }
         require!(game.action_done[4 as usize], ErrorCode::DependencyNotMet);
         require!((((c == 1) || (c == 2)) || (c == 3)), ErrorCode::GuardFailed);
         require!((game.roles[1 as usize] == signer.key()), ErrorCode::Unauthorized);
         {
             let val_bytes = (c).to_be_bytes();
             let salt_bytes = salt.to_be_bytes();
             let hash = anchor_lang::solana_program::keccak::hashv(&[&val_bytes, &salt_bytes]).0;
             require!(hash == game.Bob_c_hidden, ErrorCode::InvalidReveal);
         }
         game.Bob_c = c;
         game.done_Bob_c = true;
         game.action_done[5 as usize] = true;
         game.action_ts[5 as usize] = now;
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
         require!((game.action_done[1 as usize] || game.bailed[2 as usize]), ErrorCode::NotFinalized);
         require!((game.action_done[3 as usize] || game.bailed[0 as usize]), ErrorCode::NotFinalized);
         require!((game.action_done[5 as usize] || game.bailed[1 as usize]), ErrorCode::NotFinalized);
         let p_Bob: u64 = (std::cmp::max(0, if ((game.done_Alice_c && game.done_Bob_c) && game.done_Issuer_c) { if ((((game.Issuer_c + game.Alice_c) + game.Bob_c) % 3) == 0) { 6 } else { if ((((game.Issuer_c + game.Alice_c) + game.Bob_c) % 3) == 1) { 24 } else { 6 } } } else { if (!(game.done_Alice_c) && !(game.done_Bob_c)) { 1 } else { if (!(game.done_Alice_c) && !(game.done_Issuer_c)) { 34 } else { if (!(game.done_Bob_c) && !(game.done_Issuer_c)) { 1 } else { if !(game.done_Alice_c) { 17 } else { if !(game.done_Bob_c) { 2 } else { if !(game.done_Issuer_c) { 17 } else { 12 } } } } } } })) as u64;
         let p_Issuer: u64 = (std::cmp::max(0, if ((game.done_Alice_c && game.done_Bob_c) && game.done_Issuer_c) { if ((((game.Issuer_c + game.Alice_c) + game.Bob_c) % 3) == 0) { 6 } else { if ((((game.Issuer_c + game.Alice_c) + game.Bob_c) % 3) == 1) { 6 } else { 24 } } } else { if (!(game.done_Alice_c) && !(game.done_Bob_c)) { 34 } else { if (!(game.done_Alice_c) && !(game.done_Issuer_c)) { 1 } else { if (!(game.done_Bob_c) && !(game.done_Issuer_c)) { 1 } else { if !(game.done_Alice_c) { 17 } else { if !(game.done_Bob_c) { 17 } else { if !(game.done_Issuer_c) { 2 } else { 12 } } } } } } })) as u64;
         let p_Alice: u64 = (std::cmp::max(0, if ((game.done_Alice_c && game.done_Bob_c) && game.done_Issuer_c) { if ((((game.Issuer_c + game.Alice_c) + game.Bob_c) % 3) == 0) { 24 } else { if ((((game.Issuer_c + game.Alice_c) + game.Bob_c) % 3) == 1) { 6 } else { 6 } } } else { if (!(game.done_Alice_c) && !(game.done_Bob_c)) { 1 } else { if (!(game.done_Alice_c) && !(game.done_Issuer_c)) { 1 } else { if (!(game.done_Bob_c) && !(game.done_Issuer_c)) { 34 } else { if !(game.done_Alice_c) { 2 } else { if !(game.done_Bob_c) { 17 } else { if !(game.done_Issuer_c) { 17 } else { 12 } } } } } } })) as u64;
         if ((((0 + p_Bob) + p_Issuer) + p_Alice) > spendable_pot) {
             game.claim_amount[0 as usize] = game.deposited[0 as usize];
             game.claim_amount[1 as usize] = game.deposited[1 as usize];
             game.claim_amount[2 as usize] = game.deposited[2 as usize];
         } else {
             game.claim_amount[0 as usize] = p_Alice;
             game.claim_amount[1 as usize] = p_Bob;
             game.claim_amount[2 as usize] = p_Issuer;
         }
         if (game.claim_amount[0 as usize] == 0) {
             game.claimed[0 as usize] = true;
         }
         if (game.claim_amount[1 as usize] == 0) {
             game.claimed[1 as usize] = true;
         }
         if (game.claim_amount[2 as usize] == 0) {
             game.claimed[2 as usize] = true;
         }
         game.is_finalized = true;
        Ok(())
    }

    pub fn claim_Alice(ctx: Context<Claim_Alice>, ) -> Result<()> {
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

    pub fn claim_Bob(ctx: Context<Claim_Bob>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let recipient = &mut ctx.accounts.recipient;
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
                 **recipient.to_account_info().try_borrow_mut_lamports()? += amount;
             }
         }
        Ok(())
    }

    pub fn claim_Issuer(ctx: Context<Claim_Issuer>, ) -> Result<()> {
        let game = &mut ctx.accounts.game;
        let recipient = &mut ctx.accounts.recipient;
         require!(game.is_finalized, ErrorCode::NotFinalized);
         require!(!(game.claimed[2 as usize]), ErrorCode::AlreadyClaimed);
         game.claimed[2 as usize] = true;
         {
             let amount = game.claim_amount[2];
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
pub struct Timeout_Alice<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
}

#[derive(Accounts)]
pub struct Timeout_Bob<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
}

#[derive(Accounts)]
pub struct Timeout_Issuer<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
}

#[derive(Accounts)]
#[instruction(hidden_c: [u8; 32])]
pub struct Move_Issuer_0<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
#[instruction(hidden_c: [u8; 32])]
pub struct Move_Alice_2<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
#[instruction(hidden_c: [u8; 32])]
pub struct Move_Bob_4<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
#[instruction(c: u8, salt: u64)]
pub struct Move_Issuer_1<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(c: u8, salt: u64)]
pub struct Move_Alice_3<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    pub signer: Signer<'info>,
}

#[derive(Accounts)]
#[instruction(c: u8, salt: u64)]
pub struct Move_Bob_5<'info> {
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
pub struct Claim_Alice<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    #[account(address = game.roles[0] @ ErrorCode::Unauthorized)]
    pub recipient: SystemAccount<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Claim_Bob<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    #[account(address = game.roles[1] @ ErrorCode::Unauthorized)]
    pub recipient: SystemAccount<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Claim_Issuer<'info> {
    #[account(mut)]
    #[account(seeds = [b"game", game.game_id.to_le_bytes().as_ref()], bump)]
    pub game: Account<'info, GameState>,
    #[account(mut)]
    #[account(address = game.roles[2] @ ErrorCode::Unauthorized)]
    pub recipient: SystemAccount<'info>,
    pub system_program: Program<'info, System>,
}

#[account]
#[derive(InitSpace)]
pub struct GameState {
    pub creator: Pubkey,
    pub game_id: u64,
    pub roles: [Pubkey; 3],
    pub joined: [bool; 3],
    pub deposited: [u64; 3],
    pub last_ts: i64,
    pub bailed: [bool; 3],
    pub action_done: [bool; 6],
    pub action_ts: [i64; 6],
    pub timeout: i64,
    pub is_finalized: bool,
    pub claimed: [bool; 3],
    pub claim_amount: [u64; 3],
    pub Issuer_c: u8,
    pub done_Issuer_c: bool,
    pub Issuer_c_hidden: [u8; 32],
    pub done_Issuer_c_hidden: bool,
    pub Alice_c: u8,
    pub done_Alice_c: bool,
    pub Alice_c_hidden: [u8; 32],
    pub done_Alice_c_hidden: bool,
    pub Bob_c: u8,
    pub done_Bob_c: bool,
    pub Bob_c_hidden: [u8; 32],
    pub done_Bob_c_hidden: bool,
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
