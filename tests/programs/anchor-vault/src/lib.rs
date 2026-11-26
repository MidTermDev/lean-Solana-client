//! A token vault, written with Anchor.
//!
//! It exists to exercise what Anchor programs do when they call other
//! programs: create accounts through the system program under a derived
//! signature, have the Associated Token Account program (itself a Rust
//! program that calls two more) open a token account, move tokens with and
//! without a derived signer, and emit events.

use anchor_lang::prelude::*;
use anchor_spl::associated_token::AssociatedToken;
use anchor_spl::token::{self, Mint, Token, TokenAccount, Transfer};

declare_id!("7Ygt9ghxooFNu4aH8TbsNpvXVTZUxQx45Dm6dvYQHKYJ");

#[program]
pub mod anchor_vault {
    use super::*;

    /// Creates the vault's state account and its token account.
    pub fn initialize(ctx: Context<Initialize>) -> Result<()> {
        let vault = &mut ctx.accounts.vault;
        vault.owner = ctx.accounts.owner.key();
        vault.mint = ctx.accounts.mint.key();
        vault.deposited = 0;
        vault.bump = ctx.bumps.vault;
        Ok(())
    }

    /// Moves tokens from the owner into the vault. The owner signs.
    pub fn deposit(ctx: Context<Move>, amount: u64) -> Result<()> {
        token::transfer(
            CpiContext::new(
                ctx.accounts.token_program.to_account_info(),
                Transfer {
                    from: ctx.accounts.owner_tokens.to_account_info(),
                    to: ctx.accounts.vault_tokens.to_account_info(),
                    authority: ctx.accounts.owner.to_account_info(),
                },
            ),
            amount,
        )?;
        let vault = &mut ctx.accounts.vault;
        vault.deposited = vault.deposited.checked_add(amount).ok_or(VaultError::Overflow)?;
        emit!(Moved { vault: vault.key(), amount, deposited: vault.deposited });
        Ok(())
    }

    /// Moves tokens back out. The vault signs, with the seeds of its address.
    pub fn withdraw(ctx: Context<Move>, amount: u64) -> Result<()> {
        require!(amount <= ctx.accounts.vault.deposited, VaultError::TooMuch);
        let owner = ctx.accounts.owner.key();
        let mint = ctx.accounts.mint.key();
        let seeds: &[&[u8]] = &[b"vault", mint.as_ref(), owner.as_ref(), &[ctx.accounts.vault.bump]];
        token::transfer(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                Transfer {
                    from: ctx.accounts.vault_tokens.to_account_info(),
                    to: ctx.accounts.owner_tokens.to_account_info(),
                    authority: ctx.accounts.vault.to_account_info(),
                },
                &[seeds],
            ),
            amount,
        )?;
        let vault = &mut ctx.accounts.vault;
        vault.deposited -= amount;
        emit!(Moved { vault: vault.key(), amount, deposited: vault.deposited });
        Ok(())
    }
}

#[derive(Accounts)]
pub struct Initialize<'info> {
    #[account(mut)]
    pub owner: Signer<'info>,
    pub mint: Account<'info, Mint>,
    #[account(
        init,
        payer = owner,
        space = 8 + Vault::INIT_SPACE,
        seeds = [b"vault", mint.key().as_ref(), owner.key().as_ref()],
        bump
    )]
    pub vault: Account<'info, Vault>,
    #[account(
        init,
        payer = owner,
        associated_token::mint = mint,
        associated_token::authority = vault
    )]
    pub vault_tokens: Account<'info, TokenAccount>,
    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Move<'info> {
    pub owner: Signer<'info>,
    pub mint: Account<'info, Mint>,
    #[account(
        mut,
        has_one = owner,
        has_one = mint,
        seeds = [b"vault", mint.key().as_ref(), owner.key().as_ref()],
        bump = vault.bump
    )]
    pub vault: Account<'info, Vault>,
    #[account(mut, token::mint = mint, token::authority = vault)]
    pub vault_tokens: Account<'info, TokenAccount>,
    #[account(mut, token::mint = mint, token::authority = owner)]
    pub owner_tokens: Account<'info, TokenAccount>,
    pub token_program: Program<'info, Token>,
}

#[account]
#[derive(InitSpace)]
pub struct Vault {
    pub owner: Pubkey,
    pub mint: Pubkey,
    pub deposited: u64,
    pub bump: u8,
}

#[event]
pub struct Moved {
    pub vault: Pubkey,
    pub amount: u64,
    pub deposited: u64,
}

#[error_code]
pub enum VaultError {
    #[msg("the deposit total would overflow")]
    Overflow,
    #[msg("the vault does not hold that much")]
    TooMuch,
}
