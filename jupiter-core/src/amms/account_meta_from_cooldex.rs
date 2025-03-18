use anchor_lang::prelude::{AccountMeta, Pubkey};

#[derive(Copy, Clone, Debug)]
pub struct CoolDex {
    pub cooldex_program: Pubkey,
    pub token_program: Pubkey,
    pub amm_info: Pubkey,
    pub amm_authority: Pubkey,
    pub swap_coin_account: Pubkey,
    pub swap_pc_account: Pubkey,
    pub token_transfer_authority: Pubkey,
    pub source_token_account: Pubkey,
    pub swap_source: Pubkey,
    pub swap_destination: Pubkey,
    pub destination_token_account: Pubkey,
    pub pool_mint: Pubkey,
    pub pool_fee: Pubkey,
}

impl From<CoolDex> for Vec<AccountMeta> {
    fn from(accounts: CoolDex) -> Self {
        vec![
            AccountMeta::new_readonly(accounts.cooldex_program, false),
            AccountMeta::new_readonly(accounts.token_program, false),
            AccountMeta::new_readonly(accounts.amm_info, false),
            AccountMeta::new_readonly(accounts.amm_authority, false),
            AccountMeta::new(accounts.swap_coin_account, false),
            AccountMeta::new(accounts.swap_pc_account, false),
            AccountMeta::new_readonly(accounts.user_transfer_authority, false),
            AccountMeta::new(accounts.source, false),
            AccountMeta::new(accounts.swap_source, false),
            AccountMeta::new(accounts.swap_destination, false),
            AccountMeta::new(accounts.destination, false),
            AccountMeta::new(accounts.pool_mint, false),
            AccountMeta::new(accounts.pool_fee, false),
        ]
    }
}
