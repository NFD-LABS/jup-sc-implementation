use anyhow::Result;
use jupiter_amm_interface::{
    try_get_account_data, AccountMap, Amm, AmmContext, KeyedAccount, Quote, Swap,
    SwapAndAccountMetas, SwapParams,
};
use solana_sdk::{instruction::AccountMeta, program_pack::Pack, pubkey, pubkey::Pubkey};
use spl_associated_token_account::get_associated_token_address;
use spl_math::{checked_ceil_div::CheckedCeilDiv, uint::U256};
use spl_token::state::Account as TokenAccount;

mod cooldex_constants {
    use super::*;
    pub const COOLDEX_PROGRAM_ID: Pubkey = pubkey!("HAXJWG2uMp4Fegh5ZmKF4QbDc5WaJ4LnL1dePcooLDEX");
    pub const ADMIN_FEE_ACCOUNT: Pubkey = pubkey!("ETjXM6Yh8iXKeCEsrrqrnLRKivzajc1uThZM6Ua8RKqQ");
}

const COOLPAD_BURN_RATE_DENOMINATOR: u64 = 10000;

pub struct CoolDexAmm {
    amm_info: Pubkey,

    reserve_mints: [Pubkey; 2],
    reserve_accounts: [Pubkey; 2],
    reserves: [u128; 2],

    swap_fee_numerator: u64,
    swap_fee_denominator: u64,

    cooldex_team_fee_wsol_fee_numerator: u64,
    cooldex_team_fee_wsol_fee_denominator: u64,

    burn_rate: u64,

    token_program_id: Pubkey,
    pda_for_reserves: Pubkey,
    admin_fee_account: Pubkey,

    cult_wsol_account: Pubkey,
    cult_token_account: Pubkey,
}

impl CoolDexAmm {
    pub fn swap_token_amount_base_in(
        amount_in: U256,
        total_pc_without_take_pnl: U256,
        total_coin_without_take_pnl: U256,
        swap_direction_is_coin2pc: bool,
    ) -> U256 {
        let amount_out;
        match swap_direction_is_coin2pc {
            true => {
                // (x + delta_x) * (y + delta_y) = x * y
                // (coin + amount_in) * (pc - amount_out) = coin * pc
                // => amount_out = pc - coin * pc / (coin + amount_in)
                // => amount_out = ((pc * coin + pc * amount_in) - coin * pc) / (coin + amount_in)
                // => amount_out =  pc * amount_in / (coin + amount_in)
                let denominator = total_coin_without_take_pnl.checked_add(amount_in).unwrap();
                amount_out = total_pc_without_take_pnl
                    .checked_mul(amount_in)
                    .unwrap()
                    .checked_div(denominator)
                    .unwrap();
            }
            false => {
                // (x + delta_x) * (y + delta_y) = x * y
                // (pc + amount_in) * (coin - amount_out) = coin * pc
                // => amount_out = coin - coin * pc / (pc + amount_in)
                // => amount_out = (coin * pc + coin * amount_in - coin * pc) / (pc + amount_in)
                // => amount_out = coin * amount_in / (pc + amount_in)
                let denominator = total_pc_without_take_pnl.checked_add(amount_in).unwrap();
                amount_out = total_coin_without_take_pnl
                    .checked_mul(amount_in)
                    .unwrap()
                    .checked_div(denominator)
                    .unwrap();
            }
        }
        return amount_out;
    }

    pub fn swap_token_amount_base_out(
        amount_out: U256,
        total_pc_without_take_pnl: U256,
        total_coin_without_take_pnl: U256,
        swap_direction_is_coin2pc: bool,
    ) -> U256 {
        let amount_in;
        match swap_direction_is_coin2pc {
            true => {
                // (x + delta_x) * (y + delta_y) = x * y
                // (coin + amount_in) * (pc - amount_out) = coin * pc
                // => amount_in = coin * pc / (pc - amount_out) - coin
                // => amount_in = (coin * pc - pc * coin + amount_out * coin) / (pc - amount_out)
                // => amount_in = (amount_out * coin) / (pc - amount_out)
                let denominator =
                    U256::from(total_pc_without_take_pnl.checked_sub(amount_out).unwrap());
                amount_in = total_coin_without_take_pnl
                    .checked_mul(amount_out)
                    .unwrap()
                    .checked_ceil_div(denominator)
                    .unwrap()
                    .0
            }
            false => {
                // (x + delta_x) * (y + delta_y) = x * y
                // (pc + amount_in) * (coin - amount_out) = coin * pc
                // => amount_out = coin - coin * pc / (pc + amount_in)
                // => amount_out = (coin * pc + coin * amount_in - coin * pc) / (pc + amount_in)
                // => amount_out = coin * amount_in / (pc + amount_in)

                // => amount_in = coin * pc / (coin - amount_out) - pc
                // => amount_in = (coin * pc - pc * coin + pc * amount_out) / (coin - amount_out)
                // => amount_in = (pc * amount_out) / (coin - amount_out)
                let denominator: U256 =
                    U256::from(total_coin_without_take_pnl.checked_sub(amount_out).unwrap());
                amount_in = total_pc_without_take_pnl
                    .checked_mul(amount_out)
                    .unwrap()
                    .checked_ceil_div(denominator)
                    .unwrap()
                    .0
            }
        }
        return amount_in;
    }
}

impl Clone for CoolDexAmm {
    fn clone(&self) -> Self {
        Self {
            amm_info: self.amm_info,
            reserve_mints: self.reserve_mints,
            reserve_accounts: self.reserve_accounts,
            reserves: self.reserves,
            swap_fee_numerator: self.swap_fee_numerator,
            swap_fee_denominator: self.swap_fee_denominator,
            cooldex_team_fee_wsol_fee_numerator: self.cooldex_team_fee_wsol_fee_numerator,
            cooldex_team_fee_wsol_fee_denominator: self.cooldex_team_fee_wsol_fee_denominator,
            burn_rate: self.burn_rate,
            token_program_id: self.token_program_id,
            pda_for_reserves: self.pda_for_reserves,
            admin_fee_account: self.admin_fee_account,
            cult_token_account: self.cult_token_account,
            cult_wsol_account: self.cult_wsol_account,
        }
    }
}

impl Amm for CoolDexAmm {
    fn from_keyed_account(keyed_account: &KeyedAccount, _amm_context: &AmmContext) -> Result<Self> {
        let reserve_mints = [
            Pubkey::new_from_array(
                keyed_account.account.data[0x1a0..0x1a0 + 32]
                    .try_into()
                    .unwrap(),
            ),
            Pubkey::new_from_array(
                keyed_account.account.data[0x1c0..0x1c0 + 32]
                    .try_into()
                    .unwrap(),
            ),
        ];
        let reserve_accounts = [
            Pubkey::new_from_array(
                keyed_account.account.data[0x160..0x160 + 32]
                    .try_into()
                    .unwrap(),
            ),
            Pubkey::new_from_array(
                keyed_account.account.data[0x180..0x180 + 32]
                    .try_into()
                    .unwrap(),
            ),
        ];
        let burn_rate = u64::from_le_bytes(
            keyed_account.account.data[0x308..0x308 + 8]
                .try_into()
                .unwrap(),
        );
        let swap_fee_numerator = u64::from_le_bytes(
            keyed_account.account.data[0x0b0..0x0b0 + 8]
                .try_into()
                .unwrap(),
        );
        let swap_fee_denominator = u64::from_le_bytes(
            keyed_account.account.data[0x0b8..0x0b8 + 8]
                .try_into()
                .unwrap(),
        );
        let cooldex_team_fee_wsol_fee_numerator = u64::from_le_bytes(
            keyed_account.account.data[0x0c0..0x0c0 + 8]
                .try_into()
                .unwrap(),
        );
        let cooldex_team_fee_wsol_fee_denominator = u64::from_le_bytes(
            keyed_account.account.data[0x0c8..0x0c8 + 8]
                .try_into()
                .unwrap(),
        );
        // const [RAYDIUM_PDA, RAYDIUM_PDA_NONCE] = PublicKey.findProgramAddressSync([Buffer.from("amm authority")], RAYDIUM_PROGRAM_ID);
        let pda_for_reserves = Pubkey::find_program_address(
            &[b"amm authority"],
            &cooldex_constants::COOLDEX_PROGRAM_ID,
        )
        .0;
        let admin_fee_account =
            get_associated_token_address(&cooldex_constants::ADMIN_FEE_ACCOUNT, &reserve_mints[1]);
        Ok(Self {
            amm_info: keyed_account.key,
            reserve_mints,
            reserve_accounts,
            burn_rate,
            swap_fee_numerator,
            swap_fee_denominator,
            cooldex_team_fee_wsol_fee_numerator,
            cooldex_team_fee_wsol_fee_denominator,
            reserves: Default::default(),
            token_program_id: Pubkey::default(),
            pda_for_reserves,
            admin_fee_account,
            cult_token_account: Pubkey::default(),
            cult_wsol_account: Pubkey::default(),
        })
    }
    fn label(&self) -> String {
        "CoolDex".to_string()
    }
    fn program_id(&self) -> Pubkey {
        cooldex_constants::COOLDEX_PROGRAM_ID
    }
    fn key(&self) -> Pubkey {
        self.amm_info
    }
    fn get_reserve_mints(&self) -> Vec<Pubkey> {
        self.reserve_mints.to_vec()
    }
    fn get_accounts_to_update(&self) -> Vec<Pubkey> {
        vec![
            self.amm_info,
            self.reserve_accounts[0],
            self.reserve_accounts[1],
        ]
    }
    fn update(&mut self, account_map: &AccountMap) -> Result<()> {
        let token_a_account = try_get_account_data(account_map, &self.reserve_accounts[0])?;
        let token_a_token_account = TokenAccount::unpack(token_a_account)?;

        let token_b_account = try_get_account_data(account_map, &self.reserve_accounts[1])?;
        let token_b_token_account = TokenAccount::unpack(token_b_account)?;

        self.reserves = [
            token_a_token_account.amount.into(),
            token_b_token_account.amount.into(),
        ];

        let amm_info_account = try_get_account_data(account_map, &self.amm_info)?;
        self.burn_rate = u64::from_le_bytes(amm_info_account[0x308..0x308 + 8].try_into().unwrap());
        self.swap_fee_numerator =
            u64::from_le_bytes(amm_info_account[0x0b0..0x0b0 + 8].try_into().unwrap());
        self.swap_fee_denominator =
            u64::from_le_bytes(amm_info_account[0x0b8..0x0b8 + 8].try_into().unwrap());
        self.cooldex_team_fee_wsol_fee_numerator =
            u64::from_le_bytes(amm_info_account[0x0c0..0x0c0 + 8].try_into().unwrap());
        self.cooldex_team_fee_wsol_fee_denominator =
            u64::from_le_bytes(amm_info_account[0x0c8..0x0c8 + 8].try_into().unwrap());

        if self.token_program_id == Pubkey::default() {
            // Only Token->Token or Token22->Token22 :-(
            self.token_program_id = account_map
                .get(&self.reserve_accounts[0])
                .map(|account| account.owner)
                .unwrap(); // Impossible to fail, as this was already checked.
            self.cult_wsol_account =
                Pubkey::create_with_seed(&self.reserve_mints[0], "w", &self.token_program_id)?;
            self.cult_token_account =
                Pubkey::create_with_seed(&self.reserve_mints[0], "w", &self.token_program_id)?;
        }

        Ok(())
    }

    fn quote(
        &self,
        quote_params: &jupiter_amm_interface::QuoteParams,
    ) -> Result<jupiter_amm_interface::Quote> {
        match (
            quote_params.swap_mode,
            quote_params.input_mint.eq(&self.reserve_mints[1]),
        ) {
            // == Total amount of tax is calculated using the formula: input token * fee.
            //    it is just a matter of splitting the tax between platform and cult,
            //    what makes things slightly more complicated.
            (jupiter_amm_interface::SwapMode::ExactIn, /* is buy */ true) => {
                // = Buying exactIn. Input == WSOL. Output == TOKEN.
                let amount_in = U256::from(quote_params.amount);
                let taxable_amount = amount_in
                    .checked_mul(self.swap_fee_numerator.into())
                    .unwrap()
                    .checked_ceil_div(self.swap_fee_denominator.into())
                    .unwrap()
                    .0;
                // Platform tax is compouted in WSOL
                let platform_tax = taxable_amount
                    .checked_mul(self.cooldex_team_fee_wsol_fee_numerator.into())
                    .unwrap()
                    .checked_ceil_div(self.cooldex_team_fee_wsol_fee_denominator.into())
                    .unwrap()
                    .0;
                let cult_wsol = taxable_amount
                    .checked_sub(platform_tax)
                    .unwrap()
                    .checked_mul((COOLPAD_BURN_RATE_DENOMINATOR - self.burn_rate).into())
                    .unwrap()
                    .checked_ceil_div((2 * COOLPAD_BURN_RATE_DENOMINATOR).into())
                    .unwrap()
                    .0;
                let input_token_to_hold = platform_tax + cult_wsol;
                let platform_tax = platform_tax.as_u64();
                let cult_wsol = cult_wsol.as_u64();

                let swap_in_after_deduct_fee = amount_in.checked_sub(input_token_to_hold).unwrap();
                let swap_amount_out = CoolDexAmm::swap_token_amount_base_in(
                    swap_in_after_deduct_fee,
                    U256::from(self.reserves[1]),
                    U256::from(self.reserves[0]),
                    false,
                );

                // Restoring the theoretical amount of out tokens, if fees were not applied.
                // let taxable_output_amount = swap_amount_out
                //     .checked_mul(amount_in)
                //     .unwrap()
                //    .checked_ceil_div(swap_in_after_deduct_fee);
                let taxable_amount_token = swap_amount_out
                    .checked_mul(amount_in)
                    .unwrap()
                    .checked_mul(self.swap_fee_numerator.into())
                    .unwrap()
                    .checked_mul(
                        (self.cooldex_team_fee_wsol_fee_denominator
                            - self.cooldex_team_fee_wsol_fee_numerator)
                            .into(),
                    )
                    .unwrap()
                    .checked_ceil_div(
                        swap_in_after_deduct_fee
                            .checked_mul(self.swap_fee_denominator.into())
                            .unwrap()
                            .checked_mul(self.cooldex_team_fee_wsol_fee_denominator.into())
                            .unwrap(),
                    )
                    .unwrap()
                    .0;
                let burn_token = taxable_amount_token
                    .checked_mul(self.burn_rate.into())
                    .unwrap()
                    .checked_div(COOLPAD_BURN_RATE_DENOMINATOR.into())
                    .unwrap();
                let cult_token = taxable_amount_token
                    .checked_sub(burn_token)
                    .unwrap()
                    .checked_div(U256::from(2u64))
                    .unwrap();
                let swap_amount_out_to_user = swap_amount_out
                    .checked_sub(burn_token)
                    .unwrap()
                    .checked_sub(cult_token)
                    .unwrap();

                Ok(jupiter_amm_interface::Quote {
                    fee_pct: self.swap_fee_numerator.into(),
                    in_amount: quote_params.amount,
                    out_amount: swap_amount_out_to_user.as_u64(),
                    fee_amount: cult_wsol + platform_tax,
                    fee_mint: self.reserve_mints[1],
                    ..Quote::default()
                })
            }
            (jupiter_amm_interface::SwapMode::ExactIn, /* is buy */ false) => {
                let amount_in = U256::from(quote_params.amount);
                let taxable_amount = U256::from(amount_in)
                    .checked_mul(self.swap_fee_numerator.into())
                    .unwrap()
                    .checked_mul(
                        (self.cooldex_team_fee_wsol_fee_denominator
                            - self.cooldex_team_fee_wsol_fee_numerator)
                            .into(),
                    )
                    .unwrap()
                    .checked_ceil_div(
                        ((self.cooldex_team_fee_wsol_fee_denominator as u64)
                            * self.swap_fee_denominator)
                            .into(),
                    )
                    .unwrap()
                    .0;
                let amount_to_burn = taxable_amount
                    .checked_mul(self.burn_rate.into())
                    .unwrap()
                    .checked_ceil_div(COOLPAD_BURN_RATE_DENOMINATOR.into())
                    .unwrap()
                    .0;
                let cult_token = taxable_amount
                    .checked_sub(amount_to_burn)
                    .unwrap()
                    .checked_ceil_div(2.into())
                    .unwrap()
                    .0;
                let input_token_to_hold = amount_to_burn + cult_token;
                let swap_in_after_deduct_fee = amount_in.checked_sub(input_token_to_hold).unwrap();
                let swap_amount_out = CoolDexAmm::swap_token_amount_base_in(
                    swap_in_after_deduct_fee,
                    U256::from(self.reserves[1]),
                    U256::from(self.reserves[0]),
                    false,
                );

                let taxable_amount_wsol = U256::from(swap_amount_out)
                    .checked_mul(amount_in.into())
                    .unwrap()
                    .checked_mul(self.swap_fee_numerator.into())
                    .unwrap()
                    .checked_ceil_div(
                        swap_in_after_deduct_fee
                            .checked_mul(self.swap_fee_denominator.into())
                            .unwrap(),
                    )
                    .unwrap()
                    .0;
                let platform_tax = taxable_amount_wsol
                    .checked_mul(self.cooldex_team_fee_wsol_fee_numerator.into())
                    .unwrap()
                    .checked_ceil_div(self.cooldex_team_fee_wsol_fee_denominator.into())
                    .unwrap()
                    .0;
                let cult_wsol = taxable_amount_wsol
                    .checked_sub(platform_tax)
                    .unwrap()
                    .checked_mul((COOLPAD_BURN_RATE_DENOMINATOR - self.burn_rate).into())
                    .unwrap()
                    .checked_div((2 * COOLPAD_BURN_RATE_DENOMINATOR).into())
                    .unwrap();
                let swap_amount_out_to_user = swap_amount_out
                    .checked_sub(platform_tax)
                    .unwrap()
                    .checked_sub(cult_wsol)
                    .unwrap();

                Ok(jupiter_amm_interface::Quote {
                    in_amount: quote_params.amount,
                    out_amount: swap_amount_out_to_user.as_u64(),
                    fee_pct: self.swap_fee_numerator.into(),
                    fee_amount: (cult_wsol + platform_tax).as_u64(),
                    fee_mint: self.reserve_mints[1],
                    ..Quote::default()
                })
            }
            (jupiter_amm_interface::SwapMode::ExactOut, /* is buy */ true) => {
                let amount_out = U256::from(quote_params.amount);
                let swap_in_before_add_fee = CoolDexAmm::swap_token_amount_base_out(
                    amount_out,
                    U256::from(self.reserves[1]),
                    U256::from(self.reserves[0]),
                    false,
                );
                let swap_in_after_add_fee = swap_in_before_add_fee
                    .checked_mul(self.swap_fee_denominator.into())
                    .unwrap()
                    .checked_ceil_div(
                        (self
                            .swap_fee_denominator
                            .checked_sub(self.swap_fee_numerator)
                            .unwrap())
                        .into(),
                    )
                    .unwrap()
                    .0;
                let swap_fee = swap_in_after_add_fee
                    .checked_sub(swap_in_before_add_fee)
                    .unwrap();
                let virtual_amount_out = amount_out
                    .checked_mul(swap_in_after_add_fee.into())
                    .unwrap()
                    .checked_ceil_div(swap_in_before_add_fee.into())
                    .unwrap()
                    .0;
                let taxable_output = virtual_amount_out
                    .checked_mul(self.swap_fee_numerator.into())
                    .unwrap()
                    .checked_ceil_div(self.swap_fee_denominator.into())
                    .unwrap()
                    .0;
                let taxable_input = swap_in_after_add_fee
                    .checked_mul(self.swap_fee_numerator.into())
                    .unwrap()
                    .checked_ceil_div(self.swap_fee_denominator.into())
                    .unwrap()
                    .0;
                let platform_tax = taxable_input
                    .checked_mul(self.cooldex_team_fee_wsol_fee_numerator.into())
                    .unwrap()
                    .checked_ceil_div(self.cooldex_team_fee_wsol_fee_denominator.into())
                    .unwrap()
                    .0;
                let cult_wsol = taxable_input
                    .checked_sub(platform_tax)
                    .unwrap()
                    .checked_mul((COOLPAD_BURN_RATE_DENOMINATOR - self.burn_rate).into())
                    .unwrap()
                    .checked_ceil_div((2 * COOLPAD_BURN_RATE_DENOMINATOR).into())
                    .unwrap()
                    .0;
                let taxable_output = taxable_output
                    .checked_mul(
                        (self.cooldex_team_fee_wsol_fee_denominator
                            - self.cooldex_team_fee_wsol_fee_numerator)
                            .into(),
                    )
                    .unwrap()
                    .checked_ceil_div(self.cooldex_team_fee_wsol_fee_denominator.into())
                    .unwrap()
                    .0;
                let burn_amount = taxable_output
                    .checked_mul(self.burn_rate.into())
                    .unwrap()
                    .checked_ceil_div(COOLPAD_BURN_RATE_DENOMINATOR.into())
                    .unwrap()
                    .0;
                let cult_contribution_token = taxable_output
                    .checked_sub(burn_amount)
                    .unwrap()
                    .checked_ceil_div(2.into())
                    .unwrap()
                    .0;
                Ok(jupiter_amm_interface::Quote {
                    in_amount: taxable_input.as_u64(),
                    out_amount: quote_params.amount,
                    fee_pct: self.swap_fee_numerator.into(),
                    fee_amount: (cult_wsol + platform_tax).as_u64(),
                    fee_mint: self.reserve_mints[1],
                    ..Quote::default()
                })
            }
            (jupiter_amm_interface::SwapMode::ExactOut, /* is buy */ false) => {
                let amount_out = U256::from(quote_params.amount);
                let swap_in_before_add_fee = CoolDexAmm::swap_token_amount_base_out(
                    amount_out,
                    U256::from(self.reserves[1]),
                    U256::from(self.reserves[0]),
                    true,
                );
                let swap_in_after_add_fee = swap_in_before_add_fee
                    .checked_mul(self.swap_fee_denominator.into())
                    .unwrap()
                    .checked_ceil_div(
                        (self
                            .swap_fee_denominator
                            .checked_sub(self.swap_fee_numerator)
                            .unwrap())
                        .into(),
                    )
                    .unwrap()
                    .0;
                let swap_fee = swap_in_after_add_fee
                    .checked_sub(swap_in_before_add_fee)
                    .unwrap();
                let virtual_amount_out = U256::from(quote_params.amount)
                    .checked_mul(swap_in_after_add_fee.into())
                    .unwrap()
                    .checked_ceil_div(swap_in_before_add_fee.into())
                    .unwrap()
                    .0;
                let taxable_output = virtual_amount_out
                    .checked_mul(self.swap_fee_numerator.into())
                    .unwrap()
                    .checked_ceil_div(self.swap_fee_denominator.into())
                    .unwrap()
                    .0;
                let taxable_input = U256::from(swap_in_after_add_fee)
                    .checked_mul(self.swap_fee_numerator.into())
                    .unwrap()
                    .checked_ceil_div(self.swap_fee_denominator.into())
                    .unwrap()
                    .0;
                let taxable_input = taxable_input
                    .checked_mul(
                        (self.cooldex_team_fee_wsol_fee_denominator
                            - self.cooldex_team_fee_wsol_fee_numerator)
                            .into(),
                    )
                    .unwrap()
                    .checked_ceil_div(self.cooldex_team_fee_wsol_fee_denominator.into())
                    .unwrap()
                    .0;
                let burn_amount = taxable_input
                    .checked_mul(self.burn_rate.into())
                    .unwrap()
                    .checked_ceil_div(COOLPAD_BURN_RATE_DENOMINATOR.into())
                    .unwrap()
                    .0;
                let cult_contribution_token = taxable_input
                    .checked_sub(burn_amount)
                    .unwrap()
                    .checked_ceil_div(2.into())
                    .unwrap()
                    .0
                    .as_u64();
                let platform_tax = taxable_output
                    .checked_mul(self.cooldex_team_fee_wsol_fee_numerator.into())
                    .unwrap()
                    .checked_ceil_div(self.cooldex_team_fee_wsol_fee_denominator.into())
                    .unwrap()
                    .0;
                let cult_wsol = taxable_output
                    .checked_sub(platform_tax)
                    .unwrap()
                    .checked_mul(((COOLPAD_BURN_RATE_DENOMINATOR as u64) - self.burn_rate).into())
                    .unwrap()
                    .checked_ceil_div((2 * COOLPAD_BURN_RATE_DENOMINATOR).into())
                    .unwrap()
                    .0;
                let mut token_to_deposit = swap_in_after_add_fee;
                Ok(jupiter_amm_interface::Quote {
                    in_amount: taxable_input.as_u64(),
                    out_amount: quote_params.amount,
                    fee_pct: self.swap_fee_numerator.into(),
                    fee_amount: (cult_wsol + platform_tax).as_u64(),
                    fee_mint: self.reserve_mints[1],
                    ..Quote::default()
                })
            }
        }
    }

    fn get_swap_and_account_metas(
        &self,
        swap_params: &jupiter_amm_interface::SwapParams,
    ) -> Result<jupiter_amm_interface::SwapAndAccountMetas> {
        let SwapParams {
            token_transfer_authority,
            source_token_account,
            destination_token_account,
            ..
        } = swap_params;

        Ok(SwapAndAccountMetas {
            swap: Swap::TokenSwap, /* TODO: Swap::CoolDexSwap */
            account_metas: vec![
                AccountMeta::new_readonly(self.token_program_id, false),
                AccountMeta::new(self.amm_info, false),
                AccountMeta::new_readonly(self.pda_for_reserves, false),
                AccountMeta::new(self.reserve_accounts[0], false),
                AccountMeta::new(self.reserve_accounts[1], false),
                AccountMeta::new(*source_token_account, false),
                AccountMeta::new(*destination_token_account, false),
                AccountMeta::new_readonly(*token_transfer_authority, true),
                // Coin mint - needed to be writeable as we burn
                AccountMeta::new(self.reserve_mints[0], false),
                AccountMeta::new(self.admin_fee_account, false),
                AccountMeta::new(self.cult_wsol_account, false),
                AccountMeta::new(self.cult_token_account, false),
            ],
        })
    }

    fn supports_exact_out(&self) -> bool {
        true
    }

    fn clone_amm(&self) -> Box<dyn Amm + Send + Sync> {
        Box::new(self.clone())
    }
}
