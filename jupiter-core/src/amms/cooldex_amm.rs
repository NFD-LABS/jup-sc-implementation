use anyhow::{ anyhow, Result };
use jupiter_amm_interface::{
    try_get_account_data,
    AccountMap,
    Amm,
    AmmContext,
    KeyedAccount,
    Quote,
    Swap,
    SwapAndAccountMetas,
    SwapParams,
};
use solana_sdk::{ instruction::AccountMeta, program_pack::Pack, pubkey, pubkey::Pubkey };
use spl_math::{ checked_ceil_div::CheckedCeilDiv, uint::U256 };
use spl_token::state::Account as TokenAccount;
use std::convert::TryInto; // Required for try_into

mod cooldex_constants {
    use super::*;
    pub const COOLDEX_PROGRAM_ID: Pubkey = pubkey!("HAXJWG2uMp4Fegh5ZmKF4QbDc5WaJ4LnL1dePcooLDEX");
    pub const ADMIN_FEE_ACCOUNT: Pubkey = pubkey!("ETjXM6Yh8iXKeCEsrrqrnLRKivzajc1uThZM6Ua8RKqQ");
}

const COOLPAD_BURN_RATE_DENOMINATOR: u64 = 10000;

// Helper macro for U256 to u64 conversion with check
macro_rules! u256_to_u64_safe {
    ($value:expr, $context:expr) => {
        if $value > U256::from(u64::MAX) {
            Err(anyhow!(
                "Value {} exceeds u64::MAX in context: {}",
                $value,
                $context
            ))
        } else {
            Ok($value.as_u64())
        }
    };
}

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

    cult_wsol_account: Pubkey,
    cult_token_account: Pubkey,
}

impl CoolDexAmm {
    // User-provided version, assumed to be correct for this refactoring pass
    pub fn swap_token_amount_base_in(
        amount_in: U256,
        total_pc_without_take_pnl: U256,
        total_coin_without_take_pnl: U256,
        swap_direction_is_coin2pc: bool
    ) -> Result<U256> {
        let amount_out;
        match swap_direction_is_coin2pc {
            true => {
                // coin to pc
                // (x + delta_x) * (y + delta_y) = x * y
                // (coin + amount_in) * (pc - amount_out) = coin * pc
                // => amount_out = pc - coin * pc / (coin + amount_in)
                // => amount_out = ((pc * coin + pc * amount_in) - coin * pc) / (coin + amount_in)
                // => amount_out =  pc * amount_in / (coin + amount_in)
                let denominator = total_coin_without_take_pnl
                    .checked_add(amount_in)
                    .ok_or_else(||
                        anyhow!(
                            "swap_base_in (coin2pc): Overflow calculating denominator (coin + amount_in)"
                        )
                    )?;
                if denominator == U256::zero() {
                    return Err(
                        anyhow!(
                            "swap_base_in (coin2pc): Division by zero (denominator coin + amount_in is zero)"
                        )
                    );
                }
                amount_out = total_pc_without_take_pnl
                    .checked_mul(amount_in)
                    .ok_or_else(|| {
                        anyhow!("swap_base_in (coin2pc): Overflow multiplying pc by amount_in")
                    })?
                    .checked_div(denominator)
                    .ok_or_else(|| {
                        anyhow!(
                            "swap_base_in (coin2pc): Division error (pc * amount_in) / denominator"
                        )
                    })?;
            }
            false => {
                // pc to coin
                // (x + delta_x) * (y + delta_y) = x * y
                // (pc + amount_in) * (coin - amount_out) = coin * pc
                // => amount_out = coin - coin * pc / (pc + amount_in)
                // => amount_out = (coin * pc + coin * amount_in - coin * pc) / (pc + amount_in)
                // => amount_out = coin * amount_in / (pc + amount_in)
                let denominator = total_pc_without_take_pnl
                    .checked_add(amount_in)
                    .ok_or_else(||
                        anyhow!(
                            "swap_base_in (pc2coin): Overflow calculating denominator (pc + amount_in)"
                        )
                    )?;
                if denominator == U256::zero() {
                    return Err(
                        anyhow!(
                            "swap_base_in (pc2coin): Division by zero (denominator pc + amount_in is zero)"
                        )
                    );
                }
                amount_out = total_coin_without_take_pnl
                    .checked_mul(amount_in)
                    .ok_or_else(||
                        anyhow!("swap_base_in (pc2coin): Overflow multiplying coin by amount_in")
                    )?
                    .checked_div(denominator)
                    .ok_or_else(||
                        anyhow!(
                            "swap_base_in (pc2coin): Division error (coin * amount_in) / denominator"
                        )
                    )?;
            }
        }
        Ok(amount_out)
    }

    pub fn swap_token_amount_base_out(
        amount_out_target: U256,
        total_pc_without_take_pnl: U256,
        total_coin_without_take_pnl: U256,
        swap_direction_is_coin2pc: bool
    ) -> Result<U256> {
        let amount_in;
        match swap_direction_is_coin2pc {
            true => {
                // User wants PC, selling COIN. Calculate COIN in.
                // (x + delta_x) * (y + delta_y) = x * y
                // (coin + amount_in) * (pc - amount_out) = coin * pc
                // => amount_in = coin * pc / (pc - amount_out) - coin
                // => amount_in = (coin * pc - pc * coin + amount_out * coin) / (pc - amount_out)
                // => amount_in = (amount_out * coin) / (pc - amount_out)
                if total_pc_without_take_pnl <= amount_out_target {
                    return Err(
                        anyhow!(
                            "swap_base_out (coin2pc): Not enough PC liquidity (total_pc {} <= amount_out_target {}) for exact out.",
                            total_pc_without_take_pnl,
                            amount_out_target
                        )
                    );
                }
                let denominator = total_pc_without_take_pnl
                    .checked_sub(amount_out_target)
                    .ok_or_else(||
                        anyhow!(
                            "swap_base_out (coin2pc): Underflow calculating denominator (pc - amount_out_target). This should not happen due to prior check."
                        )
                    )?;
                if denominator == U256::zero() {
                    return Err(
                        anyhow!(
                            "swap_base_out (coin2pc): Division by zero (denominator pc - amount_out_target is zero). This should not happen due to prior check."
                        )
                    );
                }

                amount_in = total_coin_without_take_pnl
                    .checked_mul(amount_out_target)
                    .ok_or_else(||
                        anyhow!(
                            "swap_base_out (coin2pc): Overflow multiplying coin by amount_out_target"
                        )
                    )?
                    .checked_ceil_div(denominator)
                    .ok_or_else(||
                        anyhow!("swap_base_out (coin2pc): Division error for amount_in")
                    )?.0;
            }
            false => {
                // User wants COIN, selling PC. Calculate PC in.
                // (x + delta_x) * (y + delta_y) = x * y
                // (pc + amount_in) * (coin - amount_out) = coin * pc
                // => amount_out = coin - coin * pc / (pc + amount_in)
                // => amount_out = (coin * pc + coin * amount_in - coin * pc) / (pc + amount_in)
                // => amount_out = coin * amount_in / (pc + amount_in)

                // => amount_in = coin * pc / (coin - amount_out) - pc
                // => amount_in = (coin * pc - pc * coin + pc * amount_out) / (coin - amount_out)
                // => amount_in = (pc * amount_out) / (coin - amount_out)
                if total_coin_without_take_pnl <= amount_out_target {
                    return Err(
                        anyhow!(
                            "swap_base_out (pc2coin): Not enough COIN liquidity (total_coin {} <= amount_out_target {}) for exact out.",
                            total_coin_without_take_pnl,
                            amount_out_target
                        )
                    );
                }
                let denominator = total_coin_without_take_pnl
                    .checked_sub(amount_out_target)
                    .ok_or_else(||
                        anyhow!(
                            "swap_base_out (pc2coin): Underflow calculating denominator (coin - amount_out_target). This should not happen due to prior check."
                        )
                    )?;
                if denominator == U256::zero() {
                    return Err(
                        anyhow!(
                            "swap_base_out (pc2coin): Division by zero (denominator coin - amount_out_target is zero). This should not happen due to prior check."
                        )
                    );
                }

                amount_in = total_pc_without_take_pnl
                    .checked_mul(amount_out_target)
                    .ok_or_else(|| {
                        anyhow!(
                            "swap_base_out (pc2coin): Overflow multiplying pc by amount_out_target"
                        )
                    })?
                    .checked_ceil_div(denominator)
                    .ok_or_else(|| {
                        anyhow!("swap_base_out (pc2coin): Division error for amount_in")
                    })?.0;
            }
        }
        Ok(amount_in)
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
            cult_token_account: self.cult_token_account,
            cult_wsol_account: self.cult_wsol_account,
        }
    }
}

impl Amm for CoolDexAmm {
    fn from_keyed_account(keyed_account: &KeyedAccount, _amm_context: &AmmContext) -> Result<Self> {
        let account_data = &keyed_account.account.data;

        let get_pubkey_at = |offset: usize, name: &str| -> Result<Pubkey> {
            let slice: &[u8] = account_data
                .get(offset..offset + 32)
                .ok_or_else(|| {
                    anyhow!("Data slice out of bounds for {} at offset {}", name, offset)
                })?;
            let array: [u8; 32] = slice
                .try_into()
                .map_err(|e| anyhow!("Failed to convert slice to array for {}: {:?}", name, e))?;
            Ok(Pubkey::new_from_array(array))
        };

        let get_u64_at = |offset: usize, name: &str| -> Result<u64> {
            let slice: &[u8] = account_data
                .get(offset..offset + 8)
                .ok_or_else(|| {
                    anyhow!("Data slice out of bounds for {} at offset {}", name, offset)
                })?;
            let array: [u8; 8] = slice
                .try_into()
                .map_err(|e| anyhow!("Failed to convert slice to array for {}: {:?}", name, e))?;
            Ok(u64::from_le_bytes(array))
        };

        let reserve_mints = [
            get_pubkey_at(0x1a0, "reserve_mint_0")?,
            get_pubkey_at(0x1c0, "reserve_mint_1")?,
        ];
        let reserve_accounts = [
            get_pubkey_at(0x160, "reserve_account_0")?,
            get_pubkey_at(0x180, "reserve_account_1")?,
        ];
        let burn_rate = get_u64_at(0x308, "burn_rate")?;
        let swap_fee_numerator = get_u64_at(0x0b0, "swap_fee_numerator")?;
        let swap_fee_denominator = get_u64_at(0x0b8, "swap_fee_denominator")?;
        let cooldex_team_fee_wsol_fee_numerator = get_u64_at(
            0x0c0,
            "cooldex_team_fee_wsol_fee_numerator"
        )?;
        let cooldex_team_fee_wsol_fee_denominator = get_u64_at(
            0x0c8,
            "cooldex_team_fee_wsol_fee_denominator"
        )?;

        let (pda_for_reserves, _bump_seed) = Pubkey::find_program_address(
            &[b"amm authority"],
            &cooldex_constants::COOLDEX_PROGRAM_ID
        );
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
        vec![self.amm_info, self.reserve_accounts[0], self.reserve_accounts[1]]
    }
    fn update(&mut self, account_map: &AccountMap) -> Result<()> {
        let token_a_account_data = try_get_account_data(account_map, &self.reserve_accounts[0])?;
        let token_a_token_account = TokenAccount::unpack(token_a_account_data).map_err(|e|
            anyhow!("Failed to unpack token_a_account: {:?}", e)
        )?;

        let token_b_account_data = try_get_account_data(account_map, &self.reserve_accounts[1])?;
        let token_b_token_account = TokenAccount::unpack(token_b_account_data).map_err(|e|
            anyhow!("Failed to unpack token_b_account: {:?}", e)
        )?;

        self.reserves = [token_a_token_account.amount.into(), token_b_token_account.amount.into()];

        let amm_info_account_data = try_get_account_data(account_map, &self.amm_info)?;

        let get_u64_at = |slice: &[u8], offset: usize, name: &str| -> Result<u64> {
            let data_slice = slice
                .get(offset..offset + 8)
                .ok_or_else(|| {
                    anyhow!("Update: Data slice out of bounds for {} at offset {}", name, offset)
                })?;
            let array: [u8; 8] = data_slice
                .try_into()
                .map_err(|e| {
                    anyhow!("Update: Failed to convert slice to array for {}: {:?}", name, e)
                })?;
            Ok(u64::from_le_bytes(array))
        };

        self.burn_rate = get_u64_at(amm_info_account_data, 0x308, "burn_rate")?;
        self.swap_fee_numerator = get_u64_at(amm_info_account_data, 0x0b0, "swap_fee_numerator")?;
        self.swap_fee_denominator = get_u64_at(
            amm_info_account_data,
            0x0b8,
            "swap_fee_denominator"
        )?;
        self.cooldex_team_fee_wsol_fee_numerator = get_u64_at(
            amm_info_account_data,
            0x0c0,
            "cooldex_team_fee_wsol_fee_numerator"
        )?;
        self.cooldex_team_fee_wsol_fee_denominator = get_u64_at(
            amm_info_account_data,
            0x0c8,
            "cooldex_team_fee_wsol_fee_denominator"
        )?;

        if self.token_program_id == Pubkey::default() {
            self.token_program_id = account_map
                .get(&self.reserve_accounts[0])
                .map(|account| account.owner)
                .ok_or_else(|| {
                    anyhow!(
                        "Update: Reserve account 0 not found in account_map for token_program_id"
                    )
                })?;

            // Assuming reserve_mints[0] is the base for these PDAs as per original logic.
            // Consider if different base keys or seeds are needed if these are distinct accounts.
            self.cult_wsol_account = Pubkey::create_with_seed(
                &self.reserve_mints[0],
                "w",
                &self.token_program_id
            ).map_err(|e| anyhow!("Failed to create cult_wsol_account PDA: {:?}", e))?;
            self.cult_token_account = Pubkey::create_with_seed(
                &self.reserve_mints[0],
                "t",
                &self.token_program_id
            ).map_err(|e| anyhow!("Failed to create cult_token_account PDA: {:?}", e))?;
        }

        Ok(())
    }

    fn quote(
        &self,
        quote_params: &jupiter_amm_interface::QuoteParams
    ) -> Result<jupiter_amm_interface::Quote> {
        // Ensure denominators are not zero before use to prevent division by zero panics
        if self.swap_fee_denominator == 0 {
            return Err(anyhow!("swap_fee_denominator is zero"));
        }
        if self.cooldex_team_fee_wsol_fee_denominator == 0 {
            return Err(anyhow!("cooldex_team_fee_wsol_fee_denominator is zero"));
        }
        if COOLPAD_BURN_RATE_DENOMINATOR == 0 {
            // This is a const, but good practice for variables
            return Err(anyhow!("COOLPAD_BURN_RATE_DENOMINATOR is zero"));
        }

        let coolpad_burn_rate_denominator_u256 = U256::from(COOLPAD_BURN_RATE_DENOMINATOR);
        let two_u256 = U256::from(2u64);

        match
            (
                quote_params.swap_mode,
                quote_params.input_mint.eq(&self.reserve_mints[1]), // True if input_mint is reserve_mints[1] (e.g. WSOL)
            )
        {
            (
                jupiter_amm_interface::SwapMode::ExactIn,
                /* is_input_wsol (buy token with wsol) */ true,
            ) => {
                let amount_in_u256 = U256::from(quote_params.amount);

                let taxable_amount = amount_in_u256
                    .checked_mul(self.swap_fee_numerator.into())
                    .ok_or_else(|| {
                        anyhow!(
                            "ExactIn Buy: Overflow calculating taxable_amount (mul swap_fee_num)"
                        )
                    })?
                    .checked_ceil_div(self.swap_fee_denominator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Division error for taxable_amount (div swap_fee_den)")
                    })?.0;

                let platform_tax_u256 = taxable_amount
                    .checked_mul(self.cooldex_team_fee_wsol_fee_numerator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Overflow calculating platform_tax (mul wsol_fee_num)")
                    })?
                    .checked_ceil_div(self.cooldex_team_fee_wsol_fee_denominator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Division error for platform_tax (div wsol_fee_den)")
                    })?.0;

                let cult_wsol_numerator_factor_val = COOLPAD_BURN_RATE_DENOMINATOR.checked_sub(
                    self.burn_rate
                ).ok_or_else(||
                    anyhow!(
                        "ExactIn Buy: Underflow for cult_wsol_numerator_factor (burn_rate > denom)"
                    )
                )?;
                let cult_wsol_denominator_val = (2u64)
                    .checked_mul(COOLPAD_BURN_RATE_DENOMINATOR)
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Overflow for cult_wsol_denominator_val")
                    })?;
                if cult_wsol_denominator_val == 0 {
                    return Err(anyhow!("ExactIn Buy: cult_wsol_denominator_val is zero"));
                }

                let cult_wsol_u256 = taxable_amount
                    .checked_sub(platform_tax_u256)
                    .ok_or_else(||
                        anyhow!(
                            "ExactIn Buy: Underflow calculating cult_wsol base (taxable - platform_tax)"
                        )
                    )?
                    .checked_mul(cult_wsol_numerator_factor_val.into())
                    .ok_or_else(||
                        anyhow!("ExactIn Buy: Overflow calculating cult_wsol (mul factor)")
                    )?
                    .checked_ceil_div(cult_wsol_denominator_val.into())
                    .ok_or_else(|| anyhow!("ExactIn Buy: Division error for cult_wsol"))?.0;

                let input_token_to_hold_u256 = platform_tax_u256
                    .checked_add(cult_wsol_u256)
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Overflow calculating input_token_to_hold")
                    })?;

                let platform_tax_final = u256_to_u64_safe!(
                    platform_tax_u256,
                    "platform_tax_u256 to u64"
                )?;
                let cult_wsol_final = u256_to_u64_safe!(cult_wsol_u256, "cult_wsol_u256 to u64")?;

                let swap_in_after_deduct_fee = amount_in_u256
                    .checked_sub(input_token_to_hold_u256)
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Underflow calculating swap_in_after_deduct_fee")
                    })?;

                // Assuming input is WSOL (reserve[1]), output is TOKEN (reserve[0]) => pc_to_coin => false
                let swap_amount_out_u256 = CoolDexAmm::swap_token_amount_base_in(
                    swap_in_after_deduct_fee,
                    U256::from(self.reserves[1]), // PC reserve (WSOL)
                    U256::from(self.reserves[0]), // COIN reserve (TOKEN)
                    false
                )?;

                if swap_in_after_deduct_fee == U256::zero() {
                    // If no amount is swapped after input fees, output fees should also be zero or handled.
                    // Division by zero would occur below if not handled.
                    if swap_amount_out_u256 != U256::zero() {
                        return Err(
                            anyhow!(
                                "ExactIn Buy: Inconsistent state - swap_in_after_deduct_fee is zero but swap_amount_out is non-zero."
                            )
                        );
                    }
                    // If both are zero, then taxable_amount_token, burn_token, cult_token are zero.
                    let out_amount_final = u256_to_u64_safe!(
                        swap_amount_out_u256,
                        "swap_amount_out_u256 (zero path) to u64"
                    )?;
                    let fee_amount_val = platform_tax_final
                        .checked_add(cult_wsol_final)
                        .ok_or_else(||
                            anyhow!(
                                "ExactIn Buy: Overflow adding platform_tax_final and cult_wsol_final for fee_amount (zero path)"
                            )
                        )?;

                    return Ok(Quote {
                        fee_pct: self.swap_fee_numerator.into(),
                        in_amount: quote_params.amount,
                        out_amount: out_amount_final, // Likely 0
                        fee_amount: fee_amount_val,
                        fee_mint: self.reserve_mints[1], // Fee taken in input token (WSOL)
                        ..Quote::default()
                    });
                }

                let wsol_fee_den_minus_num_val = self.cooldex_team_fee_wsol_fee_denominator
                    .checked_sub(self.cooldex_team_fee_wsol_fee_numerator)
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Underflow for wsol_fee_den_minus_num_val")
                    })?;

                let tat_num_part1 = swap_amount_out_u256
                    .checked_mul(amount_in_u256)
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Overflow for taxable_amount_token num p1")
                    })?;
                let tat_num_part2 = tat_num_part1
                    .checked_mul(self.swap_fee_numerator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Overflow for taxable_amount_token num p2")
                    })?;
                let tat_numerator = tat_num_part2
                    .checked_mul(wsol_fee_den_minus_num_val.into())
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Overflow for taxable_amount_token num final")
                    })?;

                let tat_den_part1 = swap_in_after_deduct_fee
                    .checked_mul(self.swap_fee_denominator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Overflow for taxable_amount_token den p1")
                    })?;
                let tat_denominator = tat_den_part1
                    .checked_mul(self.cooldex_team_fee_wsol_fee_denominator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Overflow for taxable_amount_token den final")
                    })?;

                if tat_denominator == U256::zero() {
                    return Err(anyhow!("ExactIn Buy: taxable_amount_token denominator is zero"));
                }
                let taxable_amount_token = tat_numerator
                    .checked_ceil_div(tat_denominator)
                    .ok_or_else(||
                        anyhow!("ExactIn Buy: Division error for taxable_amount_token")
                    )?.0;

                let burn_token = taxable_amount_token
                    .checked_mul(self.burn_rate.into())
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Overflow calculating burn_token (mul burn_rate)")
                    })?
                    .checked_div(coolpad_burn_rate_denominator_u256)
                    .ok_or_else(|| anyhow!("ExactIn Buy: Division error for burn_token"))?;

                let cult_token_intermediate = taxable_amount_token
                    .checked_sub(burn_token)
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Underflow calculating cult_token_intermediate")
                    })?;
                let cult_token = cult_token_intermediate
                    .checked_div(two_u256)
                    .ok_or_else(|| anyhow!("ExactIn Buy: Division error calculating cult_token"))?;

                let total_output_token_fees = burn_token
                    .checked_add(cult_token)
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Overflow calculating total_output_token_fees")
                    })?;

                let swap_amount_out_to_user_u256 = swap_amount_out_u256
                    .checked_sub(total_output_token_fees)
                    .ok_or_else(|| {
                        anyhow!("ExactIn Buy: Underflow calculating swap_amount_out_to_user")
                    })?;

                let out_amount_final = u256_to_u64_safe!(
                    swap_amount_out_to_user_u256,
                    "swap_amount_out_to_user_u256 to u64"
                )?;
                let fee_amount_val = platform_tax_final
                    .checked_add(cult_wsol_final)
                    .ok_or_else(||
                        anyhow!(
                            "ExactIn Buy: Overflow adding platform_tax_final and cult_wsol_final for fee_amount"
                        )
                    )?;

                Ok(Quote {
                    fee_pct: self.swap_fee_numerator.into(),
                    in_amount: quote_params.amount,
                    out_amount: out_amount_final,
                    fee_amount: fee_amount_val,
                    fee_mint: self.reserve_mints[1], // Fee taken in input token (WSOL)
                    ..Quote::default()
                })
            }
            (
                jupiter_amm_interface::SwapMode::ExactIn,
                /* is_input_wsol (sell token for wsol) */ false,
            ) => {
                // Input == TOKEN. Output == WSOL.
                let amount_in_u256 = U256::from(quote_params.amount);

                let wsol_fee_den_minus_num_val = self.cooldex_team_fee_wsol_fee_denominator
                    .checked_sub(self.cooldex_team_fee_wsol_fee_numerator)
                    .ok_or_else(|| {
                        anyhow!("ExactIn Sell: Underflow for wsol_fee_den_minus_num_val")
                    })?;

                let taxable_num_part1 = amount_in_u256
                    .checked_mul(self.swap_fee_numerator.into())
                    .ok_or_else(|| anyhow!("ExactIn Sell: Overflow for taxable_amount num p1"))?;
                let taxable_numerator = taxable_num_part1
                    .checked_mul(wsol_fee_den_minus_num_val.into())
                    .ok_or_else(|| {
                        anyhow!("ExactIn Sell: Overflow for taxable_amount num final")
                    })?;

                let taxable_den_val = (
                    self.cooldex_team_fee_wsol_fee_denominator as u64 // Cast to u64 is fine as it's a u64 field
                )
                    .checked_mul(self.swap_fee_denominator)
                    .ok_or_else(|| anyhow!("ExactIn Sell: Overflow for taxable_amount den val"))?;
                if taxable_den_val == 0 {
                    return Err(anyhow!("ExactIn Sell: taxable_amount denominator value is zero"));
                }
                let taxable_amount = taxable_numerator
                    .checked_ceil_div(taxable_den_val.into())
                    .ok_or_else(|| anyhow!("ExactIn Sell: Division error for taxable_amount"))?.0;

                let amount_to_burn = taxable_amount
                    .checked_mul(self.burn_rate.into())
                    .ok_or_else(|| {
                        anyhow!("ExactIn Sell: Overflow calculating amount_to_burn (mul burn_rate)")
                    })?
                    .checked_ceil_div(coolpad_burn_rate_denominator_u256)
                    .ok_or_else(|| anyhow!("ExactIn Sell: Division error for amount_to_burn"))?.0;

                let cult_token_intermediate = taxable_amount
                    .checked_sub(amount_to_burn)
                    .ok_or_else(|| {
                        anyhow!("ExactIn Sell: Underflow calculating cult_token_intermediate")
                    })?;
                let cult_token = cult_token_intermediate
                    .checked_ceil_div(two_u256)
                    .ok_or_else(|| anyhow!("ExactIn Sell: Division error for cult_token"))?.0;

                let input_token_to_hold_u256 = amount_to_burn
                    .checked_add(cult_token)
                    .ok_or_else(|| {
                        anyhow!("ExactIn Sell: Overflow calculating input_token_to_hold")
                    })?;

                let swap_in_after_deduct_fee = amount_in_u256
                    .checked_sub(input_token_to_hold_u256)
                    .ok_or_else(|| {
                        anyhow!("ExactIn Sell: Underflow calculating swap_in_after_deduct_fee")
                    })?;

                // Assuming input is TOKEN (reserve[0]), output is WSOL (reserve[1]) => coin_to_pc => true
                let swap_amount_out_u256 = CoolDexAmm::swap_token_amount_base_in(
                    swap_in_after_deduct_fee,
                    U256::from(self.reserves[1]), // PC reserve (WSOL)
                    U256::from(self.reserves[0]), // COIN reserve (TOKEN)
                    true
                )?;

                if swap_in_after_deduct_fee == U256::zero() {
                    if swap_amount_out_u256 != U256::zero() {
                        return Err(
                            anyhow!(
                                "ExactIn Sell: Inconsistent state - swap_in_after_deduct_fee is zero but swap_amount_out is non-zero."
                            )
                        );
                    }
                    // If both are zero, then taxable_amount_wsol, platform_tax, cult_wsol are zero.
                    let out_amount_final = u256_to_u64_safe!(
                        swap_amount_out_u256,
                        "swap_amount_out_u256 (zero path) to u64"
                    )?;
                    // Fee is taken from output (WSOL), but calculated based on input fees that were zeroed out.
                    // So, platform_tax and cult_wsol would be zero.
                    return Ok(Quote {
                        fee_pct: self.swap_fee_numerator.into(),
                        in_amount: quote_params.amount,
                        out_amount: out_amount_final, // Likely 0
                        fee_amount: 0, // No WSOL fee if no output
                        fee_mint: self.reserve_mints[1], // Fee mint is WSOL
                        ..Quote::default()
                    });
                }

                let taw_num_part1 = swap_amount_out_u256
                    .checked_mul(amount_in_u256)
                    .ok_or_else(|| {
                        anyhow!("ExactIn Sell: Overflow for taxable_amount_wsol num p1")
                    })?;
                let taw_numerator = taw_num_part1
                    .checked_mul(self.swap_fee_numerator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactIn Sell: Overflow for taxable_amount_wsol num final")
                    })?;

                let taw_denominator = swap_in_after_deduct_fee
                    .checked_mul(self.swap_fee_denominator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactIn Sell: Overflow for taxable_amount_wsol den final")
                    })?;

                if taw_denominator == U256::zero() {
                    return Err(anyhow!("ExactIn Sell: taxable_amount_wsol denominator is zero"));
                }
                let taxable_amount_wsol = taw_numerator
                    .checked_ceil_div(taw_denominator)
                    .ok_or_else(||
                        anyhow!("ExactIn Sell: Division error for taxable_amount_wsol")
                    )?.0;

                let platform_tax_u256 = taxable_amount_wsol
                    .checked_mul(self.cooldex_team_fee_wsol_fee_numerator.into())
                    .ok_or_else(|| {
                        anyhow!(
                            "ExactIn Sell: Overflow calculating platform_tax (mul wsol_fee_num)"
                        )
                    })?
                    .checked_ceil_div(self.cooldex_team_fee_wsol_fee_denominator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactIn Sell: Division error for platform_tax (div wsol_fee_den)")
                    })?.0;

                let cult_wsol_num_factor_val = COOLPAD_BURN_RATE_DENOMINATOR.checked_sub(
                    self.burn_rate
                ).ok_or_else(||
                    anyhow!(
                        "ExactIn Sell: Underflow for cult_wsol_num_factor_val (burn_rate > denom)"
                    )
                )?;
                let cult_wsol_den_val = (2u64)
                    .checked_mul(COOLPAD_BURN_RATE_DENOMINATOR)
                    .ok_or_else(|| anyhow!("ExactIn Sell: Overflow for cult_wsol_den_val"))?;
                if cult_wsol_den_val == 0 {
                    return Err(anyhow!("ExactIn Sell: cult_wsol_den_val is zero"));
                }

                let cult_wsol_u256 = taxable_amount_wsol
                    .checked_sub(platform_tax_u256)
                    .ok_or_else(|| anyhow!("ExactIn Sell: Underflow calculating cult_wsol base"))?
                    .checked_mul(cult_wsol_num_factor_val.into())
                    .ok_or_else(|| {
                        anyhow!("ExactIn Sell: Overflow calculating cult_wsol (mul factor)")
                    })?
                    .checked_div(cult_wsol_den_val.into()) // Original used checked_div
                    .ok_or_else(|| anyhow!("ExactIn Sell: Division error for cult_wsol"))?;

                let total_wsol_fees = platform_tax_u256
                    .checked_add(cult_wsol_u256)
                    .ok_or_else(|| anyhow!("ExactIn Sell: Overflow calculating total_wsol_fees"))?;

                let swap_amount_out_to_user_u256 = swap_amount_out_u256
                    .checked_sub(total_wsol_fees)
                    .ok_or_else(|| {
                        anyhow!("ExactIn Sell: Underflow calculating swap_amount_out_to_user")
                    })?;

                let out_amount_final = u256_to_u64_safe!(
                    swap_amount_out_to_user_u256,
                    "swap_amount_out_to_user_u256 to u64"
                )?;
                let fee_amount_final = u256_to_u64_safe!(
                    total_wsol_fees,
                    "total_wsol_fees to u64"
                )?;

                Ok(Quote {
                    in_amount: quote_params.amount,
                    out_amount: out_amount_final,
                    fee_pct: self.swap_fee_numerator.into(),
                    fee_amount: fee_amount_final,
                    fee_mint: self.reserve_mints[1], // Fee taken in output token (WSOL)
                    ..Quote::default()
                })
            }
            (
                jupiter_amm_interface::SwapMode::ExactOut,
                /* is_input_wsol (buy token with wsol) */ true,
            ) => {
                // User wants exact TOKEN out, pays with WSOL.
                // swap_direction_is_coin2pc: false (PC to COIN)
                let amount_out_u256 = U256::from(quote_params.amount);
                let swap_in_before_add_fee = CoolDexAmm::swap_token_amount_base_out(
                    amount_out_u256,
                    U256::from(self.reserves[1]), // total_pc (WSOL)
                    U256::from(self.reserves[0]), // total_coin (TOKEN)
                    false // User wants TOKEN out, so direction is PC (WSOL) -> COIN (TOKEN)
                )?;

                let fee_den_minus_num_val = self.swap_fee_denominator
                    .checked_sub(self.swap_fee_numerator)
                    .ok_or_else(|| anyhow!("ExactOut Buy: Underflow for fee_den_minus_num_val"))?;
                if fee_den_minus_num_val == 0 {
                    return Err(
                        anyhow!(
                            "ExactOut Buy: swap_fee_denominator equals swap_fee_numerator, results in division by zero for swap_in_after_add_fee"
                        )
                    );
                }
                let swap_in_after_add_fee_u256 = swap_in_before_add_fee
                    .checked_mul(self.swap_fee_denominator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactOut Buy: Overflow for swap_in_after_add_fee (mul fee_den)")
                    })?
                    .checked_ceil_div(fee_den_minus_num_val.into())
                    .ok_or_else(|| {
                        anyhow!("ExactOut Buy: Division error for swap_in_after_add_fee")
                    })?.0;

                // This swap_fee is the total fee in input token (WSOL)
                // let _swap_fee = swap_in_after_add_fee_u256
                //     .checked_sub(swap_in_before_add_fee)
                //     .ok_or_else(|| anyhow!("ExactOut Buy: Underflow for swap_fee"))?;

                if swap_in_before_add_fee == U256::zero() {
                    // If base swap requires zero input, it implies amount_out_u256 was zero or pool is one-sided.
                    // virtual_amount_out would lead to div by zero.
                    if
                        amount_out_u256 != U256::zero() &&
                        swap_in_after_add_fee_u256 != U256::zero()
                    {
                        // amount_out could be non-zero if swap_in_before_add_fee is zero due to extreme imbalance
                        return Err(
                            anyhow!(
                                "ExactOut Buy: swap_in_before_add_fee is zero but amount_out is non-zero. Cannot calculate virtual_amount_out."
                            )
                        );
                    }
                    // If amount_out_u256 is zero, then all fees are zero.
                    let in_amount_final = u256_to_u64_safe!(
                        swap_in_after_add_fee_u256,
                        "swap_in_after_add_fee_u256 (zero path) to u64"
                    )?;
                    return Ok(Quote {
                        in_amount: in_amount_final, // Likely 0 if amount_out_u256 is 0
                        out_amount: quote_params.amount, // Could be 0
                        fee_pct: self.swap_fee_numerator.into(),
                        fee_amount: 0, // No fee if no swap or zero output
                        fee_mint: self.reserve_mints[1], // Input token (WSOL)
                        ..Quote::default()
                    });
                }

                let virtual_amount_out = amount_out_u256
                    .checked_mul(swap_in_after_add_fee_u256) // Use U256 version
                    .ok_or_else(||
                        anyhow!(
                            "ExactOut Buy: Overflow for virtual_amount_out (mul swap_in_after_add_fee)"
                        )
                    )?
                    .checked_ceil_div(swap_in_before_add_fee)
                    .ok_or_else(||
                        anyhow!("ExactOut Buy: Division error for virtual_amount_out")
                    )?.0;

                // Taxable output is on the TOKEN side (output token)
                let taxable_output_token = virtual_amount_out // This is in TOKEN units
                    .checked_mul(self.swap_fee_numerator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactOut Buy: Overflow for taxable_output_token (mul fee_num)")
                    })?
                    .checked_ceil_div(self.swap_fee_denominator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactOut Buy: Division error for taxable_output_token")
                    })?.0;

                // Taxable input is on the WSOL side (input token)
                let taxable_input_wsol = swap_in_after_add_fee_u256 // This is in WSOL units
                    .checked_mul(self.swap_fee_numerator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactOut Buy: Overflow for taxable_input_wsol (mul fee_num)")
                    })?
                    .checked_ceil_div(self.swap_fee_denominator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactOut Buy: Division error for taxable_input_wsol")
                    })?.0;

                let platform_tax_u256 = taxable_input_wsol // Platform fee in WSOL
                    .checked_mul(self.cooldex_team_fee_wsol_fee_numerator.into())
                    .ok_or_else(||
                        anyhow!("ExactOut Buy: Overflow for platform_tax (mul wsol_fee_num)")
                    )?
                    .checked_ceil_div(self.cooldex_team_fee_wsol_fee_denominator.into())
                    .ok_or_else(|| anyhow!("ExactOut Buy: Division error for platform_tax"))?.0;

                let cult_wsol_num_factor_val = COOLPAD_BURN_RATE_DENOMINATOR.checked_sub(
                    self.burn_rate
                ).ok_or_else(|| {
                    anyhow!("ExactOut Buy: Underflow for cult_wsol_num_factor_val")
                })?;
                let cult_wsol_den_val = (2u64)
                    .checked_mul(COOLPAD_BURN_RATE_DENOMINATOR)
                    .ok_or_else(|| anyhow!("ExactOut Buy: Overflow for cult_wsol_den_val"))?;
                if cult_wsol_den_val == 0 {
                    return Err(anyhow!("ExactOut Buy: cult_wsol_den_val is zero"));
                }

                let cult_wsol_u256 = taxable_input_wsol // Cult fee in WSOL
                    .checked_sub(platform_tax_u256)
                    .ok_or_else(|| anyhow!("ExactOut Buy: Underflow for cult_wsol base"))?
                    .checked_mul(cult_wsol_num_factor_val.into())
                    .ok_or_else(|| anyhow!("ExactOut Buy: Overflow for cult_wsol (mul factor)"))?
                    .checked_ceil_div(cult_wsol_den_val.into())
                    .ok_or_else(|| anyhow!("ExactOut Buy: Division error for cult_wsol"))?.0;

                // Output token (TOKEN) fees calculation
                let wsol_fee_den_minus_num_val = self.cooldex_team_fee_wsol_fee_denominator
                    .checked_sub(self.cooldex_team_fee_wsol_fee_numerator)
                    .ok_or_else(||
                        anyhow!(
                            "ExactOut Buy: Underflow for wsol_fee_den_minus_num_val (output fee calc)"
                        )
                    )?;

                let taxable_output_token_for_cult_burn = taxable_output_token // This is TOKEN
                    .checked_mul(wsol_fee_den_minus_num_val.into())
                    .ok_or_else(||
                        anyhow!(
                            "ExactOut Buy: Overflow for taxable_output_token_for_cult_burn (mul factor)"
                        )
                    )?
                    .checked_ceil_div(self.cooldex_team_fee_wsol_fee_denominator.into())
                    .ok_or_else(||
                        anyhow!(
                            "ExactOut Buy: Division error for taxable_output_token_for_cult_burn"
                        )
                    )?.0;

                let burn_amount_token = taxable_output_token_for_cult_burn // TOKEN burn
                    .checked_mul(self.burn_rate.into())
                    .ok_or_else(|| {
                        anyhow!("ExactOut Buy: Overflow for burn_amount_token (mul burn_rate)")
                    })?
                    .checked_ceil_div(coolpad_burn_rate_denominator_u256)
                    .ok_or_else(||
                        anyhow!("ExactOut Buy: Division error for burn_amount_token")
                    )?.0;

                // let _cult_contribution_token = taxable_output_token_for_cult_burn // TOKEN for cult
                //     .checked_sub(burn_amount_token)
                //     .ok_or_else(|| anyhow!("ExactOut Buy: Underflow for cult_contribution_token base"))?
                //     .checked_ceil_div(two_u256)
                //     .ok_or_else(|| anyhow!("ExactOut Buy: Division error for cult_contribution_token"))?
                //     .0;
                // This cult_contribution_token is not directly used to adjust out_amount,
                // as out_amount is fixed. It's part of the fee structure.
                // The actual out amount to user is `quote_params.amount`.
                // The `in_amount` already includes all necessary input fees.

                let in_amount_final = u256_to_u64_safe!(
                    swap_in_after_add_fee_u256,
                    "swap_in_after_add_fee_u256 to u64"
                )?;
                let total_input_fees_wsol = platform_tax_u256
                    .checked_add(cult_wsol_u256)
                    .ok_or_else(|| anyhow!("ExactOut Buy: Overflow for total_input_fees_wsol"))?;
                let fee_amount_final = u256_to_u64_safe!(
                    total_input_fees_wsol,
                    "total_input_fees_wsol to u64"
                )?;

                Ok(Quote {
                    in_amount: in_amount_final, // Total WSOL user needs to provide
                    out_amount: quote_params.amount, // Exact TOKEN user receives
                    fee_pct: self.swap_fee_numerator.into(),
                    fee_amount: fee_amount_final, // Total fees in WSOL
                    fee_mint: self.reserve_mints[1], // Fee is in input token (WSOL)
                    ..Quote::default()
                })
            }
            (
                jupiter_amm_interface::SwapMode::ExactOut,
                /* is_input_wsol (sell token for wsol) */ false,
            ) => {
                // User wants exact WSOL out, pays with TOKEN.
                // swap_direction_is_coin2pc: true (COIN to PC)
                let amount_out_u256 = U256::from(quote_params.amount);
                let swap_in_before_add_fee = CoolDexAmm::swap_token_amount_base_out(
                    amount_out_u256,
                    U256::from(self.reserves[1]), // total_pc (WSOL)
                    U256::from(self.reserves[0]), // total_coin (TOKEN)
                    true // User wants WSOL out, so direction is COIN (TOKEN) -> PC (WSOL)
                )?;

                let fee_den_minus_num_val = self.swap_fee_denominator
                    .checked_sub(self.swap_fee_numerator)
                    .ok_or_else(|| anyhow!("ExactOut Sell: Underflow for fee_den_minus_num_val"))?;
                if fee_den_minus_num_val == 0 {
                    return Err(
                        anyhow!(
                            "ExactOut Sell: swap_fee_denominator equals swap_fee_numerator, results in division by zero for swap_in_after_add_fee"
                        )
                    );
                }
                let swap_in_after_add_fee_u256 = swap_in_before_add_fee // This is in TOKEN
                    .checked_mul(self.swap_fee_denominator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactOut Sell: Overflow for swap_in_after_add_fee (mul fee_den)")
                    })?
                    .checked_ceil_div(fee_den_minus_num_val.into())
                    .ok_or_else(|| {
                        anyhow!("ExactOut Sell: Division error for swap_in_after_add_fee")
                    })?.0;

                // let _swap_fee = swap_in_after_add_fee_u256
                //     .checked_sub(swap_in_before_add_fee)
                //     .ok_or_else(|| anyhow!("ExactOut Sell: Underflow for swap_fee"))?;

                if swap_in_before_add_fee == U256::zero() {
                    if
                        amount_out_u256 != U256::zero() &&
                        swap_in_after_add_fee_u256 != U256::zero()
                    {
                        return Err(
                            anyhow!(
                                "ExactOut Sell: swap_in_before_add_fee is zero but amount_out is non-zero. Cannot calculate virtual_amount_out."
                            )
                        );
                    }
                    let in_amount_final = u256_to_u64_safe!(
                        swap_in_after_add_fee_u256,
                        "swap_in_after_add_fee_u256 (zero path) to u64"
                    )?;
                    return Ok(Quote {
                        in_amount: in_amount_final,
                        out_amount: quote_params.amount,
                        fee_pct: self.swap_fee_numerator.into(),
                        fee_amount: 0, // No fee in WSOL if no output or no input swap
                        fee_mint: self.reserve_mints[1], // Fee mint is WSOL (output)
                        ..Quote::default()
                    });
                }

                let virtual_amount_out_wsol = amount_out_u256 // This is WSOL
                    .checked_mul(swap_in_after_add_fee_u256) // This is TOKEN
                    .ok_or_else(||
                        anyhow!(
                            "ExactOut Sell: Overflow for virtual_amount_out_wsol (mul swap_in_after_add_fee)"
                        )
                    )?
                    .checked_ceil_div(swap_in_before_add_fee) // This is TOKEN
                    .ok_or_else(||
                        anyhow!("ExactOut Sell: Division error for virtual_amount_out_wsol")
                    )?.0;

                // Taxable output is on the WSOL side
                let taxable_output_wsol = virtual_amount_out_wsol // WSOL
                    .checked_mul(self.swap_fee_numerator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactOut Sell: Overflow for taxable_output_wsol (mul fee_num)")
                    })?
                    .checked_ceil_div(self.swap_fee_denominator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactOut Sell: Division error for taxable_output_wsol")
                    })?.0;

                // Taxable input is on the TOKEN side
                let taxable_input_token = swap_in_after_add_fee_u256 // TOKEN
                    .checked_mul(self.swap_fee_numerator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactOut Sell: Overflow for taxable_input_token (mul fee_num)")
                    })?
                    .checked_ceil_div(self.swap_fee_denominator.into())
                    .ok_or_else(|| {
                        anyhow!("ExactOut Sell: Division error for taxable_input_token")
                    })?.0;

                // Input token (TOKEN) fees calculation
                let wsol_fee_den_minus_num_val = self.cooldex_team_fee_wsol_fee_denominator
                    .checked_sub(self.cooldex_team_fee_wsol_fee_numerator)
                    .ok_or_else(||
                        anyhow!(
                            "ExactOut Sell: Underflow for wsol_fee_den_minus_num_val (input fee calc)"
                        )
                    )?;

                let taxable_input_token_for_cult_burn = taxable_input_token // TOKEN
                    .checked_mul(wsol_fee_den_minus_num_val.into())
                    .ok_or_else(||
                        anyhow!(
                            "ExactOut Sell: Overflow for taxable_input_token_for_cult_burn (mul factor)"
                        )
                    )?
                    .checked_ceil_div(self.cooldex_team_fee_wsol_fee_denominator.into())
                    .ok_or_else(||
                        anyhow!(
                            "ExactOut Sell: Division error for taxable_input_token_for_cult_burn"
                        )
                    )?.0;

                let _burn_amount_token = taxable_input_token_for_cult_burn // TOKEN burn
                    .checked_mul(self.burn_rate.into())
                    .ok_or_else(|| {
                        anyhow!("ExactOut Sell: Overflow for burn_amount_token (mul burn_rate)")
                    })?
                    .checked_ceil_div(coolpad_burn_rate_denominator_u256)
                    .ok_or_else(||
                        anyhow!("ExactOut Sell: Division error for burn_amount_token")
                    )?.0;

                // let _cult_contribution_token_u256 = taxable_input_token_for_cult_burn // TOKEN for cult
                //     .checked_sub(burn_amount_token)
                //     .ok_or_else(|| anyhow!("ExactOut Sell: Underflow for cult_contribution_token base"))?
                //     .checked_ceil_div(two_u256)
                //     .ok_or_else(|| anyhow!("ExactOut Sell: Division error for cult_contribution_token"))?
                //     .0;
                // let _cult_contribution_token_final = u256_to_u64_safe!(_cult_contribution_token_u256, "_cult_contribution_token_u256 to u64")?;
                // This token fee is taken from the input.

                // Output token (WSOL) fees calculation
                let platform_tax_u256 = taxable_output_wsol // WSOL platform fee
                    .checked_mul(self.cooldex_team_fee_wsol_fee_numerator.into())
                    .ok_or_else(||
                        anyhow!("ExactOut Sell: Overflow for platform_tax (mul wsol_fee_num)")
                    )?
                    .checked_ceil_div(self.cooldex_team_fee_wsol_fee_denominator.into())
                    .ok_or_else(|| anyhow!("ExactOut Sell: Division error for platform_tax"))?.0;

                let cult_wsol_num_factor_val = COOLPAD_BURN_RATE_DENOMINATOR.checked_sub(
                    self.burn_rate
                ).ok_or_else(|| {
                    anyhow!("ExactOut Sell: Underflow for cult_wsol_num_factor_val")
                })?;
                let cult_wsol_den_val = (2u64)
                    .checked_mul(COOLPAD_BURN_RATE_DENOMINATOR)
                    .ok_or_else(|| anyhow!("ExactOut Sell: Overflow for cult_wsol_den_val"))?;
                if cult_wsol_den_val == 0 {
                    return Err(anyhow!("ExactOut Sell: cult_wsol_den_val is zero"));
                }

                let cult_wsol_u256 = taxable_output_wsol // WSOL cult fee
                    .checked_sub(platform_tax_u256)
                    .ok_or_else(|| anyhow!("ExactOut Sell: Underflow for cult_wsol base"))?
                    .checked_mul(cult_wsol_num_factor_val.into())
                    .ok_or_else(|| anyhow!("ExactOut Sell: Overflow for cult_wsol (mul factor)"))?
                    .checked_ceil_div(cult_wsol_den_val.into())
                    .ok_or_else(|| anyhow!("ExactOut Sell: Division error for cult_wsol"))?.0;

                let in_amount_final = u256_to_u64_safe!(
                    swap_in_after_add_fee_u256,
                    "swap_in_after_add_fee_u256 to u64"
                )?;
                let total_output_fees_wsol = platform_tax_u256
                    .checked_add(cult_wsol_u256)
                    .ok_or_else(|| anyhow!("ExactOut Sell: Overflow for total_output_fees_wsol"))?;
                let fee_amount_final = u256_to_u64_safe!(
                    total_output_fees_wsol,
                    "total_output_fees_wsol to u64"
                )?;

                Ok(Quote {
                    in_amount: in_amount_final, // Total TOKEN user needs to provide
                    out_amount: quote_params.amount, // Exact WSOL user receives
                    fee_pct: self.swap_fee_numerator.into(),
                    fee_amount: fee_amount_final, // Total fees in WSOL (taken from output)
                    fee_mint: self.reserve_mints[1], // Fee is in output token (WSOL)
                    ..Quote::default()
                })
            }
        }
    }

    fn get_swap_and_account_metas(
        &self,
        swap_params: &jupiter_amm_interface::SwapParams
    ) -> Result<jupiter_amm_interface::SwapAndAccountMetas> {
        let SwapParams {
            token_transfer_authority,
            source_token_account,
            destination_token_account,
            ..
        } = swap_params;

        if self.token_program_id == Pubkey::default() {
            return Err(
                anyhow!(
                    "get_swap_and_account_metas: token_program_id is not initialized. Call update() first."
                )
            );
        }

        let admin_fee_account_seed_byte_val = self.amm_info
            .to_bytes()
            .get(0)
            .ok_or_else(|| {
                anyhow!("AMM info pubkey is empty, cannot derive admin_fee_account seed byte")
            })?
            .clone();

        let admin_fee_account = Pubkey::create_with_seed(
            &cooldex_constants::FEE_OWNER,
            &(admin_fee_account_seed_byte_val % 8).to_string(), // Use dereferenced value
            &self.token_program_id
        ).map_err(|e| anyhow!("Failed to create admin_fee_account PDA: {:?}", e))?;

        Ok(SwapAndAccountMetas {
            swap: Swap::TokenSwap, // TODO: Should be a custom Swap variant like Swap::CoolDexSwap if you have custom instruction data
            account_metas: vec![
                AccountMeta::new_readonly(self.token_program_id, false),
                AccountMeta::new(self.amm_info, false),
                AccountMeta::new_readonly(self.pda_for_reserves, false),
                AccountMeta::new(self.reserve_accounts[0], false), // Token A reserve
                AccountMeta::new(self.reserve_accounts[1], false), // Token B reserve
                AccountMeta::new(*source_token_account, false),
                AccountMeta::new(*destination_token_account, false),
                AccountMeta::new_readonly(*token_transfer_authority, true),
                AccountMeta::new(self.reserve_mints[0], false), // Assuming reserve_mints[0] is the primary "coin" mint that might be burned
                AccountMeta::new(admin_fee_account, false),
                AccountMeta::new(self.cult_wsol_account, false),
                AccountMeta::new(self.cult_token_account, false)
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
