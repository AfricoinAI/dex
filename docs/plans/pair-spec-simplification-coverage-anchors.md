# UniswapV2PairSpec Coverage Anchors

Mapping from each `docs/spec-coverage.md` 'Current Implemented Coverage' bullet (Phase 0 snapshot) to at least one surviving named spec in `UniswapV2PairSpec.lean`.

This table is the audit artifact for Phase 8 verification step 7: every Phase-0-snapshot security/correctness obligation maps to at least one non-`private` `def pair_X` that still exists after the refactor.

It is generated at Phase 1, before any move/delete commits, and remains stable through the rest of the refactor.

## View success/frames (spec-coverage.md lines 44-53)

- `pair_decimals_run_success_frames_state`
- `pair_totalSupply_run_success_frames_state`
- `pair_balanceOf_run_success_frames_state`
- `pair_allowance_run_success_frames_state`
- `pair_factory_run_success_frames_state`
- `pair_token0_run_success_frames_state`
- `pair_token1_run_success_frames_state`
- `pair_minimumLiquidity_run_success_frames_state`
- `pair_getReserves_run_success_frames_state`
- `pair_price0CumulativeLast_run_success_frames_state`
- `pair_price1CumulativeLast_run_success_frames_state`
- `pair_kLast_run_success_frames_state`

## ERC20 trace boundary (spec-coverage.md lines 54-58)

- `pair_safeTransfer_traces_token_transfer`
- `pair_safeTransfer_event_replay_moves_token_balance`
- `pair_two_safeTransfer_events_replay_move_distinct_token_balances`

## LP ERC20 approve/transfer/transferFrom bookkeeping (spec-coverage.md lines 59-66)

- `pair_approve_succeeds`
- `pair_approve_sets_allowance`
- `pair_approve_keeps_balances`
- `pair_approve_keeps_total_supply`
- `pair_approve_keeps_pool_storage`
- `pair_approve_emits_approval`
- `pair_transfer_reverts_when_balance_low`
- `pair_transfer_to_self_keeps_balances`
- `pair_transfer_reverts_when_recipient_balance_would_overflow`
- `pair_transfer_moves_tokens_between_distinct_accounts`
- `pair_transfer_keeps_total_supply`
- `pair_transfer_keeps_pool_storage`
- `pair_transfer_emits_transfer`
- `pair_transferFrom_reverts_when_allowance_low`
- `pair_transferFrom_reverts_when_balance_low`
- `pair_transferFrom_reverts_when_recipient_balance_would_overflow`
- `pair_transferFrom_to_self_keeps_balances`
- `pair_transferFrom_moves_tokens_between_distinct_accounts`
- `pair_transferFrom_keeps_total_supply`
- `pair_transferFrom_keeps_pool_storage`
- `pair_transferFrom_keeps_infinite_allowance`
- `pair_transferFrom_spends_finite_allowance`
- `pair_transferFrom_emits_transfer`

## Exact run-result reverts (init, lock, skim, swap zero-output) (spec-coverage.md lines 67-74)

- `pair_initialize_run_revert_non_factory`
- `pair_initialize_run_revert_already_initialized`
- `pair_mint_run_revert_locked`
- `pair_burn_run_revert_locked`
- `pair_swap_run_revert_locked`
- `pair_skim_run_revert_locked`
- `pair_sync_run_revert_locked`
- `pair_skim_run_revert_balance0_below_reserve`
- `pair_skim_run_revert_balance1_below_reserve`
- `pair_swap_run_revert_zero_output`
- `pair_mint_run_revert_balance0_overflow`
- `pair_mint_run_revert_balance1_overflow`
- `pair_sync_run_revert_balance0_overflow`
- `pair_sync_run_revert_balance1_overflow`
- `pair_transfer_run_revert_balance_low`
- `pair_transfer_run_revert_recipient_balance_overflow`
- `pair_transferFrom_run_revert_allowance_low`
- `pair_transferFrom_run_revert_balance_low`
- `pair_transferFrom_run_revert_recipient_balance_overflow`

## Successful initialization (positive lifecycle) (spec-coverage.md lines 75-79)

- `pair_initialize_run_success_sets_tokens`
- `pair_initialize_run_success_keeps_amm_accounting`
- `pair_initialize_sets_tokens`

## Reentrancy invariant (lock blocks all mutating entrypoints) (spec-coverage.md lines 80-83)

- `pair_reentrancy_guard_blocks_all_mutating_entrypoints`

## Lock-open implied by success (spec-coverage.md lines 84-86)

- `pair_mint_success_run_implies_lock_open`
- `pair_burn_success_run_implies_lock_open`
- `pair_swap_success_run_implies_lock_open`
- `pair_skim_success_run_implies_lock_open`
- `pair_sync_success_run_implies_lock_open`

## Revert-frame token-balance preservation (spec-coverage.md lines 87-89)

- `pair_mint_revert_keeps_token_balances`
- `pair_burn_revert_keeps_token_balances`
- `pair_swap_revert_keeps_token_balances`
- `pair_skim_revert_keeps_token_balances`
- `pair_sync_revert_keeps_token_balances`

## Pair-local atomicity on revert (storage + events) (spec-coverage.md lines 90-92)

- `pair_mint_revert_keeps_pair_state`
- `pair_burn_revert_keeps_pair_state`
- `pair_swap_revert_keeps_pair_state`
- `pair_skim_revert_keeps_pair_state`
- `pair_sync_revert_keeps_pair_state`

## Skim public-call success: surplus transfer, reserves, lock, accounting (spec-coverage.md lines 93-99)

- `pair_skim_run_success_transfers_excess_and_restores_unlocked`
- `pair_skim_run_success_moves_exact_surplus_in_token_world`
- `pair_skim_run_success_matches_closed_world_step`
- `pair_skim_success_run_matches_closed_world_step_from_run`
- `pair_skim_success_run_restores_unlocked_from_run`
- `pair_skim_success_run_no_caller_token_balance_profit_from_run`
- `pair_skim_success_run_implies_balances_back_reserves`
- `pair_skim_success_run_preserves_good_from_run`
- `pair_skim_success_run_preserves_liquidity_supply_from_run`

## Mint/burn/swap public-call accounting connection (spec-coverage.md lines 100-118)

- `pair_first_mint_uses_balance_increase_as_deposit`
- `pair_later_mint_uses_balance_increase_as_deposit`
- `pair_burn_uses_pair_lp_balance_and_total_supply`
- `pair_burn_leaves_remaining_token_balances`
- `pair_swap_uses_final_balances_to_compute_input`
- `pair_swap_checks_k_against_final_balances`
- `pair_first_mint_success_uses_canonical_liquidity_formula`
- `pair_burn_success_pays_exact_pro_rata_amounts`
- `pair_swap_success_accounts_for_input_and_output`
- `pair_swap_success_charges_k_against_final_balances`
- `pair_swap_success_run_no_caller_spot_profit_with_valid_swap`

## Initial mint formula (spec-coverage.md lines 119-122)

- `pair_first_mint_success_uses_canonical_liquidity_formula`
- `pair_mint_first_success_run_locks_minimum_liquidity_from_run`

## Burn redemption exact amounts + reserve cache (spec-coverage.md lines 123-127)

- `pair_burn_success_pays_exact_pro_rata_amounts`
- `pair_burn_success_caches_post_redemption_balances`
- `pair_burn_success_run_updates_reserves_to_balances_from_run`

## Swap balance/K accounting (spec-coverage.md lines 128-130)

- `pair_swap_success_accounts_for_input_and_output`
- `pair_swap_success_charges_k_against_final_balances`
- `pair_swap_success_run_k_uses_final_balances_from_run`

## sync accepts in-bound balances as reserves (spec-coverage.md lines 131-132)

- `pair_sync_success_run_updates_reserves_to_balances_from_run`

## Closed-world surplus reconciliation (skim/sync) (spec-coverage.md lines 133-160)

- `pair_closed_world_skim_removes_surplus`
- `pair_closed_world_skim_eliminates_surplus`
- `pair_closed_world_skim_removes_exact_surplus_value`
- `pair_closed_world_skim_token_balance_value_never_increases`
- `pair_closed_world_skim_token_balance_value_never_increases_at_spot`
- `pair_closed_world_skim_preserves_balanced_pool`
- `pair_closed_world_skim_preserves_good`
- `pair_closed_world_skim_preserves_liquidity_supply`
- `pair_closed_world_skim_preserves_k`
- `pair_closed_world_sync_sets_reserves_to_balances`
- `pair_closed_world_sync_preserves_token_balances`
- `pair_closed_world_sync_preserves_token_balance_value`
- `pair_closed_world_sync_eliminates_surplus`
- `pair_closed_world_sync_preserves_good`
- `pair_closed_world_sync_preserves_liquidity_supply`
- `pair_closed_world_sync_never_decreases_k`
- `pair_closed_world_sync_preserves_k_without_surplus`
- `pair_closed_world_sync_preserves_balanced_pool`
- `pair_closed_world_balanced_skim_or_sync_preserves_pool`
- `pair_closed_world_balanced_skim_sync_path_preserves_pool`
- `pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_pool`
- `pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_k`
- `pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_zero_surplus`
- `pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_token_balance_value`
- `pair_closed_world_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases`
- `pair_closed_world_reachable_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases`
- `pair_closed_world_sync_k_increase_requires_surplus`
- `pair_closed_world_reserve_write_sets_reserves_to_balances`
- `pair_closed_world_skim_or_sync_token_balance_value_never_increases`
- `pair_closed_world_skim_or_sync_token_balance_value_never_increases_at_spot`
- `pair_sync_success_run_no_caller_token_balance_profit_from_run`

## TWAP/oracle reserve-update rules (spec-coverage.md lines 161-186)

- `pair_reserve_update_oracle_same_timestamp_keeps_price_cumulatives`
- `pair_reserve_update_oracle_elapsed_updates_price_cumulatives`
- `pair_reserve_update_oracle_inactive_elapsed_keeps_price_cumulatives`
- `pair_sync_oracle_same_timestamp_keeps_price_cumulatives`
- `pair_sync_oracle_elapsed_updates_price_cumulatives`
- `pair_sync_oracle_inactive_elapsed_keeps_price_cumulatives`
- `pair_sync_success_run_uses_oracle_rule`
- `pair_sync_success_run_uses_oracle_rule_from_run`
- `pair_mint_first_success_run_uses_oracle_rule`
- `pair_mint_first_success_run_uses_oracle_rule_from_run`
- `pair_mint_subsequent_success_run_uses_oracle_rule`
- `pair_mint_subsequent_success_run_uses_oracle_rule_from_run`
- `pair_burn_success_run_uses_oracle_rule`
- `pair_swap_success_run_uses_oracle_rule`
- `pair_swap_success_run_uses_oracle_rule_from_run`
- `pair_closed_world_concrete_reserve_write_uses_oracle_rule`

## PairWorldGood preservation + reachable invariants (spec-coverage.md lines 187-260)

- `pair_closed_world_step_preserves_good`
- `pair_closed_world_path_preserves_good`
- `pair_closed_world_reachable_good`
- `pair_closed_world_reachable_path_good`
- `pair_closed_world_path_preserves_reachability`
- `pair_closed_world_reachable_supply_good`
- `pair_closed_world_path_supply_good`
- `pair_closed_world_path_reserves_fit_uint112`
- `pair_closed_world_path_locked_liquidity_never_exceeds_supply`
- `pair_closed_world_positive_supply_path_remains_positive`
- `pair_closed_world_reachable_positive_supply_path_remains_positive`
- `pair_closed_world_reachable_positive_supply_has_positive_reserves`
- `pair_closed_world_reachable_positive_supply_path_has_positive_reserves`
- `pair_closed_world_reachable_positive_supply_path_has_positive_token_balances`
- `pair_concrete_state_reserves_backed`
- `pair_concrete_state_uint112_reserves`
- `pair_closed_world_reachable_reserves_backed`
- `pair_closed_world_path_reserves_backed`
- `pair_closed_world_reachable_path_reserves_backed`
- `pair_closed_world_reachable_path_reserves_fit_uint112`
- `pair_closed_world_reachable_reserves_fit_uint112`
- `pair_closed_world_nonzero_supply_locks_minimum_liquidity`
- `pair_closed_world_zero_supply_has_no_locked_liquidity`
- `pair_closed_world_locked_liquidity_never_exceeds_supply`
- `pair_closed_world_reachable_path_minimum_liquidity_lock`
- `pair_closed_world_step_locked_liquidity_never_decreases`
- `pair_closed_world_path_locked_liquidity_never_decreases`
- `pair_closed_world_reachable_path_locked_liquidity_never_decreases`
- `pair_closed_world_supply_changes_only_on_mint_or_burn`
- `pair_closed_world_reserve_changes_only_on_reserve_update_actions`
- `pair_closed_world_no_reserve_update_path_preserves_reserves`
- `pair_closed_world_no_reserve_update_path_preserves_k_and_spot_value`
- `pair_closed_world_reachable_reserve_change_requires_reserve_update`
- `pair_closed_world_non_liquidity_step_preserves_supply`
- `pair_closed_world_no_mint_burn_path_preserves_supply`
- `pair_closed_world_reachable_no_mint_burn_path_preserves_supply`
- `pair_closed_world_non_burn_step_never_decreases_supply`
- `pair_closed_world_no_burn_path_never_decreases_supply`
- `pair_closed_world_reachable_no_burn_path_never_decreases_supply`
- `pair_closed_world_non_mint_step_never_increases_supply`
- `pair_closed_world_no_mint_path_never_increases_supply`
- `pair_closed_world_reachable_no_mint_path_never_increases_supply`
- `pair_closed_world_reachable_supply_increase_requires_mint`
- `pair_closed_world_reachable_supply_decrease_requires_burn`
- `pair_closed_world_reachable_supply_change_requires_mint_or_burn`
- `pair_closed_world_approve_preserves_pool`
- `pair_closed_world_transfer_preserves_pool`
- `pair_closed_world_transferFrom_preserves_pool`
- `pair_closed_world_share_bookkeeping_path_preserves_pool_state`
- `pair_closed_world_share_bookkeeping_path_preserves_k_and_value`

## Donation framing + surplus classifier (spec-coverage.md lines 260-286)

- `pair_closed_world_donate_preserves_reserves_and_supply`
- `pair_closed_world_donate_preserves_k`
- `pair_closed_world_donation_increases_surplus_exactly`
- `pair_closed_world_non_donation_step_never_increases_surplus`
- `pair_closed_world_no_donation_path_never_increases_surplus`
- `pair_closed_world_reachable_no_donation_path_never_increases_surplus`
- `pair_closed_world_reachable_surplus_increase_requires_donation`
- `pair_closed_world_reachable_no_donation_path_surplus_value_never_increases`
- `pair_closed_world_reachable_zero_surplus_no_donation_path_preserves_zero_surplus`
- `pair_closed_world_reachable_zero_surplus_no_donation_path_ends_balanced`

## Mint/burn closed-world supply discipline + non-dilution (spec-coverage.md lines 287-326)

- `pair_closed_world_first_mint_locks_minimum_liquidity`
- `pair_closed_world_first_mint_keeps_locked_share`
- `pair_closed_world_subsequent_mint_preserves_locked_liquidity`
- `pair_closed_world_mint_strictly_increases_supply`
- `pair_closed_world_mint_adds_exact_deposits_to_reserves`
- `pair_closed_world_burn_reduces_supply_by_liquidity`
- `pair_closed_world_burn_removes_exact_redemptions_from_balances`
- `pair_closed_world_burn_never_increases_supply`
- `pair_closed_world_burn_cannot_redeem_locked_liquidity`
- `pair_closed_world_burn_preserves_positive_balances`
- `pair_closed_world_reachable_positive_supply_burn_preserves_positive_balances`
- `pair_closed_world_mint_updates_reserves_to_balances`
- `pair_closed_world_mint_never_decreases_k`
- `pair_closed_world_mint_preserves_good`
- `pair_closed_world_mint_liquidity_ratio`
- `pair_closed_world_mint_does_not_dilute_existing_lp_share`
- `pair_closed_world_burn_updates_reserves_to_balances`
- `pair_closed_world_burn_preserves_good`
- `pair_closed_world_burn_liquidity_ratio`
- `pair_closed_world_burn_does_not_dilute_remaining_lp_share`
- `pair_closed_world_swap_updates_reserves_to_balances`
- `pair_closed_world_swap_respects_fee_adjusted_k`
- `pair_closed_world_fee_adjusted_swap_implies_raw_k`
- `pair_closed_world_swap_preserves_good`
- `pair_closed_world_swap_never_decreases_k`
- `pair_closed_world_swap_has_input_and_output`
- `pair_closed_world_swap_final_balances_account_for_input_and_output`
- `pair_closed_world_swap_k_uses_final_balances`
- `pair_closed_world_swap_outputs_below_reserves`
- `pair_closed_world_swap_preserves_liquidity_supply`
- `pair_closed_world_swap_no_spot_value_extraction`
- `pair_closed_world_reachable_positive_supply_swap_no_spot_value_extraction`
- `pair_closed_world_reachable_positive_supply_swap_no_caller_spot_profit`
- `pair_closed_world_reachable_zero_surplus_swap_no_caller_token_balance_profit`

## Flash-swap callback boundary (ECM + lock + reentry) (spec-coverage.md lines 287-296)

- `pair_flash_callback_module_gates_nonempty_data`
- `pair_flash_callback_module_encodes_canonical_call`
- `pair_flash_callback_module_bubbles_callback_failure`
- `pair_flash_callback_runs_while_pair_is_locked`
- `pair_flash_callback_reentry_attempts_revert_locked`

## Same-LP-supply spot-value/token-balance no-extraction (donated-surplus story) (spec-coverage.md lines 327-355)

- `pair_closed_world_same_supply_path_never_decreases_k`
- `pair_closed_world_same_supply_path_no_spot_profit`
- `pair_closed_world_positive_supply_same_supply_path_no_spot_profit`
- `pair_closed_world_reachable_same_supply_path_never_decreases_k`
- `pair_closed_world_reachable_same_supply_path_no_spot_profit`
- `pair_closed_world_reachable_same_supply_path_pool_value_never_decreases`
- `pair_closed_world_reachable_same_supply_path_no_spot_value_extraction`
- `pair_closed_world_reachable_same_supply_path_no_token1_denominated_profit`
- `pair_closed_world_reachable_same_supply_path_token_balance_loss_bounded_by_initial_surplus`
- `pair_closed_world_reachable_same_supply_path_caller_token_balance_profit_bounded_by_initial_surplus`
- `pair_closed_world_reachable_zero_surplus_same_supply_path_no_token_balance_value_extraction`
- `pair_closed_world_reachable_zero_surplus_same_supply_path_no_caller_token_balance_profit`
- `pair_closed_world_reachable_same_supply_path_no_caller_spot_profit`
- `pair_closed_world_reachable_positive_supply_same_supply_path_no_spot_value_extraction`
- `pair_closed_world_reachable_balanced_same_supply_path_no_token_balance_value_extraction`
- `pair_closed_world_reachable_balanced_no_mint_burn_path_no_token_balance_value_extraction`
- `pair_closed_world_reachable_no_mint_burn_path_token_balance_loss_bounded_by_initial_surplus`
- `pair_closed_world_reachable_no_mint_burn_path_caller_token_balance_profit_bounded_by_initial_surplus`
- `pair_closed_world_reachable_zero_surplus_no_mint_burn_path_no_token_balance_value_extraction`
- `pair_closed_world_reachable_zero_surplus_no_mint_burn_path_no_caller_token_balance_profit`
- `pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_token_balance_value_extraction`
- `pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_caller_token_balance_profit`
- `pair_closed_world_reachable_no_mint_burn_path_no_caller_spot_profit`
- `pair_closed_world_reachable_no_mint_burn_path_no_spot_value_extraction`
- `pair_closed_world_reachable_positive_supply_no_mint_burn_path_no_spot_value_extraction`
- `pair_closed_world_reachable_no_mint_burn_path_never_decreases_k`
- `pair_closed_world_non_burn_step_never_decreases_k`
- `pair_closed_world_k_decrease_requires_burn`
- `pair_closed_world_no_burn_path_never_decreases_k`
- `pair_closed_world_reachable_no_burn_path_never_decreases_k`
- `pair_closed_world_reachable_k_decrease_excludes_burn_free_path`
- `pair_closed_world_no_burn_same_supply_path_no_spot_profit`
- `pair_closed_world_step_k_per_supply_never_decreases`
- `pair_closed_world_path_k_per_supply_never_decreases`
- `pair_closed_world_reachable_path_lp_share_backing_never_decreases`

## Single-caller portfolio safety (spec-coverage.md lines 357-371)

- `pair_wallet_swap_does_not_increase_portfolio_value`
- `pair_wallet_mint_does_not_increase_portfolio_value`
- `pair_wallet_burn_does_not_increase_portfolio_value`
- `pair_wallet_skim_does_not_increase_portfolio_value`
- `pair_wallet_passive_action_does_not_increase_portfolio_value`
- `pair_wallet_single_caller_history_no_portfolio_profit`
- `pair_successful_first_mint_matches_caller_wallet_mint`
- `pair_successful_subsequent_mint_matches_caller_wallet_mint`
- `pair_successful_burn_matches_caller_wallet_burn`
- `pair_successful_swap_matches_caller_wallet_swap`
- `pair_successful_skim_matches_caller_wallet_skim`
- `pair_successful_sync_matches_caller_wallet_sync`

