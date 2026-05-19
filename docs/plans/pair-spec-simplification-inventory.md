# UniswapV2PairSpec Simplification Inventory

Generated mechanically by name-pattern classification with anchor-table override. See `pair-spec-simplification.md` for bucket semantics.

Pre-implementation gate: every Bucket F/G/H spec is cross-checked against `pair-spec-simplification-coverage-anchors.md`; if a candidate move target is an anchor, the classifier upgrades it back to A/B/C/D. UNCLASSIFIED entries default to Bucket A (kept public) until reclassified.

Counts: total 348; A=258, B=18, C=56, D=11, E=0, F=5, G=0, H=0; exempt=22

| Spec | Bucket | Rationale | tama.toml action |
|------|--------|-----------|------------------|
| `pair_decimals_run_success_frames_state` | A | view: anchor (line 44-53) | keep row |
| `pair_totalSupply_run_success_frames_state` | A | view: anchor (line 44-53) | keep row |
| `pair_balanceOf_run_success_frames_state` | A | view: anchor (line 44-53) | keep row |
| `pair_allowance_run_success_frames_state` | A | view: anchor (line 44-53) | keep row |
| `pair_factory_run_success_frames_state` | A | view: anchor (line 44-53) | keep row |
| `pair_token0_run_success_frames_state` | A | view: anchor (line 44-53) | keep row |
| `pair_token1_run_success_frames_state` | A | view: anchor (line 44-53) | keep row |
| `pair_minimumLiquidity_run_success_frames_state` | A | view: anchor (line 44-53) | keep row |
| `pair_getReserves_run_success_frames_state` | A | view: anchor (line 44-53) | keep row |
| `pair_price0CumulativeLast_run_success_frames_state` | A | view: anchor (line 44-53) | keep row |
| `pair_price1CumulativeLast_run_success_frames_state` | A | view: anchor (line 44-53) | keep row |
| `pair_kLast_run_success_frames_state` | A | view: anchor (line 44-53) | keep row |
| `pair_safeTransfer_traces_token_transfer` | A | ERC20 trace anchor | keep row |
| `pair_safeTransfer_event_replay_moves_token_balance` | A | ERC20 trace anchor | keep row |
| `pair_two_safeTransfer_events_replay_move_distinct_token_balances` | A | ERC20 trace anchor | keep row |
| `pair_mint_revert_keeps_token_balances` | A | anchor (default keep) | keep row |
| `pair_burn_revert_keeps_token_balances` | A | anchor (default keep) | keep row |
| `pair_swap_revert_keeps_token_balances` | A | anchor (default keep) | keep row |
| `pair_skim_revert_keeps_token_balances` | A | anchor (default keep) | keep row |
| `pair_sync_revert_keeps_token_balances` | A | anchor (default keep) | keep row |
| `pair_approve_run_keeps_token_balances` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_transfer_run_keeps_token_balances` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_transferFrom_run_keeps_token_balances` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_mint_revert_keeps_pair_state` | A | anchor (default keep) | keep row |
| `pair_burn_revert_keeps_pair_state` | A | anchor (default keep) | keep row |
| `pair_swap_revert_keeps_pair_state` | A | anchor (default keep) | keep row |
| `pair_skim_revert_keeps_pair_state` | A | anchor (default keep) | keep row |
| `pair_sync_revert_keeps_pair_state` | A | anchor (default keep) | keep row |
| `pair_initialize_reverts_for_non_factory` | A | UNCLASSIFIED — keep public (default safe) | none (exempt — no row in baseline) |
| `pair_initialize_reverts_when_already_initialized` | A | UNCLASSIFIED — keep public (default safe) | none (exempt — no row in baseline) |
| `pair_initialize_sets_tokens` | A | anchor (default keep) | keep row |
| `pair_initialize_run_success_sets_tokens` | A | anchor (default keep) | keep row |
| `pair_initialize_run_success_keeps_amm_accounting` | A | anchor (default keep) | keep row |
| `pair_approve_succeeds` | A | anchor (default keep) | none (exempt — no row in baseline) |
| `pair_approve_sets_allowance` | A | anchor (default keep) | none (exempt — no row in baseline) |
| `pair_approve_keeps_balances` | A | anchor (default keep) | none (exempt — no row in baseline) |
| `pair_approve_keeps_total_supply` | A | anchor (default keep) | none (exempt — no row in baseline) |
| `pair_approve_keeps_pool_storage` | A | anchor (default keep) | keep row |
| `pair_approve_emits_approval` | A | anchor (default keep) | keep row |
| `pair_transfer_reverts_when_balance_low` | A | anchor (default keep) | none (exempt — no row in baseline) |
| `pair_transfer_to_self_keeps_balances` | A | anchor (default keep) | keep row |
| `pair_transfer_reverts_when_recipient_balance_would_overflow` | A | anchor (default keep) | keep row |
| `pair_transfer_moves_tokens_between_distinct_accounts` | A | anchor (default keep) | none (exempt — no row in baseline) |
| `pair_transfer_keeps_total_supply` | A | anchor (default keep) | none (exempt — no row in baseline) |
| `pair_transfer_keeps_pool_storage` | A | anchor (default keep) | keep row |
| `pair_transfer_emits_transfer` | A | anchor (default keep) | keep row |
| `pair_transferFrom_reverts_when_allowance_low` | A | anchor (default keep) | none (exempt — no row in baseline) |
| `pair_transferFrom_reverts_when_balance_low` | A | anchor (default keep) | none (exempt — no row in baseline) |
| `pair_transferFrom_reverts_when_recipient_balance_would_overflow` | A | anchor (default keep) | keep row |
| `pair_transferFrom_to_self_keeps_balances` | A | anchor (default keep) | keep row |
| `pair_transferFrom_moves_tokens_between_distinct_accounts` | A | anchor (default keep) | keep row |
| `pair_transferFrom_keeps_total_supply` | A | anchor (default keep) | keep row |
| `pair_transferFrom_keeps_pool_storage` | A | anchor (default keep) | keep row |
| `pair_transferFrom_keeps_infinite_allowance` | A | anchor (default keep) | none (exempt — no row in baseline) |
| `pair_transferFrom_spends_finite_allowance` | A | anchor (default keep) | none (exempt — no row in baseline) |
| `pair_transferFrom_emits_transfer` | A | anchor (default keep) | keep row |
| `pair_mint_reverts_when_locked` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_burn_reverts_when_locked` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_swap_reverts_when_locked` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_skim_reverts_when_locked` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_skim_reverts_when_balance0_below_reserve` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_skim_reverts_when_balance1_below_reserve` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_sync_reverts_when_locked` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_initialize_run_revert_non_factory` | A | anchor (default keep) | keep row |
| `pair_initialize_run_revert_already_initialized` | A | anchor (default keep) | keep row |
| `pair_transfer_run_revert_balance_low` | A | anchor (default keep) | keep row |
| `pair_transfer_run_revert_recipient_balance_overflow` | A | anchor (default keep) | keep row |
| `pair_transferFrom_run_revert_allowance_low` | A | anchor (default keep) | keep row |
| `pair_transferFrom_run_revert_balance_low` | A | anchor (default keep) | keep row |
| `pair_transferFrom_run_revert_recipient_balance_overflow` | A | anchor (default keep) | keep row |
| `pair_mint_run_revert_locked` | A | anchor (default keep) | keep row |
| `pair_mint_run_revert_balance0_overflow` | A | anchor (default keep) | keep row |
| `pair_mint_run_revert_balance1_overflow` | A | anchor (default keep) | keep row |
| `pair_burn_run_revert_locked` | A | anchor (default keep) | keep row |
| `pair_swap_run_revert_locked` | A | anchor (default keep) | keep row |
| `pair_swap_run_revert_zero_output` | A | anchor (default keep) | none (exempt — no row in baseline) |
| `pair_skim_run_revert_locked` | A | anchor (default keep) | keep row |
| `pair_skim_run_revert_balance0_below_reserve` | A | anchor (default keep) | keep row |
| `pair_skim_run_revert_balance1_below_reserve` | A | anchor (default keep) | keep row |
| `pair_skim_run_success_transfers_excess_and_restores_unlocked` | A | anchor (default keep) | keep row |
| `pair_skim_run_success_moves_exact_surplus_in_token_world` | A | anchor (default keep) | keep row |
| `pair_skim_run_success_matches_closed_world_step` | A | anchor (default keep) | keep row |
| `pair_skim_success_run_implies_balances_back_reserves` | A | anchor (default keep) | keep row |
| `pair_skim_success_run_restores_unlocked_from_run` | A | anchor (default keep) | keep row |
| `pair_skim_success_run_matches_closed_world_step_from_run` | A | anchor (default keep) | keep row |
| `pair_skim_success_run_preserves_liquidity_supply_from_run` | A | anchor (default keep) | keep row |
| `pair_skim_success_run_preserves_good_from_run` | A | anchor (default keep) | keep row |
| `pair_skim_success_run_no_caller_token_balance_profit_from_run` | A | anchor (default keep) | keep row |
| `pair_sync_run_revert_locked` | A | anchor (default keep) | keep row |
| `pair_reentrancy_guard_blocks_all_mutating_entrypoints` | A | reentrancy/callback anchor | keep row |
| `pair_flash_callback_runs_while_pair_is_locked` | A | reentrancy/callback anchor | none (exempt — no row in baseline) |
| `pair_flash_callback_reentry_attempts_revert_locked` | A | reentrancy/callback anchor | none (exempt — no row in baseline) |
| `pair_mint_success_run_implies_lock_open` | A | anchor (default keep) | keep row |
| `pair_burn_success_run_implies_lock_open` | A | anchor (default keep) | keep row |
| `pair_swap_success_run_implies_lock_open` | A | anchor (default keep) | keep row |
| `pair_swap_success_run_implies_nonzero_output` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_skim_success_run_implies_lock_open` | A | anchor (default keep) | keep row |
| `pair_sync_run_revert_balance0_overflow` | A | anchor (default keep) | keep row |
| `pair_sync_run_revert_balance1_overflow` | A | anchor (default keep) | keep row |
| `pair_sync_expected_matches_closed_world_step` | F | expected matches step (helper) | delete row |
| `pair_sync_success_run_matches_closed_world_step` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_mint_success_run_implies_balances_fit_uint112` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_sync_success_run_implies_lock_open` | A | anchor (default keep) | keep row |
| `pair_sync_success_run_implies_balances_fit_uint112` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_sync_success_run_matches_closed_world_step_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_sync_success_run_preserves_liquidity_supply_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_sync_success_run_preserves_good_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_sync_success_run_no_caller_token_balance_profit_from_run` | A | anchor (default keep) | keep row |
| `pair_sync_success_run_updates_reserves_to_balances_from_run` | A | anchor (default keep) | keep row |
| `pair_reserve_update_oracle_same_timestamp_keeps_price_cumulatives` | A | anchor (default keep) | keep row |
| `pair_reserve_update_oracle_elapsed_updates_price_cumulatives` | A | anchor (default keep) | keep row |
| `pair_reserve_update_oracle_inactive_elapsed_keeps_price_cumulatives` | A | anchor (default keep) | keep row |
| `pair_sync_oracle_same_timestamp_keeps_price_cumulatives` | A | anchor (default keep) | keep row |
| `pair_sync_oracle_elapsed_updates_price_cumulatives` | A | anchor (default keep) | keep row |
| `pair_sync_oracle_inactive_elapsed_keeps_price_cumulatives` | A | anchor (default keep) | keep row |
| `pair_sync_success_run_uses_oracle_rule` | A | anchor (default keep) | keep row |
| `pair_sync_success_run_uses_oracle_rule_from_run` | A | anchor (default keep) | keep row |
| `pair_closed_world_concrete_reserve_write_uses_oracle_rule` | A | anchor (default keep) | keep row |
| `pair_flash_callback_module_gates_nonempty_data` | A | reentrancy/callback anchor | keep row |
| `pair_flash_callback_module_encodes_canonical_call` | A | reentrancy/callback anchor | keep row |
| `pair_flash_callback_module_bubbles_callback_failure` | A | reentrancy/callback anchor | keep row |
| `pair_mint_first_expected_matches_closed_world_step` | F | expected matches step (helper) | delete row |
| `pair_mint_first_success_run_matches_closed_world_step` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_mint_first_success_run_matches_closed_world_step_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_first_mint_uses_balance_increase_as_deposit` | B | arithmetic input anchor | none (exempt — no row in baseline) |
| `pair_mint_first_success_run_preserves_good_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_mint_first_success_run_establishes_good_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_mint_first_success_run_strictly_increases_supply_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_mint_first_success_run_locks_minimum_liquidity_from_run` | A | anchor (default keep) | keep row |
| `pair_mint_first_success_run_keeps_locked_share_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_first_mint_success_uses_canonical_liquidity_formula` | A | anchor (default keep) | keep row |
| `pair_mint_first_success_run_never_decreases_k_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_mint_first_success_run_updates_reserves_to_balances_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_mint_subsequent_expected_matches_closed_world_step` | F | expected matches step (helper) | delete row |
| `pair_mint_subsequent_success_run_matches_closed_world_step` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_mint_subsequent_success_run_matches_closed_world_step_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_later_mint_uses_balance_increase_as_deposit` | B | arithmetic input anchor | none (exempt — no row in baseline) |
| `pair_mint_subsequent_success_run_preserves_good_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_mint_subsequent_success_run_strictly_increases_supply_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_mint_subsequent_success_run_preserves_locked_liquidity_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_mint_subsequent_success_run_never_decreases_k_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_mint_subsequent_success_run_updates_reserves_to_balances_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_mint_subsequent_success_run_preserves_existing_lp_share` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_burn_expected_matches_closed_world_step` | F | expected matches step (helper) | delete row |
| `pair_burn_success_run_matches_closed_world_step` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_burn_uses_pair_lp_balance_and_total_supply` | B | arithmetic input anchor | none (exempt — no row in baseline) |
| `pair_burn_leaves_remaining_token_balances` | B | arithmetic input anchor | none (exempt — no row in baseline) |
| `pair_burn_success_run_preserves_good_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_burn_success_run_reduces_supply_by_liquidity_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_burn_success_pays_exact_pro_rata_amounts` | A | anchor (default keep) | keep row |
| `pair_burn_success_run_cannot_redeem_locked_liquidity_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_burn_success_run_preserves_positive_balances_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_burn_success_run_updates_reserves_to_balances_from_run` | A | anchor (default keep) | keep row |
| `pair_burn_success_caches_post_redemption_balances` | A | anchor (default keep) | keep row |
| `pair_burn_success_run_preserves_remaining_lp_share` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_swap_expected_matches_closed_world_step` | F | expected matches step (helper) | delete row |
| `pair_swap_success_run_matches_closed_world_step` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_swap_uses_final_balances_to_compute_input` | B | arithmetic input anchor | none (exempt — no row in baseline) |
| `pair_swap_checks_k_against_final_balances` | B | arithmetic input anchor | none (exempt — no row in baseline) |
| `pair_swap_success_run_matches_closed_world_step_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_swap_success_run_preserves_good_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_swap_success_run_preserves_liquidity_supply_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_swap_success_run_never_decreases_k_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_swap_success_run_k_uses_final_balances_from_run` | A | anchor (default keep) | keep row |
| `pair_swap_success_accounts_for_input_and_output` | A | anchor (default keep) | keep row |
| `pair_swap_success_charges_k_against_final_balances` | A | anchor (default keep) | keep row |
| `pair_swap_success_run_updates_reserves_to_balances_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_swap_success_run_no_caller_spot_profit_with_valid_swap` | A | anchor (default keep) | keep row |
| `pair_swap_success_run_no_caller_spot_profit_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_swap_success_run_no_caller_token_balance_profit_from_run` | A | UNCLASSIFIED — keep public (default safe) | keep row |
| `pair_mint_first_success_run_uses_oracle_rule` | A | anchor (default keep) | keep row |
| `pair_mint_first_success_run_uses_oracle_rule_from_run` | A | anchor (default keep) | keep row |
| `pair_mint_subsequent_success_run_uses_oracle_rule` | A | anchor (default keep) | keep row |
| `pair_mint_subsequent_success_run_uses_oracle_rule_from_run` | A | anchor (default keep) | keep row |
| `pair_burn_success_run_uses_oracle_rule` | A | anchor (default keep) | keep row |
| `pair_swap_success_run_uses_oracle_rule` | A | anchor (default keep) | keep row |
| `pair_swap_success_run_uses_oracle_rule_from_run` | A | anchor (default keep) | keep row |
| `pair_closed_world_step_preserves_good` | D | good-state path/step anchor | keep row |
| `pair_closed_world_path_preserves_good` | D | good-state path/step anchor | keep row |
| `pair_closed_world_reachable_good` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_path_good` | C | reachable canonical anchor | keep row |
| `pair_closed_world_path_preserves_reachability` | D | good-state path/step anchor | keep row |
| `pair_closed_world_reachable_supply_good` | C | reachable canonical anchor | keep row |
| `pair_closed_world_path_supply_good` | D | good-state path/step anchor | keep row |
| `pair_closed_world_path_reserves_fit_uint112` | D | good-state path/step anchor | keep row |
| `pair_closed_world_path_locked_liquidity_never_exceeds_supply` | D | good-state path/step anchor | keep row |
| `pair_closed_world_positive_supply_path_remains_positive` | A | anchor (default keep) | keep row |
| `pair_closed_world_reachable_positive_supply_path_remains_positive` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_positive_supply_has_positive_reserves` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_positive_supply_path_has_positive_reserves` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_positive_supply_path_has_positive_token_balances` | C | reachable canonical anchor | keep row |
| `pair_concrete_state_reserves_backed` | A | anchor (default keep) | keep row |
| `pair_concrete_state_uint112_reserves` | A | anchor (default keep) | keep row |
| `pair_closed_world_reachable_reserves_backed` | C | reachable canonical anchor | keep row |
| `pair_closed_world_path_reserves_backed` | D | good-state path/step anchor | keep row |
| `pair_closed_world_reachable_path_reserves_backed` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_path_reserves_fit_uint112` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_reserves_fit_uint112` | C | reachable canonical anchor | keep row |
| `pair_closed_world_nonzero_supply_locks_minimum_liquidity` | A | anchor (default keep) | keep row |
| `pair_closed_world_zero_supply_has_no_locked_liquidity` | A | anchor (default keep) | keep row |
| `pair_closed_world_locked_liquidity_never_exceeds_supply` | A | anchor (default keep) | keep row |
| `pair_closed_world_reachable_path_minimum_liquidity_lock` | C | reachable canonical anchor | keep row |
| `pair_closed_world_step_locked_liquidity_never_decreases` | D | good-state path/step anchor | keep row |
| `pair_closed_world_path_locked_liquidity_never_decreases` | D | good-state path/step anchor | keep row |
| `pair_closed_world_reachable_path_locked_liquidity_never_decreases` | C | reachable canonical anchor | keep row |
| `pair_closed_world_supply_changes_only_on_mint_or_burn` | A | anchor (default keep) | keep row |
| `pair_closed_world_reserve_changes_only_on_reserve_update_actions` | A | anchor (default keep) | keep row |
| `pair_closed_world_no_reserve_update_path_preserves_reserves` | A | anchor (default keep) | keep row |
| `pair_closed_world_no_reserve_update_path_preserves_k_and_spot_value` | A | anchor (default keep) | keep row |
| `pair_closed_world_reachable_reserve_change_requires_reserve_update` | C | reachable canonical anchor | keep row |
| `pair_closed_world_non_liquidity_step_preserves_supply` | A | anchor (default keep) | keep row |
| `pair_closed_world_no_mint_burn_path_preserves_supply` | A | anchor (default keep) | keep row |
| `pair_closed_world_reachable_no_mint_burn_path_preserves_supply` | C | reachable canonical anchor | keep row |
| `pair_closed_world_non_burn_step_never_decreases_supply` | A | anchor (default keep) | keep row |
| `pair_closed_world_no_burn_path_never_decreases_supply` | A | anchor (default keep) | keep row |
| `pair_closed_world_reachable_no_burn_path_never_decreases_supply` | C | reachable canonical anchor | keep row |
| `pair_closed_world_non_mint_step_never_increases_supply` | A | anchor (default keep) | keep row |
| `pair_closed_world_no_mint_path_never_increases_supply` | A | anchor (default keep) | keep row |
| `pair_closed_world_reachable_no_mint_path_never_increases_supply` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_supply_increase_requires_mint` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_supply_decrease_requires_burn` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_supply_change_requires_mint_or_burn` | C | reachable canonical anchor | keep row |
| `pair_closed_world_approve_preserves_pool` | A | anchor (default keep) | keep row |
| `pair_closed_world_transfer_preserves_pool` | A | anchor (default keep) | keep row |
| `pair_closed_world_transferFrom_preserves_pool` | A | anchor (default keep) | keep row |
| `pair_closed_world_share_bookkeeping_path_preserves_pool_state` | A | anchor (default keep) | keep row |
| `pair_closed_world_share_bookkeeping_path_preserves_k_and_value` | A | anchor (default keep) | keep row |
| `pair_closed_world_first_mint_locks_minimum_liquidity` | A | anchor (default keep) | keep row |
| `pair_closed_world_first_mint_keeps_locked_share` | A | anchor (default keep) | keep row |
| `pair_closed_world_subsequent_mint_preserves_locked_liquidity` | A | anchor (default keep) | keep row |
| `pair_closed_world_mint_strictly_increases_supply` | A | anchor (default keep) | keep row |
| `pair_closed_world_mint_adds_exact_deposits_to_reserves` | A | anchor (default keep) | keep row |
| `pair_closed_world_burn_reduces_supply_by_liquidity` | A | anchor (default keep) | keep row |
| `pair_closed_world_burn_removes_exact_redemptions_from_balances` | A | anchor (default keep) | keep row |
| `pair_closed_world_burn_never_increases_supply` | A | anchor (default keep) | keep row |
| `pair_closed_world_burn_cannot_redeem_locked_liquidity` | A | anchor (default keep) | keep row |
| `pair_closed_world_burn_preserves_positive_balances` | A | anchor (default keep) | keep row |
| `pair_closed_world_reachable_positive_supply_burn_preserves_positive_balances` | C | reachable canonical anchor | keep row |
| `pair_closed_world_donate_preserves_reserves_and_supply` | A | anchor (default keep) | keep row |
| `pair_closed_world_donate_preserves_k` | A | anchor (default keep) | keep row |
| `pair_closed_world_donation_increases_surplus_exactly` | A | anchor (default keep) | keep row |
| `pair_closed_world_non_donation_step_never_increases_surplus` | A | anchor (default keep) | keep row |
| `pair_closed_world_no_donation_path_never_increases_surplus` | A | anchor (default keep) | keep row |
| `pair_closed_world_reachable_no_donation_path_never_increases_surplus` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_surplus_increase_requires_donation` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_no_donation_path_surplus_value_never_increases` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_zero_surplus_no_donation_path_preserves_zero_surplus` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_zero_surplus_no_donation_path_ends_balanced` | C | reachable canonical anchor | keep row |
| `pair_closed_world_mint_updates_reserves_to_balances` | A | anchor (default keep) | keep row |
| `pair_closed_world_mint_never_decreases_k` | A | anchor (default keep) | keep row |
| `pair_closed_world_mint_preserves_good` | A | anchor (default keep) | keep row |
| `pair_closed_world_mint_liquidity_ratio` | A | anchor (default keep) | keep row |
| `pair_closed_world_mint_does_not_dilute_existing_lp_share` | A | anchor (default keep) | keep row |
| `pair_closed_world_burn_updates_reserves_to_balances` | A | anchor (default keep) | keep row |
| `pair_closed_world_burn_preserves_good` | A | anchor (default keep) | keep row |
| `pair_closed_world_burn_liquidity_ratio` | A | anchor (default keep) | keep row |
| `pair_closed_world_burn_does_not_dilute_remaining_lp_share` | A | anchor (default keep) | keep row |
| `pair_closed_world_swap_updates_reserves_to_balances` | A | anchor (default keep) | keep row |
| `pair_closed_world_swap_respects_fee_adjusted_k` | A | anchor (default keep) | keep row |
| `pair_closed_world_fee_adjusted_swap_implies_raw_k` | A | anchor (default keep) | keep row |
| `pair_closed_world_swap_preserves_good` | A | anchor (default keep) | keep row |
| `pair_closed_world_swap_never_decreases_k` | A | anchor (default keep) | keep row |
| `pair_closed_world_swap_has_input_and_output` | A | anchor (default keep) | keep row |
| `pair_closed_world_swap_final_balances_account_for_input_and_output` | A | anchor (default keep) | keep row |
| `pair_closed_world_swap_k_uses_final_balances` | A | anchor (default keep) | keep row |
| `pair_closed_world_swap_outputs_below_reserves` | A | anchor (default keep) | keep row |
| `pair_closed_world_swap_preserves_liquidity_supply` | A | anchor (default keep) | keep row |
| `pair_closed_world_swap_no_spot_value_extraction` | A | anchor (default keep) | keep row |
| `pair_closed_world_reachable_positive_supply_swap_no_spot_value_extraction` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_positive_supply_swap_no_caller_spot_profit` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_zero_surplus_swap_no_caller_token_balance_profit` | C | reachable canonical anchor | keep row |
| `pair_closed_world_step_k_per_supply_never_decreases` | D | good-state path/step anchor | keep row |
| `pair_closed_world_path_k_per_supply_never_decreases` | D | good-state path/step anchor | keep row |
| `pair_closed_world_reachable_path_lp_share_backing_never_decreases` | C | reachable canonical anchor | keep row |
| `pair_wallet_swap_does_not_increase_portfolio_value` | B | caller wallet anchor | keep row |
| `pair_wallet_mint_does_not_increase_portfolio_value` | B | caller wallet anchor | keep row |
| `pair_wallet_burn_does_not_increase_portfolio_value` | B | caller wallet anchor | keep row |
| `pair_wallet_skim_does_not_increase_portfolio_value` | B | caller wallet anchor | keep row |
| `pair_wallet_passive_action_does_not_increase_portfolio_value` | B | caller wallet anchor | keep row |
| `pair_wallet_single_caller_history_no_portfolio_profit` | B | caller wallet anchor | keep row |
| `pair_successful_first_mint_matches_caller_wallet_mint` | B | caller wallet anchor | keep row |
| `pair_successful_subsequent_mint_matches_caller_wallet_mint` | B | caller wallet anchor | keep row |
| `pair_successful_burn_matches_caller_wallet_burn` | B | caller wallet anchor | keep row |
| `pair_successful_swap_matches_caller_wallet_swap` | B | caller wallet anchor | keep row |
| `pair_successful_skim_matches_caller_wallet_skim` | B | caller wallet anchor | keep row |
| `pair_successful_sync_matches_caller_wallet_sync` | B | caller wallet anchor | keep row |
| `pair_closed_world_same_supply_path_never_decreases_k` | A | anchor (default keep) | keep row |
| `pair_closed_world_same_supply_path_no_spot_profit` | A | anchor (default keep) | keep row |
| `pair_closed_world_positive_supply_same_supply_path_no_spot_profit` | A | anchor (default keep) | keep row |
| `pair_closed_world_reachable_same_supply_path_never_decreases_k` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_same_supply_path_no_spot_profit` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_same_supply_path_pool_value_never_decreases` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_same_supply_path_no_spot_value_extraction` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_same_supply_path_no_token1_denominated_profit` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_same_supply_path_token_balance_loss_bounded_by_initial_surplus` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_same_supply_path_caller_token_balance_profit_bounded_by_initial_surplus` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_zero_surplus_same_supply_path_no_token_balance_value_extraction` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_zero_surplus_same_supply_path_no_caller_token_balance_profit` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_same_supply_path_no_caller_spot_profit` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_positive_supply_same_supply_path_no_spot_value_extraction` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_balanced_same_supply_path_no_token_balance_value_extraction` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_balanced_no_mint_burn_path_no_token_balance_value_extraction` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_no_mint_burn_path_token_balance_loss_bounded_by_initial_surplus` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_no_mint_burn_path_caller_token_balance_profit_bounded_by_initial_surplus` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_zero_surplus_no_mint_burn_path_no_token_balance_value_extraction` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_zero_surplus_no_mint_burn_path_no_caller_token_balance_profit` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_token_balance_value_extraction` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_caller_token_balance_profit` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_no_mint_burn_path_no_caller_spot_profit` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_no_mint_burn_path_no_spot_value_extraction` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_positive_supply_no_mint_burn_path_no_spot_value_extraction` | C | phase-6 reachable canonical anchor | keep row |
| `pair_closed_world_reachable_no_mint_burn_path_never_decreases_k` | C | reachable canonical anchor | keep row |
| `pair_closed_world_non_burn_step_never_decreases_k` | A | anchor (default keep) | keep row |
| `pair_closed_world_k_decrease_requires_burn` | A | anchor (default keep) | keep row |
| `pair_closed_world_no_burn_path_never_decreases_k` | A | anchor (default keep) | keep row |
| `pair_closed_world_reachable_no_burn_path_never_decreases_k` | C | reachable canonical anchor | keep row |
| `pair_closed_world_reachable_k_decrease_excludes_burn_free_path` | C | reachable canonical anchor | keep row |
| `pair_closed_world_no_burn_same_supply_path_no_spot_profit` | A | anchor (default keep) | keep row |
| `pair_closed_world_skim_removes_surplus` | A | anchor (default keep) | keep row |
| `pair_closed_world_skim_eliminates_surplus` | A | anchor (default keep) | keep row |
| `pair_closed_world_skim_removes_exact_surplus_value` | A | anchor (default keep) | keep row |
| `pair_closed_world_skim_token_balance_value_never_increases` | A | anchor (default keep) | keep row |
| `pair_closed_world_skim_token_balance_value_never_increases_at_spot` | A | anchor (default keep) | keep row |
| `pair_closed_world_skim_preserves_balanced_pool` | A | anchor (default keep) | keep row |
| `pair_closed_world_skim_preserves_good` | A | anchor (default keep) | keep row |
| `pair_closed_world_skim_preserves_liquidity_supply` | A | anchor (default keep) | keep row |
| `pair_closed_world_skim_preserves_k` | A | anchor (default keep) | keep row |
| `pair_closed_world_sync_sets_reserves_to_balances` | A | anchor (default keep) | keep row |
| `pair_closed_world_sync_preserves_token_balances` | A | anchor (default keep) | keep row |
| `pair_closed_world_sync_preserves_token_balance_value` | A | anchor (default keep) | keep row |
| `pair_closed_world_reserve_write_sets_reserves_to_balances` | A | anchor (default keep) | keep row |
| `pair_closed_world_skim_or_sync_token_balance_value_never_increases` | A | anchor (default keep) | keep row |
| `pair_closed_world_skim_or_sync_token_balance_value_never_increases_at_spot` | A | anchor (default keep) | keep row |
| `pair_closed_world_sync_eliminates_surplus` | A | anchor (default keep) | keep row |
| `pair_closed_world_sync_preserves_good` | A | anchor (default keep) | keep row |
| `pair_closed_world_sync_preserves_liquidity_supply` | A | anchor (default keep) | keep row |
| `pair_closed_world_sync_never_decreases_k` | A | anchor (default keep) | keep row |
| `pair_closed_world_sync_preserves_k_without_surplus` | A | anchor (default keep) | keep row |
| `pair_closed_world_sync_preserves_balanced_pool` | A | anchor (default keep) | keep row |
| `pair_closed_world_balanced_skim_or_sync_preserves_pool` | A | anchor (default keep) | keep row |
| `pair_closed_world_balanced_skim_sync_path_preserves_pool` | A | anchor (default keep) | keep row |
| `pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_pool` | A | anchor (default keep) | keep row |
| `pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_k` | A | anchor (default keep) | keep row |
| `pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_zero_surplus` | A | anchor (default keep) | keep row |
| `pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_token_balance_value` | A | anchor (default keep) | keep row |
| `pair_closed_world_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases` | A | anchor (default keep) | keep row |
| `pair_closed_world_reachable_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases` | C | reachable canonical anchor | keep row |
| `pair_closed_world_sync_k_increase_requires_surplus` | A | anchor (default keep) | keep row |
