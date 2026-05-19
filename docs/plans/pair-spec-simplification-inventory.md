# UniswapV2PairSpec Simplification Inventory (aggressive)

Regenerated after `docs/spec-coverage.md` was deleted (Phase 7). The previous anchor table was the binding constraint that blocked most consolidation; with the markdown gone, the spec file itself is SSoT and classification is governed by structural reasoning, not by external prose.

Rules:

- A: revert frames, exact guard reverts, ERC20 trace, reentrancy/callback safety, view `_run_success_frames_state`, LP bookkeeping success specs, initialize.
- B: per-call canonical accounting connectors — the `_from_run` form per mutating call (or burn's `_success_run_` shape), the strongest reader-facing `_preserves_*_from_run` corollaries, the per-call arithmetic input specs, oracle reserve-update rules, wallet portfolio links, swap/burn explicit accounting.
- C: strongest reachable canonical forms; phase-6 no-extraction anchors; reachable invariants over finite histories.
- D: good-state path forms that compose into reachable forms (the inductive-step layer of the assurance argument).
- H: everything else closed_world / non-public — `_step_` lemmas, non-canonical `_path_` forms, `_expected_matches_closed_world_step`, non-from-run lifts, older variants superseded by `_positive_supply_` strongest forms. Moved into `UniswapV2PairProof.lean` as `private def` + `private theorem`.

Counts: total 346; A=94, B=152, C=54, D=6, E=0, F=0, G=0, H=40; exempt=22

| Spec | Bucket | Rationale | tama.toml action |
|------|--------|-----------|------------------|
| `pair_allowance_run_success_frames_state` | A | view: run-success frames state | keep row |
| `pair_approve_emits_approval` | A | LP bookkeeping public spec | keep row |
| `pair_approve_keeps_balances` | A | LP bookkeeping public spec | none (exempt — no row in baseline) |
| `pair_approve_keeps_pool_storage` | A | LP bookkeeping public spec | keep row |
| `pair_approve_keeps_total_supply` | A | LP bookkeeping public spec | none (exempt — no row in baseline) |
| `pair_approve_run_keeps_token_balances` | A | frame (token balances) | keep row |
| `pair_approve_sets_allowance` | A | LP bookkeeping public spec | none (exempt — no row in baseline) |
| `pair_approve_succeeds` | A | LP bookkeeping public spec | none (exempt — no row in baseline) |
| `pair_balanceOf_run_success_frames_state` | A | view: run-success frames state | keep row |
| `pair_burn_expected_matches_closed_world_step` | H | expected matches step (helper) | delete row |
| `pair_burn_leaves_remaining_token_balances` | B | per-call canonical anchor | none (exempt — no row in baseline) |
| `pair_burn_revert_keeps_pair_state` | A | revert frame | keep row |
| `pair_burn_revert_keeps_token_balances` | A | revert frame | keep row |
| `pair_burn_reverts_when_locked` | A | guard revert | keep row |
| `pair_burn_run_revert_locked` | A | exact guard run revert | keep row |
| `pair_burn_success_caches_post_redemption_balances` | B | per-call canonical anchor | keep row |
| `pair_burn_success_pays_exact_pro_rata_amounts` | B | per-call canonical anchor | keep row |
| `pair_burn_success_run_cannot_redeem_locked_liquidity_from_run` | B | per-call canonical anchor | keep row |
| `pair_burn_success_run_implies_lock_open` | B | per-call canonical anchor | keep row |
| `pair_burn_success_run_matches_closed_world_step` | B | per-call canonical anchor | keep row |
| `pair_burn_success_run_preserves_good_from_run` | B | per-call canonical anchor | keep row |
| `pair_burn_success_run_preserves_positive_balances_from_run` | B | per-call canonical anchor | keep row |
| `pair_burn_success_run_preserves_remaining_lp_share` | B | per-call canonical anchor | keep row |
| `pair_burn_success_run_reduces_supply_by_liquidity_from_run` | B | per-call canonical anchor | keep row |
| `pair_burn_success_run_updates_reserves_to_balances_from_run` | B | per-call canonical anchor | keep row |
| `pair_burn_success_run_uses_oracle_rule` | A | UNCLASSIFIED — keep (default) | keep row |
| `pair_burn_uses_pair_lp_balance_and_total_supply` | B | per-call canonical anchor | none (exempt — no row in baseline) |
| `pair_closed_world_approve_preserves_pool` | B | per-call canonical anchor | keep row |
| `pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_k` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_pool` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_token_balance_value` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_zero_surplus` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_balanced_skim_or_sync_preserves_pool` | B | per-call canonical anchor | keep row |
| `pair_closed_world_balanced_skim_sync_path_preserves_pool` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_burn_cannot_redeem_locked_liquidity` | B | per-call canonical anchor | keep row |
| `pair_closed_world_burn_does_not_dilute_remaining_lp_share` | B | per-call canonical anchor | keep row |
| `pair_closed_world_burn_liquidity_ratio` | B | per-call canonical anchor | keep row |
| `pair_closed_world_burn_never_increases_supply` | B | per-call canonical anchor | keep row |
| `pair_closed_world_burn_preserves_good` | B | per-call canonical anchor | keep row |
| `pair_closed_world_burn_preserves_positive_balances` | B | per-call canonical anchor | keep row |
| `pair_closed_world_burn_reduces_supply_by_liquidity` | B | per-call canonical anchor | keep row |
| `pair_closed_world_burn_removes_exact_redemptions_from_balances` | B | per-call canonical anchor | keep row |
| `pair_closed_world_burn_updates_reserves_to_balances` | B | per-call canonical anchor | keep row |
| `pair_closed_world_concrete_reserve_write_uses_oracle_rule` | B | per-call canonical anchor | keep row |
| `pair_closed_world_donate_preserves_k` | B | per-call canonical anchor | keep row |
| `pair_closed_world_donate_preserves_reserves_and_supply` | B | per-call canonical anchor | keep row |
| `pair_closed_world_donation_increases_surplus_exactly` | B | per-call canonical anchor | keep row |
| `pair_closed_world_fee_adjusted_swap_implies_raw_k` | B | per-call canonical anchor | keep row |
| `pair_closed_world_first_mint_keeps_locked_share` | B | per-call canonical anchor | keep row |
| `pair_closed_world_first_mint_locks_minimum_liquidity` | B | per-call canonical anchor | keep row |
| `pair_closed_world_k_decrease_requires_burn` | B | per-call canonical anchor | keep row |
| `pair_closed_world_locked_liquidity_never_exceeds_supply` | B | per-call canonical anchor | keep row |
| `pair_closed_world_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_mint_adds_exact_deposits_to_reserves` | B | per-call canonical anchor | keep row |
| `pair_closed_world_mint_does_not_dilute_existing_lp_share` | B | per-call canonical anchor | keep row |
| `pair_closed_world_mint_liquidity_ratio` | B | per-call canonical anchor | keep row |
| `pair_closed_world_mint_never_decreases_k` | B | per-call canonical anchor | keep row |
| `pair_closed_world_mint_preserves_good` | B | per-call canonical anchor | keep row |
| `pair_closed_world_mint_strictly_increases_supply` | B | per-call canonical anchor | keep row |
| `pair_closed_world_mint_updates_reserves_to_balances` | B | per-call canonical anchor | keep row |
| `pair_closed_world_no_burn_path_never_decreases_k` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_no_burn_path_never_decreases_supply` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_no_burn_same_supply_path_no_spot_profit` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_no_donation_path_never_increases_surplus` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_no_mint_burn_path_preserves_supply` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_no_mint_path_never_increases_supply` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_no_reserve_update_path_preserves_k_and_spot_value` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_no_reserve_update_path_preserves_reserves` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_non_burn_step_never_decreases_k` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_non_burn_step_never_decreases_supply` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_non_donation_step_never_increases_surplus` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_non_liquidity_step_preserves_supply` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_non_mint_step_never_increases_supply` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_nonzero_supply_locks_minimum_liquidity` | B | per-call canonical anchor | keep row |
| `pair_closed_world_path_k_per_supply_never_decreases` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_path_locked_liquidity_never_decreases` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_path_locked_liquidity_never_exceeds_supply` | D | good-state path form | keep row |
| `pair_closed_world_path_preserves_good` | D | good-state path form | keep row |
| `pair_closed_world_path_preserves_reachability` | D | good-state path form | keep row |
| `pair_closed_world_path_reserves_backed` | D | good-state path form | keep row |
| `pair_closed_world_path_reserves_fit_uint112` | D | good-state path form | keep row |
| `pair_closed_world_path_supply_good` | D | good-state path form | keep row |
| `pair_closed_world_positive_supply_path_remains_positive` | B | per-call canonical anchor | keep row |
| `pair_closed_world_positive_supply_same_supply_path_no_spot_profit` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_reachable_balanced_no_mint_burn_path_no_token_balance_value_extraction` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_balanced_same_supply_path_no_token_balance_value_extraction` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_good` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_k_decrease_excludes_burn_free_path` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_no_burn_path_never_decreases_k` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_no_burn_path_never_decreases_supply` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_no_donation_path_never_increases_surplus` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_no_donation_path_surplus_value_never_increases` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_no_mint_burn_path_caller_token_balance_profit_bounded_by_initial_surplus` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_no_mint_burn_path_never_decreases_k` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_no_mint_burn_path_no_caller_spot_profit` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_no_mint_burn_path_no_spot_value_extraction` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_reachable_no_mint_burn_path_preserves_supply` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_no_mint_burn_path_token_balance_loss_bounded_by_initial_surplus` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_no_mint_path_never_increases_supply` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_path_good` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_path_locked_liquidity_never_decreases` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_path_lp_share_backing_never_decreases` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_path_minimum_liquidity_lock` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_path_reserves_backed` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_path_reserves_fit_uint112` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_positive_supply_burn_preserves_positive_balances` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_positive_supply_has_positive_reserves` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_positive_supply_no_mint_burn_path_no_spot_value_extraction` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_positive_supply_path_has_positive_reserves` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_positive_supply_path_has_positive_token_balances` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_positive_supply_path_remains_positive` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_positive_supply_same_supply_path_no_spot_value_extraction` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_positive_supply_swap_no_caller_spot_profit` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_positive_supply_swap_no_spot_value_extraction` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_reserve_change_requires_reserve_update` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_reserves_backed` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_reserves_fit_uint112` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_same_supply_path_caller_token_balance_profit_bounded_by_initial_surplus` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_same_supply_path_never_decreases_k` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_reachable_same_supply_path_no_caller_spot_profit` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_same_supply_path_no_spot_profit` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_reachable_same_supply_path_no_spot_value_extraction` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_reachable_same_supply_path_no_token1_denominated_profit` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_same_supply_path_pool_value_never_decreases` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_same_supply_path_token_balance_loss_bounded_by_initial_surplus` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_supply_change_requires_mint_or_burn` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_supply_decrease_requires_burn` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_supply_good` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_supply_increase_requires_mint` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_surplus_increase_requires_donation` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_caller_token_balance_profit` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_token_balance_value_extraction` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_zero_surplus_no_donation_path_ends_balanced` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_zero_surplus_no_donation_path_preserves_zero_surplus` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_zero_surplus_no_mint_burn_path_no_caller_token_balance_profit` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_zero_surplus_no_mint_burn_path_no_token_balance_value_extraction` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_zero_surplus_same_supply_path_no_caller_token_balance_profit` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_zero_surplus_same_supply_path_no_token_balance_value_extraction` | C | reachable canonical | keep row |
| `pair_closed_world_reachable_zero_surplus_swap_no_caller_token_balance_profit` | C | reachable canonical | keep row |
| `pair_closed_world_reserve_changes_only_on_reserve_update_actions` | B | per-call canonical anchor | keep row |
| `pair_closed_world_reserve_write_sets_reserves_to_balances` | B | per-call canonical anchor | keep row |
| `pair_closed_world_same_supply_path_never_decreases_k` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_same_supply_path_no_spot_profit` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_share_bookkeeping_path_preserves_k_and_value` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_share_bookkeeping_path_preserves_pool_state` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_skim_eliminates_surplus` | B | per-call canonical anchor | keep row |
| `pair_closed_world_skim_or_sync_token_balance_value_never_increases` | B | per-call canonical anchor | keep row |
| `pair_closed_world_skim_or_sync_token_balance_value_never_increases_at_spot` | B | per-call canonical anchor | keep row |
| `pair_closed_world_skim_preserves_balanced_pool` | B | per-call canonical anchor | keep row |
| `pair_closed_world_skim_preserves_good` | B | per-call canonical anchor | keep row |
| `pair_closed_world_skim_preserves_k` | B | per-call canonical anchor | keep row |
| `pair_closed_world_skim_preserves_liquidity_supply` | B | per-call canonical anchor | keep row |
| `pair_closed_world_skim_removes_exact_surplus_value` | B | per-call canonical anchor | keep row |
| `pair_closed_world_skim_removes_surplus` | B | per-call canonical anchor | keep row |
| `pair_closed_world_skim_token_balance_value_never_increases` | B | per-call canonical anchor | keep row |
| `pair_closed_world_skim_token_balance_value_never_increases_at_spot` | B | per-call canonical anchor | keep row |
| `pair_closed_world_step_k_per_supply_never_decreases` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_step_locked_liquidity_never_decreases` | B | per-call canonical anchor | keep row |
| `pair_closed_world_step_preserves_good` | H | closed-world helper (move private) | delete row |
| `pair_closed_world_subsequent_mint_preserves_locked_liquidity` | B | per-call canonical anchor | keep row |
| `pair_closed_world_supply_changes_only_on_mint_or_burn` | B | per-call canonical anchor | keep row |
| `pair_closed_world_swap_final_balances_account_for_input_and_output` | B | per-call canonical anchor | keep row |
| `pair_closed_world_swap_has_input_and_output` | B | per-call canonical anchor | keep row |
| `pair_closed_world_swap_k_uses_final_balances` | B | per-call canonical anchor | keep row |
| `pair_closed_world_swap_never_decreases_k` | B | per-call canonical anchor | keep row |
| `pair_closed_world_swap_no_spot_value_extraction` | B | per-call canonical anchor | keep row |
| `pair_closed_world_swap_outputs_below_reserves` | B | per-call canonical anchor | keep row |
| `pair_closed_world_swap_preserves_good` | B | per-call canonical anchor | keep row |
| `pair_closed_world_swap_preserves_liquidity_supply` | B | per-call canonical anchor | keep row |
| `pair_closed_world_swap_respects_fee_adjusted_k` | B | per-call canonical anchor | keep row |
| `pair_closed_world_swap_updates_reserves_to_balances` | B | per-call canonical anchor | keep row |
| `pair_closed_world_sync_eliminates_surplus` | B | per-call canonical anchor | keep row |
| `pair_closed_world_sync_k_increase_requires_surplus` | B | per-call canonical anchor | keep row |
| `pair_closed_world_sync_never_decreases_k` | B | per-call canonical anchor | keep row |
| `pair_closed_world_sync_preserves_balanced_pool` | B | per-call canonical anchor | keep row |
| `pair_closed_world_sync_preserves_good` | B | per-call canonical anchor | keep row |
| `pair_closed_world_sync_preserves_k_without_surplus` | B | per-call canonical anchor | keep row |
| `pair_closed_world_sync_preserves_liquidity_supply` | B | per-call canonical anchor | keep row |
| `pair_closed_world_sync_preserves_token_balance_value` | B | per-call canonical anchor | keep row |
| `pair_closed_world_sync_preserves_token_balances` | B | per-call canonical anchor | keep row |
| `pair_closed_world_sync_sets_reserves_to_balances` | B | per-call canonical anchor | keep row |
| `pair_closed_world_transferFrom_preserves_pool` | B | per-call canonical anchor | keep row |
| `pair_closed_world_transfer_preserves_pool` | B | per-call canonical anchor | keep row |
| `pair_closed_world_zero_supply_has_no_locked_liquidity` | B | per-call canonical anchor | keep row |
| `pair_concrete_state_reserves_backed` | C | reachable canonical | keep row |
| `pair_concrete_state_uint112_reserves` | C | reachable canonical | keep row |
| `pair_decimals_run_success_frames_state` | A | view: run-success frames state | keep row |
| `pair_factory_run_success_frames_state` | A | view: run-success frames state | keep row |
| `pair_first_mint_success_uses_canonical_liquidity_formula` | B | per-call canonical anchor | keep row |
| `pair_first_mint_uses_balance_increase_as_deposit` | B | per-call canonical anchor | none (exempt — no row in baseline) |
| `pair_flash_callback_module_bubbles_callback_failure` | A | reentrancy/flash callback | keep row |
| `pair_flash_callback_module_encodes_canonical_call` | A | reentrancy/flash callback | keep row |
| `pair_flash_callback_module_gates_nonempty_data` | A | reentrancy/flash callback | keep row |
| `pair_flash_callback_reentry_attempts_revert_locked` | A | reentrancy/flash callback | none (exempt — no row in baseline) |
| `pair_flash_callback_runs_while_pair_is_locked` | A | reentrancy/flash callback | none (exempt — no row in baseline) |
| `pair_getReserves_run_success_frames_state` | A | view: run-success frames state | keep row |
| `pair_initialize_reverts_for_non_factory` | A | initialize public spec | none (exempt — no row in baseline) |
| `pair_initialize_reverts_when_already_initialized` | A | initialize public spec | none (exempt — no row in baseline) |
| `pair_initialize_run_revert_already_initialized` | A | exact guard run revert | keep row |
| `pair_initialize_run_revert_non_factory` | A | exact guard run revert | keep row |
| `pair_initialize_run_success_keeps_amm_accounting` | A | initialize public spec | keep row |
| `pair_initialize_run_success_sets_tokens` | A | initialize public spec | keep row |
| `pair_initialize_sets_tokens` | A | initialize public spec | keep row |
| `pair_kLast_run_success_frames_state` | A | view: run-success frames state | keep row |
| `pair_later_mint_uses_balance_increase_as_deposit` | B | per-call canonical anchor | none (exempt — no row in baseline) |
| `pair_minimumLiquidity_run_success_frames_state` | A | view: run-success frames state | keep row |
| `pair_mint_first_success_run_establishes_good_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_first_success_run_keeps_locked_share_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_first_success_run_locks_minimum_liquidity_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_first_success_run_matches_closed_world_step` | H | non-from-run matches-step lift (helper) | delete row |
| `pair_mint_first_success_run_matches_closed_world_step_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_first_success_run_never_decreases_k_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_first_success_run_preserves_good_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_first_success_run_strictly_increases_supply_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_first_success_run_updates_reserves_to_balances_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_first_success_run_uses_oracle_rule` | A | UNCLASSIFIED — keep (default) | keep row |
| `pair_mint_first_success_run_uses_oracle_rule_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_revert_keeps_pair_state` | A | revert frame | keep row |
| `pair_mint_revert_keeps_token_balances` | A | revert frame | keep row |
| `pair_mint_reverts_when_locked` | A | guard revert | keep row |
| `pair_mint_run_revert_balance0_overflow` | A | exact guard run revert | keep row |
| `pair_mint_run_revert_balance1_overflow` | A | exact guard run revert | keep row |
| `pair_mint_run_revert_locked` | A | exact guard run revert | keep row |
| `pair_mint_subsequent_expected_matches_closed_world_step` | H | expected matches step (helper) | delete row |
| `pair_mint_subsequent_success_run_matches_closed_world_step` | H | non-from-run matches-step lift (helper) | delete row |
| `pair_mint_subsequent_success_run_matches_closed_world_step_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_subsequent_success_run_never_decreases_k_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_subsequent_success_run_preserves_existing_lp_share` | B | per-call canonical anchor | keep row |
| `pair_mint_subsequent_success_run_preserves_good_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_subsequent_success_run_preserves_locked_liquidity_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_subsequent_success_run_strictly_increases_supply_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_subsequent_success_run_updates_reserves_to_balances_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_subsequent_success_run_uses_oracle_rule` | A | UNCLASSIFIED — keep (default) | keep row |
| `pair_mint_subsequent_success_run_uses_oracle_rule_from_run` | B | per-call canonical anchor | keep row |
| `pair_mint_success_run_implies_balances_fit_uint112` | B | per-call canonical anchor | keep row |
| `pair_mint_success_run_implies_lock_open` | B | per-call canonical anchor | keep row |
| `pair_price0CumulativeLast_run_success_frames_state` | A | view: run-success frames state | keep row |
| `pair_price1CumulativeLast_run_success_frames_state` | A | view: run-success frames state | keep row |
| `pair_reentrancy_guard_blocks_all_mutating_entrypoints` | A | reentrancy/flash callback | keep row |
| `pair_reserve_update_oracle_elapsed_updates_price_cumulatives` | B | per-call canonical anchor | keep row |
| `pair_reserve_update_oracle_inactive_elapsed_keeps_price_cumulatives` | B | per-call canonical anchor | keep row |
| `pair_reserve_update_oracle_same_timestamp_keeps_price_cumulatives` | B | per-call canonical anchor | keep row |
| `pair_safeTransfer_event_replay_moves_token_balance` | A | ERC20 trace (allowlist) | keep row |
| `pair_safeTransfer_traces_token_transfer` | A | ERC20 trace (allowlist) | keep row |
| `pair_skim_revert_keeps_pair_state` | A | revert frame | keep row |
| `pair_skim_revert_keeps_token_balances` | A | revert frame | keep row |
| `pair_skim_reverts_when_balance0_below_reserve` | A | guard revert | keep row |
| `pair_skim_reverts_when_balance1_below_reserve` | A | guard revert | keep row |
| `pair_skim_reverts_when_locked` | A | guard revert | keep row |
| `pair_skim_run_revert_balance0_below_reserve` | A | exact guard run revert | keep row |
| `pair_skim_run_revert_balance1_below_reserve` | A | exact guard run revert | keep row |
| `pair_skim_run_revert_locked` | A | exact guard run revert | keep row |
| `pair_skim_run_success_matches_closed_world_step` | H | non-from-run matches-step lift (helper) | delete row |
| `pair_skim_run_success_moves_exact_surplus_in_token_world` | B | per-call canonical anchor | keep row |
| `pair_skim_run_success_transfers_excess_and_restores_unlocked` | B | per-call canonical anchor | keep row |
| `pair_skim_success_run_implies_balances_back_reserves` | B | per-call canonical anchor | keep row |
| `pair_skim_success_run_implies_lock_open` | B | per-call canonical anchor | keep row |
| `pair_skim_success_run_matches_closed_world_step_from_run` | B | per-call canonical anchor | keep row |
| `pair_skim_success_run_no_caller_token_balance_profit_from_run` | B | per-call canonical anchor | keep row |
| `pair_skim_success_run_preserves_good_from_run` | B | per-call canonical anchor | keep row |
| `pair_skim_success_run_preserves_liquidity_supply_from_run` | B | per-call canonical anchor | keep row |
| `pair_skim_success_run_restores_unlocked_from_run` | B | per-call canonical anchor | keep row |
| `pair_successful_burn_matches_caller_wallet_burn` | B | per-call canonical anchor | keep row |
| `pair_successful_first_mint_matches_caller_wallet_mint` | B | per-call canonical anchor | keep row |
| `pair_successful_skim_matches_caller_wallet_skim` | B | per-call canonical anchor | keep row |
| `pair_successful_subsequent_mint_matches_caller_wallet_mint` | B | per-call canonical anchor | keep row |
| `pair_successful_swap_matches_caller_wallet_swap` | B | per-call canonical anchor | keep row |
| `pair_successful_sync_matches_caller_wallet_sync` | B | per-call canonical anchor | keep row |
| `pair_swap_checks_k_against_final_balances` | B | per-call canonical anchor | none (exempt — no row in baseline) |
| `pair_swap_expected_matches_closed_world_step` | H | expected matches step (helper) | delete row |
| `pair_swap_revert_keeps_pair_state` | A | revert frame | keep row |
| `pair_swap_revert_keeps_token_balances` | A | revert frame | keep row |
| `pair_swap_reverts_when_locked` | A | guard revert | keep row |
| `pair_swap_run_revert_locked` | A | exact guard run revert | keep row |
| `pair_swap_run_revert_zero_output` | A | exact guard run revert | none (exempt — no row in baseline) |
| `pair_swap_success_accounts_for_input_and_output` | B | per-call canonical anchor | keep row |
| `pair_swap_success_charges_k_against_final_balances` | B | per-call canonical anchor | keep row |
| `pair_swap_success_run_implies_lock_open` | B | per-call canonical anchor | keep row |
| `pair_swap_success_run_implies_nonzero_output` | B | per-call canonical anchor | keep row |
| `pair_swap_success_run_k_uses_final_balances_from_run` | B | per-call canonical anchor | keep row |
| `pair_swap_success_run_matches_closed_world_step` | H | non-from-run matches-step lift (helper) | delete row |
| `pair_swap_success_run_matches_closed_world_step_from_run` | B | per-call canonical anchor | keep row |
| `pair_swap_success_run_never_decreases_k_from_run` | B | per-call canonical anchor | keep row |
| `pair_swap_success_run_no_caller_spot_profit_from_run` | A | UNCLASSIFIED — keep (default) | keep row |
| `pair_swap_success_run_no_caller_spot_profit_with_valid_swap` | B | per-call canonical anchor | keep row |
| `pair_swap_success_run_no_caller_token_balance_profit_from_run` | B | per-call canonical anchor | keep row |
| `pair_swap_success_run_preserves_good_from_run` | B | per-call canonical anchor | keep row |
| `pair_swap_success_run_preserves_liquidity_supply_from_run` | B | per-call canonical anchor | keep row |
| `pair_swap_success_run_updates_reserves_to_balances_from_run` | B | per-call canonical anchor | keep row |
| `pair_swap_success_run_uses_oracle_rule` | A | UNCLASSIFIED — keep (default) | keep row |
| `pair_swap_success_run_uses_oracle_rule_from_run` | B | per-call canonical anchor | keep row |
| `pair_swap_uses_final_balances_to_compute_input` | B | per-call canonical anchor | none (exempt — no row in baseline) |
| `pair_sync_oracle_elapsed_updates_price_cumulatives` | B | per-call canonical anchor | keep row |
| `pair_sync_oracle_inactive_elapsed_keeps_price_cumulatives` | B | per-call canonical anchor | keep row |
| `pair_sync_oracle_same_timestamp_keeps_price_cumulatives` | B | per-call canonical anchor | keep row |
| `pair_sync_revert_keeps_pair_state` | A | revert frame | keep row |
| `pair_sync_revert_keeps_token_balances` | A | revert frame | keep row |
| `pair_sync_reverts_when_locked` | A | guard revert | keep row |
| `pair_sync_run_revert_balance0_overflow` | A | exact guard run revert | keep row |
| `pair_sync_run_revert_balance1_overflow` | A | exact guard run revert | keep row |
| `pair_sync_run_revert_locked` | A | exact guard run revert | keep row |
| `pair_sync_success_run_implies_balances_fit_uint112` | B | per-call canonical anchor | keep row |
| `pair_sync_success_run_implies_lock_open` | B | per-call canonical anchor | keep row |
| `pair_sync_success_run_matches_closed_world_step` | H | non-from-run matches-step lift (helper) | delete row |
| `pair_sync_success_run_matches_closed_world_step_from_run` | B | per-call canonical anchor | keep row |
| `pair_sync_success_run_no_caller_token_balance_profit_from_run` | B | per-call canonical anchor | keep row |
| `pair_sync_success_run_preserves_good_from_run` | B | per-call canonical anchor | keep row |
| `pair_sync_success_run_preserves_liquidity_supply_from_run` | B | per-call canonical anchor | keep row |
| `pair_sync_success_run_updates_reserves_to_balances_from_run` | B | per-call canonical anchor | keep row |
| `pair_sync_success_run_uses_oracle_rule` | A | UNCLASSIFIED — keep (default) | keep row |
| `pair_sync_success_run_uses_oracle_rule_from_run` | B | per-call canonical anchor | keep row |
| `pair_token0_run_success_frames_state` | A | view: run-success frames state | keep row |
| `pair_token1_run_success_frames_state` | A | view: run-success frames state | keep row |
| `pair_totalSupply_run_success_frames_state` | A | view: run-success frames state | keep row |
| `pair_transferFrom_emits_transfer` | A | LP bookkeeping public spec | keep row |
| `pair_transferFrom_keeps_infinite_allowance` | A | LP bookkeeping public spec | none (exempt — no row in baseline) |
| `pair_transferFrom_keeps_pool_storage` | A | LP bookkeeping public spec | keep row |
| `pair_transferFrom_keeps_total_supply` | A | LP bookkeeping public spec | keep row |
| `pair_transferFrom_moves_tokens_between_distinct_accounts` | A | LP bookkeeping public spec | keep row |
| `pair_transferFrom_reverts_when_allowance_low` | A | guard revert | none (exempt — no row in baseline) |
| `pair_transferFrom_reverts_when_balance_low` | A | guard revert | none (exempt — no row in baseline) |
| `pair_transferFrom_reverts_when_recipient_balance_would_overflow` | A | guard revert | keep row |
| `pair_transferFrom_run_keeps_token_balances` | A | frame (token balances) | keep row |
| `pair_transferFrom_run_revert_allowance_low` | A | exact guard run revert | keep row |
| `pair_transferFrom_run_revert_balance_low` | A | exact guard run revert | keep row |
| `pair_transferFrom_run_revert_recipient_balance_overflow` | A | exact guard run revert | keep row |
| `pair_transferFrom_spends_finite_allowance` | A | LP bookkeeping public spec | none (exempt — no row in baseline) |
| `pair_transferFrom_to_self_keeps_balances` | A | LP bookkeeping public spec | keep row |
| `pair_transfer_emits_transfer` | A | LP bookkeeping public spec | keep row |
| `pair_transfer_keeps_pool_storage` | A | LP bookkeeping public spec | keep row |
| `pair_transfer_keeps_total_supply` | A | LP bookkeeping public spec | none (exempt — no row in baseline) |
| `pair_transfer_moves_tokens_between_distinct_accounts` | A | LP bookkeeping public spec | none (exempt — no row in baseline) |
| `pair_transfer_reverts_when_balance_low` | A | guard revert | none (exempt — no row in baseline) |
| `pair_transfer_reverts_when_recipient_balance_would_overflow` | A | guard revert | keep row |
| `pair_transfer_run_keeps_token_balances` | A | frame (token balances) | keep row |
| `pair_transfer_run_revert_balance_low` | A | exact guard run revert | keep row |
| `pair_transfer_run_revert_recipient_balance_overflow` | A | exact guard run revert | keep row |
| `pair_transfer_to_self_keeps_balances` | A | LP bookkeeping public spec | keep row |
| `pair_two_safeTransfer_events_replay_move_distinct_token_balances` | A | ERC20 trace (allowlist) | keep row |
| `pair_wallet_burn_does_not_increase_portfolio_value` | B | per-call canonical anchor | keep row |
| `pair_wallet_mint_does_not_increase_portfolio_value` | B | per-call canonical anchor | keep row |
| `pair_wallet_passive_action_does_not_increase_portfolio_value` | B | per-call canonical anchor | keep row |
| `pair_wallet_single_caller_history_no_portfolio_profit` | B | per-call canonical anchor | keep row |
| `pair_wallet_skim_does_not_increase_portfolio_value` | B | per-call canonical anchor | keep row |
| `pair_wallet_swap_does_not_increase_portfolio_value` | B | per-call canonical anchor | keep row |
