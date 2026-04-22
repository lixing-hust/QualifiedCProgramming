## Proof round 1: generated manual obligations

- Fresh `symexec` generated eight manual placeholders in `coq/generated/max_subarray_sum_proof_manual.v`: `safety_wit_4`, `safety_wit_5`, `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, `entail_wit_2_3`, `entail_wit_2_4`, and `return_wit_1`.
- The two safety witnesses are overflow obligations for `cur + a[i]`. The invariant provides `cur = sum(sublist(start, i, l))` and the contract provides `INT_MIN <= sum(sublist(lo, hi, l)) <= INT_MAX` for all nonempty subarrays, so these should reduce to rewriting `cur + Znth i l 0` as `sum(sublist(start, i + 1, l))` and applying the contract guard.
- The entailment witnesses are the four branch combinations after updating `cur` and `best`. They need a list/recurrence bridge connecting the direct subarray maximum facts in the invariant with `max_subarray_sum_spec(sublist(0, i + 1, l))`.
- The return witness should be simple after `i >= n_pre` and `i <= n_pre` give `i = n_pre`, followed by `Zlength l = n_pre` and `sublist(0, n_pre, l) = l`.
- First proof attempt will compile the generated files as-is through `goal` and `proof_auto`, then replace the placeholders with conservative `pre_process; entailer!` skeletons to identify the first stable Coq blocker.

## Proof round 2: accumulator invariant proof

- After changing the invariant to `max_subarray_sum_acc(cur, best, sublist(i, n, l)) == max_subarray_sum_spec(l)`, fresh `symexec` regenerated the same eight manual obligation names but with simpler accumulator-shaped branch equalities.
- Added local helper lemmas in `coq/generated/max_subarray_sum_proof_manual.v`:
  - `sublist_head_cons`: exposes `sublist i n l` as the current element followed by `sublist (i + 1) n l`.
  - `sum_sublist_snoc`: rewrites a suffix ending at `i + 1` as the previous suffix sum plus `Znth i l 0`.
  - `max_subarray_sum_acc_sublist_step`: aligns one C loop iteration with one unfolding step of `max_subarray_sum_acc`.
  - `suffix_bound_new` and `suffix_bound_extend`: preserve the maximum-suffix property in the two Kadane update cases.
- First stable proof compile blockers and fixes:
  - `compile_proof_manual.log` initially failed in `entail_wit_1` because Coq was importing a stale `max_subarray_sum_goal.vo` from the previous invariant shape. I deleted non-`.v` generated artifacts and recompiled `goal.v` and `proof_auto.v` before compiling `proof_manual.v` again.
  - The initialization proof needed an explicit `l = Znth 0 l 0 :: sublist 1 n_pre l` bridge derived from `sublist 0 n_pre l = l` and `sublist_head_cons`; rewriting `max_subarray_sum_spec l` through that nonempty-list shape made the accumulator equality definitional.
  - Branch witnesses needed bullet order adjusted to the actual `entailer!` goal order: accumulator equality first, suffix-bound universal fact second, and concrete current-suffix equality last.
  - The return witness had unstable generated hypothesis names, so the final script uses a `match goal` pattern to find the accumulator equality, rewrites `sublist n_pre n_pre l` to `nil`, simplifies, and finishes with that equality.
- Final result: `max_subarray_sum_proof_manual.v` compiled successfully; `max_subarray_sum_goal_check.v` also compiled successfully in the full replay. `proof_manual.v` contains no `Admitted.` and no new top-level `Axiom` declaration.

