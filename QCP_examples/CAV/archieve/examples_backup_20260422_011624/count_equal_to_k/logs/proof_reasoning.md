# Proof Reasoning

## Round 1

- Read `count_equal_to_k_goal.v`, `count_equal_to_k_proof_auto.v`, and `count_equal_to_k_goal_check.v`.
- Manual obligations generated in `count_equal_to_k_proof_manual.v`:
  - `proof_of_count_equal_to_k_safety_wit_3`
  - `proof_of_count_equal_to_k_entail_wit_1`
  - `proof_of_count_equal_to_k_entail_wit_2_1`
  - `proof_of_count_equal_to_k_entail_wit_2_2`
  - `proof_of_count_equal_to_k_entail_wit_3`
  - `proof_of_count_equal_to_k_return_wit_1`
- First hypothesis:
  - `entail_wit_1` should only need `sublist 0 0 l = nil` and simplification of `count_equal_to_k_spec`.
  - `entail_wit_2_1` and `entail_wit_2_2` should need one-step prefix extension lemmas obtained by splitting `sublist 0 (i + 1) l` into `sublist 0 i l ++ [Znth i l 0]`, then simplifying the recursive spec using the current branch fact `Znth i l 0 = k` or `<> k`.
  - `entail_wit_3` should need `i = n_pre` from the bounds plus `sublist 0 n_pre l = l`.
  - `return_wit_1` should collapse by `subst k`.
  - `safety_wit_3` is expected to be arithmetic after exposing the integer bounds already carried by the typed local variables.
- Planned proof style:
  - keep the main witness proofs short
  - add a local helper lemma for appending one element to `count_equal_to_k_spec` only if direct rewriting is too brittle
  - compile immediately after the first proof pass to see the first stable failure

## Round 2

- First stable compile failure: `proof_of_count_equal_to_k_safety_wit_3` stayed incomplete after a plain `entailer!`.
- Debug step: created a temporary `logs/debug_safety.v` to print the proof state after `entailer!`.
- What the debug state showed:
  - after `entailer!`, the proof split into two pure arithmetic goals
  - proving them only from `ret = count_equal_to_k_spec(sublist 0 i l, k)` was insufficient because the proof also needed an explicit `int` bound on `n_pre`
- Fix direction:
  - switch the safety proof to `pre_process`
  - use `store_int_range` on `&( "n") # Int |-> n_pre` to recover `Int.min_signed <= n_pre <= Int.max_signed`
  - combine that with the local lemma `0 <= ret <= i` and `i < n_pre` so `entailer!` can finish the overflow side conditions

## Round 3

- After fixing the safety witness, the next compile failure showed `proof_of_count_equal_to_k_entail_wit_1` had no remaining goals after `entailer!`.
- That means the generated witness for the loop initialization was already trivial; the manual `sublist_nil` rewrite was unnecessary and caused a `No such goal` error.
- Fix: reduce `entail_wit_1` to the minimal `entailer!` proof and continue the compile-driven iteration for the remaining list witnesses.

## Round 4

- The next failure in `proof_of_count_equal_to_k_entail_wit_2_1` was again a proof script overshoot rather than a semantic gap.
- After rewriting the extended prefix and simplifying with the branch fact `Znth i l 0 = k`, the goal closed at `destruct (Z.eq_dec k k); lia`.
- The trailing `contradiction` branch was unreachable and caused another `No such goal` error, so it was removed.

## Round 5

- The next compile failure was different: the return witness still distinguished `k` from `k_pre`.
- Diagnosis:
  - this was not a Coq-side rewrite problem
  - the annotation layer had failed to preserve the unchanged scalar parameter `k == k@pre`
- Action:
  - stop proof iteration
  - go back to `annotated/verify_20260418_021719_count_equal_to_k.c`
  - add `k == k@pre` to the loop invariant and loop-exit assertion
  - clear generated files and rerun `symexec`
- Result:
  - regenerated goals use `k_pre` consistently
  - `return_wit_1` disappeared from `proof_manual.v`
  - the final manual proof file contains exactly the remaining five nontrivial obligations and compiles successfully
