# Proof Reasoning

## Round 1

- Fresh `symexec` generated `binary_search_goal.v`, `binary_search_proof_auto.v`, `binary_search_proof_manual.v`, and `binary_search_goal_check.v`.
- `binary_search_proof_manual.v` contains six admitted manual obligations:
  - `proof_of_binary_search_safety_wit_4`: overflow/range safety for `left + (right - left) / 2`;
  - `proof_of_binary_search_entail_wit_1`: initialization of the loop invariant;
  - `proof_of_binary_search_entail_wit_2`: midpoint bridge assertion after `mid = left + (right - left) / 2`;
  - `proof_of_binary_search_entail_wit_3`: preservation of the midpoint bridge after the first failed equality test;
  - `proof_of_binary_search_entail_wit_4_1`: invariant preservation after moving `right = mid - 1`;
  - `proof_of_binary_search_entail_wit_4_2`: invariant preservation after moving `left = mid + 1`.
- Available semantic hypotheses in the branch witnesses include:
  - adjacent sortedness: `forall i, 0 <= i /\ i + 1 < n -> Znth i l 0 <= Znth (i + 1) l 0`;
  - excluded lower segment: every `j < left` has `Znth j l 0 < target`;
  - excluded upper segment: every `right < j < n` has `target < Znth j l 0`;
  - midpoint bounds: `left <= mid <= right` and `0 <= mid < n`.
- The midpoint safety and bridge obligations are arithmetic plus separation-logic framing. The only nontrivial pure reasoning is that adjacent sortedness can be chained:
  - for the right branch, `mid <= j` implies `Znth mid l 0 <= Znth j l 0`;
  - for the left branch, `j <= mid` implies `Znth j l 0 <= Znth mid l 0`.
- Planned proof edit:
  - add a local helper lemma `binary_search_sorted_adjacent_mono` proving the chained monotonicity fact from adjacent sortedness;
  - add `binary_search_quot2_bounds` for bounds on `(right - left) ÷ 2`;
  - use `store_int_undef_store_int` in the two loop-preservation entailments where the generated goal changes the local `mid` stack slot from a concrete value to undef.

## Round 2

- First compile attempt of `binary_search_proof_manual.v` failed in `proof_of_binary_search_safety_wit_4` with `Attempt to save an incomplete proof`.
- The first script only introduced `binary_search_quot2_bounds (right - left)` as an unapplied theorem, so `entailer!` did not get the concrete fact `0 <= (right - left) ÷ 2 <= right - left`.
- Next proof edit: replace the loose `pose proof` in `safety_wit_4` and `entail_wit_2` with an explicit asserted bound discharged by `apply binary_search_quot2_bounds; lia`.

## Round 3

- After making the quotient bound explicit, `proof_of_binary_search_safety_wit_4` still had an open goal.
- `coqtop` showed the remaining pure goal was `left + (right - left) ÷ 2 <= 2147483647` under the heap assertion containing `&( "left") # Int |-> left` and `&( "right") # Int |-> right`.
- The missing facts are the signed-int ranges of the stack values `left` and `right`. These are not pure hypotheses until extracted from the heap.
- Next proof edit: use `prop_apply (store_int_range (&("left")) left)` and `prop_apply (store_int_range (&("right")) right)` in `safety_wit_4`, then normalize `Int.min_signed` and `Int.max_signed` before `entailer!`.

## Round 4

- After adding stack-slot range extraction, `safety_wit_4` compiled through, and the next failure was `No such goal` at `proof_of_binary_search_entail_wit_1`.
- This means `pre_process` alone closed the initialization entailment; the following unconditional `entailer!` was being run after all goals were already solved.
- Next proof edit: replace that proof body with just `pre_process.`

## Round 5

- The next compile failure was the same `No such goal` pattern at `proof_of_binary_search_entail_wit_3`.
- This witness is just the midpoint bridge assertion after learning `Znth mid l 0 <> target_pre`; `pre_process` already closes it.
- Next proof edit: remove the redundant `entailer!` after `pre_process` in `entail_wit_3`.

## Round 6

- The annotation was corrected and `symexec` regenerated the VCs. The fresh `binary_search_entail_wit_4_1` now includes both:
  - `Znth mid l 0 >= target_pre`
  - `Znth mid l 0 <> target_pre`
- This is enough to derive `target_pre < Znth mid l 0` for the `j == mid` case in the new upper excluded region.
- Instead of handling the forall subgoal after `entailer!` and then manually discharging reordered pure side goals, the next proof edit asserts the complete new forall fact before the entailment:
  - for `right = mid - 1`, assert `forall j, mid - 1 < j < n_pre -> target_pre < Znth j l 0`;
  - for `left = mid + 1`, assert `forall j, 0 <= j < mid + 1 -> Znth j l 0 < target_pre`.
- The assertions use `binary_search_sorted_adjacent_mono`; then `store_int_undef_store_int` and `entailer!` should close the heap and remaining pure goals.

## Round 7

- After recompiling the fresh `goal.v`, `proof_of_binary_search_entail_wit_4` failed with `No such goal` at the `entailer!` line.
- The branch assertion VC from `>=` plus `<>` to strict `target_pre < Znth mid l 0` is solved completely by `pre_process`.
- Next proof edit: remove the redundant `entailer!` from `entail_wit_4`.

## Final Proof State

- After adding loop-bound facts to the bridge assertions and regenerating with `symexec`, the final manual obligations were:
  - `proof_of_binary_search_safety_wit_4`;
  - `proof_of_binary_search_entail_wit_1`;
  - `proof_of_binary_search_entail_wit_2`;
  - `proof_of_binary_search_entail_wit_3`;
  - `proof_of_binary_search_entail_wit_4`;
  - `proof_of_binary_search_entail_wit_5_1`;
  - `proof_of_binary_search_entail_wit_5_2`.
- Final proof structure:
  - `binary_search_quot2_bounds` proves bounds for division by two;
  - `binary_search_sorted_adjacent_mono` proves monotonicity from adjacent sortedness;
  - `safety_wit_4` extracts `left` and `right` signed-int ranges with `store_int_range`;
  - `entail_wit_5_1` proves the upper excluded region after moving `right`;
  - `entail_wit_5_2` proves the lower excluded region after moving `left`.
- Full compile replay succeeded for `binary_search_goal.v`, `binary_search_proof_auto.v`, `binary_search_proof_manual.v`, and `binary_search_goal_check.v`.
- Final grep found no `Admitted.` in `binary_search_proof_manual.v` and no top-level `Axiom` declaration added there.
