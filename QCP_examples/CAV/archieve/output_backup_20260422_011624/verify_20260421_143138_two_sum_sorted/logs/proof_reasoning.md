# Proof Reasoning

## Round 1

- Current generated manual file: `output/verify_20260421_143138_two_sum_sorted/coq/generated/two_sum_sorted_proof_manual.v`.
- Manual obligations present: `two_sum_sorted_safety_wit_4`, `two_sum_sorted_entail_wit_1`, `two_sum_sorted_entail_wit_2`, `two_sum_sorted_entail_wit_3`, `two_sum_sorted_entail_wit_4`, `two_sum_sorted_entail_wit_5_1`, `two_sum_sorted_entail_wit_5_2`, and `two_sum_sorted_return_wit_2`.
- Expected easy obligations:
  - safety and bridge entailments should be pure arithmetic/list restatements plus unchanged `IntArray.full`, so the first attempt is `pre_process; entailer!; try lia`.
  - `entail_wit_5_1` and `entail_wit_5_2` are loop preservation after `right--` and `left++`; they may need explicit monotonicity reasoning over sorted `Znth` values.
  - `return_wit_2` is loop exit: from `left >= right` and `left <= right + 1`, every pair `i < j` must have either `i < left` or `right < j`; this may need an explicit case split on `i < left`.
- First proof edit: replace the generated `Admitted.` bodies with the shortest skeleton. If Coq leaves goals, inspect the first failing witness and refine that one.

## Round 2

- First compile after the proof skeleton failed at `two_sum_sorted_proof_manual.v:24` in `proof_of_two_sum_sorted_safety_wit_4` with `Attempt to save an incomplete proof`.
- `coqtop` after `pre_process; entailer!; try lia` showed two remaining pure goals:
  - `INT_MIN <= Znth left l 0 + Znth right l 0`;
  - `Znth left l 0 + Znth right l 0 <= INT_MAX`.
- Available hypothesis includes the contract pair-sum range guard as a `forall i j` fact over `0 <= i < j` and `j < n_pre`; loop condition and invariant provide `0 <= left`, `left < right`, and `right < n_pre`.
- Next proof edit: in `proof_of_two_sum_sorted_safety_wit_4`, after `entailer!`, match the pair-sum range hypothesis, specialize it at `left` and `right`, and finish both subgoals by `lia`.

## Round 3

- After fixing `safety_wit_4`, compile failed at `proof_of_two_sum_sorted_entail_wit_5_1`.
- `coqtop` after `pre_process; entailer!; try lia` showed two remaining goals:
  - stack permission conversion `&( "s") # Int |-> s |-- &( "s") # Int |->_`;
  - the upper excluded-pair invariant after `right--`, namely every pair with `right - 1 < j` is not a target pair.
- The stack permission goal matches the documented local-temporary pattern and should use `store_int_undef_store_int`.
- For the pure invariant goal, if `right < j`, reuse the old upper excluded-pair invariant. Otherwise integer arithmetic gives `j = right`; then split on `i < left`. If `i < left`, reuse the lower excluded-pair invariant. If `left <= i`, sortedness gives `l[left] <= l[i]`, so from `target < l[left] + l[right]` we get `target < l[i] + l[right]`, hence the pair sum is not equal to target.

## Round 4

- After fixing `entail_wit_5_1`, compile failed at `proof_of_two_sum_sorted_entail_wit_5_2`.
- `coqtop` showed the symmetric leftover goals:
  - stack permission conversion for `s`;
  - the lower excluded-pair invariant after `left++`, namely every pair with `i < left + 1` is not a target pair.
- The stack goal again uses `store_int_undef_store_int`.
- For the pure goal, if `i < left`, reuse the old lower excluded-pair invariant. Otherwise `i = left`. If `right < j`, reuse the old upper excluded-pair invariant. Otherwise `j <= right`, and sortedness gives `l[j] <= l[right]`; combined with `l[left] + l[right] < target`, this proves `l[left] + l[j] <> target`.

## Round 5

- After fixing both loop-preservation witnesses, compile failed at `proof_of_two_sum_sorted_return_wit_2`.
- `coqtop` showed that `pre_process; entailer!; try lia` left the whole postcondition disjunction:
  - left side: `0 = 0` plus the universal no-pair fact and unchanged `IntArray.full`;
  - right side: impossible `0 = 1` existential found-pair case.
- Next proof edit: choose the left disjunct first, run `entailer!`, then prove the universal no-pair fact. For any valid `i < j`, split on `i < left`. If true, use the lower excluded-pair invariant. Otherwise `left <= i`; since loop exit gives `left >= right`, `right < j`, so use the upper excluded-pair invariant.

## Round 6

- The previous `return_wit_2` script tried to choose the postcondition disjunction with `left` before `entailer!`, but Coq reported `No product even after head-reduction` at the later `intros`, because the goal was still an assertion applied to a model rather than the pure universal proposition.
- Better pattern from existing examples: prove the pure helper fact first in ordinary Coq context, then call `entailer!` and let the separation-logic tactic consume the assertion-level conjunction/disjunction.
- Next proof edit: define `Hno_pair` before `entailer!`, using the same split on `i < left`; then finish the whole return witness with `entailer!`.

## Round 7

- The `Hno_pair` plus `entailer!` attempt still left the assertion-level postcondition unsolved; `coqtop` showed it as `IntArray.full ... |-- ([|0 = 0|] && ([|forall ...|] && IntArray.full ...)) || ...`.
- Existing examples such as `array_has_adjacent_equal_return_wit_2` solve this shape by unfolding the witness, using `Intros`, choosing `left`, then manually splitting the pure and heap parts after `entailer!`.
- Next proof edit: rewrite `return_wit_2` in that style. The universal no-pair subgoal is proved directly by splitting on `i < left`, using the lower excluded-pair invariant in the first branch and the upper excluded-pair invariant in the second branch.
