# Proof Reasoning

## Iteration 1: manual obligations after successful symexec

- Fresh `symexec` succeeded after the annotated work copy used the suffix postcondition shape and generated:
  - `coq/generated/lower_bound_goal.v`
  - `coq/generated/lower_bound_proof_auto.v`
  - `coq/generated/lower_bound_proof_manual.v`
  - `coq/generated/lower_bound_goal_check.v`
- `lower_bound_proof_manual.v` contains six admitted manual obligations:
  - `proof_of_lower_bound_safety_wit_2`
  - `proof_of_lower_bound_entail_wit_1`
  - `proof_of_lower_bound_entail_wit_2`
  - `proof_of_lower_bound_entail_wit_3`
  - `proof_of_lower_bound_entail_wit_4_1`
  - `proof_of_lower_bound_entail_wit_4_2`
- Expected proof shape:
  - `safety_wit_2` is the midpoint arithmetic safety obligation for `left + (right - left) / 2`; it should need division-by-2 bounds plus integer-range facts.
  - `entail_wit_1` is invariant initialization, expected to be pure arithmetic and vacuous quantified ranges.
  - `entail_wit_2` and `entail_wit_3` are bridge assertions that mostly restate the current facts and midpoint bounds.
  - `entail_wit_4_1` is the right-branch preservation proof after `right = mid`; it needs sortedness to extend the upper suffix and the branch fact `l[mid] >= target`.
  - `entail_wit_4_2` is the left-branch preservation proof after `left = mid + 1`; it needs sortedness to extend the lower prefix and, for the empty interval point fact, the old upper suffix when `mid + 1 == right`.
- First proof edit plan:
  - add local helper lemmas for division-by-2 bounds and sorted-list monotonic instantiation if direct `lia`/first-order reasoning is not enough;
  - keep each generated theorem proof short: `pre_process`, expose pure facts, solve separation logic with `entailer!`, then handle remaining pure obligations with helper lemmas and `lia`.

## Iteration 2: first compile failure

- First `coqc` compile of `lower_bound_proof_manual.v` failed at line 56 in `proof_of_lower_bound_entail_wit_2` with `Attempt to save an incomplete proof`.
- The current proof used the quotient bound helper and `entailer!`, so the remaining goal is likely one of the midpoint strict bounds, especially `left + (right - left) ÷ 2 < right`.
- Next step: inspect the exact proof state for `lower_bound_entail_wit_2` with `coqtop`, then add a more precise quotient lemma for the positive interval case if needed.

## Iteration 3: final proof repair

- `coqtop` on `lower_bound_entail_wit_2` after `pre_process`, the non-strict quotient bound, and `entailer!` showed two remaining pure goals:
  - `left + (right - left) ÷ 2 < n_pre`
  - `left + (right - left) ÷ 2 < right`
- The missing fact was the strict division bound `(right - left) ÷ 2 < right - left`, which follows because the loop condition gives `0 < right - left`.
- Proof edit:
  - added helper lemma `lower_bound_quot2_lt`;
  - used it in `proof_of_lower_bound_entail_wit_2`;
  - loosened the `match goal` patterns for the generated sortedness hypotheses in `entail_wit_4_1` and `entail_wit_4_2`, because Coq prints the generated premise as chained inequalities.
- Final compile replay from `/home/yangfp/QualifiedCProgramming/SeparationLogic` succeeded for:
  - `lower_bound_goal.v`
  - `lower_bound_proof_auto.v`
  - `lower_bound_proof_manual.v`
  - `lower_bound_goal_check.v`
- `lower_bound_proof_manual.v` contains no `Admitted.` and no top-level `Axiom` declarations after the final edit.
