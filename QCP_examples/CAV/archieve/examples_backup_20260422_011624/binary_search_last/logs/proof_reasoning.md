# Proof Reasoning

## Iteration 1 - 2026-04-21 04:29:49 +0800

- Fresh `symexec` succeeded for `annotated/verify_20260421_042558_binary_search_last.c` and generated `binary_search_last_goal.v`, `binary_search_last_proof_auto.v`, `binary_search_last_proof_manual.v`, and `binary_search_last_goal_check.v`.
- `binary_search_last_proof_manual.v` contains seven admitted manual obligations: `safety_wit_2`, `entail_wit_1`, `entail_wit_2`, `entail_wit_3`, `entail_wit_4_1`, `entail_wit_4_2`, and `return_wit_2`.
- The proof shape matches the successful `upper_bound` and `binary_search_first` examples:
  - `safety_wit_2` needs quotient-by-2 bounds plus stack `Int` ranges for `left` and `right`;
  - `entail_wit_1` and `entail_wit_3` should close with `pre_process`;
  - `entail_wit_2` needs midpoint range facts from quotient bounds;
  - `entail_wit_4_1` and `entail_wit_4_2` are loop-preservation obligations for the upper suffix and lower prefix respectively, using sortedness and `store_int_undef_store_int` to turn `mid` back to undefined at the loop head;
  - `return_wit_2` is the missing-target branch after `left > 0` and `a[left - 1] != target`; it needs `left = right`, sortedness to show every prefix element is below `target`, and the upper suffix fact to show every suffix element is above `target`.
- Planned proof edit: add the same quotient helper lemmas as the close examples, fill the six loop/safety obligations with the established pattern, and prove `return_wit_2` by splitting an arbitrary index into `i < left` and `left <= i`.

## Iteration 2 - 2026-04-21 04:31:55 +0800

- The first compile of `binary_search_last_proof_manual.v` failed at line 161 with `Syntax error: ',' or '|-' expected (in [match_context_rule])`.
- The proof logic was not the blocker; one `match goal` branch for the upper-suffix hypothesis omitted the required `|- _` separator in the pattern.
- Fixed the pattern to `| Hupper: forall q, ... |- _ => ...`.
- Recompiled `binary_search_last_proof_manual.v` and `binary_search_last_goal_check.v` successfully, then replayed the full compile sequence for `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`. The manual proof file has no `Admitted.` and no `Axiom`.
