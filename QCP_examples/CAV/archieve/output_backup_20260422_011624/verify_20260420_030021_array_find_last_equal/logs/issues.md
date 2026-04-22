# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes

## Issue 1: active annotated file had no loop invariant

- Symptom: the active annotated file `annotated/verify_20260420_030021_array_find_last_equal.c` initially had a `for (i = 0; i < n; ++i)` loop with no `Inv`, so `symexec` would not have a reusable summary for the mutable accumulator `ans` or the preserved array ownership.
- Trigger: the postcondition requires a whole-array last-match property, but the implementation proves it incrementally over the processed prefix.
- Diagnosis: the loop head must record that `[0,i)` has already been scanned and that `ans` is either `-1` with no processed match or the last processed index whose element equals `k`.
- Fix: added an implication-based invariant before the loop and a loop-exit `Assert` after the loop. The invariant preserves `0 <= i <= n`, unchanged parameters, `-1 <= ans < i`, the processed-prefix last-match facts, and `IntArray::full(a, n, l)`.
- Result: `symexec` succeeded on the latest annotated file and regenerated `array_find_last_equal_goal.v`, `array_find_last_equal_proof_auto.v`, `array_find_last_equal_proof_manual.v`, and `array_find_last_equal_goal_check.v`.

## Issue 2: avoid top-level disjunction inside loop invariant

- Symptom avoided: the earlier completed workspace for the same function recorded a `symexec` failure, `The number of now assertions and loop inv pre assertions does not match`, when the invariant used a top-level disjunction for the two `ans` states.
- Trigger: a branch-shaped invariant can make the verifier's loop pre-assertion branch count unstable.
- Diagnosis: the same semantic content can be encoded as conjunctive facts plus implications, which keeps the assertion shape stable.
- Fix: used `ans == -1 => ...`, `0 <= ans => ...`, and a universal later-index fact instead of a top-level invariant disjunction.
- Result: the first `symexec` attempt in this workspace completed successfully.

## Issue 3: manual witnesses were generated as admitted proofs

- Symptom: `coq/generated/array_find_last_equal_proof_manual.v` contained `Admitted.` for `proof_of_array_find_last_equal_entail_wit_1`, `proof_of_array_find_last_equal_entail_wit_3`, and `proof_of_array_find_last_equal_return_wit_1`.
- Trigger: the generated VCs needed explicit pure proof steps for the loop-exit quantifiers and the disjunctive return postcondition.
- Diagnosis: `entail_wit_3` needs `i = n_pre` derived from bounds before applying quantified invariant hypotheses. `return_wit_1` needs a case split on `ans = -1` to choose the no-match or match branch.
- Fix: completed the three manual lemma bodies. `entail_wit_1` closes with `entailer!`; `entail_wit_3` establishes `i = n_pre` in all subgoals and applies `H6`/`H4`; `return_wit_1` destructs `Z.eq_dec ans (-1)` and explicitly selects the postcondition branch.
- Result: `array_find_last_equal_proof_manual.v` compiled and `rg "\bAdmitted\.|\bAxiom\b"` on the manual proof file produced no matches.

## Final checks

- `symexec` succeeded on the latest active annotated file.
- `array_find_last_equal_goal.v`, `array_find_last_equal_proof_auto.v`, `array_find_last_equal_proof_manual.v`, and `array_find_last_equal_goal_check.v` all compiled successfully.
- `array_find_last_equal_proof_manual.v` contains no `Admitted.` and no `Axiom`.
- Non-`.v` artifacts under `output/verify_20260420_030021_array_find_last_equal/coq/` were removed after compilation.
