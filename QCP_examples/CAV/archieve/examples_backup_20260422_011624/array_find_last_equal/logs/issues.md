# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes

## Issue 1: initial loop invariant used a top-level disjunction

- Symptom: after adding the first invariant and exit assertion, `symexec` failed at `annotated/verify_20260420_000745_array_find_last_equal.c:43:4` with `The number of now assertions and loop inv pre assertions does not match.`
- Trigger: the first invariant encoded the two accumulator states as a top-level disjunction: either `ans == -1` and no processed match exists, or `0 <= ans` and `ans` is the last processed match.
- Diagnosis: stable loop examples in this workspace avoid top-level disjunctions inside `Inv`. The verifier split the invariant into a branch shape that did not match the loop pre-assertion shape.
- Fix: rewrote the invariant and loop-exit assertion into an implication-based conjunctive form:
  - `-1 <= ans && ans < i`
  - `ans == -1 => forall processed j, l[j] != k`
  - `0 <= ans => l[ans] == k`
  - `forall processed j after ans, l[j] != k`
- Result: after clearing partial generated files and rerunning `symexec`, symbolic execution completed successfully and regenerated `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`.

## Issue 2: exit witness needed explicit quantified facts

- Symptom: first manual proof attempt compiled `goal.v` and `proof_auto.v`, but `proof_manual.v` failed in `proof_of_array_find_last_equal_entail_wit_3` with `Attempt to save an incomplete proof`.
- Trigger: `entailer!` left two pure quantified goals after proving loop exit:
  - later processed indices after `ans` still differ from `k`
  - when `ans == -1`, all indices in `[0,n)` differ from `k`
- Diagnosis: the proof needed to use `i >= n_pre` and `i <= n_pre` to establish `i = n_pre`, then apply the invariant hypotheses at the rewritten bound.
- Fix: added explicit subproofs after `entailer!`, applying `H6` for the later-index fact and `H4` for the `ans == -1` no-match fact. A second compile attempt showed the equality rewrite had only been applied to the first bullet, so the proof was changed to apply `assert (i = n_pre) by lia; subst i` to all generated subgoals.
- Result: `proof_of_array_find_last_equal_entail_wit_3` compiled.

## Issue 3: return witness needed explicit disjunction branch selection

- Symptom: `proof_manual.v` then failed in `proof_of_array_find_last_equal_return_wit_1` with bullet/focus errors because the first branch after splitting on `ans = -1` still had an unfinished separation-logic disjunction goal.
- Trigger: `entailer!` did not automatically choose the disjunctive postcondition branch.
- Diagnosis: examples with disjunctive postconditions choose `left` or `right` explicitly before calling `entailer!`. In this witness, the `ans = -1` branch must select the no-match disjunct, and the `ans <> -1` branch must derive `0 <= ans` then select the match disjunct.
- Fix: rewrote the proof to use `pre_process`, destruct `Z.eq_dec ans (-1)`, then use `right`/`left` explicitly. The model-level conjunctions remaining after `entailer!` were closed by unfolding `andp` and `coq_prop`, simplifying, and using `repeat split; auto`.
- Result: `proof_manual.v` compiled, and the final `goal_check.v` compile passed.

## Final checks

- `symexec` succeeded on the latest annotated file.
- `array_find_last_equal_goal.v`, `array_find_last_equal_proof_auto.v`, `array_find_last_equal_proof_manual.v`, and `array_find_last_equal_goal_check.v` all compiled successfully.
- `array_find_last_equal_proof_manual.v` contains no `Admitted.` and no `Axiom`.
- Non-`.v` artifacts under `output/verify_20260420_000745_array_find_last_equal/coq/` were removed after compilation.
