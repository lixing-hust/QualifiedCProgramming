# Verify Issues

## Resolved

### 1. Missing verify annotations in the loop body

- Phenomenon: the initial annotated copy was identical to `input/set_zero.c`, so `symexec` had no invariant or bridge assertions to justify the array write.
- Cause: verify-stage loop annotations had not been added yet.
- Fix: added the standard zero-prefix invariant plus the two `which implies` bridges around `a[i] = 0`.
- Result: `symexec` completed successfully and generated `set_zero_goal.v`, `set_zero_proof_auto.v`, `set_zero_proof_manual.v`, and `set_zero_goal_check.v`.

### 2. Generated manual proof file contained admitted witnesses

- Phenomenon: `set_zero_proof_manual.v` initially contained four `Admitted.` placeholders.
- Cause: the zero-fill loop requires manual normalization lemmas for loop entry, loop exit, and the two array bridge steps.
- Fix: implemented `proof_of_set_zero_entail_wit_1`, `proof_of_set_zero_return_wit_1`, `proof_of_set_zero_which_implies_wit_1`, and `proof_of_set_zero_which_implies_wit_2`.
- Result: the full Coq compile chain passed through `set_zero_goal_check.v`.

## Final Outcome

- `goal.v`: pass
- `proof_auto.v`: pass
- `proof_manual.v`: pass
- `goal_check.v`: pass
- `proof_manual.v` contains no `Admitted.` and no added `Axiom`.
