# Verification Issues

## Missing Loop Invariant In Initial Annotated Copy

- Phenomenon: the active annotated C initially matched `input/digit_sum.c` and had no invariant for `while (n > 0)`.
- Trigger: the postcondition refers to `digit_sum_z(n@pre)`, but the loop destructively updates `n`, so symbolic execution needs a retained relation between the original input, the current quotient, and `sum`.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_022514_digit_sum.c`, immediately before the `while` loop.
- Fix: added an invariant with `0 <= n`, `0 <= sum`, `sum + n <= n@pre`, and `sum + digit_sum_z(n) == digit_sum_z(n@pre)`. Added a minimal loop-exit assertion fixing `n == 0` and `sum == digit_sum_z(n@pre)`.
- Result: after clearing generated files and rerunning `symexec`, `logs/qcp_run.log` ended with `Successfully finished symbolic execution`, and fresh `digit_sum_goal.v`, `digit_sum_proof_auto.v`, `digit_sum_proof_manual.v`, and `digit_sum_goal_check.v` were generated.

## Manual Digit Sum Unfolding Proof Needed Stable Fuel Lemmas

- Phenomenon: `coq/generated/digit_sum_proof_manual.v` initially had three admitted obligations: `proof_of_digit_sum_safety_wit_3`, `proof_of_digit_sum_entail_wit_2`, and `proof_of_digit_sum_entail_wit_3`.
- Trigger: `digit_sum_z` is defined as `digit_sum_fuel n (Z.to_nat n)`, while loop preservation needs to relate `digit_sum_z n` to `n % 10 + digit_sum_z (n ÷ 10)`.
- Location: `coq/generated/digit_sum_proof_manual.v`.
- Fix: added local helper lemmas for nonpositive fuel results, quotient decrease, stable extra fuel, one-step `digit_sum_z` unfolding, and positive remainder bounds. Completed the safety, loop-preservation, and loop-exit witnesses without adding axioms.
- Result: `digit_sum_proof_manual.v` compiles and contains no `Admitted.` or added `Axiom`.

## Compile Wrapper Initially Masked Failure

- Phenomenon: an early compile replay continued after `coqc` failures and later printed a final timestamp, even though `digit_sum_proof_manual.v` had failed and `goal_check.v` could not find the manual proof library.
- Trigger: the first shell wrapper did not use `set -e`, so later commands ran after a failed `coqc`.
- Location: `logs/compile_full.log`; the failed run reported a proof error in `digit_sum_proof_manual.v` and then a missing `digit_sum_proof_manual` path while compiling `digit_sum_goal_check.v`.
- Fix: reran the full compile template with `set -euo pipefail`, so any failing `coqc` stopped the replay immediately. Iterated on the proof until the hard-fail compile chain passed.
- Result: the final `logs/compile_full.log` contains only the start and end timestamps for the successful ordered compile through `digit_sum_goal_check.v`.

## Cleanup

- Phenomenon: successful Coq compilation produced normal `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` byproducts under `coq/generated/`.
- Trigger: normal `coqc` output.
- Location: `coq/generated/`.
- Fix: deleted all non-`.v` files under the workspace `coq/` directory after successful compile replay.
- Result: `find coq -type f ! -name '*.v'` returns no files.
