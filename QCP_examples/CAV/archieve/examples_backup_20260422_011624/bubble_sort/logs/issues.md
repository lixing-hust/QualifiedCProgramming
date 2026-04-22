# Issues

## Manual proof blocker

- Stage: `proof_manual`
- Status: blocked
- Current manual witnesses in `coq/generated/bubble_sort_proof_manual.v`:
  - `proof_of_bubble_sort_entail_wit_1`
  - `proof_of_bubble_sort_entail_wit_2`
  - `proof_of_bubble_sort_entail_wit_3_1`
  - `proof_of_bubble_sort_entail_wit_4`
  - `proof_of_bubble_sort_return_wit_1`
- Symptom:
  - After strengthening the loop invariants to carry permutation, sorted suffix, and prefix-to-suffix ordering, `symexec` succeeds, but the generated proof obligations are still pure list-theoretic obligations about adjacent swap preservation and suffix extension.
- Cause:
  - The current task-local Coq input only defines `sorted_z`; it does not provide reusable helper lemmas for adjacent swaps, unchanged suffixes under `replace_Znth`, or extending a sorted suffix by the bubbled maximum element.
- Handling attempted:
  - Started proving the witnesses interactively with `coqtop`.
  - Confirmed `entail_wit_1` and `entail_wit_2` are close to straightforward.
  - Identified that `entail_wit_3_1` and `entail_wit_4` require several helper lemmas on `replace_Znth`, `Znth`, and `sublist`.
- Result:
  - Verification is not complete yet because `proof_manual.v` still contains `Admitted.` and `goal_check.v` has not been compiled successfully end to end.

## Compile path note

- Initial compile of `bubble_sort_goal.v` failed because `Require Import bubble_sort` was not on the load path.
- Resolved locally by compiling the workspace copy `original/bubble_sort.v` with `-Q $WS/original ''` before loading the generated files.
