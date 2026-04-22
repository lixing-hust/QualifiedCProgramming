# Issues

## Summary

- Status: completed.
- Blocking issues: resolved.
- Annotation changes required: yes.
- Manual proof required: yes.
- Final verification result: `goal_check.v` compiled successfully.

## Fingerprint initialization

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: workspace was freshly initialized before verification.
- Localization: `logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, filled in a non-empty lower-bound binary-search semantic description, and used only controlled vocabulary values for the `keywords` object.
- Result: fingerprint JSON validates and now records the final `verification_status`.

## Missing loop invariant and midpoint bridges

- Phenomenon: the active annotated C initially had no invariant for `while (left < right)`.
- Trigger: lower-bound binary search needs a loop-head summary for the half-open candidate interval `[left, right)`, the lower excluded prefix, the upper excluded suffix, and preserved array ownership.
- Localization: `annotated/verify_20260420_233617_lower_bound.c`, loop before the `mid` assignment.
- Fix: added a loop invariant carrying:
  - `0 <= left <= right <= n`;
  - unchanged parameters `a`, `n`, and `target`;
  - `n <= INT_MAX`, `Zlength(l) == n`, and sortedness;
  - lower prefix fact `j < left -> l[j] < target`;
  - upper suffix fact `right <= j < n -> l[j] >= target`;
  - empty-interval point fact `(left == right && left < n) -> l[left] >= target`;
  - `IntArray::full(a, n, l)`.
- Result: `symexec` could reach the loop body.

## Return-witness generation failed on disjunctive postcondition

- Phenomenon: multiple `symexec` runs exited with status 1 and logged messages such as `The array i_94 of Znth is not a list type.` The generated `lower_bound_goal.v` was truncated at `Definition lower_bound_return_wit_1 :=`.
- Trigger: the original annotated postcondition shape used the disjunction `(__return == n) || (__return < n && l[__return] >= target)`. The frontend failed while generating the final return witness for this disjunctive indexed array access.
- Localization: `logs/qcp_run.log` and truncated `coq/generated/lower_bound_goal.v` during return-witness generation.
- Fix attempts:
  - reoriented non-strict comparisons from `target <= l[j]` to `l[j] >= target`;
  - tried a loop-exit assertion with explicit `left == right`, which failed with `Fail to Remove Memory Permission of mid`;
  - strengthened the invariant with an empty-interval point fact;
  - tried preserving the local `mid` permission in a post-loop assertion;
  - tried a semantically equivalent C-level final branch for `left == n`.
- Final fix: in the active annotated work copy, replaced the unstable disjunctive lower-bound postcondition with the sorted-array suffix form `(forall i, __return <= i < n -> l[i] >= target)`, which is stronger and implies the original disjunction under the sortedness precondition.
- Result: `symexec` completed successfully and generated complete Coq files.

## Manual proof obligations

- Phenomenon: `lower_bound_proof_manual.v` contained six `Admitted.` placeholders after successful `symexec`.
- Trigger: midpoint division bounds and branch preservation require arithmetic and sortedness reasoning beyond the generated auto proofs.
- Localization: `coq/generated/lower_bound_proof_manual.v`.
- Fix:
  - added `lower_bound_quot2_bounds` and `lower_bound_quot2_lt` for quotient-by-2 bounds;
  - proved midpoint bridge obligations using those bounds;
  - proved right-branch preservation by instantiating sortedness from `mid` to each upper-suffix index;
  - proved left-branch preservation by instantiating sortedness from each newly excluded lower index to `mid`;
  - used `store_int_undef_store_int` to turn the local `mid` slot back to undef in loop-preservation entailments.
- Result: `lower_bound_proof_manual.v` compiles without `Admitted.` and without user-added top-level `Axiom`.

## Compile and cleanup

- Phenomenon: successful Coq compilation left `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated`.
- Trigger: normal `coqc` output.
- Localization: `output/verify_20260420_233617_lower_bound/coq/generated`.
- Fix: removed all non-`.v` files under `coq/` after the full compile replay succeeded.
- Result: only the four generated `.v` files remain under `coq/generated`.
