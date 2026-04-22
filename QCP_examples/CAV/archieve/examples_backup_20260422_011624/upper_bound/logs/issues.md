# Verification Issues

## Fingerprint Initialization

- Phenomenon: `logs/workspace_fingerprint.json` started with an empty `semantic_description` and `{}` keywords.
- Trigger: normal verify bootstrap leaves placeholders that must be filled early in the task.
- Location: `logs/workspace_fingerprint.json`.
- Fix action: read `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/doc/retrieval/INDEX.md`, then filled a non-empty description of read-only binary-search upper_bound and used only controlled vocabulary values. After final verification, added `verification_status` values `goal_check_passed`, `proof_check_passed`, and `auto_proof_contains_admitted`.
- Result: the fingerprint now has reusable semantic metadata and controlled keywords.

## Missing Loop Invariant

- Phenomenon: the active annotated file initially matched the input and had no invariant for `while (left < right)`.
- Trigger: binary search requires the verifier to know the shrinking half-open interval, the excluded prefix `l[j] <= target`, the excluded suffix `l[j] > target`, and unchanged array ownership.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_040514_upper_bound.c`, loop around `while (left < right)`.
- Fix action: added a loop invariant with `0 <= left <= right <= n`, unchanged parameter facts, sortedness, prefix/suffix facts, an empty-interval point fact, and `IntArray::full(a, n, l)`. Added a midpoint bridge assertion before reading `a[mid]` and an else-branch assertion recording `l[mid] > target`.
- Result: symbolic execution reached final witness generation instead of failing at loop or array-read preconditions.

## Disjunctive Return Postcondition Generation

- Phenomenon: the first `symexec` run after adding loop annotations exited with status 1. `logs/qcp_run.log` reported `The array i_94 of Znth is not a list type. The type is Z`, and `coq/generated/upper_bound_goal.v` was truncated at `Definition upper_bound_return_wit_1 :=`.
- Trigger: the generated return witness was unstable on the original indexed disjunction `(__return == n) || (__return < n && l[__return] > target)`.
- Location: generated return witness in `coq/generated/upper_bound_goal.v`; source postcondition in the active annotated copy.
- Fix action: first tried a semantically equivalent C-level split after the loop, `if (left == n) { return left; } return left;`, without changing the contract text. That still failed at the same truncated return witness. Then replaced the active annotated copy's disjunctive condition with the stronger sorted-suffix form `(forall (i: Z), (__return <= i && i < n) => l[i] > target)`, which implies the original condition for sorted upper_bound results.
- Result: the next clean `symexec` run completed successfully at `2026-04-21T04:09:20+08:00` and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files. This is a frontend contract-shape workaround applied only to the active annotated verification copy; `input/upper_bound.c` was not modified.

## Manual Proof Obligations

- Phenomenon: fresh `coq/generated/upper_bound_proof_manual.v` contained six `Admitted.` placeholders for one midpoint safety witness and five entailment witnesses.
- Trigger: binary-search arithmetic and quantified prefix/suffix preservation are outside the generated manual proof skeleton.
- Location: `coq/generated/upper_bound_proof_manual.v`.
- Fix action: added local quotient helper lemmas, proved midpoint overflow/safety using stack `Int` ranges and quotient bounds, proved the midpoint bridge, and proved both loop-preservation branches using sortedness plus `store_int_undef_store_int` for the local `mid` permission.
- Result: `upper_bound_proof_manual.v` compiled successfully and contains no `Admitted.` and no added top-level `Axiom`.

## Final Coq Replay And Cleanup

- Phenomenon: completion requires the current generated files to compile in order and requires removal of non-`.v` Coq intermediates.
- Trigger: the successful proof generated `.vo`, `.glob`, `.vok`, `.vos`, and `.aux` files under `coq/generated/`.
- Location: `logs/compile_full.log` and `coq/generated/`.
- Fix action: compiled `upper_bound_goal.v`, `upper_bound_proof_auto.v`, `upper_bound_proof_manual.v`, and `upper_bound_goal_check.v` from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the documented load-path template, then deleted all non-`.v` files under `coq/`.
- Result: final replay reached `goal_check.v`, `proof_manual.v` has no `Admitted.` or added top-level `Axiom`, and `coq/` now contains only `.v` source files.
