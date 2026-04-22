# Issues

## Fingerprint initialization

- Phenomenon: `logs/workspace_fingerprint.json` started with an empty `semantic_description` and empty `keywords`.
- Trigger: the verify workspace was freshly initialized.
- Localization: `output/verify_20260421_015041_gcd_iterative/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, filled a non-empty description of iterative Euclidean gcd, and used only controlled vocabulary values. After successful verification, added `verification_status` values `goal_check_passed` and `proof_check_passed`.
- Result: fingerprint metadata is complete and controlled-vocabulary compliant.

## Missing loop invariant

- Phenomenon: the active annotated C file initially had no invariant for `while (b != 0)`.
- Trigger: the loop mutates both `a` and `b`, but the postcondition refers to the gcd of the original pair through `gcd_iterative_spec(a@pre, b@pre, __return)`.
- Localization: `annotated/verify_20260421_015041_gcd_iterative.c`, immediately before the `while` loop.
- Fix: appended `logs/annotation_reasoning.md`, then added a loop invariant with existential `g`, preserving nonnegativity, the original nonzero-sum fact, `gcd_iterative_spec(a@pre, b@pre, g)`, `gcd_iterative_spec(a, b, g)`, and `emp`.
- Result: `symexec` succeeded and generated non-empty `gcd_iterative_goal.v`, `gcd_iterative_proof_auto.v`, `gcd_iterative_proof_manual.v`, and `gcd_iterative_goal_check.v`.

## Manual proof: Euclidean step rewrite

- Phenomenon: the first manual proof script for `proof_of_gcd_iterative_entail_wit_2` failed with `Found no subterm matching "Zgcd (? mod ?) ?"`.
- Trigger: the goal after unfolding was guarded inside a separation-logic entailment and used the C remainder expression from the generated VC.
- Localization: `coq/generated/gcd_iterative_proof_manual.v`, theorem `proof_of_gcd_iterative_entail_wit_2`; compile evidence in `logs/coq_compile.log`.
- Fix: used `coqtop` to inspect the post-`pre_process` state, asserted the gcd step as a pure fact, bridged C remainder `a % (b)` to Coq `a mod b` via `Z.rem_mod_nonneg`, and used `Z.gcd_mod` plus `Z.gcd_comm`.
- Result: the Euclidean preservation obligation compiled.

## Manual proof: heap weakening for `r`

- Phenomenon: after the pure gcd facts were available, `entailer!` still left a heap goal of the form `r |-> value |-- r |->_`.
- Trigger: the invariant after the assignment `r = a % b` only needs `r` as an unspecified local cell for the next loop head.
- Localization: `proof_of_gcd_iterative_entail_wit_2` in `coq/generated/gcd_iterative_proof_manual.v`.
- Fix: followed local examples and applied `sep_apply store_int_undef_store_int` before `entailer!`.
- Result: the heap obligation and remaining pure obligations were solved.

## Manual proof: loop-exit return witness

- Phenomenon: the first return proof rewrote `Z.gcd_0_r` in the wrong hypothesis and failed.
- Trigger: after unfolding `gcd_iterative_spec` and substituting `b = 0`, the relevant current-state fact is `H4 : g = Z.gcd a 0`, not the original-pair fact `H3 : g = Z.gcd a_pre b_pre`.
- Localization: `proof_of_gcd_iterative_return_wit_1` in `coq/generated/gcd_iterative_proof_manual.v`.
- Fix: rewrote `Z.gcd_0_r` in `H4`, simplified `Z.abs a` using `0 <= a`, derived `a = Z.gcd a_pre b_pre`, and closed the entailment with `entailer!`.
- Result: `proof_manual.v` compiled without `Admitted.` or added top-level `Axiom`.

## Full compile and cleanup

- Phenomenon: verification is only complete after the full compile replay and cleanup.
- Trigger: `goal_check.v` imports both generated proof modules under the workspace logical prefix.
- Localization: `logs/coq_compile.log` and `output/verify_20260421_015041_gcd_iterative/coq/`.
- Fix: compiled `original/gcd_iterative.v`, `gcd_iterative_goal.v`, `gcd_iterative_proof_auto.v`, `gcd_iterative_proof_manual.v`, and `gcd_iterative_goal_check.v` from `/home/yangfp/QualifiedCProgramming/SeparationLogic` using the documented load-path template. Removed all non-`.v` files under the workspace `coq/` directory afterward.
- Result: final compile replay succeeded, `goal_check.v` compiled, `proof_manual.v` has no `Admitted.` and no added top-level `Axiom`, and `coq/` contains only `.v` files.

