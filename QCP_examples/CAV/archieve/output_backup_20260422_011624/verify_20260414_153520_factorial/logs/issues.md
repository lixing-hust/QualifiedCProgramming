# Verify Issues

## Run Notes

- External Codex no longer hit the earlier cache/write-permission failures once the driver was rerun outside the outer sandbox.
- The generated `factorial_proof_manual.v` still needed manual cleanup before compilation passed:
  - `proof_of_fac_safety_wit_3` needed the safety goal split handled after `entailer!`, with finite case analysis on `1 <= i <= 10`.
  - `proof_of_fac_entail_wit_3` needed arithmetic normalization before the final `entailer!`.
- The documented `opam` switch `coq8201` is not installed in this environment. The actual working compiler is `coqc 8.20.1` from the active `qcp-8.20` switch.
- Generated read-only files still contain known tool artifacts:
  - `coq/generated/factorial_proof_auto.v` contains `Admitted.`
  - `coq/generated/factorial_goal.v` contains witness `Axiom` declarations
- These read-only generator artifacts did not block the required outcome because `coq/generated/factorial_proof_manual.v` is complete and `coq/generated/factorial_goal_check.v` now compiles.
