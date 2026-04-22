# Issues

## Fingerprint initialization

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty
  `semantic_description` and empty `keywords`.
- Trigger: the verify workflow requires filling these fields early using only
  the controlled vocabulary from `doc/retrieval/INDEX.md`.
- Localization: `logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, described the scalar recurrence and filled
  controlled keywords for dynamic programming/accumulation, branch plus for-loop
  control flow, scalar data, loop-invariant and pure-arithmetic proof patterns,
  numeric overflow/range properties, and final verification status.
- Result: the fingerprint is non-empty valid JSON and uses only controlled keys
  and values.

## Annotation layer

- Phenomenon: the active annotated file initially had no invariant for
  `for (i = 2; i <= n; ++i)`.
- Trigger: the postcondition requires `__return == ways_to_reach_z(n@pre)`, but
  the recurrence relation is maintained only through the rolling scalar
  accumulators `a` and `b`.
- Localization:
  `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_035821_ways_to_reach.c`,
  immediately before the `for` loop.
- Fix: added a guard-point invariant preserving `n == n@pre`, bounding
  `2 <= i <= n + 1`, and recording
  `a == ways_to_reach_z(i - 2)` and
  `b == ways_to_reach_z(i - 1)`.
- Result: rerunning `symexec` generated fresh `ways_to_reach_goal.v`,
  `ways_to_reach_proof_auto.v`, `ways_to_reach_proof_manual.v`, and
  `ways_to_reach_goal_check.v`.

## Symexec

- Phenomenon: symbolic execution had to be rerun after adding the loop
  invariant.
- Trigger: any `Inv` change invalidates previous generated VC files.
- Localization: `logs/qcp_run.log`.
- Fix: cleared stale generated VC files and ran
  `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` with explicit
  `--goal-file`, `--proof-auto-file`, `--proof-manual-file`,
  `--proof-check-file`, the active annotated C path,
  `--coq-logic-path=SimpleC.EE.CAV.verify_20260421_035821_ways_to_reach`,
  `--no-exec-info`, and `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/
  SimpleC.EE`.
- Result: `symexec` exited 0 and `logs/qcp_run.log` records
  `Successfully finished symbolic execution`.

## Manual proof obligations

- Phenomenon: `coq/generated/ways_to_reach_proof_manual.v` contained four
  admitted obligations: `safety_wit_6`, `entail_wit_1`, `entail_wit_2`, and
  `return_wit_1`.
- Trigger: the automatic proof did not know the local recurrence step for
  `ways_to_reach_z`, the finite integer bound for recurrence values up to 45, or
  the concrete base case for the imported specification.
- Localization: `coq/generated/ways_to_reach_proof_manual.v`.
- Fix: added local helper lemmas for the recurrence step and the finite
  `0..45` signed-int bound, then completed the four manual witnesses using the
  same stable pair-recurrence proof pattern as the existing `fibonacci` example.
- Result: `ways_to_reach_proof_manual.v` compiles and contains no `Admitted.`
  and no top-level `Axiom`.

## Compile completion and cleanup

- Phenomenon: successful Coq compilation produced `.aux`, `.glob`, `.vo`,
  `.vok`, and `.vos` files under `coq/generated/`.
- Trigger: `coqc` emits intermediate artifacts during the full compile replay.
- Localization:
  `output/verify_20260421_035821_ways_to_reach/coq/generated/`.
- Fix: deleted all non-`.v` files under `coq/` after `goal_check.v` passed.
- Result: only generated `.v` files remain under `coq/`.

## Final outcome

- `symexec` succeeded on the latest active annotated C file.
- `original/ways_to_reach.v`, `ways_to_reach_goal.v`,
  `ways_to_reach_proof_auto.v`, `ways_to_reach_proof_manual.v`, and
  `ways_to_reach_goal_check.v` all compile successfully with the workspace load
  path.
- `ways_to_reach_proof_manual.v` contains no `Admitted.` and no top-level
  `Axiom`.
- Non-`.v` Coq intermediate files were removed.
