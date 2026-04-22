# Issues

## Fingerprint initialization

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the verify workflow requires filling these fields early using only the controlled vocabulary from `doc/retrieval/INDEX.md`.
- Localization: `logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, described the scalar iterative tribonacci loop, and filled controlled keywords for dynamic programming, branch plus for-loop control flow, scalar data, loop-invariant/pure-arithmetic/range-bound proof patterns, numeric bounds, and final verification status.
- Result: the fingerprint is non-empty and valid JSON.

## Annotation layer

- Phenomenon: the active annotated file initially had no invariant for `for (i = 3; i <= n; ++i)`.
- Trigger: the postcondition requires `__return == tribonacci_z(n@pre)`, but the loop maintains that relation only through rolling scalar accumulators `a`, `b`, and `c`.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_221428_tribonacci.c`, immediately before the `for` loop.
- Fix: added a guard-point invariant preserving `n == n@pre`, bounding `3 <= i <= n + 1`, and recording `a == tribonacci_z(i - 3)`, `b == tribonacci_z(i - 2)`, and `c == tribonacci_z(i - 1)`.
- Result: rerunning `symexec` generated fresh `tribonacci_goal.v`, `tribonacci_proof_auto.v`, `tribonacci_proof_manual.v`, and `tribonacci_goal_check.v`.

## Symexec

- Phenomenon: symbolic execution had to be rerun after adding the loop invariant.
- Trigger: any `Inv` change invalidates previous generated VC files.
- Localization: `logs/qcp_run.log`.
- Fix: cleared stale generated VC files and ran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` with explicit `--goal-file`, `--proof-auto-file`, `--proof-manual-file`, `--coq-logic-path=SimpleC.EE.CAV.verify_20260420_221428_tribonacci`, `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`, and the active annotated C path.
- Result: `symexec` exited 0 and `logs/qcp_run.log` records `Successfully finished symbolic execution`.

## Manual proof obligations

- Phenomenon: `coq/generated/tribonacci_proof_manual.v` contained six `Admitted.` obligations: `safety_wit_9`, `safety_wit_10`, `entail_wit_1`, `entail_wit_2`, `return_wit_1`, and `return_wit_2`.
- Trigger: the automatic proof did not know the tribonacci recurrence, bounded overflow facts for loop sums, or the concrete base cases of `tribonacci_z`.
- Localization: `coq/generated/tribonacci_proof_manual.v`.
- Fix: added local helper lemmas for the tribonacci recurrence and bounded finite-range arithmetic over indices `3..37`, then completed the six manual witnesses.
- Result: `tribonacci_proof_manual.v` compiles and contains no `Admitted.` and no top-level `Axiom`.

## Tuple destruct in recurrence helper

- Phenomenon: the first proof compile failed in `tribonacci_nat_step` with `Expects a disjunctive pattern with 3 branches`, then a second destruct attempt produced an unused-pattern warning and failed with `Cannot find witness`.
- Trigger: the tuple returned by `tribonacci_triple` is represented as `(Z * Z) * Z`; the initial destruct patterns did not match that shape.
- Localization: `coq/generated/tribonacci_proof_manual.v`, `tribonacci_nat_step`.
- Fix: probed the goal in `coqtop` and changed the destruct pattern to `destruct (tribonacci_triple n) as [[a b] c]`.
- Result: the recurrence helper compiled and the proof progressed to loop-preservation obligations.

## Preservation proof order

- Phenomenon: `proof_of_tribonacci_entail_wit_2` failed with unification errors around shifted accumulator goals.
- Trigger: after `entailer!`, Coq generated the remaining pure goals in the order `a + b + c = T(i)`, `c = T(i - 1)`, then `b = T(i - 2)`, not in the textual invariant order.
- Localization: `coq/generated/tribonacci_proof_manual.v`, `proof_of_tribonacci_entail_wit_2`.
- Fix: inspected the post-`entailer!` state in `coqtop` and reordered the proof bullets to match the generated goal order.
- Result: the shifted accumulator goals closed by rewriting `H4` and `H3`.

## Recurrence rewrite target

- Phenomenon: `rewrite tribonacci_z_step by lia` failed with `Cannot find witness`.
- Trigger: the rewrite tactic tried to instantiate the recurrence lemma on an earlier subterm such as `tribonacci_z (i - 3)`, whose side condition `3 <= i - 3` is unavailable.
- Localization: `coq/generated/tribonacci_proof_manual.v`, recurrence subgoal in `proof_of_tribonacci_entail_wit_2`.
- Fix: explicitly posed `tribonacci_z_step i H0` as a named equality and rewrote with that equality.
- Result: the recurrence subgoal closed by `lia`.

## Compile completion and cleanup

- Phenomenon: successful Coq compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger: `coqc` emits intermediate artifacts during full compile replay.
- Localization: `output/verify_20260420_221428_tribonacci/coq/generated/`.
- Fix: deleted all non-`.v` files under `coq/` after `goal_check` passed.
- Result: only the four generated `.v` files remain under `coq/generated/`.

## Final outcome

- `symexec` succeeded on the latest annotated C file.
- `original/tribonacci.v`, `tribonacci_goal.v`, `tribonacci_proof_auto.v`, `tribonacci_proof_manual.v`, and `tribonacci_goal_check.v` all compile successfully with the workspace load path.
- `tribonacci_proof_manual.v` contains no `Admitted.` and no top-level `Axiom`.
- Non-`.v` Coq intermediate files were removed.
