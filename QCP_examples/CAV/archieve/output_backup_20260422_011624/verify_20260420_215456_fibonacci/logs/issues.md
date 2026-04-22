# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes

## Fingerprint initialization

- Phenomenon: the initialized `logs/workspace_fingerprint.json` had an empty `semantic_description` and empty `keywords`.
- Trigger: the verify workflow requires those fields to be filled early, with keywords restricted to the controlled vocabulary from `doc/retrieval/INDEX.md`.
- Localization: `logs/workspace_fingerprint.json`.
- Fix: read the retrieval index, described the scalar iterative Fibonacci loop, and filled controlled keywords for dynamic programming / accumulation, branch plus for-loop control flow, scalar data, loop invariant and arithmetic proof patterns, numeric bounds, and final verification status.
- Result: the fingerprint is non-empty and `python3 -m json.tool logs/workspace_fingerprint.json` accepts the JSON.

## Annotation layer

- Phenomenon: the active annotated file initially had no invariant for `for (i = 2; i <= n; ++i)`.
- Trigger: the postcondition requires `__return == fib_z(n@pre)`, but the loop body only maintains this through the pair of scalar accumulators `a` and `b`.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_215456_fibonacci.c`, immediately before the `for` loop.
- Fix: added a guard-point invariant preserving `n == n@pre`, bounding `2 <= i <= n + 1`, and recording `a == fib_z(i - 2)` plus `b == fib_z(i - 1)`.
- Result: after rerunning `symexec`, the verifier generated fresh `fibonacci_goal.v`, `fibonacci_proof_auto.v`, `fibonacci_proof_manual.v`, and `fibonacci_goal_check.v`.

## Symexec invocation

- Phenomenon: the first `symexec` launch failed immediately with `goal file not specified`.
- Trigger: this environment requires explicit generated output file flags; providing only `--input-file`, `-slp`, and `--coq-logic-path` is insufficient.
- Localization: `logs/qcp_run.log`.
- Fix: reran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` with explicit `--goal-file`, `--proof-auto-file`, and `--proof-manual-file` paths under `coq/generated/`.
- Result: `logs/qcp_run.log` records `Successfully finished symbolic execution`.

## Manual proof obligations

- Phenomenon: the generated `coq/generated/fibonacci_proof_manual.v` contained four `Admitted.` placeholders:
  - `proof_of_fibonacci_safety_wit_6`
  - `proof_of_fibonacci_entail_wit_1`
  - `proof_of_fibonacci_entail_wit_2`
  - `proof_of_fibonacci_return_wit_1`
- Trigger: the automatic proof did not discharge the Fibonacci recurrence, bounded signed-int range for `a + b`, or the early-return `fib_z(0)` fact.
- Localization: `coq/generated/fibonacci_proof_manual.v`.
- Fix: added local helper lemmas for the Fibonacci recurrence (`fib_nat_step`, `fib_z_step`) and a bounded table lemma (`fib_z_int_bound_0_46`), then used them in the safety and loop-preservation witnesses. The early-return witness is closed by substituting `n_pre = 0`.
- Result: `fibonacci_proof_manual.v` compiles without `Admitted.` and without a user-added `Axiom`.

## Proof tactic iteration

- Phenomenon: an early finite-split proof failed with `Cannot find witness`.
- Trigger: after `vm_compute`, true `Z` inequalities reduced to constructor-discrimination goals such as `Lt = Gt -> False`, which `lia` did not close.
- Localization: first attempted local tactic in `coq/generated/fibonacci_proof_manual.v`.
- Fix: recognized that computed comparison goals need `discriminate` or `reflexivity`, not just `lia`.
- Result: that immediate failure was resolved, but the approach was later replaced by helper lemmas because it produced too much proof search inside generated VC contexts.

## Long-running compile attempt

- Phenomenon: one `coqc` run on `fibonacci_proof_manual.v` ran for more than two minutes without output.
- Trigger: the guarded finite-split tactic was repeatedly splitting the bounded loop index inside witness proof contexts, creating an expensive proof term/search path.
- Localization: compile process for `coq/generated/fibonacci_proof_manual.v`.
- Fix: stopped that compile attempt and replaced the broad finite split with reusable helper lemmas, leaving only one isolated finite table proof for `fib_z` range over `0..46`.
- Result: the next proof iterations compiled quickly and progressed to the final return witness.

## Compile completion and cleanup

- Phenomenon: successful Coq compilation left `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger: `coqc` emits these intermediate artifacts during the full compile replay.
- Localization: `coq/generated/`.
- Fix: deleted all non-`.v` files under `coq/` after `goal_check` passed.
- Result: only the four generated `.v` files remain under `coq/generated/`.

## Final outcome

- `symexec` succeeded on the latest annotated file.
- `original/fibonacci.v`, `fibonacci_goal.v`, `fibonacci_proof_auto.v`, `fibonacci_proof_manual.v`, and `fibonacci_goal_check.v` all compiled successfully.
- `fibonacci_proof_manual.v` contains no `Admitted.` and no user-added `Axiom`.
- Non-`.v` files under `coq/` were deleted after the successful compile pass.
