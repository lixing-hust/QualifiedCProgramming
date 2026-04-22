## Fingerprint

- Phenomenon: `logs/workspace_fingerprint.json` had the initialized empty `semantic_description` and `{}` keywords.
- Trigger: early workspace inspection before verification.
- Localization: `output/verify_20260421_043521_lcm_simple/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, filled a non-empty semantic description, and used only controlled-vocabulary keyword keys and values. After successful verification, added controlled `verification_status: goal_check_passed`.
- Result: the fingerprint has non-empty semantic fields and controlled keywords.

## Loop Annotation

- Phenomenon: the input loop had no invariant, so the verifier had no way to establish range safety for `x + a` or prove that the exit value is the least common multiple.
- Trigger: initial annotated file matched the input and contained `while (x % b != 0)` without `Inv`.
- Localization: `annotated/verify_20260421_043521_lcm_simple.c`, loop before `x = x + a`.
- Fix: added a loop invariant preserving positive inputs, parameter identity, `1 <= x`, `x <= lcm_simple_value(a,b)`, `x % a == 0`, a conditional range bridge for the next step, and a quantified fact that all smaller positive multiples of `a` are not divisible by `b`.
- Result: `symexec` succeeded and generated Coq VCs.

## Bad Loop-Exit Assertion

- Phenomenon: the first proof attempt with a post-loop `Assert x == lcm_simple_value(a@pre,b@pre) && emp` produced an unprovable heap goal after converting live stack locations to undef: `&( "b") # Int |->_ ** &( "a") # Int |->_ |-- emp`.
- Trigger: compiling `lcm_simple_entail_wit_3` in the first generated `lcm_simple_proof_manual.v`.
- Localization: first generated `coq/generated/lcm_simple_goal.v`, `lcm_simple_entail_wit_3`; active source assertion immediately after the `while`.
- Fix: removed the explicit post-loop assertion and reran `symexec`, letting the final return witness consume the loop-exit pure facts without creating a standalone assertion entailment that drops local permissions.
- Result: the regenerated manual proof had only `entail_wit_1`, `entail_wit_2`, and `return_wit_1`, with no impossible heap-discard obligation.

## Manual Proof

- Phenomenon: regenerated `coq/generated/lcm_simple_proof_manual.v` contained three `Admitted.` obligations.
- Trigger: fresh `symexec` after removing the bad loop-exit assertion.
- Localization: `proof_of_lcm_simple_entail_wit_1`, `proof_of_lcm_simple_entail_wit_2`, and `proof_of_lcm_simple_return_wit_1`.
- Fix: added local arithmetic helper lemmas for C remainder/divisibility, positive lcm facts, consecutive multiples, next-step range, and final lcm equality. Reordered proof bullets to match the actual `entailer!` subgoal order and used `lcm_simple_exit_eq` for the return witness.
- Result: `lcm_simple_proof_manual.v` compiles and contains no `Admitted.` or top-level `Axiom`.

## Compile Replay

- Phenomenon: one full replay initially failed because `return_wit_1` had compiled against a stale generated goal shape; after rebuilding `goal.v`, `pre_process` alone left open goals.
- Trigger: full documented compile order from `/home/yangfp/QualifiedCProgramming/SeparationLogic`.
- Localization: `logs/compile_proof_manual.log`, `proof_of_lcm_simple_return_wit_1`.
- Fix: made the return proof explicit by unfolding `lcm_simple_spec`, running `entailer!`, and applying `lcm_simple_exit_eq`.
- Result: `original/lcm_simple.v`, `lcm_simple_goal.v`, `lcm_simple_proof_auto.v`, `lcm_simple_proof_manual.v`, and `lcm_simple_goal_check.v` all compile with empty compile logs.

## Cleanup

- Phenomenon: successful Coq compilation left `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger: final compile replay.
- Localization: `output/verify_20260421_043521_lcm_simple/coq/generated/`.
- Fix: deleted all non-`.v` files under the workspace `coq/` directory.
- Result: `find output/verify_20260421_043521_lcm_simple/coq -type f ! -name '*.v'` prints no files.
