# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: no

## Fingerprint Initialization

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the workspace was freshly initialized before verify-specific semantic metadata had been filled.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_015753_is_prime_simple/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a non-empty scalar trial-division description and used only controlled vocabulary keys and values, later adding successful verification status values.
- Result: fingerprint metadata is non-empty and uses the controlled vocabulary.

## Loop Annotation

- Phenomenon: the active annotated copy initially had no invariant for the `for (d = 2; d < n; ++d)` loop.
- Trigger: proving the successful return requires preserving that all candidate divisors in the processed range `[2, d)` do not divide `n`; without an invariant, `symexec` has no loop-head summary for that fact.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_015753_is_prime_simple.c`.
- Fix action: added a loop invariant before the `for` statement carrying `2 <= d`, `d <= n`, `n == n@pre`, and `forall i, 2 <= i && i < d => n % i != 0`.
- Result: after later placement and assertion repairs, `symexec` generated fresh Coq artifacts successfully.

## Symexec Flag Form

- Phenomenon: the first manual `symexec` attempt exited immediately with `goal file not specified` and `Start to symbolic execution on program : (null)`.
- Trigger: this binary expects output and input options in `--flag=value` form; the split `--flag value` form was not parsed for these options.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_015753_is_prime_simple/logs/qcp_run.log`.
- Fix action: reran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` with `--goal-file=...`, `--proof-auto-file=...`, `--proof-manual-file=...`, `--input-file=...`, `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`, `--coq-logic-path=SimpleC.EE.CAV.verify_20260421_015753_is_prime_simple`, and `--no-exec-info`.
- Result: the command reached frontend parsing and symbolic execution of `is_prime_simple`.

## Invariant Placement

- Phenomenon: the first real `symexec` run with equals-form flags failed with `Expected loop after loop invariant` at the opening brace following the `for` header.
- Trigger: the invariant block had been placed between `for (d = 2; d < n; ++d)` and `{`, but this frontend expects `/*@ Inv ... */` immediately before the loop statement.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_015753_is_prime_simple.c:28` in the failed version.
- Fix action: moved the same invariant block above the `for` statement.
- Result: the next `symexec` run progressed through loop parsing and reached the final return.

## Post-loop Assertion Cleanup Failure

- Phenomenon: after moving the invariant, `symexec` failed at the final `return 1` with `Fail to Remove Memory Permission of d:66`.
- Trigger: the post-loop `Assert` was placed after loop exit and before local variable cleanup, matching the known failure mode where a late exit assertion interferes with local permission removal.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_015753_is_prime_simple.c:40` in the failed version.
- Fix action: removed the post-loop assertion and relied on the loop invariant plus the loop exit condition to give the pure arithmetic fact needed by the final return witness.
- Result: the clean `symexec` rerun exited with status 0 and `logs/qcp_run.log` ends with `Successfully finished symbolic execution`.

## Coq Compile And Cleanup

- Phenomenon: completion required a full compile replay, not just successful `symexec`.
- Trigger: the verify workflow requires `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile under the workspace logical path, and requires cleanup of non-`.v` Coq intermediates.
- Location: compile logs under `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_015753_is_prime_simple/logs/`.
- Fix action: compiled all generated Coq files from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the documented base `-R` load paths and `-R coq/generated SimpleC.EE.CAV.verify_20260421_015753_is_prime_simple`; confirmed `proof_manual.v` has no `Admitted.` and no `Axiom`; deleted non-`.v` files under the workspace `coq/` directory.
- Result: `is_prime_simple_goal_check.v` compiled successfully and no non-`.v` files remain under the workspace `coq/` directory.
