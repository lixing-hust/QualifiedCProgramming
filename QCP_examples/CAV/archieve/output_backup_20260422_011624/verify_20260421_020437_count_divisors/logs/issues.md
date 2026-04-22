# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes

## Issue 1: missing loop invariant for divisor-count prefix

- Phenomenon: the active annotated C initially matched the input C and had no invariant for `for (d = 1; d <= n; ++d)`, so the verifier had no loop-head summary connecting `cnt` to the final `count_divisors_spec(n@pre)` postcondition.
- Trigger: `cnt` is updated conditionally inside the loop, while the postcondition describes the full range `1..n`.
- Localization: `annotated/verify_20260421_020437_count_divisors.c`, immediately before the `for` loop.
- Fix: added an invariant with `1 <= d && d <= n + 1`, `n == n@pre`, and `cnt == count_divisors_prefix(n, d - 1)`, plus a loop-exit assertion bridging `d == n + 1` and `cnt == count_divisors_spec(n)`.
- Result: after the later helper-name fixes, `symexec` generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Issue 2: annotation referenced an undeclared Coq helper

- Phenomenon: the first `symexec` run after adding the invariant failed with `Use of undeclared identifier 'count_divisors_upto'`.
- Trigger: the invariant needed the input V helper for a partial divisor count, but only `count_divisors_spec` had an `Extern Coq` declaration in the C annotation.
- Localization: `logs/qcp_run.log` from the failed run and the invariant in `annotated/verify_20260421_020437_count_divisors.c`.
- Fix: first attempted to expose `count_divisors_upto`, then found the next parser issue described below.
- Result: this identified that the partial-count helper had to be made parser-friendly for C annotations.

## Issue 3: annotation parser rejected `Z.to_nat`

- Phenomenon: after exposing `count_divisors_upto`, `symexec` failed with `Use of undeclared identifier 'Z'` at the invariant expression `Z.to_nat(d - 1)`.
- Trigger: the C annotation frontend did not accept the module-qualified Coq function name in an annotation expression.
- Localization: `logs/qcp_run.log` from the second failed run and the invariant in `annotated/verify_20260421_020437_count_divisors.c`.
- Fix: added workspace-local dependency `coq/deps/count_divisors_verify_aux.v` defining `count_divisors_prefix (n limit : Z) := count_divisors_upto n (Z.to_nat limit)`, imported it in the annotated C, and changed the invariant to use `count_divisors_prefix(n, d - 1)`.
- Result: rerunning `symexec` succeeded and `logs/qcp_run.log` ended with `Successfully finished symbolic execution`.

## Issue 4: manual proof needed explicit nat/Z normalization

- Phenomenon: the first manual proof compile failed in `count_divisors_upto_bounds` with `Cannot find witness`.
- Trigger: after simplification, Coq exposed `Z.pos (Pos.of_succ_nat fuel)` rather than a form `lia` could directly relate to `Z.of_nat fuel + 1`.
- Localization: `coq/generated/count_divisors_proof_manual.v`, helper lemma `count_divisors_upto_bounds`.
- Fix: explicitly changed the successor form back to `Z.of_nat (S fuel)` and rewrote `Nat2Z.inj_succ` before calling `lia`.
- Result: the bounds helper compiled.

## Issue 5: step lemmas needed controlled rewriting

- Phenomenon: proof attempts for the loop-preservation witnesses failed while rewriting `count_divisors_prefix_step_hit` and `count_divisors_prefix_step_miss`.
- Trigger: unrestricted `rewrite` tried to use the step lemma on the old prefix expression as well as the new one, producing side conditions such as `1 <= d - 1`; Coq also needed explicit conversion between `Z.to_nat d`, `S (Z.to_nat (d - 1))`, and the generated successor-positive divisor term.
- Localization: `coq/generated/count_divisors_proof_manual.v`, helper lemmas `Z_to_nat_succ_pred`, `count_divisors_prefix_step_hit`, `count_divisors_prefix_step_miss`, and witnesses `proof_of_count_divisors_entail_wit_2_1` / `_2_2`.
- Fix: added `Z_to_nat_succ_pred`, normalized the generated divisor term back to `d`, asserted the step equation separately in each witness, and rewrote only the new prefix expression.
- Result: `count_divisors_proof_manual.v` compiled without `Admitted.` or added `Axiom`.

## Issue 6: compile script initially did not fail fast

- Phenomenon: an early compile command continued to `goal_check.v` after `proof_manual.v` had already failed, leaving a confusing secondary load-path error for `count_divisors_proof_manual`.
- Trigger: the shell block did not use `set -e`.
- Localization: `logs/coq_compile.log` from the first compile attempt.
- Fix: reran the documented compile sequence with `set -e` so the first real error was reported.
- Result: subsequent compile iterations targeted the actual proof failures; the final fail-fast compile completed successfully.

## Issue 7: Coq intermediate files produced by successful compilation

- Phenomenon: successful Coq compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`, `coq/deps/`, and `original/`.
- Trigger: normal `coqc` output.
- Localization: `output/verify_20260421_020437_count_divisors/`.
- Fix: deleted all non-`.v` files under the workspace `coq/` tree after the final successful compile, and removed the generated non-source Coq intermediates from `original/` while preserving `original/count_divisors.c` and `original/count_divisors.v`.
- Result: only source `.v` files remain under `coq/`, and `original/` contains only the source C/V inputs.
