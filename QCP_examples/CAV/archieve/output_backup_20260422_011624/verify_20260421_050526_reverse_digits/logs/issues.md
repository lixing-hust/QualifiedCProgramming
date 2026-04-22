# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes

## Issue 1: missing loop invariant for accumulator digit reversal

- Phenomenon: the active annotated C initially matched `input/reverse_digits.c` and had no invariant for `while (n > 0)`, so the verifier had no loop-head relation between the shrinking `n`, the accumulator `ans`, and the original value `n@pre`.
- Trigger: the postcondition is stated with `reverse_digits_z(n@pre)`, but the loop body mutates both `ans` and `n`.
- Localization: `annotated/verify_20260421_050526_reverse_digits.c`, immediately before the `while` loop.
- Fix: added a loop invariant preserving integer bounds, `ans <= reverse_digits_z(n@pre)`, the final overflow guard, and the semantic relation `reverse_digits_acc_z(n, ans) == reverse_digits_z(n@pre)`. Added a loop-exit assertion fixing `n == 0` and `ans == reverse_digits_z(n@pre)`.
- Result: after adding the helper module described below, `symexec` completed and regenerated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Issue 2: annotation needed a parser-friendly accumulator helper

- Phenomenon: the useful state relation is naturally `reverse_digits_fuel n ans (Z.to_nat n)`, but previous scalar-fuel tasks showed the annotation frontend rejects direct `Z.to_nat` expressions.
- Trigger: `input/reverse_digits.v` exposes `reverse_digits_fuel`, but the C annotation language is more stable with first-order `Z -> Z -> Z` helper symbols.
- Localization: invariant in `annotated/verify_20260421_050526_reverse_digits.c`.
- Fix: added `coq/deps/reverse_digits_verify_aux.v` with `reverse_digits_acc_z (n acc : Z) := reverse_digits_fuel n acc (Z.to_nat n)`, imported it in the annotated C, and used `reverse_digits_acc_z(n, ans)` in the invariant.
- Result: `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` succeeded; `logs/qcp_run.log` ends with `Successfully finished symbolic execution`.

## Issue 3: manual proof required fuel-stability and accumulator lemmas

- Phenomenon: `coq/generated/reverse_digits_proof_manual.v` contained five generated `Admitted.` placeholders after successful symbolic execution: `safety_wit_3`, `safety_wit_5`, `entail_wit_1`, `entail_wit_2`, and `entail_wit_3`.
- Trigger: auto proof could not unfold the fuel-bounded accumulator relation or prove the assignment overflow bounds from the final result guard.
- Localization: `output/verify_20260421_050526_reverse_digits/coq/generated/reverse_digits_proof_manual.v`.
- Fix: added local helper lemmas for nonpositive fuel, quotient decrease, remainder bounds, fuel stability beyond `Z.to_nat`, one positive loop step, zero exit, initialization, and accumulator monotonicity. Used these lemmas to prove the five manual witnesses.
- Result: `reverse_digits_proof_manual.v` compiles and contains no `Admitted.`; it adds no `Axiom`.

## Issue 4: proof scripts had to match generated subgoal order

- Phenomenon: early compile attempts failed with errors including `IHfuel was not found`, rejected induction intro-pattern syntax, `Cannot find witness`, and `Wrong bullet -: No more goals`.
- Trigger: the Coq version accepts older induction syntax more reliably, and `entailer!` generated pure conjunct subgoals in an order different from the displayed entailment order for several witnesses.
- Localization: `logs/coq_compile.log` during proof iterations; helper lemma `reverse_digits_fuel_acc_ge`; witnesses `proof_of_reverse_digits_safety_wit_3`, `proof_of_reverse_digits_safety_wit_5`, `proof_of_reverse_digits_entail_wit_1`, `proof_of_reverse_digits_entail_wit_2`, and `proof_of_reverse_digits_entail_wit_3`.
- Fix: closed the induction base case before using `IHfuel`, avoided unsupported newer induction patterns, used `coqtop` to inspect the exact post-`entailer!` subgoal order, and reordered proof bullets accordingly.
- Result: the final compile replay completed successfully through `reverse_digits_goal_check.v`.

## Issue 5: Coq intermediate cleanup

- Phenomenon: successful compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/deps/` and `coq/generated/`.
- Trigger: normal `coqc` output.
- Localization: `output/verify_20260421_050526_reverse_digits/coq/`.
- Fix: deleted all non-`.v` files under the workspace `coq/` directory after the final successful compile.
- Result: only source `.v` files remain under `coq/`.
