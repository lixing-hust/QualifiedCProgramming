# Verification Issues

## Pre-assignment assertion dropped local `s`

- Symptom: the first `symexec` run after adding the initial invariant failed with `fatal error: cannot find the program variable s(111) in assertion, please check the @pre or related which implies in annotated/verify_20260421_143138_two_sum_sorted.c:77:8`.
- Trigger: a bridge `Assert` was placed immediately before `s = a[left] + a[right]`. At that point `s` had been declared but not assigned, and the assertion restated heap and pure facts without preserving the local-variable permission for `s`.
- Location: `annotated/verify_20260421_143138_two_sum_sorted.c`, before the assignment to `s`.
- Fix: removed the pre-assignment bridge and moved the bridge to immediately after the assignment, where it states `s == l[left] + l[right]`. The branch-local assertions also keep this equality.
- Result: rerunning `symexec` succeeded and generated `two_sum_sorted_goal.v`, `two_sum_sorted_proof_auto.v`, `two_sum_sorted_proof_manual.v`, and `two_sum_sorted_goal_check.v`.

## Wrong generated logical prefix on first successful symexec

- Symptom: the first successful `symexec` invocation generated Coq files importing `SimpleC.EE.CAV.output.verify_20260421_143138_two_sum_sorted.coq.generated`, which did not match the workflow compile template.
- Trigger: the `--coq-logic-path` argument was initially set to the physical output path shape instead of the workspace logical prefix.
- Location: generated imports in `output/verify_20260421_143138_two_sum_sorted/coq/generated/*.v`.
- Fix: cleaned generated files and reran `symexec` with `--coq-logic-path=SimpleC.EE.CAV.verify_20260421_143138_two_sum_sorted`.
- Result: generated files now use the compile-template-compatible logical prefix.

## Manual proof obligations after symexec

- Symptom: generated `two_sum_sorted_proof_manual.v` contained eight `Admitted.` bodies: `safety_wit_4`, `entail_wit_1`, `entail_wit_2`, `entail_wit_3`, `entail_wit_4`, `entail_wit_5_1`, `entail_wit_5_2`, and `return_wit_2`.
- Trigger: the two-pointer invariant produced preservation and loop-exit witnesses that require explicit pure reasoning over sortedness and excluded pair regions.
- Location: `output/verify_20260421_143138_two_sum_sorted/coq/generated/two_sum_sorted_proof_manual.v`.
- Fix: replaced all manual `Admitted.` bodies. The easy bridge witnesses use `pre_process; entailer!`; `safety_wit_4` specializes the pair-sum range guard at `left` and `right`; `entail_wit_5_1` and `entail_wit_5_2` use `store_int_undef_store_int` plus monotonicity case splits; `return_wit_2` chooses the no-solution branch and proves the universal pair fact by splitting on `i < left`.
- Result: `two_sum_sorted_proof_manual.v` compiles and contains no `Admitted.` proof bodies or added axioms.

## Return witness disjunction proof shape

- Symptom: an intermediate `return_wit_2` proof using `pre_process; left; entailer!; intros ...` failed with `No product even after head-reduction`.
- Trigger: after choosing the assertion-level disjunction, the goal was still an assertion applied to a model rather than a Coq-level universal proposition.
- Location: `proof_of_two_sum_sorted_return_wit_2` in `two_sum_sorted_proof_manual.v`.
- Fix: followed the pattern from existing examples: unfold the witness, run `Intros`, choose `left`, run `entailer!`, then manually split the assertion-level conjunction and prove the pure universal fact.
- Result: `return_wit_2` compiles.

## Final compile and cleanup

- Symptom: Coq compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` artifacts under `coq/generated/`.
- Trigger: normal `coqc` output during full compile.
- Location: `output/verify_20260421_143138_two_sum_sorted/coq/generated/`.
- Fix: deleted all non-`.v` files under the workspace `coq/` directory after `goal_check.v` compiled.
- Result: only the four generated `.v` files remain under `coq/generated/`.
