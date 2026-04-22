# Issues

## 2026-04-20 annotation: loop needed prefix-count invariant

Symptom: the active annotated C initially had no `Inv` or loop-exit `Assert`, so the `while (1)` scan had no persistent relation between `i`, `cnt`, the string heap, and `string_count_digits_spec(l)`.

Trigger: verifying `annotated/verify_20260420_185755_string_count_digits.c` before adding loop annotations.

Location: `annotated/verify_20260420_185755_string_count_digits.c`, at the `while (1)` loop and immediately after it.

Fix: added an existential prefix/suffix invariant `exists l1 l2` with `l == app(l1, l2)`, `Zlength(l1) == i`, `cnt == string_count_digits_spec(l1)`, unchanged `s`, the nonzero-prefix fact, and the full `CharArray::full` heap. Added a loop-exit assertion recording `i == n`, unchanged heap, and `cnt == string_count_digits_spec(l)`.

Result: `symexec` completed successfully and generated `string_count_digits_goal.v`, `string_count_digits_proof_auto.v`, `string_count_digits_proof_manual.v`, and `string_count_digits_goal_check.v`.

## 2026-04-20 proof: generated manual witnesses were admitted

Symptom: `coq/generated/string_count_digits_proof_manual.v` contained six generated `Proof. Admitted.` placeholders: `safety_wit_7`, `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, `entail_wit_2_3`, and `entail_wit_3`.

Trigger: after successful symbolic execution.

Location: `output/verify_20260420_185755_string_count_digits/coq/generated/string_count_digits_proof_manual.v`.

Fix: added `string_count_digits_spec_range` and `string_count_digits_spec_app_single`, then completed each witness proof by adapting the stable string-counting prefix/suffix proof pattern to the digit range `48 <= x <= 57`.

Result: `string_count_digits_proof_manual.v` compiled, and a search for `Admitted.` in the manual file returned no matches.

## 2026-04-20 compile: first compile attempt used wrong working directory

Symptom: the first Coq compile attempt produced `Cannot find a physical path bound to logical path int_auto with prefix AUXLib` and warnings such as `Cannot open auxlibs`.

Trigger: running the compile template from `/home/yangfp/QualifiedCProgramming`, where the relative `-R auxlibs AUXLib` path does not exist in this checkout.

Location: `logs/compile.log` was overwritten by the corrected successful compile; the initial failure was observed before rerunning.

Fix: reran the same compile template from `/home/yangfp/QualifiedCProgramming/SeparationLogic`, where `auxlibs`, `unifysl`, `sets`, `examples`, and the other load-path directories exist.

Result: `original/string_count_digits.v`, `string_count_digits_goal.v`, `string_count_digits_proof_auto.v`, `string_count_digits_proof_manual.v`, and `string_count_digits_goal_check.v` all compiled successfully.
