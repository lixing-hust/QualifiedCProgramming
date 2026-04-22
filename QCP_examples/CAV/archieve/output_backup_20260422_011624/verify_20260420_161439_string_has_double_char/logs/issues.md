# Issues

## Fingerprint placeholder

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the workspace had been initialized before semantic metadata was filled in.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_161439_string_has_double_char/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled in a non-empty description and controlled-vocabulary keywords for a read-only string search with loop-invariant, case-split, termination-bound, and heap-preservation proof patterns.
- Result: the fingerprint now has non-empty semantic metadata and, after final verification, records `goal_check_passed` and `proof_check_passed`.

## Missing loop invariant

- Phenomenon: the active annotated C copy initially had no invariant for the `while (1)` scan.
- Trigger: `string_has_double_char` scans adjacent pairs with an index `i`; without a loop-head summary, symbolic execution has no stable relation between `i` and the already-checked prefix.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_161439_string_has_double_char.c`.
- Fix: added a loop invariant with `0 <= i && i <= n`, `s == s@pre`, the nonzero-prefix contract fact, the processed-prefix adjacent-inequality property, and preserved `CharArray::full`.
- Result: the invariant made the loop semantics explicit, but the first symexec attempt still exposed a local bound bridge gap before reading `s[i + 1]`.

## Bridge assertion for `s[i + 1]`

- Phenomenon: the first `symexec` attempt failed with `Cannot derive the precondition of Memory Read` at `annotated/verify_20260420_161439_string_has_double_char.c:32`, the read of `s[i + 1]`.
- Trigger: after passing the `s[i] == 0` guard, the verifier did not derive `i + 1 <= n` automatically from `s[i] != 0` and the nonzero-prefix fact.
- Localization: `logs/qcp_run.log` from the failed run and the read point in the annotated C file.
- Fix: added a bridge `Assert` immediately after the first guard, restating `i + 1 <= n` along with the preserved heap and prefix facts.
- Result: the next `symexec` run generated Coq artifacts successfully.

## Bridge assertion initially dropped `n` range facts

- Phenomenon: after the first successful VC generation, manual inspection showed impossible or unnecessarily hard witnesses such as `safety_wit_4`, `safety_wit_7`, `safety_wit_10`, and `entail_wit_3` lacking `0 <= n` and `n < INT_MAX` in their premises.
- Trigger: the bridge assertion introduced for `s[i + 1]` had not preserved those stable contract facts.
- Localization: generated `string_has_double_char_goal.v` after the second symexec run.
- Fix: strengthened the bridge assertion with `0 <= n && n < INT_MAX`, then cleared generated files and reran `symexec`.
- Result: the regenerated manual proof file shrank to five semantic obligations: `entail_wit_2`, `entail_wit_3`, and three return witnesses.

## Manual proof obligations

- Phenomenon: `string_has_double_char_proof_manual.v` contained generated `Admitted.` placeholders.
- Trigger: the remaining obligations required pure reasoning about the terminator position, adjacent-pair processed-prefix preservation, and the disjunctive postcondition.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_161439_string_has_double_char/coq/generated/string_has_double_char_proof_manual.v`.
- Fix: proved `entail_wit_2` by deriving `Zlength l = n` from `CharArray.full_length` and forcing `i < n`; proved `entail_wit_3` by splitting `j < i + 1` into old-prefix and current-pair cases; proved return witnesses by deriving `i + 1 = n` or `i = n` from the terminator and using the processed-prefix invariant, or by using the current equal pair as the existential witness.
- Result: `proof_manual.v` compiles and contains no `Admitted.` and no newly added `Axiom`.

## Fragile generated hypothesis names

- Phenomenon: early proof scripts failed by applying unrelated hypotheses such as `n < INT_MAX` where the processed-prefix or nonzero-prefix fact was needed.
- Trigger: the proof scripts initially relied on generated names like `H3` and `H4`, which changed across proof shapes.
- Localization: compile failures in `proof_of_string_has_double_char_entail_wit_3` and `proof_of_string_has_double_char_return_wit_2`.
- Fix: replaced fragile hypothesis-name uses with `match goal` patterns that select hypotheses by their type shape.
- Result: the manual proof became stable under the current generated VC order.

## Disjunctive return witness proof shape

- Phenomenon: `return_wit_1` and `return_wit_2` initially failed after branch selection with model-level disjunction/conjunction goals; errors included a `derivable1s_exp_r` type mismatch and `No product even after head-reduction`.
- Trigger: the script mixed `pre_process`/`entailer!` with ordinary Coq branch and existential introductions in a goal that had already become model-level.
- Localization: `string_has_double_char_proof_manual.v` around `proof_of_string_has_double_char_return_wit_1` and `proof_of_string_has_double_char_return_wit_2`.
- Fix: used direct `intros; Intros` for return witnesses, lower-case `exists` for the model-level existential branch, and explicit `unfold andp, coq_prop; simpl; repeat split` where `entailer!` left model-level conjunctions.
- Result: all return witnesses compiled.

## Full replay and cleanup

- Phenomenon: completion required a full replay, not only individual `proof_manual.v` compilation.
- Trigger: verify completion requires `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile with the workspace load path.
- Localization: `logs/compile.log`.
- Fix: compiled the four generated files using the documented `COMPILE.md` template from `/home/yangfp/QualifiedCProgramming/SeparationLogic`, then removed all non-`.v` files under `coq/`.
- Result: `goal_check.v` compiled successfully, `proof_manual.v` has no `Admitted.` or added `Axiom`, and `coq/` contains only `.v` source files.
