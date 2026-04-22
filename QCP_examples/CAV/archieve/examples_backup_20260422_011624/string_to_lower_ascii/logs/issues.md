# Verify Issues

## Issue 1: workspace fingerprint had empty retrieval fields

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the workspace was bootstrapped before this manual continuation and only contained the original inputs and bootstrap logs.
- Localization: `output/verify_20260420_155956_string_to_lower_ascii/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled the semantic description and controlled-vocabulary keywords for an in-place string update over a null-terminated `CharArray::full`.
- Result: the fingerprint now includes non-empty semantics and `verification_status: goal_check_passed`.

## Issue 2: active annotated C lacked the loop invariant

- Phenomenon: the active annotated file had a `while (1)` scan loop with no `Inv`.
- Trigger: `string_to_lower_ascii` updates the buffer in place, so symbolic execution needs a loop-head summary of the transformed prefix, original suffix, and terminator.
- Localization: `annotated/verify_20260420_155956_string_to_lower_ascii.c`, immediately before the `while (1)` loop.
- Fix: added an existential split invariant over `l1` and `l2`, preserving `l == app(l1, l2)`, `Zlength(l) == n`, `Zlength(l1) == i`, `Zlength(l2) == n - i`, the nonzero-prefix contract fact, and the current buffer as `app(app(string_to_lower_ascii_spec(l1), l2), cons(0, nil))`.
- Result: a clean `symexec` run completed and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Issue 3: initialization witness had an extra post-`entailer!` script

- Phenomenon: the first compile attempt failed in `string_to_lower_ascii_proof_manual.v` at line 131 with `Error: No such goal.`
- Trigger: the proof was adapted from the older upper-case example, but this generated initialization witness was already fully closed by `entailer!`.
- Localization: `coq/generated/string_to_lower_ascii_proof_manual.v`, lemma `proof_of_string_to_lower_ascii_entail_wit_1`.
- Fix: removed the stale length-rewrite steps after `entailer!`.
- Result: compilation advanced to the loop-preservation witnesses.

## Issue 4: generated hypothesis names differed from the reused proof pattern

- Phenomenon: repeated compile attempts failed with errors such as `Found no subterm matching "Zlength nil" in H7` or `H8`.
- Trigger: this task's invariant includes an explicit `Zlength(l) == n`, so generated pure hypothesis numbering differs from the `string_to_upper_ascii` example.
- Localization: `coq/generated/string_to_lower_ascii_proof_manual.v`, lemmas `proof_of_string_to_lower_ascii_entail_wit_2_1`, `_2_2`, `_2_3`, and `proof_of_string_to_lower_ascii_return_wit_1`.
- Fix: used `coqtop` to inspect the actual contexts, then updated references to the split, prefix-length, suffix-length, and nonzero hypotheses.
- Result: `string_to_lower_ascii_proof_manual.v` compiled.

## Final Outcome

- `symexec` succeeded on the latest active annotated C file.
- `string_to_lower_ascii_goal.v`, `string_to_lower_ascii_proof_auto.v`, `string_to_lower_ascii_proof_manual.v`, and `string_to_lower_ascii_goal_check.v` all compiled with the required load-path template.
- `string_to_lower_ascii_proof_manual.v` contains no `Admitted.` and no added `Axiom`.
- Non-`.v` files under `coq/` were deleted after the successful compile replay.
