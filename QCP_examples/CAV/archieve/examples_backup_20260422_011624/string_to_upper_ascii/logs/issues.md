# Verify Issues

## Issue 1: workspace fingerprint initially had empty retrieval fields

- Phenomenon: `logs/workspace_fingerprint.json` was still at the script-initialized state with an empty `semantic_description` and `{}` keywords.
- Trigger: the existing workspace only contained the original inputs and bootstrap logs when this verification was resumed.
- Localization: `output/verify_20260419_084727_string_to_upper_ascii/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled a non-empty semantic description and controlled-vocabulary keywords for an in-place string update over `CharArray::full`.
- Result: the fingerprint now includes the task semantics and `verification_status: goal_check_passed`.

## Issue 2: active annotated C lacked a loop invariant

- Phenomenon: the active annotated file had a `while (1)` scan loop with no `Inv`.
- Trigger: `string_to_upper_ascii` modifies the string in place, so `symexec` needs a loop-head summary of the transformed prefix and original suffix.
- Localization: `annotated/verify_20260419_084727_string_to_upper_ascii.c`, immediately before the `while (1)` loop.
- Fix: added an existential split invariant over `l1` and `l2`, preserving `l == app(l1, l2)`, bounds on `i`, the nonzero contract fact, and the current buffer as `app(app(string_to_upper_ascii_spec(l1), l2), cons(0, nil))`.
- Result: a clean `symexec` run completed and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Issue 3: loop-initialization proof needed explicit CharArray length extraction

- Phenomenon: the first manual proof skeleton `pre_process; entailer!` failed for `proof_of_string_to_upper_ascii_entail_wit_1` with an incomplete proof; the remaining pure goal was `Zlength l = n - 0`.
- Trigger: the length of `l` is implicit in `CharArray.full s_pre (n + 1) (l ++ 0 :: nil)`, but it was not automatically exposed by `entailer!`.
- Localization: `coq/generated/string_to_upper_ascii_proof_manual.v`, lemma `proof_of_string_to_upper_ascii_entail_wit_1`.
- Fix: used `prop_apply CharArray.full_length`, then rewrote with `Zlength_app_cons` before `lia`.
- Result: the invariant initialization witness compiles.

## Issue 4: loop-preservation witnesses needed list helper lemmas

- Phenomenon: the three `entail_wit_2_*` witnesses were not solved by the default proof skeleton.
- Trigger: each branch has to split the unprocessed suffix into `x :: xs`, relate the current buffer index to `x`, and show that extending the processed prefix matches `upper_ascii_char x`.
- Localization: `coq/generated/string_to_upper_ascii_proof_manual.v`, lemmas `proof_of_string_to_upper_ascii_entail_wit_2_1`, `_2_2`, and `_2_3`.
- Fix: added local helper lemmas for `string_to_upper_ascii_spec` append/length, the three ASCII branch cases, current-head lookup after the processed prefix, lowercase replacement, and non-lowercase preservation.
- Result: all three loop-preservation witnesses compile.

## Issue 5: return witness needed the explicit `i = n` bridge

- Phenomenon: the return witness could not close directly from the invariant buffer shape.
- Trigger: the postcondition requires the full `string_to_upper_ascii_spec(l)` output, while the invariant only gives transformed prefix plus original suffix. The proof first has to show that the loop stopped at the terminator index.
- Localization: `coq/generated/string_to_upper_ascii_proof_manual.v`, lemma `proof_of_string_to_upper_ascii_return_wit_1`.
- Fix: proved `i = n` by contradiction. If `i < n`, destructing `l2` either contradicts its length or exposes a head `x` where the loop exit says `x = 0` and the preserved contract fact says `Znth i l 0 != 0`.
- Result: after substituting `i = n`, the suffix is empty and the final `CharArray.full` entailment closes.

## Final Outcome

- `symexec` succeeded on the latest annotated file.
- `string_to_upper_ascii_goal.v`, `string_to_upper_ascii_proof_auto.v`, `string_to_upper_ascii_proof_manual.v`, and `string_to_upper_ascii_goal_check.v` all compiled with the required load-path template.
- `string_to_upper_ascii_proof_manual.v` contains no `Admitted.` and no `Axiom`.
- Non-`.v` files under `coq/` were deleted after the successful compile replay.
