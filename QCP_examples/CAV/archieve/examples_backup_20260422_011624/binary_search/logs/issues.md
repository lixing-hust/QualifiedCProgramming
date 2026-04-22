# Issues

## Summary

- Status: completed.
- Blocking issues: resolved.
- Annotation changes required: yes.
- Manual proof required: yes.
- Final verification result: `goal_check.v` compiled successfully.

## Symexec invocation path

- Phenomenon: the first manual `symexec` invocation failed immediately with `/bin/bash: line 5: symexec: command not found`.
- Trigger: the shell `PATH` did not include the verifier binary.
- Localization: `logs/qcp_run.log` after the first attempt; command exit status `127` in `logs/metrics.md`.
- Fix: reran the same explicit-output invocation with `/home/yangfp/QualifiedCProgramming/linux-binary/symexec`.
- Result: the verifier reached the annotated program on subsequent attempts.

## Missing loop invariant and read bridges

- Phenomenon: the active annotated C initially matched the input and had no loop invariant for `while (left <= right)`.
- Trigger: binary search needs a loop-head summary for the candidate interval and the excluded lower and upper regions.
- Localization: `annotated/verify_20260420_231624_binary_search.c`, loop before the `mid` assignment.
- Fix: added a loop invariant carrying:
  - loop bounds for `left` and `right`;
  - unchanged parameters `a`, `n`, and `target`;
  - `Zlength(l) == n` and adjacent sortedness;
  - lower excluded region `j < left -> l[j] < target`;
  - upper excluded region `right < j < n -> target < l[j]`;
  - `IntArray::full(a, n, l)`.
- Result: `symexec` then reached the loop body.

## Midpoint memory-read precondition

- Phenomenon: `symexec` failed at the first read `a[mid]` with `Cannot derive the precondition of Memory Read`.
- Trigger: the verifier did not derive `0 <= mid < n` automatically from `mid = left + (right - left) / 2`.
- Localization: `annotated/verify_20260420_231624_binary_search.c:40` in the earlier annotated version.
- Fix: added bridge assertions after the `mid` assignment and after the failed equality branch, restating midpoint bounds and heap ownership.
- Result: the array-read precondition failure disappeared.

## Post-loop assertion interfered with local cleanup

- Phenomenon: after adding an explicit loop-exit assertion, `symexec` failed with `Fail to Remove Memory Permission of mid:105`.
- Trigger: the post-loop assertion was placed while local variable cleanup still had to remove the `mid` stack slot.
- Localization: `logs/qcp_run.log`, failure at the post-loop assertion in the earlier annotated version.
- Fix: removed the post-loop assertion and relied on the invariant plus the false loop condition for the final `return -1` witness.
- Result: `symexec` completed successfully after this correction.

## Right-branch strictness fact

- Phenomenon: manual proof of the right-branch invariant update could not prove the new upper excluded region from only `l[mid] >= target`.
- Trigger: the invariant requires `target < l[j]` for `j > right`, and the `j == mid` case needs strict inequality.
- Localization: generated `binary_search_entail_wit_5_1` after adding the right-branch bridge.
- Fix: added an assertion inside the `else` branch before `right = mid - 1` stating `target < l[mid]`, plus the loop bounds, sortedness, excluded-region facts, and heap ownership.
- Result: the regenerated VC gave the proof enough strictness for the branch update.

## Bridge assertions initially dropped loop bounds

- Phenomenon: `binary_search_entail_wit_5_1` still lacked facts such as `0 <= left`.
- Trigger: bridge assertions restated midpoint bounds but not the original loop bounds; each bridge becomes the current assertion for the next step.
- Localization: read and branch bridge assertions in `annotated/verify_20260420_231624_binary_search.c`.
- Fix: added `0 <= left`, `left <= n`, `-1 <= right`, `right < n`, and `left <= right + 1` to the bridge assertions.
- Result: branch-preservation VCs had the arithmetic facts needed for invariant re-establishment.

## Manual proof obligations

- Phenomenon: the final generated `binary_search_proof_manual.v` required proofs for `safety_wit_4`, `entail_wit_1`, `entail_wit_2`, `entail_wit_3`, `entail_wit_4`, `entail_wit_5_1`, and `entail_wit_5_2`.
- Trigger: midpoint division bounds, bridge assertions, and binary-search interval preservation require arithmetic and monotonicity reasoning beyond auto proof.
- Localization: `output/verify_20260420_231624_binary_search/coq/generated/binary_search_proof_manual.v`.
- Fix:
  - added `binary_search_quot2_bounds` for `(right - left) ÷ 2`;
  - added `binary_search_sorted_adjacent_mono` to chain adjacent sortedness;
  - used `store_int_range` to recover stack-slot integer ranges for midpoint safety;
  - used `store_int_undef_store_int` when changing the local `mid` slot to undef in loop-preservation entailments.
- Result: `binary_search_proof_manual.v` compiled, contains no `Admitted.`, and has no top-level `Axiom`.

## Final compile and cleanup

- Phenomenon: after final proof edits, the workspace still had Coq intermediate build products.
- Trigger: `coqc` generated `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` files under `coq/generated`.
- Localization: `output/verify_20260420_231624_binary_search/coq/generated`.
- Fix: after successful full compile replay, deleted all non-`.v` files under `coq/`.
- Result: only generated `.v` files remain under `coq/`, and the full compile replay through `binary_search_goal_check.v` succeeded.
