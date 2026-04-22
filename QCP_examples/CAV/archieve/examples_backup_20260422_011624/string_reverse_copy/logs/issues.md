# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes

## Symexec invocation and annotation alignment

- Phenomenon: the first manual `symexec` retry failed before producing useful VC output.
- Trigger: the first shell invocation had broken command quoting.
- Localization: `logs/qcp_run.log`
- Fix:
  - reran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` with the canonical `--flag=value` form
  - passed explicit output paths for:
    - `--goal-file`
    - `--proof-auto-file`
    - `--proof-manual-file`
    - `--input-file`
    - `--coq-logic-path=SimpleC.EE.CAV.verify_20260418_195028_string_reverse_copy`
    - `--no-exec-info`
    - `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`
- Result: the next run reached symbolic execution on the current annotated file.

## Exit assertion blocked the final char write

- Phenomenon: the first real symbolic run failed with:
  - `Assign Exec fail in .../annotated/verify_20260418_195028_string_reverse_copy.c:47:4`
- Trigger: I had inserted a loop-exit `Assert` that re-packed `dst` as a full array immediately before `dst[n] = 0`.
- Diagnosis:
  - the loop invariant itself was already sufficient
  - nearby successful char-array examples (`string_copy`, `string_set_a`) let the verifier derive the final writable cell directly from loop exit
  - the explicit exit assertion over-constrained the final control point instead of helping it
- Fix:
  - removed the exit assertion
  - kept the loop invariant that tracks:
    - `0 <= i <= n`
    - unchanged parameters
    - a split destination list
    - the processed-prefix relation `l1[k] = l[n - 1 - k]`
  - cleared generated files and reran `symexec`
- Result:
  - `qcp_run.log` ended with `Successfully finished symbolic execution`
  - fresh `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` were generated from the latest annotated file

## Manual proof normalization bug in the loop-step witness

- Phenomenon: the first `coqc` pass on `string_reverse_copy_proof_manual.v` failed in `proof_of_string_reverse_copy_entail_wit_2`.
- Trigger: the proof incorrectly normalized the mirrored source read with `app_Znth2`, as if the read index had already crossed into the final `0 :: nil` suffix.
- Diagnosis:
  - for `i < n_pre`, the mirrored index `n_pre - 1 - i` is still inside `l`
  - the correct rewrite is `app_Znth1`
- Fix:
  - switched the proof to `app_Znth1`
  - kept the rest of the `replace_Znth_app_r` / `replace_Znth_nothing` normalization pattern
- Result: `entail_wit_2` compiled and the remaining failures moved to the return witness only.

## Return witness needed an explicit reverse-index helper

- Phenomenon: `proof_of_string_reverse_copy_return_wit_1` initially failed after the `i = n_pre` step because the proof still needed to identify `l1` with `rev l`.
- Trigger: the invariant stores the processed destination prefix pointwise as `l1[k] = l[n_pre - 1 - k]`, but the postcondition is phrased using `rev l`.
- Fix:
  - added a local helper lemma:
    - `Znth_rev_Z`
  - used `list_eq_ext` plus that helper to prove `l1 = rev l`
- Result: the proof moved from the list-extensionality step to the final `replace_Znth` normalization.

## Final `replace_Znth` normalization needed proof-state inspection

- Phenomenon: repeated compile attempts on `return_wit_1` ended with an incomplete final goal even though the high-level argument was correct.
- Trigger:
  - some edits were normalizing the wrong length term
  - others rewrote terms that were no longer present after earlier proof steps
- Localization:
  - file: `coq/generated/string_reverse_copy_proof_manual.v`
  - lemma: `proof_of_string_reverse_copy_return_wit_1`
- Diagnosis process:
  - used `coqtop` to inspect the exact final goal before `Qed`
  - confirmed the residual target was the final shape:
    - `CharArray.full dst_pre ... (replace_Znth n_pre 0 (rev l ++ x :: nil))`
    - versus
    - `CharArray.full dst_pre ... (rev l ++ 0 :: nil)`
- Fix chain:
  - keep the suffix witness as exactly one cell `x :: nil`
  - use:
    - `replace_Znth_app_r`
    - `replace_Znth_nothing`
    - `replace (n_pre - Zlength (rev l)) with 0 by lia`
    - `replace (Z.to_nat (n_pre - Zlength (rev l))) with 0%nat by lia`
  - finish with `simpl; entailer!`
- Result:
  - `string_reverse_copy_proof_manual.v` compiled
  - `string_reverse_copy_goal_check.v` compiled

## Compile replay and workspace cleanup

- Phenomenon: one intermediate compile replay produced a logical-path mismatch:
  - `contains library string_reverse_copy_goal and not library SimpleC.EE.CAV.verify_20260418_195028_string_reverse_copy.string_reverse_copy_goal`
- Trigger: I had compiled `goal.v` once without the workspace `-R "$GEN" "$LP"` path, which produced the wrong logical library name for the generated `.vo`.
- Fix:
  - deleted generated non-`.v` artifacts under `coq/`
  - reran the compile chain with the correct workspace `-R` path on every generated file
- Result:
  - `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compiled successfully
  - remaining non-`.v` files under `coq/` were deleted after the successful replay

## Final outcome

- `symexec` succeeded on the current annotated file.
- `string_reverse_copy_goal.v`, `string_reverse_copy_proof_auto.v`, `string_reverse_copy_proof_manual.v`, and `string_reverse_copy_goal_check.v` all compiled successfully.
- `string_reverse_copy_proof_manual.v` contains no `Admitted.` and no user-added `Axiom`.
- Only `.v` files remain under `coq/`.
