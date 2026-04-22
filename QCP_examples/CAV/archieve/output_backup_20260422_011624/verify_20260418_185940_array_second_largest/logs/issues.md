# Issues

## Summary

- Status: failed
- Blocking issues: unresolved manual proof
- Annotation changes required: yes
- Manual proof required: yes

## Issue 1: first invariant used an undeclared helper symbol

- Phenomenon:
  - the first `symexec` retry stopped with:
    - `Use of undeclared identifier 'max_list_nonempty'`
- Trigger:
  - the initial loop invariant mentioned `max_list_nonempty`, but this task’s annotated input only declared `second_largest_list`
- Localization:
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260418_185940_array_second_largest.c`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_185940_array_second_largest/logs/qcp_run.log`
- Diagnosis:
  - the frontend could parse the file structure, but the annotation language for this task had no visible declaration for that helper
- Fix:
  - added `Extern Coq (second_largest_acc : Z -> Z -> list Z -> Z)`
  - replaced the invariant with:
    - `second_largest_acc(max1, max2, sublist(i, n, l)) == second_largest_list(l)`
- Result:
  - rerunning `symexec` succeeded and generated fresh `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`

## Issue 2: manual proof hit several Coq-environment compatibility problems before the real semantic blocker

- Phenomenon:
  - the first `coqc` pass on `array_second_largest_proof_manual.v` failed on proof-script syntax and then on guessed library-lemma names / exact-match rewrites
- Trigger:
  - the initial helper proofs used newer destruct syntax and a guessed sublist helper name
- Localization:
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_185940_array_second_largest/coq/generated/array_second_largest_proof_manual.v`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_185940_array_second_largest/logs/compile_proof_manual.log`
- Diagnosis:
  - this Coq environment rejects some `destruct ... as ...` forms used inline with bullets
  - the sublist normalization needed the exact intermediate shape revealed by `coqtop`:
    - `sublist (2 - 1) (Zlength (x1 :: x2 :: xs) - 1) (x2 :: xs)`
  - side conditions for `sublist_cons2` also had to be proved explicitly instead of delegated to `lia`
- Fix chain:
  - rewrote the destructs into the repository’s more conservative style
  - removed the non-existent helper name
  - switched to two explicit `sublist_cons2` rewrites plus `sublist_self`
  - normalized the intermediate index `2 - 1` explicitly
- Result:
  - the initialization helper lemmas progressed much further, and the compile blocker moved deeper into the proof

## Issue 3: verification still blocks in the contradiction branch of `second_largest_list_init_le`

- Phenomenon:
  - the current compile pass still fails in `array_second_largest_proof_manual.v` with:
    - `Cannot find witness`
- Trigger:
  - the branch where `Z_gt_dec x2 x1` returns `left` must be discharged under the opposite initialization hypothesis `Znth 1 l 0 <= Znth 0 l 0`
- Localization:
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_185940_array_second_largest/coq/generated/array_second_largest_proof_manual.v:172`
- Diagnosis:
  - this is a manual-proof contradiction step, not a symbolic-execution or ownership problem
  - the current proof script has already reduced the goal to the branch comparison, but the environment is still not accepting the contradiction closure as written
- Fix attempts:
  - `lia`
  - `exfalso` plus branch-local contradiction synthesis
  - direct use of the `Z_gt_dec` branch fact
- Result:
  - unresolved
  - `proof_manual.v` does not compile
  - `goal_check.v` was not recompiled successfully end to end after the proof failure

## Final outcome

- `symexec` succeeded on the current annotated file.
- `array_second_largest_goal.v` and `array_second_largest_proof_auto.v` compiled successfully.
- `array_second_largest_proof_manual.v` still fails to compile.
- `array_second_largest_goal_check.v` was not compiled successfully in the final replay.
- `array_second_largest_proof_manual.v` currently contains no `Admitted.` and no added `Axiom`, but the workspace is still incomplete because the compile chain does not pass.
- Non-`.v` files under `coq/` were deleted after the final failed compile pass.
