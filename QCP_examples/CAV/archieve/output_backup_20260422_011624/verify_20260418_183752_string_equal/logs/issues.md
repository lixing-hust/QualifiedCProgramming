# Verify Issues

## Issue 1: post-loop `Assert` originally used concrete array reads

- Phenomenon:
  - the first manual `symexec` retry failed with:
    - `fatal error: Cannot infer size of array`
- Trigger:
  - the post-loop assertion restated the break condition as `a[i] == 0 || b[i] == 0`
- Localization:
  - active annotated file: `annotated/verify_20260418_183752_string_equal.c`
  - failing line: the first post-loop `Assert`
- Diagnosis:
  - this frontend is unstable when `Assert` formulas re-read concrete array cells directly
  - the right layer for this fact is the pure index/list consequence, not another concrete array access
- Fix:
  - replace that assertion fragment with the semantic consequence `i == na || i == nb`
- Result:
  - the parser got past the array-size inference failure

## Issue 2: bracket notation in the quantified prefix invariant was not translated robustly

- Phenomenon:
  - the next `symexec` run failed with:
    - `The array j_107 of Znth is not a list type.`
- Trigger:
  - the quantified prefix-equality invariant used `la[j] == lb[j]`
- Localization:
  - active annotated file: `annotated/verify_20260418_183752_string_equal.c`
  - affected formulas: loop invariant and exit/branch assertions
- Diagnosis:
  - in this char-array task, bracket notation inside the quantified annotation was not normalized stably
  - the generated Coq files already use explicit `Znth`, so the annotation should match that form directly
- Fix:
  - rewrite the quantified prefix-equality formulas to `Znth(j, la, 0) == Znth(j, lb, 0)`
- Result:
  - `symexec` completed successfully and generated fresh Coq artifacts

## Issue 3: the first generated exit witnesses dropped the nonzero-prefix contract facts

- Phenomenon:
  - the first generated `entail_wit_4_1` / `entail_wit_4_2` obligations tried to prove `na = nb` without carrying the original “all earlier characters are nonzero” assumptions
- Trigger:
  - the initial loop-exit and branch-local assertions only kept bounds, prefix equality, and ownership
- Localization:
  - generated file: `output/verify_20260418_183752_string_equal/coq/generated/string_equal_goal.v`
- Diagnosis:
  - this was an annotation-layer information-loss bug
  - without those preserved nonzero-prefix facts, the exit witnesses were too weak for a correct manual proof
- Fix:
  - add both preserved contract facts
    - `forall k < na, Znth(k, la, 0) != 0`
    - `forall k < nb, Znth(k, lb, 0) != 0`
  - to the loop invariant, the loop-exit assertion, and the `return 1` branch assertion
  - clear generated files and rerun `symexec`
- Result:
  - the regenerated `goal.v` kept the expected nonzero-prefix information in `entail_wit_4_1`, `entail_wit_4_2`, `return_wit_3`, and `return_wit_4`

## Issue 4: manual proof helper layer still fails before witness replay completes

- Phenomenon:
  - compiling `string_equal_proof_manual.v` still fails
- Trigger:
  - the active proof file mixes partial helper-lemma progress with witness scripts that still need to be rewritten into the repository’s stable `pre_process` style
- Localization:
  - file: `output/verify_20260418_183752_string_equal/coq/generated/string_equal_proof_manual.v`
  - latest compile log: `output/verify_20260418_183752_string_equal/logs/compile_proof_manual.log`
- Diagnosis:
  - several early failures were pure Coq-compatibility issues:
    - older-parser rejection of `induction ... as ...`
    - `Znth` rewriting side conditions needing explicit arithmetic facts
    - helper lemmas needing explicit normalization instead of relying on automation
  - after those fixes, the remaining blocker is that the witness proofs themselves still need a full `pre_process`-based rewrite
- Fix actions attempted:
  - added helper lemmas for:
    - the appended terminator index
    - “first zero is at the logical end”
    - `string_equal_spec` symmetry, equality, mismatch, and shorter-string cases
  - repeatedly recompiled `proof_manual.v` and corrected the first stable helper-lemma failures
  - removed all `Admitted.` placeholders from the active `proof_manual.v`
- Result:
  - progress exists in the helper layer
  - but `proof_manual.v` still does not compile, so `goal_check.v` has not been replayed successfully

## Final state

- `symexec` succeeds on the current annotated file.
- The generated Coq files are aligned with the current annotations.
- `string_equal_proof_manual.v` contains no `Admitted.` placeholders, but it still does not compile.
- `goal_check.v` was therefore not compiled successfully end to end.
- Non-`.v` Coq intermediates under the workspace were cleaned before closing the failed run.
