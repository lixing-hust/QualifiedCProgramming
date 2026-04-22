# Issues

## Summary

- Status: completed
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes

## Issue 1: first manual `symexec` call used the wrong flag form

- Phenomenon:
  - `qcp_run.log` only contained:
    - `goal file not specified`
    - `Start to symbolic execution on program : (null)`
- Trigger condition:
  - the Linux `symexec` binary in this environment expects `--flag=value`, not a split `--flag value` form
- Diagnosis:
  - the verifier had not processed the annotated file yet; this was invocation shape only
- Fix:
  - rerun with explicit `=` flags for:
    - `--goal-file=...`
    - `--proof-auto-file=...`
    - `--proof-manual-file=...`
    - `--input-file=...`
- Result:
  - the next run reached parsing of the active annotated program

## Issue 2: contract binder syntax in the active annotated copy was not frontend-compatible

- Phenomenon:
  - `symexec` failed with:
    - `unexpected PT_COMMA, expecting PT_REQUIRE`
- Trigger condition:
  - the function contract used `With la, lb`
- Diagnosis:
  - this frontend accepts space-separated binders in `With`
  - the semantic contract itself did not need redesign
- Fix:
  - normalize only the active annotated copy from `With la, lb` to `With la lb`
- Result:
  - parsing advanced past the contract and into the function body

## Issue 3: loop invariant was attached to the wrong control point

- Phenomenon:
  - `symexec` then failed with:
    - `Expected loop after loop invariant`
- Trigger condition:
  - the first annotation pass placed `Inv` as the first statement inside the loop body
- Diagnosis:
  - this verifier attaches loop invariants only when the comment appears immediately before the loop statement
- Fix:
  - move the invariant block to the line directly above `for (i = 0; i < n; ++i)`
- Result:
  - `qcp_run.log` ended with `Successfully finished symbolic execution`
  - fresh `array_equal_goal.v`, `array_equal_proof_auto.v`, `array_equal_proof_manual.v`, and `array_equal_goal_check.v` were generated

## Issue 4: manual proof script needed Coq-version-compatible structure

- Phenomenon:
  - the first `coqc` pass for `array_equal_proof_manual.v` failed on proof-script syntax
- Trigger condition:
  - the helper lemmas initially used newer pattern forms such as `induction ... as [...]`
- Diagnosis:
  - this Coq environment accepts the older proof style more reliably
- Fix:
  - rewrite the helper lemmas to use:
    - `induction la.`
    - plain `destruct`
    - explicit `IHla`
- Result:
  - the helper lemmas entered semantic proof checking instead of failing at parser level

## Issue 5: return-witness proofs needed actual proof-state inspection

- Phenomenon:
  - compile-driven iterations then failed with:
    - missing induction-hypothesis names
    - `Cannot find witness`
    - incorrect assumptions about generated variable names
- Trigger condition:
  - the first witness scripts guessed context names instead of reading the generated proof state
- Diagnosis:
  - `coqtop` showed:
    - `return_wit_1` already exposed the needed pure hypotheses as `H` through `H6`
    - `return_wit_2` uses list names `la` and `lb`, not a generic `l`
    - both array lengths must be recovered explicitly from the two `IntArray.full` resources
- Fix chain:
  - replace brittle `lia` calls in `return_wit_1` with the exact hypotheses from `entailer!`
  - add helper lemmas:
    - `array_equal_spec_mismatch`
    - `array_equal_spec_equal`
  - extract both resource lengths explicitly with:
    - `prop_apply (IntArray.full_length a_pre n_pre la). Intros.`
    - `prop_apply (IntArray.full_length b_pre n_pre lb). Intros.`
  - rebuild `Zlength` equalities via `Zlength_correct` before applying the helper lemma
- Result:
  - `array_equal_proof_manual.v` compiled
  - `array_equal_goal_check.v` compiled
  - `array_equal_proof_manual.v` contains no `Admitted.` and no added `Axiom`

## Final outcome

- `symexec` succeeded on the current annotated file.
- `array_equal_goal.v`, `array_equal_proof_auto.v`, `array_equal_proof_manual.v`, and `array_equal_goal_check.v` all compiled successfully.
- `proof_manual_grep.log` is effectively empty because direct grep found no `Admitted.` or `Axiom` in `array_equal_proof_manual.v`.
- Non-`.v` files under `coq/` were removed after the successful compile replay.
