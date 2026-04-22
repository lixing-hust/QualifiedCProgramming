# Issues

## Summary

- Status: success
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes

## Issue 1: the input-side Coq spec file was not structurally accepted by Coq

- Phenomenon:
  - compiling `original/array_count_increasing_steps.v` failed with Coq's structural-recursion check
- Trigger:
  - the provided definition recursed on `y :: xs`, which Coq did not recognize as a direct structural subterm in that surface form
- Diagnosis:
  - this blocked `goal.v` from importing `array_count_increasing_steps`
  - the C-side verification input itself was still usable by `symexec`
- Fix:
  - added a workspace-local replacement module:
    - `coq/deps/array_count_increasing_steps.v`
  - rewrote the same spec into a nested-match form that recurses on `xs`
  - compiled it with:
    - `-Q "$DEPS" ""`
- Result:
  - the generated Coq files could import `array_count_increasing_steps` successfully inside this workspace

## Issue 2: richer invariant syntax initially failed in the frontend

- Phenomenon:
  - early annotation retries failed before useful VC generation
- Trigger chain:
  - `Z.min(...)` inside the invariant was parsed as an undeclared identifier
  - a loop-level disjunction for the whole semantic summary caused:
    - `The number of now assertions and loop inv pre assertions does not match`
- Diagnosis:
  - this frontend was fragile around richer loop-head syntax, especially top-level disjunctions
- Fix:
  - kept the semantic summary in the stable form:
    - `cnt == array_count_increasing_steps_spec(sublist(0, i + 1, l))`
  - eventually replaced the rejected disjunction with the implication-form reachable-state fact:
    - `0 < n => i + 1 <= n`
- Result:
  - `symexec` completed successfully on the current annotated file
  - the generated VCs carried the needed loop-head arithmetic fact in a proof-friendly shape

## Issue 3: a first stronger invariant candidate was accepted but not inductive

- Phenomenon:
  - adding `i + 1 <= INT_MAX` removed the old `safety_wit_3` blocker, but the next compile replay still failed in the loop-step witness
- Trigger:
  - the regenerated `entail_wit_2_1` needed the next-head fact `i + 2 <= INT_MAX`
  - the step witness did not expose an explicit pure bound on `n_pre`
- Diagnosis:
  - the direct machine-range fact was useful for the current head but too weak as an inductive loop summary
- Fix:
  - replaced that clause with the inductive implication:
    - `0 < n => i + 1 <= n`
- Result:
  - the regenerated witnesses became inductive and the proof could proceed

## Issue 4: stale compiled artifacts briefly masked the new VC shape

- Phenomenon:
  - after rerunning `symexec`, one compile replay still showed proof states from the pre-retry VC
- Trigger:
  - old non-`.v` files under `coq/generated/` were still present and could be reused by Coq
- Diagnosis:
  - the regenerated source files were correct, but the compiled artifacts were stale
- Fix:
  - deleted all non-`.v` files under:
    - `coq/generated/`
    - `coq/deps/`
  - recompiled in the canonical order:
    - `deps`
    - `goal`
    - `proof_auto`
    - `proof_manual`
    - `goal_check`
- Result:
  - the proof state matched the current implication-form invariant, and the replay became reliable

## Issue 5: manual proof needed local helper lemmas and one extra `store_int_range`

- Phenomenon:
  - the regenerated `proof_manual.v` still had nontrivial witnesses after `symexec`
- Fix chain:
  - restored local helper lemmas for:
    - short-list initialization
    - prefix-step normalization
    - nonempty bounds on `array_count_increasing_steps_spec`
    - full-prefix collapse
  - used `store_int_range (&("n")) n_pre` in `proof_of_array_count_increasing_steps_safety_wit_7`
  - proved the two loop-step witnesses with the shared step lemma
  - proved the return witness by collapsing `sublist 0 (i + 1) l` to the whole list at exit
- Result:
  - `array_count_increasing_steps_proof_manual.v` compiled
  - it contains no `Admitted.`
  - it contains no user-added `Axiom`

## Issue 6: the workspace looked finished in reasoning logs but was not yet closed out on disk

- Phenomenon:
  - the reasoning logs already described a successful proof, but the retry workspace still had an incomplete final state
- Trigger:
  - `logs/metrics.md` was missing
  - compile artifacts under `coq/generated/` and `coq/deps/` had been recreated by validation compiles and needed cleanup again
- Diagnosis:
  - there was no remaining proof blocker
  - the real blocker in this retry round was completion hygiene rather than verification logic
- Fix:
  - reran the canonical compile sequence to confirm the current generated files still pass
  - recreated `logs/metrics.md` with the final status and compile summary
  - removed all non-`.v` files under:
    - `coq/generated/`
    - `coq/deps/`
- Result:
  - the workspace now satisfies the verify skill completion rules as written
  - the successful state is reflected both in compiled validation and in the final logs

## Final state

- `symexec` succeeds on the current annotated file.
- The workspace uses a local dependency shim at:
  - `coq/deps/array_count_increasing_steps.v`
- `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compile successfully.
- `coq/generated/` and `coq/deps/` contain only `.v` files after cleanup.
- `logs/metrics.md` is present and ends with `Final Result: Success`.
- The current verify workspace is successful end to end.

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `124`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_213619_array_count_increasing_steps/logs/codex_stderr_20260418_222035.log`
- Detail: `external codex run exceeded remaining timeout budget of 943 seconds`

## External Codex Failure

- Stage: `external-codex-run`
- Exit code: `124`
- Stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_213619_array_count_increasing_steps/logs/codex_stderr_20260418_223618.log`
- Detail: `external codex run exceeded remaining timeout budget of 1 seconds`
