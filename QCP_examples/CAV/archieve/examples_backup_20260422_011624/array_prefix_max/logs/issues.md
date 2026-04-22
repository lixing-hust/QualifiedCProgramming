# Issues

## Issue 1: annotated header binder syntax was rejected by the front end

- Stage: `annotation / symexec`
- Phenomenon:
  - the first `symexec` run failed with `unexpected PT_COMMA, expecting PT_REQUIRE`
- Trigger:
  - the bootstrapped annotated copy kept `With la, lo`
- Localization:
  - `annotated/verify_20260418_205317_array_prefix_max.c`
  - `logs/qcp_run.log`
- Diagnosis:
  - this front end rejects comma-separated `With` binders in the annotated working copy, matching the already documented `array_add` behavior
- Fix:
  - normalized the binder line to `With la lo`
- Result:
  - the parser moved on to real symbolic execution

## Issue 2: opening both arrays before the branch destabilized symbolic execution

- Stage: `annotation / symexec`
- Phenomenon:
  - an early annotation attempt failed at `cur = a[i];` with `Assign Exec fail`
- Trigger:
  - I opened both `a[i]` and `out[i]` before entering the `if (a[i] > cur)` branch
- Localization:
  - `annotated/verify_20260418_205317_array_prefix_max.c:70`
  - `logs/qcp_run.log`
- Diagnosis:
  - the branch only needs the read-only source array in full form; forcing `missing_i` shape before the branch misaligned the control point
- Fix:
  - removed the pre-branch heap opening and kept only the logical post-branch summary of `cur`
- Result:
  - `symexec` progressed to the write step

## Issue 3: `cur` needed an explicit post-branch assertion before the store

- Stage: `annotation / symexec`
- Phenomenon:
  - the next `symexec` retry failed at `out[i] = cur;` with `cannot write null value to memory`
- Trigger:
  - after the branch merge, the executor had not stabilized the program variable `cur` strongly enough for the store
- Localization:
  - `annotated/verify_20260418_205317_array_prefix_max.c:71`
  - `logs/qcp_run.log`
- Diagnosis:
  - a local `Assert` after the `if` was needed to re-anchor `cur == max_list_nonempty(sublist(0, i + 1, la))`
- Fix:
  - replaced the write-specific `which implies` blocks with one explicit post-`if` assertion
- Result:
  - `symexec` succeeded and generated `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`

## Issue 4: generated Coq imports needed a workspace-local compiled dependency

- Stage: `compile`
- Phenomenon:
  - `goal.v` failed immediately with `Cannot find a physical path bound to logical path array_max`
- Trigger:
  - generated Coq files use `Require Import array_max`, but this task has no paired `original/<name>.v`
- Localization:
  - `logs/compile_goal.log`
  - `coq/generated/array_prefix_max_goal.v`
- Diagnosis:
  - pointing Coq at `CAV/input/` was not enough because `Require Import` needs a compiled dependency and writing build products into `input/` would be outside the verify workspace
- Fix:
  - staged `coq/deps/array_max.v` inside the workspace
  - compiled it first with `-Q "$DEPS" ""`
  - compiled generated files with both `-Q "$DEPS" ""` and `-R "$GEN" "$LP"`
- Result:
  - the compile chain reached `proof_manual.v`

## Issue 5: first proof attempt exposed a missing loop-range fact

- Stage: `proof -> annotation`
- Phenomenon:
  - the original proof attempt got stuck on `safety_wit_5`, which required `i + 1 <= INT_MAX`
- Trigger:
  - the invariant only preserved `1 <= i <= n` and the prefix semantics, but no explicit signed-int bound for `i + 1`
- Localization:
  - initial `proof_manual.v`
  - `coq/generated/array_prefix_max_goal.v`
  - `logs/proof_reasoning.md`
- Diagnosis:
  - this is an annotation-layer gap, not a pure Coq issue; the loop head and next iteration both use `i + 1`
- Fix attempt:
  - strengthened the invariant and post-`if` assertion with:
    - `i + 1 <= INT_MAX`
    - `n == n@pre`
    - `n <= INT_MAX`
  - cleared generated Coq files and reran `symexec`
- Result:
  - the regenerated proof surface became smaller:
    - `safety_wit_5` dropped out of the manual proof
    - the `> cur` branch witness also dropped out of the manual proof

## Issue 6: strengthened invariant exposed a contract-boundary blocker

- Stage: `proof / contract boundary`
- Phenomenon:
  - after the strengthened rerun, `entail_wit_1` required proving `n_pre <= INT_MAX`
- Trigger:
  - the new invariant stores `n <= INT_MAX`, so the initialization witness must derive the same fact from the formal input
- Localization:
  - `coq/generated/array_prefix_max_goal.v`
  - `coq/generated/array_prefix_max_proof_manual.v`
  - `logs/proof_reasoning.md`
- Diagnosis:
  - `coqtop` inspection showed the initialization context only contains:
    - `n_pre <> 0`
    - `0 <= n_pre`
    - `Zlength la = n_pre`
    - `Zlength lo = n_pre`
    - array ownership
  - there is no remaining local `n` store or contract assumption from which Verify can derive `n_pre <= INT_MAX`
  - removing the bound reintroduces the earlier loop-range witness gap
- Fix action considered:
  - adding an explicit upper bound such as `n <= INT_MAX` to the input contract would likely unblock the proof, but that is a Contract-stage modification and outside Verify permissions
- Result:
  - verification is currently blocked at the formal-input boundary
  - `goal_check.v` was not compiled successfully end to end

## Issue 7: stale `pre_process` numbering after regenerating the VC

- Stage: `proof`
- Phenomenon:
  - after the regenerated `goal.v` was compiled, `proof_manual.v` still failed inside `entail_wit_3`
  - the concrete error was `Found no subterm matching "cur" in the current goal`
- Trigger:
  - the proof script still used the old hypothesis numbers from the previous VC shape
- Localization:
  - `coq/generated/array_prefix_max_proof_manual.v`
  - `proof_of_array_prefix_max_entail_wit_3`
- Diagnosis:
  - on the fresh VC, `pre_process` produced:
    - `H4 : Zlength l1_2 = i`
    - `H5 : cur = max_list_nonempty (...)`
    - `H6 : forall k_2, ...`
  - the stale script was still treating `H5` as the length equality
- Fix:
  - re-inspected the goal in `coqtop`
  - updated the proof to use the fresh hypothesis numbering
- Result:
  - `entail_wit_3` compiled successfully

## Issue 8: `return_wit_1` needed `entailer!` before proving `i_2 = n_pre`

- Stage: `proof`
- Phenomenon:
  - `return_wit_1` failed with `Cannot find witness` when asserting `i_2 = n_pre` too early
- Trigger:
  - the proof tried to solve the arithmetic equality before the pure assumptions had been extracted from the entailment
- Localization:
  - `coq/generated/array_prefix_max_proof_manual.v`
  - `proof_of_array_prefix_max_return_wit_1`
- Diagnosis:
  - `coqtop` showed that after `Exists l1; entailer!`, the proof cleanly splits into:
    - one spatial goal reducing `l1 ++ sublist i_2 n_pre lo` to `l1`
    - one pointwise prefix goal
  - before `entailer!`, that equality is buried inside the entailment and not convenient to derive directly
- Fix:
  - moved `assert (i_2 = n_pre) by lia` into the post-`entailer!` bullets
  - rewrote `sublist i_2 n_pre lo` to `nil`
  - explicitly normalized `l1 ++ nil` to `l1`
- Result:
  - `return_wit_1` compiled successfully

## Final status snapshot

- `symexec` succeeded on the latest annotated file
- workspace-local dependency staging succeeded
- `goal.v` compiled
- `proof_auto.v` compiled
- `proof_manual.v` compiled
- `goal_check.v` compiled
- verification is complete in this workspace
