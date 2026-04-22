# Proof Reasoning

## Round 1

- Read `array_count_increasing_steps_goal.v`, `array_count_increasing_steps_proof_auto.v`, `array_count_increasing_steps_proof_manual.v`, and `array_count_increasing_steps_goal_check.v`.
- The generated `proof_manual.v` contains exactly six unfinished lemmas:
  - `proof_of_array_count_increasing_steps_safety_wit_3`
  - `proof_of_array_count_increasing_steps_safety_wit_7`
  - `proof_of_array_count_increasing_steps_entail_wit_1`
  - `proof_of_array_count_increasing_steps_entail_wit_2_1`
  - `proof_of_array_count_increasing_steps_entail_wit_2_2`
  - `proof_of_array_count_increasing_steps_return_wit_1`
- First classification:
  - `safety_wit_3` should be pure arithmetic from `0 <= i <= n_pre`.
  - `safety_wit_7` should use the signed range of `n_pre` together with a bound showing the prefix step count is at most `i`.
  - `entail_wit_1` is the loop initialization witness and should reduce to the fact that the spec on a prefix of length at most `1` is `0`.
  - `entail_wit_2_1` and `entail_wit_2_2` are the two loop-step witnesses. They should both use the same list-normalization pattern:
    - split `sublist 0 (i + 2) l` into the old prefix plus the last two elements
    - relate that to `sublist 0 (i + 1) l`
    - simplify the final branch with the concrete comparison fact
  - `return_wit_1` should be the standard exit rewrite:
    - derive `n_pre <= i + 1 <= n_pre`, hence `i + 1 = n_pre`
    - rewrite the invariant summary to `sublist 0 n_pre l`
    - collapse that to `l`
- Planned helper lemmas:
  - one local lemma that appending a new last element extends the spec by exactly the comparison between the previous last element and the new one
  - one local lemma that bounds the spec on any nonempty list by `Zlength l - 1`
- Planned proof style:
  - use conservative scripts only
  - prefer explicit rewrites over large tactics
  - compile after the first proof pass and then inspect the first stable failure instead of guessing later proof-state names

## Round 2

- The first compile replay did not reach any witness proof.
- First stable failure:
  - file: `original/array_count_increasing_steps.v`
  - error: Coq rejected the recursive definition as ill-formed because the call is on `y :: xs` instead of a structural subterm
- Diagnosis:
  - this is not a proof-script problem
  - the generated Coq files only need a module named `array_count_increasing_steps` that exposes the same spec definition
  - Verify permissions allow adding workspace-local files under `coq/deps/`
- Next step:
  - place a workspace-local replacement module in `coq/deps/array_count_increasing_steps.v`
  - keep the semantics identical but rewrite the recursion into a structurally accepted nested-match form
  - compile using `-Q "$DEPS" ""` so the generated files resolve that local module without modifying `input/` or `original/`

## Round 3

- The workspace-local dependency unblocked Coq loading.
- I then replaced the `Admitted.` stubs with a first manual proof pass and iterated on three local helper lemmas:
  - the two-element step lemma for `array_count_increasing_steps_spec`
  - the nonempty upper-bound lemma for the spec
  - the short-list lemma for initialization
- Those helper iterations were mostly Coq-parser and normalization work:
  - remove newer `as [...]` induction/destruct syntax
  - avoid brittle rewrites on `match`-expanded recursive calls
  - expose `Zlength` arithmetic in a form `lia` can actually consume
- The compile replay progressed far enough to reach the first real witness theorem:
  - `proof_of_array_count_increasing_steps_safety_wit_3`

## Round 4

- First stable semantic blocker in the manual proof:
  - file: `coq/generated/array_count_increasing_steps_proof_manual.v`
  - compile status at that point: helper lemmas accepted, but `proof_of_array_count_increasing_steps_safety_wit_3` still had open goals
- Diagnosis:
  - this witness needs the loop invariant to justify signed safety of computing `i + 1`
  - the accepted invariant only preserves `0 <= i <= n`
  - the natural stronger fact is `i + 1 <= n || n == 0`
- I tried pushing that fact back into the annotation layer and rerunning `symexec`.
- Result:
  - the verifier frontend rejected that disjunctive invariant form before VC generation
  - so the remaining blocker is not a missing tactic in `proof_manual.v`, but an annotation/frontend boundary:
    - weaker accepted invariant: proof does not go through
    - stronger natural invariant: frontend rejects it

## Round 5

- Rechecked the generated VC against nearby counted-scan examples instead of assuming the invariant had to change.
- New diagnosis:
  - `array_count_increasing_steps_safety_wit_3` and `safety_wit_7` can likely be discharged from the existing invariant plus the fact that `n` and `cnt` are stored as C `Int`
  - the missing ingredient is a local pure lemma about the step-count spec on prefixes, not a stronger frontend invariant
- Reusable proof plan for this workspace:
  - use `prop_apply (store_int_range (&("n")) n_pre)` to recover the signed range of `n_pre`
  - use a local nonempty-prefix bound lemma to show `array_count_increasing_steps_spec prefix <= Zlength prefix - 1`
  - use a local step lemma to rewrite `array_count_increasing_steps_spec (sublist 0 (i + 2) l)` into the old prefix summary plus the branch contribution from comparing `Znth i l 0` and `Znth (i + 1) l 0`
  - use a local full-prefix lemma `sublist 0 k l = l` when `Zlength l <= k` for the return witness, so the `n = 0` exit case is covered without forcing `i = n_pre`
- Next step:
  - patch `coq/generated/array_count_increasing_steps_proof_manual.v` only
  - compile `proof_manual.v` directly with the workspace-local dependency in `coq/deps/`
  - if a witness still fails, inspect the concrete proof state before touching annotations

## Round 6

- Replaced the placeholder manual proof with concrete helper lemmas and witness scripts, then iterated on Coq-parser compatibility and list-normalization details until the compile replay reached the first real witness again.
- Stable proof-state observation for `proof_of_array_count_increasing_steps_safety_wit_3`:
  - after `pre_process`, `store_int_range`, and separation-logic cleanup, the remaining arithmetic obligation is exactly:
    - `i + 1 <= 2147483647`
  - available pure facts at that point are only:
    - `0 <= i`
    - `i <= n_pre`
    - `0 <= n_pre`
    - `n_pre <= 2147483647`
- Counterexample:
  - `i = 2147483647`
  - `n_pre = 2147483647`
  - all current assumptions hold, but `i + 1 <= 2147483647` is false
- Conclusion:
  - this is not a tactic gap in `proof_manual.v`
  - the current input/program pair permits a loop-head signed-overflow state for the guard expression `i + 1`
  - verification cannot be completed within Verify-only permissions unless the contract is strengthened (for example `n < INT_MAX`) or the implementation is rewritten to avoid evaluating `i + 1` at the loop head

## Round 7

- Retried the blocker from the annotation layer instead of treating it as final.
- New invariant experiment:
  - keep the accepted prefix-summary invariant
  - add only the pure loop-head safety fact:
    - `i + 1 <= INT_MAX`
- Result:
  - `symexec` accepted this shape and regenerated fresh `goal/proof_auto/proof_manual/goal_check`
  - the impossible old blocker in `safety_wit_3` disappeared because the fact is now present directly in the VC
- New generated proof surface:
  - the regenerated `proof_manual.v` now contains five witness lemmas:
    - `proof_of_array_count_increasing_steps_safety_wit_7`
    - `proof_of_array_count_increasing_steps_entail_wit_1`
    - `proof_of_array_count_increasing_steps_entail_wit_2_1`
    - `proof_of_array_count_increasing_steps_entail_wit_2_2`
    - `proof_of_array_count_increasing_steps_return_wit_1`
- Proof repair plan from here:
  - restore the earlier local helper lemmas for:
    - short-list initialization
    - prefix-step normalization
    - full-prefix collapse
    - bounds on `array_count_increasing_steps_spec`
  - adapt the loop-step witnesses to the new arithmetic side condition:
    - `((i + 1) + 1) <= INT_MAX`
  - compile `proof_manual.v` again and continue from the first concrete failing witness instead of assuming the remaining scripts still work unchanged

## Round 8

- The direct machine-range invariant `i + 1 <= INT_MAX` was accepted by `symexec`, but the regenerated `entail_wit_2_1` exposed that this fact was not inductive:
  - the next loop head needed `i + 2 <= INT_MAX`
  - the step witness did not expose any explicit pure upper bound on `n_pre`
- I therefore returned to the annotation layer and replaced that clause with the implication form:
  - `0 < n => i + 1 <= n`
- Result:
  - `symexec` accepted this implication form
  - the regenerated `goal.v` carried the implication through the invariant witnesses
  - the previously impossible `safety_wit_3` disappeared from the manual theorem list again

## Round 9

- After the implication-form rerun, the first compile replay still showed stale pre-retry assumptions in the proof state.
- Diagnosis:
  - old `.vo/.glob/.aux` artifacts under `coq/generated/` were still being reused
- Fix:
  - deleted all non-`.v` files under:
    - `coq/generated/`
    - `coq/deps/`
  - recompiled from the fresh regenerated `.v` files in order:
    - `deps`
    - `goal`
    - `proof_auto`
    - `proof_manual`
- Result:
  - the proof state then matched the new implication-form VC exactly

## Round 10

- With the stale artifacts removed, the remaining proof work was routine:
  - `safety_wit_7` needed `store_int_range (&("n")) n_pre` again so `cnt + 1` could be bounded by `i + 1 < n_pre <= INT_MAX`
  - `entail_wit_1` was discharged by direct case analysis on the prefix of length at most `1`
  - `entail_wit_2_1` and `entail_wit_2_2` reduced to the local step lemma
  - `return_wit_1` reduced by collapsing `sublist 0 (i + 1) l` to the full list at loop exit
- Final compile result:
  - `coq/deps/array_count_increasing_steps.v`: compiled
  - `array_count_increasing_steps_goal.v`: compiled
  - `array_count_increasing_steps_proof_auto.v`: compiled
  - `array_count_increasing_steps_proof_manual.v`: compiled
  - `array_count_increasing_steps_goal_check.v`: compiled
- Final proof state:
  - `proof_manual.v` contains no `Admitted.`
  - `proof_manual.v` contains no user-added `Axiom`

## Round 11

- Retry-round validation started from the existing workspace instead of regenerating anything.
- Re-read the active annotated file, generated Coq files, `qcp_run.log`, compile logs, and the current reasoning logs to identify the live blocker from disk state rather than from memory.
- Current blocker found in this retry:
  - there was no longer a proof blocker
  - `symexec` was already succeeding on the current annotated file
  - `proof_manual.v` already contained completed witness proofs
  - the remaining gap was workspace completion:
    - `logs/metrics.md` was missing
    - non-`.v` artifacts under `coq/generated/` and `coq/deps/` still needed cleanup after compile replay
- Validation action:
  - reran the canonical compile sequence in `/home/yangfp/QualifiedCProgramming/SeparationLogic` using the workspace-local dependency shim under `coq/deps/`
  - compile results:
    - `coq/deps/array_count_increasing_steps.v`: passed
    - `array_count_increasing_steps_goal.v`: passed
    - `array_count_increasing_steps_proof_auto.v`: passed
    - `array_count_increasing_steps_proof_manual.v`: passed
    - `array_count_increasing_steps_goal_check.v`: passed
- Result:
  - this retry confirmed the proof scripts and current annotations are already sufficient
  - no further proof repair was needed; only final workspace bookkeeping remained
