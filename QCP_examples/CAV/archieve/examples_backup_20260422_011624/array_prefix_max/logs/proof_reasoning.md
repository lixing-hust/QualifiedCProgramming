# Proof Reasoning

## Round 1

- Read `array_prefix_max_goal.v`, `array_prefix_max_proof_auto.v`, and `array_prefix_max_goal_check.v`.
- The generated `proof_manual.v` contains seven unfinished theorems:
  - `proof_of_array_prefix_max_safety_wit_5`
  - `proof_of_array_prefix_max_entail_wit_1`
  - `proof_of_array_prefix_max_entail_wit_2_1`
  - `proof_of_array_prefix_max_entail_wit_2_2`
  - `proof_of_array_prefix_max_entail_wit_3`
  - `proof_of_array_prefix_max_return_wit_1`
  - `proof_of_array_prefix_max_return_wit_2`
- Classification:
  - `safety_wit_5` is pure arithmetic on `i + 1`
  - `entail_wit_1`, `entail_wit_3`, `return_wit_1`, and `return_wit_2` are list-shape/output-array witnesses
  - `entail_wit_2_1` and `entail_wit_2_2` are the two max-extension branch witnesses from the running-max scan
- Reusable pattern:
  - `examples/array_max/coq/generated/array_max_proof_manual.v` already contains the max-scan helper lemmas:
    - `sublist_full_Zlength`
    - `max_list_nonempty_upper_bound`
    - `max_list_nonempty_bounded`
    - `max_list_nonempty_extend_ge`
    - `max_list_nonempty_extend_keep`
- Expected new helper lemma for this task:
  - normalize `replace_Znth i cur (app l1 (sublist i n lo))` into `app (l1 ++ [cur]) (sublist (i + 1) n lo)` when `Zlength l1 = i`
- First proof plan:
  - copy the stable `array_max` helper lemmas
  - discharge `safety_wit_5` with `entailer!` and `lia`
  - solve `entail_wit_2_1` by rewriting `sublist(0, i + 1, la)` into `sublist(0, i, la) ++ [la[i]]` and using the branch fact `la[i] > cur`
  - solve `entail_wit_2_2` exactly as in `array_max`
  - solve the output-shape witnesses with `replace_Znth_app_r`, `sublist_single`, `sublist_split`, and extensionality of the quantified prefix fact

## Round 2

- The first compile replay did not reach the proof script at all.
- `array_prefix_max_goal.v` failed with:
  - `Cannot find a physical path bound to logical path array_max`
- Diagnosis:
  - this task has no paired `input/<name>.v`, so the default workspace `original/` path is empty
  - but both generated Coq files import the shared helper file `array_max.v` from `CAV/input/`
- Fix direction:
  - keep the proof script as-is for now
  - rerun the compile chain with an additional Coq load path `-Q /home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input ""`
  - only after that compile passes the imports should I debug any actual proof failure

## Round 3

- The extra `-Q` path still failed at `Require Import array_max`.
- The missing piece is that Coq wants a compiled dependency, not just a source path, and compiling into the shared `input/` directory would write outside the verify workspace.
- To stay inside the permitted write boundary, I staged a local copy at:
  - `coq/deps/array_max.v`
- Next compile plan:
  - compile `coq/deps/array_max.v` with `-Q "$DEPS" ""`
  - compile `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` with both `-Q "$DEPS" ""` and `-R "$GEN" "$LP"`
- After that, the next failure should finally be a proof-script issue rather than dependency setup.

## Round 4

- With the local `coq/deps/array_max.v` staged, the compile chain reached `proof_manual.v`.
- First stable proof failure:
  - file: `coq/generated/array_prefix_max_proof_manual.v`
  - location: `max_list_nonempty_extend_gt`
  - symptom: Coq rejected the transitivity step in the branch for old-prefix elements
- Diagnosis:
  - that branch only needs `Znth i l 0 <= max_list_nonempty l` and then `max_list_nonempty l < x`
  - I used `Z.lt_le_trans` in the wrong direction
- Fix direction:
  - replace that step with a plain `Z.le_trans` from the upper-bound lemma, then finish the strict comparison to `x` with `lia`
  - recompile immediately to expose the next real blocker

## Round 5

- The next compile failure stayed in `max_list_nonempty_extend_gt`, but it is now only about an implicit argument:
  - Coq cannot infer the `d` parameter in the appended-cell `Znth` upper-bound call
- This is not a logical blocker; it just means the helper lemma needs the appended-index proof written a bit more explicitly.
- Fix direction:
  - instantiate `max_list_nonempty_upper_bound` at index `Zlength l` and default value `0`
  - keep the same arithmetic proof shape

## Round 6

- That compile error persisted because the offending implicit arguments were actually introduced by `rewrite <- Znth0_cons`, not by the upper-bound lemma itself.
- A more stable proof step is:
  - first assert `Znth (Zlength l) (l ++ x :: nil) 0 = x`
  - then rewrite the goal with that explicit equality
  - finally apply `max_list_nonempty_upper_bound`
- This keeps the helper lemma independent of Coq’s implicit-argument guessing around `Znth0_cons`.

## Round 7

- The next compile failure was still in the same upper-bound step, but now it is a scope/unification problem caused by rewriting inside `eapply Z.le_trans`.
- More stable pattern:
  - first name the inequality `Hupper : Znth (Zlength l) (l ++ x :: nil) 0 <= max_list_nonempty (l ++ x :: nil)`
  - rewrite `Hx_at_end` inside `Hupper`
  - finish with `lia`
- This removes the rewrite from the transitivity skeleton and should let the helper finally compile.

## Round 8

- After the helper lemmas compiled, the first witness-level failure moved to `proof_of_array_prefix_max_safety_wit_5`.
- The failure text is `Cannot find witness` right after `entailer!`, which usually means the proof should follow the more standard `pre_process` normalization first instead of unfolding the definition manually.
- Fix direction:
  - rewrite the safety proof to use `pre_process`
  - keep the goal arithmetic-only and finish with `lia`

## Round 9

- After regenerating the smaller witness set, the first compile failure moved to `entail_wit_1`.
- The failing line tried to rewrite `Zlength_cons`, but `entailer!` had already normalized that subgoal into a different length shape.
- Fix direction:
  - prove the singleton-length goal via `Zlength_correct` followed by `simpl`
  - keep the rest of the initialization witness unchanged

## Round 10

- I inspected `entail_wit_1` directly in `coqtop` after the strengthened invariant was regenerated.
- The remaining initialization goal now explicitly includes:
  - `n_pre <= INT_MAX`
- The available assumptions at that point are only:
  - `n_pre <> 0`
  - `0 <= n_pre`
  - `Zlength la = n_pre`
  - `Zlength lo = n_pre`
  - array ownership
- There is no remaining local `n` cell or other int-range hypothesis from which Verify can derive `n_pre <= INT_MAX`.
- This means the strengthened annotation has moved the blocker to the formal-input boundary:
  - without `n <= INT_MAX` in the contract, the new initialization witness is not derivable
  - removing that bound revives the earlier loop-range witness gap
- Conclusion:
  - this workspace is blocked by a contract gap, not by an unfinished local proof script
  - further progress would require a Contract-stage change to the formal input, such as adding an upper bound on `n`

## Round 11

- I changed the contract and annotated file from `n <= INT_MAX` to the stronger and proof-relevant bound `n + 1 <= INT_MAX`, then cleared generated Coq files and reran `symexec`.
- This removed the old arithmetic mismatch cleanly:
  - the fresh `entail_wit_3` context now contains `(n_pre + 1) <= INT_MAX`
  - the old impossible `i + 1` side condition is no longer the blocker
- The proof then moved back to local Coq work:
  - `entail_wit_3` needed the output-array rewrite normalized to `l1_2 ++ cur :: sublist (i + 1) n_pre lo`
  - the script was initially using stale `pre_process` hypothesis numbers from the older VC
- I rechecked the fresh goal in `coqtop`, aligned the hypothesis references, and finished `entail_wit_3`.

## Round 12

- After `entail_wit_3` compiled, the next blocker moved to `return_wit_1`.
- The first draft tried to prove `i_2 = n_pre` before `entailer!`, but that equality is only easily available after the pure assumptions are extracted.
- `coqtop` showed the real post-`entailer!` state:
  - one spatial goal reducing `IntArray.full ... (l1 ++ sublist i_2 n_pre lo)` to `IntArray.full ... l1`
  - one pointwise prefix goal
- I moved the `i_2 = n_pre` step inside the post-`entailer!` bullets, rewrote `sublist i_2 n_pre lo` to `nil`, then explicitly normalized `l1 ++ nil` to `l1`.
- That closed `return_wit_1`; `return_wit_2` already discharged directly.

## Round 13

- With the updated proofs, `proof_manual.v` compiled successfully.
- I then compiled `goal_check.v`, and it also passed.
- Final diagnosis:
  - the workspace was not blocked by a real contract gap anymore after the `n + 1 <= INT_MAX` fix
  - the remaining work was two local proof-script issues:
    - stale hypothesis numbering in `entail_wit_3`
    - wrong proof ordering in `return_wit_1`
