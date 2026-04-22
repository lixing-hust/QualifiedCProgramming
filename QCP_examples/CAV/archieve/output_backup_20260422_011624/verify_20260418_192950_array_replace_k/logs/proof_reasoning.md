# Proof Reasoning

## Iteration 1: classify the generated obligations

- Read `array_replace_k_goal.v`, `array_replace_k_proof_auto.v`, and `array_replace_k_goal_check.v`.
- `symexec` on the current minimal annotated file generated five manual obligations:
  - `entail_wit_1`
  - `entail_wit_2_1`
  - `entail_wit_2_2`
  - `entail_wit_3`
  - `return_wit_1`
- These are all list-shape witnesses, not missing ownership facts:
  - initialize the loop split with empty processed prefix;
  - advance the split in the replace branch;
  - advance the split in the keep-original branch;
  - collapse the zero-length suffix at loop exit;
  - pass the final existential list directly to the function return witness.
- Expected helper facts:
  - `app nil l = l` for initialization;
  - a split lemma turning `app l1 l2` with `Zlength l1 = i` and suffix relation on `l2` into `app l1 (cons (Znth i l 0) (sublist (i + 1) n l))`;
  - `Zlength l2 = 0 -> l2 = nil` for loop exit;
  - `replace_Znth i v (app l1 l2)` rewritten into `app (l1 ++ v :: nil) (sublist (i + 1) n l)` under the loop hypotheses.
- Next step:
  - inspect the proof state in `coqtop` after `pre_process; entailer!` so the helper lemmas and witness scripts match the generated context instead of guessing names.

## Iteration 2: first compile failed at parser level

- `coqc` failed before checking any goals:
  - file: `coq/generated/array_replace_k_proof_manual.v`
  - line: 24
  - error: `Syntax error: [ltac_use_default] expected after [tactic]`
- The failing script used combined existential witness syntax such as `Exists l, (@nil Z).`
- Existing stable proofs in this repo use the older style:
  - one `Exists ... .` per witness
- Fix:
  - rewrite every combined `Exists ... , ...` into two sequential `Exists` commands before continuing semantic proof debugging.

## Iteration 3: first witness was already solved by `entailer!`

- The next `coqc` pass failed with:
  - `Wrong bullet -: No more goals.`
- Location:
  - `proof_of_array_replace_k_entail_wit_1`
- Diagnosis:
  - after the two `Exists` witnesses and `rewrite app_nil_l`, `entailer!` discharged the initialization witness completely;
  - the manual bullet proof for the vacuous prefix condition and suffix equality was unnecessary.
- Fix:
  - delete the extra bullets and keep `entail_wit_1` as the minimal `pre_process; Exists; rewrite; entailer!` script.

## Iteration 4: replace missing library lemma with a local extensionality lemma

- The next compile failed with:
  - `The variable Zlength_eq was not found in the current environment.`
- Diagnosis:
  - the draft proof assumed a convenient list extensionality lemma name from memory, but that lemma is not exported on this workspace load-path.
- Fix:
  - add a local helper lemma specialized to `list Z`:
    - equal `Zlength`
    - pointwise equal `Znth`
    - conclude list equality
  - use that helper in the two places where the proof needs to reconstruct `l2_2 = sublist i n_pre l`.

## Iteration 5: helper lemma needed older Coq proof syntax

- The next compile again failed at the parser:
  - line 28 in `list_eq_by_Znth`
  - error after `induction ... as [...]`
- Diagnosis:
  - this Coq environment is sensitive to newer intro-pattern syntax in proof scripts.
- Fix:
  - rewrite the helper lemma using older proof structure only:
    - `induction l1.`
    - `destruct l2.`
    - plain `IHl1`

## Iteration 6: normalize the nil-length base case explicitly

- The next compile reached the helper lemma body and failed in the base case:
  - `Unable to apply lemma ... Zlength l = 0 -> l = nil`
  - current hypothesis shape: `Zlength nil = Zlength l2`
- Diagnosis:
  - `Zlength_nil_inv` needs an explicit `Zlength l2 = 0`, not an equality with `Zlength nil`.
- Fix:
  - rewrite `Zlength_nil` in the base-case hypothesis before applying `Zlength_nil_inv`.

## Iteration 7: orient the zero-length equality for `Zlength_nil_inv`

- After normalizing `Zlength nil`, the base case still failed because the hypothesis was:
  - `0 = Zlength l2`
- `Zlength_nil_inv` expects:
  - `Zlength l2 = 0`
- Fix:
  - add `symmetry in Hlen` before applying `Zlength_nil_inv`.

## Iteration 8: make the impossible cons-vs-nil branch explicit

- The next failure was `Cannot find witness` inside the helper lemma’s branch where:
  - left list is `a :: l1`
  - right list is `nil`
- Diagnosis:
  - `lia` could not use the contradiction until the lengths were first normalized to:
    - `Zlength_cons`
    - `Zlength_nil`
- Fix:
  - rewrite both length lemmas in that branch before calling `lia`.

## Iteration 9: feed `lia` the nonnegativity fact explicitly

- Even after normalizing lengths, the impossible `cons` versus `nil` branch still did not close automatically.
- Diagnosis:
  - the branch contradiction is really:
    - `Zlength l1 + 1 = 0`
    - together with `0 <= Zlength l1`
  - making the nonnegativity fact explicit is cheaper than fighting the automation.
- Fix:
  - add `pose proof (Zlength_nonneg l1)` before `lia`.

## Iteration 10: expand the `Znth_cons` side conditions explicitly

- The next compile failed at the first `Znth_cons` side condition in the helper lemma.
- Diagnosis:
  - `Znth_cons` needs explicit range facts like `0 < Zlength (a :: l1)`;
  - after rewriting `Zlength_cons`, `lia` still benefits from an explicit `Zlength_nonneg l1`.
- Fix:
  - in both helper-lemma branches that call `Znth_cons`, add `pose proof (Zlength_nonneg l1)` before `lia`.

## Iteration 11: use `simpl` for the head element instead of `Znth_cons`

- The next compile showed that `Znth_cons` in this library has the precondition:
  - `n > 0`
- The helper lemma was trying to rewrite the `n = 0` head case with it.
- Fix:
  - leave the tail case on `Znth_cons`
  - change the head case to plain `simpl in Hnth`

## Iteration 12: normalize the tail index after `Znth_cons`

- The next compile reached the tail case of the helper lemma.
- `Znth_cons` rewrote the hypothesis to:
  - `Znth (k + 1 - 1) ...`
- The induction hypothesis needs the cleaner shape:
  - `Znth k ...`
- Fix:
  - insert `replace (k + 1 - 1) with k in Hnth by lia`.

## Iteration 13: delay `Zlength_correct` until after the split-list reconstruction

- The next compile reached `entail_wit_2_1` and failed while reconstructing `l2_2 = sublist i n_pre l`.
- Diagnosis:
  - `rewrite Zlength_correct in *` had already changed the length hypotheses into `Z.of_nat (length ...)` form, so the proof script no longer matched the generated `Zlength`-based hypotheses cleanly.
- Fix:
  - postpone `rewrite Zlength_correct in *` until after:
    - `Hl2`
    - the branch-specific array equality (`Hreplace` / `Happ`)
  - keep the split reconstruction in the native `Zlength` form first.

## Iteration 14: remove dependence on unstable generated hypothesis numbers

- The next compile still failed in `Hl2`, but the real problem was proof brittleness:
  - the script assumed fixed names like `H4` and `H5`
  - after earlier edits, those names no longer referred to the same facts
- Fix:
  - replace numbered-hypothesis rewrites with `match goal` patterns keyed on the logical shape:
    - `Zlength l2_2 = n_pre - i`
    - the suffix relation for `l2_2`
  - do the same for the miss-branch inequality proof.

## Iteration 15: orient the sublist-length equality correctly

- A concrete proof-state dump showed the exact current goal in `Hl2`:
  - `n_pre - i = Zlength (sublist i n_pre l)`
- `Zlength_sublist0` proves the reverse orientation.
- Fix:
  - add `symmetry.` before `apply Zlength_sublist0; lia.` in both `Hl2` proofs.

## Iteration 16: use the general sublist-length lemma

- The proof-state dump showed the real sublist shape was:
  - `sublist i n_pre l`
- `Zlength_sublist0` only applies to:
  - `sublist 0 hi l`
- Fix:
  - replace it with `Zlength_sublist`, supplying the bounds `0 <= i <= n_pre <= Zlength l`.

## Iteration 17: normalize addition order in the suffix proof

- The next failure in `Hl2` was:
  - expected `Znth (k + i) l 0`
  - had `Znth (i + k) l 0`
- This is just commutativity noise from the sublist library.
- Fix:
  - add `replace (k + i) with (i + k) by lia` before finishing the suffix equality proof.
