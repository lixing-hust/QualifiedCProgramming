# Proof Reasoning

## Iteration 1: first read of generated obligations

- Read `array_contains_goal.v`, `array_contains_proof_auto.v`, and `array_contains_goal_check.v`.
- The generated `array_contains_proof_manual.v` contains exactly two unresolved theorems:
  - `proof_of_array_contains_return_wit_1`
  - `proof_of_array_contains_return_wit_2`
- Shape diagnosis:
  - `return_wit_1` is the early-return branch where `Znth i l 0 = k` and every earlier index is known to differ from `k`
  - `return_wit_2` is the loop-exit branch where every index in the whole list is known to differ from `k`
- These are pure list-spec obligations, not missing-shape or missing-annotation obligations, so this is the proof layer described in `SYMEXEC.md`.
- Planned proof structure:
  - add a helper lemma showing `array_contains_spec l k = 1` once the current index hits `k` and all earlier indices are known to miss
  - add a helper lemma showing `array_contains_spec l k = 0` when every valid index misses
  - keep the actual witness proofs short: `entailer!` to discharge separation logic, then call the helper lemma

## Iteration 2: implementation plan before first compile

- The helper lemmas should use conservative induction on `l`.
- For the hit lemma:
  - split on whether the head already equals `k`
  - if not, rewrite `Znth` through the list tail with `Znth_cons`
  - shift the prefix-no-match hypothesis by one index
- For the miss lemma:
  - the head cannot equal `k`, otherwise the quantified miss hypothesis at index `0` contradicts `Znth0_cons`
  - recurse on the tail after shifting the index range by one
- I will avoid fragile compact tactics and keep the witness proofs to explicit `unfold`, `intros`, `entailer!`, and one helper application.

## Iteration 3: first compile failure in the hit helper lemma

- First stable blocker: compiling `array_contains_proof_manual.v` failed in `array_contains_spec_hit`.
- Error location: line 57 in the generated file.
- Error text: the proof tried to feed the local fact `0 < i` where the shifted prefix hypothesis needed `0 <= j + 1`.
- Diagnosis:
  - this is only a naming / proof-state management bug
  - the helper-lemma design is still correct; the script just reused `H` after introducing the index-shift side conditions
- Fix direction:
  - rename the positivity fact for `i`
  - give the shifted side conditions explicit names before specializing the prefix hypothesis
  - recompile `proof_manual.v`

## Iteration 4: normalize the shifted `Znth` index

- The next compile failure stayed in the same helper branch after `rewrite Znth_cons in Hprev by lia`.
- Residual mismatch:
  - obtained `Znth (j + 1 - 1) l 0 <> k`
  - needed `Znth j l 0 <> k`
- This is pure arithmetic normalization, not a missing semantic fact.
- Fix direction:
  - explicitly replace `j + 1 - 1` with `j` by `lia`
  - keep the helper lemma otherwise unchanged

## Iteration 5: the miss helper needs the same normalization

- After fixing the hit helper, compilation moved to `array_contains_spec_miss`.
- The residual goal was the same shape:
  - obtained `Znth (j + 1 - 1) l 0 <> k`
  - needed `Znth j l 0 <> k`
- This confirms the helper-lemma strategy is sound; both branches just require the same explicit arithmetic normalization after `Znth_cons`.

## Iteration 6: witness equality orientation

- After both helper lemmas compiled, the next failure moved to `proof_of_array_contains_return_wit_1`.
- The generated witness goal is oriented as `1 = array_contains_spec l k_pre`, while the helper lemma concludes `array_contains_spec l k_pre = 1`.
- This is again a proof-script alignment issue, not a missing fact.
- Fix direction:
  - insert `symmetry` in `return_wit_1`
  - do the analogous orientation fix in `return_wit_2` for `0 = array_contains_spec l k_pre`

## Iteration 7: make helper instantiation explicit

- The next failure was `Cannot find witness` at the first side-condition bullet of `return_wit_1`.
- A direct `coqtop` probe showed the post-`entailer!` goal is the expected pure equality
  - `array_contains_spec l k_pre = 1`
- So the missing piece is not a logical fact but likely implicit instantiation through `eapply`.
- Fix direction:
  - call the helper lemmas with explicit arguments `l`, `k_pre`, and `i`
  - keep the side-condition bullets unchanged

## Iteration 8: witness proof used the wrong post-`entailer!` hypothesis

- The next compile failure stayed in `proof_of_array_contains_return_wit_1`.
- After `entailer!`, the prefix no-match hypothesis is `H3`, while `H4` is only `0 <= n_pre`.
- I had accidentally applied `H4` in the final side-condition bullet, which explains the type mismatch.
- Fix direction:
  - switch that bullet to use `H3`
  - keep the explicit helper instantiation

## Iteration 9: same post-`entailer!` indexing issue in `return_wit_2`

- After `return_wit_1` was fixed, compilation moved to `proof_of_array_contains_return_wit_2`.
- The remaining `Cannot find witness` was again caused by using the wrong hypothesis number after `entailer!`.
- The proof only needs the universal miss fact from the exit assertion, so the fix is to apply that quantified hypothesis directly.

## Iteration 10: recover `Zlength l = n_pre` from `IntArray.full`

- A direct `coqtop` probe of `return_wit_2` showed that `entailer!` alone does not expose the list length needed by `array_contains_spec_miss`.
- The missing fact is available from `IntArray.full_length`, which yields `Z.of_nat (length l) = n_pre`.
- Fix direction:
  - switch `return_wit_2` to `pre_process`
  - apply `IntArray.full_length`
  - rewrite that result into `Zlength l = n_pre`
  - then use the exit hypothesis `forall j < n_pre, ...` to satisfy the helper lemma’s `forall j < Zlength l, ...`

## Iteration 11: correct the `Zlength_correct` rewrite direction

- The first attempt at the length bridge failed because it tried to rewrite `Z.of_nat (length l)` out of a goal that still mentioned `Zlength l`.
- `Zlength_correct` has to be used in the forward direction here:
  - `rewrite Zlength_correct`
  - then discharge the goal with the fact from `IntArray.full_length`

## Iteration 12: rewrite the helper side condition in the correct direction

- The next compile failure happened in the final side-condition proof for `array_contains_spec_miss`.
- At that point `Hjlt` is already `j < Zlength l`, and the exit hypothesis wants `j < n_pre`.
- So the bound should be rewritten with `Hlen` directly, not with `<- Hlen`.
