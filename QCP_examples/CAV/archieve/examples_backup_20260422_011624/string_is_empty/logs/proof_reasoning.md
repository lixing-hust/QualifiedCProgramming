# Proof Reasoning

## Round 1

- `proof_manual.v` contains exactly two unresolved theorems:
  - `proof_of_string_is_empty_return_wit_1`
  - `proof_of_string_is_empty_return_wit_2`
- Both goals are return witnesses for the same one-step branch split on `s[0]`.
- The key semantic bridge is not separation logic structure but the list length hidden inside `CharArray::full`.
- Reusable pattern from the nearby `string_copy` proof:
  - use `prop_apply CharArray.full_length`
  - derive `Zlength l = n` from the generated equality on `l ++ [0]`
  - destruct `l`
- Expected branch outcomes:
  - for `return_wit_1`, `l = nil` should force `n = 0`, while `l = a :: l'` contradicts the contract fact that every `l[k]` for `0 <= k < n` is nonzero together with the branch assumption that the first element is `0`
  - for `return_wit_2`, `l = nil` contradicts the branch assumption that the first element is nonzero, while `l = a :: l'` should force `0 < n`

## Planned proof

- Keep each witness proof short:
  - `pre_process`
  - expose the `CharArray::full_length` fact
  - derive `Zlength l = n`
  - split on `l`
  - finish the surviving arithmetic branch with `entailer!` and `lia`
- Avoid adding helper lemmas unless the first compile shows the generated hypothesis shape differs from the expected one.

## Round 2

- The first `coqc` pass failed before proof checking with an older-parser syntax error at `destruct l as [| a l']`.
- This repository already warns that proof scripts should use conservative syntax for older Coq builds.
- The proof strategy itself is still valid; only the binder name shape is too modern/brittle for this environment.

## Fix

- Rewrite the destruct patterns to avoid apostrophe-suffixed binders and keep the rest of the proof unchanged.
- Re-run the full compile chain to see the first real proof-state failure, if any.

## Round 3

- The next compile showed the problem is broader: this Coq build rejects `destruct ... as ...` at that proof location, not just apostrophe-suffixed names.
- That matches the repo guidance to avoid depending on newer intro-pattern parsing.

## Fix

- Switch to plain `destruct l.` and recover the needed hypotheses by `match goal` shape instead of explicit branch binder names.
- Re-run the compile chain again from `goal.v` through `goal_check.v`.

## Round 4

- The next compile reached the proof body and failed with `Cannot find witness` in the `l = nil` branch of `return_wit_1`.
- Diagnosis:
  - choosing the disjunct with `right` was correct
  - but `entailer!` still did not know `n = 0` explicitly
  - similarly, the nonempty branch of `return_wit_2` should expose `0 < n` before calling `entailer!`

## Fix

- In the `l = nil` branch of `return_wit_1`, derive `n = 0` from `Hlen_l`, `subst n`, then call `entailer!`.
- In the cons branch of `return_wit_2`, derive `0 < n` from `Hlen_l` before `entailer!`.

## Round 5

- The updated script still failed in the `l = nil` branch, but now the failure was just that `lia` could not use `Hlen_l` until `Zlength nil` was normalized explicitly.

## Fix

- Rewrite `Zlength_nil` in `Hlen_l` before calling `lia`.

## Round 6

- `coqtop` showed the nil branch of `return_wit_1` was no longer blocked on arithmetic discovery.
- After `right. entailer!`, the remaining goal was already the concrete assertion semantics:
  - prove `n = 0`
  - prove the trivial equality `1 = 1`
  - reuse the existing `CharArray.full ... m`
- So the remaining work is not a missing lemma. It is just the final conjunction over the current model.

## Fix

- Keep `entailer!` to enter the model-level goal.
- Then finish both successful branches with `simpl; repeat split; auto; lia`.

## Round 7

- The next compile moved to the cons-branch arithmetic, where `lia` still would not conclude `0 < n` from `Zlength_cons`.
- The missing ingredient is explicit tail nonnegativity; this repo’s arithmetic automation does not always reconstruct it from the `Zlength` library lemmas on its own.

## Fix

- After `rewrite Zlength_cons in Hlen_l`, add `pose proof Zlength_nonneg l`.
- Reuse that fact in both cons branches before `lia`.

## Round 8

- The next compile failure was not semantic. It came from using the name `a` outside a branch where `destruct l.` had introduced implementation-dependent binder names.
- Since the script is already using `match goal` for robustness, the cleanest fix is to keep the head-value contradiction entirely inside one pattern match.

## Fix

- Replace the free-standing `assert (a <> 0)` with a single `match goal` block that simultaneously binds:
  - the nonzero-prefix hypothesis on the cons case
  - the branch hypothesis `Znth 0 ((?a :: ?tl) ++ 0 :: nil) 0 = 0`
- Derive the head nonzero fact locally inside that block and close the contradiction there.

## Round 9

- The combined `match goal` arm then hit another parser-compatibility issue in this Coq build.
- The underlying proof idea is still fine; the problem is only the Ltac pattern syntax.

## Fix

- Replace the multi-hypothesis `match goal` arm with two nested single-hypothesis matches.
- Keep the contradiction proof unchanged inside the inner match.

## Round 10

- Even the nested `match goal` form still hit Ltac parser compatibility issues.
- At that point the tactic machinery was no longer buying anything, because `coqtop` had already shown the branch-local hypothesis names produced by `destruct l.` in this environment.

## Fix

- Drop the Ltac matching entirely in the cons contradiction branch.
- Use the direct branch hypotheses:
  - `z` for the head element
  - `H2` for the nonzero-prefix fact
  - `H` for the branch assumption that the head is `0`
- This is less abstract but more stable for this generated proof file.
