# Proof Reasoning

## 2026-04-20 18:31:55 +0800 - Initial manual witness plan

- Generated `string_starts_with_char_proof_manual.v` contains three unfinished return witnesses: `proof_of_string_starts_with_char_return_wit_1`, `proof_of_string_starts_with_char_return_wit_2`, and `proof_of_string_starts_with_char_return_wit_3`.
- The generated goal file shows all three are postcondition-disjunction obligations after reading `s[0]` and returning 0 or 1; the heap assertion is unchanged and should be reused directly.
- Key pure facts needed:
  - In the empty branch, `Znth 0 (l ++ 0 :: nil) 0 = 0` plus the contract fact that every `l[k]` for `0 <= k < n` is nonzero should imply `n = 0`; otherwise `k = 0` contradicts the nonzero-prefix precondition.
  - In the nonempty branches, `Znth 0 (l ++ 0 :: nil) 0 <> 0` should imply `0 < n`; if `n = 0`, the appended terminator is at index 0 and contradicts the branch fact.
  - Once `0 < n` is known, `Znth 0 (l ++ 0 :: nil) 0 = Znth 0 l 0` follows by `app_Znth1` and the length lower bound from `Zlength_nonneg` plus `n > 0`.
- Planned edit: add small local helper lemmas for these pure bridges, then keep each return witness short with `pre_process`, selecting the correct disjunct, applying the helper facts, and finishing the unchanged `CharArray.full` frame with `entailer!`.

## 2026-04-20 18:32:20 +0800 - First manual compile failure

- First compile attempt reached `string_starts_with_char_proof_manual.v` and failed at line 35 with `Error: Not an inductive goal with 2 constructors.`
- The failing statement was `right; right` in `proof_of_string_starts_with_char_return_wit_1`.
- Diagnosis: the generated three-way postcondition is parsed as left-associated `((branch1 || branch2) || branch3)`, so the third branch is selected by a single `right`; the second branch is `left; right`; and the first branch is `left; left`.
- Planned repair: change only the three branch-selection commands and recompile the full generated set.

## 2026-04-20 18:32:45 +0800 - Entailment needed branch facts earlier

- Second compile attempt failed in `proof_of_string_starts_with_char_return_wit_1` at line 38 with `Error: Tactic failure: Cannot find witness.`
- The failure occurred after selecting the empty-string postcondition branch and running `entailer!`; the proof only derived `n = 0` after `entailer!`, so the tactic could not instantiate the pure branch facts.
- Planned repair: derive branch-specific pure facts (`n = 0`, `0 < n`, and the simplified head equality/disequality) before selecting the postcondition disjunct, then run `entailer!` with those facts already available.

## 2026-04-20 18:33:20 +0800 - Manual proof completed

- Final proof shape:
  - `return_wit_1`: destruct `l`; empty branch selects the third postcondition branch, nonempty branch contradicts the nonzero-prefix precondition.
  - `return_wit_2`: empty branch contradicts the nonzero read fact; nonempty branch selects the first-character-equals branch.
  - `return_wit_3`: empty branch contradicts the nonzero read fact; nonempty branch selects the first-character-differs branch.
- Full compile order completed successfully for `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`.
- `string_starts_with_char_proof_manual.v` contains no `Admitted.` and no added `Axiom`.
