# Proof Reasoning

## 2026-04-20 03:33:10 +0800 - Manual witness plan

- `symexec` succeeded on the latest annotated file and generated five admitted lemmas in `coq/generated/string_count_not_char_proof_manual.v`:
  - `string_count_not_char_safety_wit_5`
  - `string_count_not_char_entail_wit_1`
  - `string_count_not_char_entail_wit_2_1`
  - `string_count_not_char_entail_wit_2_2`
  - `string_count_not_char_entail_wit_3`
- Current proof shape:
  - `entail_wit_1` initializes the loop invariant with `l1 = nil`, `l2 = l`.
  - `entail_wit_2_1` handles the branch where the current character is nonzero and not equal to `c`; it must move the head of `l2_2` into the processed prefix and show the count increases by one.
  - `entail_wit_2_2` handles the branch where the current character is nonzero and equal to `c`; it must move the same head into the prefix and show the count is unchanged.
  - `entail_wit_3` is the loop-exit assertion; it must prove `i = n` from the read value `0`, the invariant bound `i <= n`, and the contract fact that all positions `< n` in `l` are nonzero, then rewrite the processed prefix to the whole list.
  - `safety_wit_5` must show `count + 1` remains in signed-int range on the incrementing branch.
- Available similar proof pattern: `examples/string_contains_char/coq/generated/string_contains_char_proof_manual.v` already proves the same prefix/suffix decomposition and `i = n` exit fact for a string scan. This task additionally needs arithmetic bounds for the count accumulator and append-one lemmas for `string_count_not_char_spec`.
- Planned proof edits:
  - add a helper lemma `string_count_not_char_spec_range` showing the count is between `0` and `Zlength l`;
  - add `string_count_not_char_spec_app_single`, plus direct equal/not-equal corollaries through case splitting;
  - adapt the `string_contains_char` witness proofs for prefix/suffix decomposition and the exit assertion.

## 2026-04-20 03:34:20 +0800 - First compile failure in helper lemma

- Compile command: full ordered `coqc` chain from `/home/yangfp/QualifiedCProgramming/SeparationLogic`.
- Error: `string_count_not_char_proof_manual.v`, line 27, `Tactic failure: Cannot find witness`.
- Location: base case of helper lemma `string_count_not_char_spec_range`.
- Diagnosis: after `simpl`, the local Coq environment did not reduce `Zlength nil` into a shape that `lia` could solve directly.
- Repair: rewrite `Zlength_nil` explicitly in the base case before invoking `lia`.

## 2026-04-20 03:35:18 +0800 - Branch-bound contradiction index mismatch

- Compile error: `string_count_not_char_proof_manual.v`, line 69, unable to unify `0` with `Znth (Zlength l1 - Zlength l) (0 :: nil) 0`.
- Location: the contradiction used to prove `i < n` in `safety_wit_5`.
- Diagnosis: after `pre_process`, `i` was already normalized through `Zlength l1`, so the post-`app_Znth2` index was `Zlength l1 - Zlength l`; the script tried to replace only `n - Zlength l`.
- Repair: replace the actual index expression found in the `Znth _ (0 :: nil) 0 <> 0` hypothesis with `0` by `lia`, then simplify.

## 2026-04-20 03:36:09 +0800 - Loop-step subgoal order

- Compile error: `string_count_not_char_proof_manual.v`, line 131, `Found no subterm matching "Zlength (... ++ ... :: nil)"`.
- Location: first bullet after `entailer!` in `entail_wit_2_1`.
- Diagnosis: for this witness, `entailer!` leaves the semantic count equation before the `Zlength` equation. The proof script tried the length rewrite against the count goal.
- Repair: prove the count equation first with `string_count_not_char_spec_app_single`, then prove the length equation with `Zlength_app_cons`, then close the append decomposition.

## 2026-04-20 03:37:02 +0800 - Ltac parser pattern in exit witness

- Compile error: `string_count_not_char_proof_manual.v`, line 225, `Syntax error: ',' or '|-' expected`.
- Location: `match goal` pattern inside `entail_wit_3` for selecting the nonzero-prefix hypothesis.
- Diagnosis: the local Ltac parser rejected the explicit chained inequality syntax inside a match pattern.
- Repair: match the implication premise as `_` and keep the conclusion shape `Znth k l 0 <> 0`, then discharge the premise with `lia`.

## 2026-04-20 03:37:54 +0800 - Exit nil-tail goal already normalized

- Compile error: `string_count_not_char_proof_manual.v`, line 237, `Found no subterm matching "? ++ nil" in the current goal`.
- Location: nil-tail branch after proving `i = n` in `entail_wit_3`.
- Diagnosis: `entailer!` and `subst l` already normalized the final count goal enough that there was no remaining `app_nil_r` rewrite target.
- Repair: make the rewrite optional and close the branch from the existing count invariant assumption.

## 2026-04-20 03:39:02 +0800 - Exit witness substituted `i` the wrong way

- Inspection method: opened `entail_wit_3` in `coqtop` with the same load paths and replayed the proof to the failing branch.
- Observed proof state: after `subst i`, the heap goal still contained `&( "i") # Int |-> Zlength l1 |-- &( "i") # Int |-> n`.
- Diagnosis: `subst i` used the invariant equation `Zlength l1 = i` and rewrote `i` to `Zlength l1` instead of using the freshly proved `Hi_eq_n : i = n`.
- Repair: rewrite with `Hi_eq_n` explicitly before `entailer!`, so the pointer cell value is normalized to `n` at the separation-logic entailment step.
