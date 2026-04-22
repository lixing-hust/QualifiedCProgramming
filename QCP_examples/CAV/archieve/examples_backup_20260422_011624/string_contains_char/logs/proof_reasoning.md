# Proof Reasoning

## Round 1

- `proof_manual.v` contains four admitted goals:
  - `proof_of_string_contains_char_entail_wit_1`
  - `proof_of_string_contains_char_entail_wit_2`
  - `proof_of_string_contains_char_return_wit_1`
  - `proof_of_string_contains_char_return_wit_2`
- First pass classification:
  - `entail_wit_1`: initialization witness, likely just `Exists nil l`
  - `entail_wit_2`: loop-step witness, likely needs a nonempty-suffix split and one small spec lemma for extending a prefix with a non-`c` character
  - `return_wit_1`: return-1 branch, likely needs a nonempty-suffix split plus a lemma that a matching next character makes the whole spec equal `1`
  - `return_wit_2`: return-0 branch, likely needs to show the current index is exactly the string terminator position, then conclude `l = l1`
- Expected proof shape:
  - start each theorem with `unfold ...; intros; entailer!`
  - for the step/return witnesses, destruct the suffix list carried by `l = app(l1, l2)`
  - use small local helper lemmas instead of forcing all list rewriting directly inside the witness
- Current blocker is not yet a specific Coq error message; the next step is to inspect the proof states in `coqtop` and record the first stable failure before editing `proof_manual.v`.

## Round 2

- After compiling `original/<name>.v`, `goal.v`, and `proof_auto.v`, I inspected the four manual obligations in `coqtop`.
- Stable post-`entailer!` shapes:
  - `entail_wit_1`: pure existential witness over `l1` and `l2`, with the heap already in the required form
  - `entail_wit_2`: still needs the heap, but the real work is proving `i + 1 <= n`, choosing the next prefix/suffix split, and showing the extended prefix still has spec `0`
  - `return_wit_1`: pure goal `1 = string_contains_char_spec l c_pre`
  - `return_wit_2`: pure goal `0 = string_contains_char_spec l c_pre`
- The inspection confirmed this is a proof-layer problem, not an annotation gap:
  - the invariant-generated witnesses preserve the intended prefix/suffix structure
  - the remaining obligations are list decomposition and string-spec normalization
- Planned proof additions:
  - one lemma for appending a single nonmatching character to a prefix whose spec is already `0`
  - one lemma for a matching next character after a prefix whose spec is already `0`
  - `CharArray.full_length` bridge in the continue and return-0 proofs to recover `Zlength l = n`

## Round 3

- First stable compile failure: `compile_proof_manual.log` reported `No such contradiction` in `proof_of_string_contains_char_entail_wit_2`.
- Diagnosis:
  - the `i < n` subproof tried to derive impossibility from `H : Znth i (l ++ 0 :: nil) 0 <> c_pre`
  - that is too weak, because the terminator `0` could still differ from `c_pre`
  - the contradiction must use the stronger branch fact `H0 : Znth i (l ++ 0 :: nil) 0 <> 0`
- Fix direction:
  - switch the boundary contradiction in the `i = n` case from `H` to `H0`
  - make the same correction in the empty-suffix subcase of `entail_wit_2`

## Round 4

- The next compile stayed at the same boundary proof, still in `proof_of_string_contains_char_entail_wit_2`.
- Although the rewritten branch semantically reduces to `0 <> 0`, `contradiction` did not pick it up reliably after simplification.
- This is a proof-script stability issue, not a missing fact.
- Fix direction:
  - replace the implicit `contradiction` with the explicit form `exfalso; apply H0; reflexivity`
  - do the same in the empty-suffix contradiction branch

## Round 5

- The next compile exposed the precise residual shape after `app_Znth2`:
  - `H0 : Znth (Zlength l1_2 - Zlength l) (0 :: nil) 0 <> 0`
- So the branch was still missing one explicit arithmetic normalization from the derived length equalities.
- Fix direction:
  - rewrite the boundary index with `Zlength l1_2 = n` and `Zlength l = n`
  - only then finish the contradiction on `Znth 0 (0 :: nil) 0`

## Round 6

- The next compile failure moved from semantics to parser compatibility:
  - this Coq version still rejected the `as [| ...]` destruct naming form
- This matches the repo-wide guidance to prefer conservative syntax and avoid brittle intro-pattern variations.
- Fix direction:
  - switch to plain `destruct`
  - then rename the generated head/tail variables explicitly inside the cons branch

## Round 7

- After switching to plain `destruct`, the next compile failure was `No such hypothesis: H3`.
- Cause:
  - `subst l` had already consumed the equality that introduced the old numbered hypothesis
  - the nil-branch script was still trying to rewrite through that stale name
- Fix direction:
  - stop referencing the consumed equality hypothesis
  - rewrite the trivial `app_nil_r` directly in the remaining branch hypotheses/goals

## Round 8

- The next compile failure moved to the existential witness branch of `entail_wit_2`.
- `entailer!` no longer left an `app_assoc`-shaped subgoal, so the manual `rewrite app_assoc` had no matching target.
- Fix direction:
  - remove that stale rewrite
  - leave the branch to close with the remaining pure obligations only

## Round 9

- A focused `coqtop` probe of `entail_wit_2` showed the post-`entailer!` witness branch is mostly arithmetic; the manual `Zlength_app` rewrite was not aligned with the actual residual goal.
- Fix direction:
  - simplify that bullet to a bare arithmetic discharge
  - keep the real semantic work concentrated in the `Hxneq` branch and the earlier `i < n` proof

## Round 10

- A direct `coqtop` inspection of `entail_wit_2` showed the post-`entailer!` goals in the continue branch were exactly:
  - `string_contains_char_spec (l1_2 ++ x :: nil) c_pre = 0`
  - `Zlength (l1_2 ++ x :: nil) = i + 1`
  - `l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs`
- So the earlier script was failing because it tried to solve the first goal with `lia`, but that goal is not arithmetic.
- Fix:
  - prove the spec goal first using `string_contains_char_spec_app_single`
  - extract `x <> c_pre` from the branch hypothesis after rewriting `H` with `app_assoc` and `app_Znth2`
  - then prove the length goal with `Zlength_app_cons`
  - close the final list equality by `rewrite <- app_assoc`

## Round 11

- After `entail_wit_2` compiled, the blocker moved to `return_wit_1`.
- The remaining issue was structurally the same:
  - the script needed to extract `x = c_pre` from `H`
  - but `H` was still on `((l1 ++ x :: xs) ++ 0 :: nil)`
- Fix:
  - rewrite `H` by `app_assoc` first
  - then use `app_Znth2`, normalize the zero offset, and recover the head element equality

## Round 12

- The last blocker was in `return_wit_2`.
- Two stale proof fragments remained from earlier states:
  - rewriting `app_nil_r` in a hypothesis that no longer had `++ nil`
  - rewriting by a vanished numbered hypothesis `H3`
- The actual nil-branch proof only needed to rewrite the target by `H2` and reduce `l1 ++ nil` back to `l1`.
- The cons-branch only needed the length contradiction from:
  - `l = l1 ++ x :: xs`
  - `Zlength l = n`
  - `Zlength l1 = i = n`
- After removing those stale rewrites and keeping only the current equalities, `proof_manual.v` and `goal_check.v` both compiled successfully.
