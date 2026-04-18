# Proof Reasoning

## Round 1

- `symexec` succeeded on the current annotated file and generated five manual obligations:
  - `proof_of_string_all_lowercase_entail_wit_1`
  - `proof_of_string_all_lowercase_entail_wit_2`
  - `proof_of_string_all_lowercase_return_wit_1`
  - `proof_of_string_all_lowercase_return_wit_2`
  - `proof_of_string_all_lowercase_return_wit_3`
- Obligation split:
  - `entail_wit_1` is the invariant initialization and should be a direct existential witness with `l1 = nil`, `l2 = l`
  - `entail_wit_2` is the invariant preservation step after reading one lowercase character
  - `return_wit_1` and `return_wit_2` should show the full-list spec becomes `0` when the current character is outside `[97, 122]`
  - `return_wit_3` should show the full-list spec becomes `1` when the current character is the terminator `0`
- The closest reusable pattern is `examples/string_contains_char/coq/generated/string_contains_char_proof_manual.v`:
  - use an append-based helper lemma for the prefix summary
  - prove the continue-step entailment by destructing the suffix `l2`
  - prove the terminator return witness by first deriving `i = n` from the nonzero-prefix contract
- Planned helper lemmas:
  - append one lowercase character preserves `string_all_lowercase_spec = 1`
  - appending a character below `97` forces the spec to `0`
  - appending a character above `122` forces the spec to `0`
- First proof attempt will keep the main witnesses short:
  - `Exists` / `subst` / suffix destruct
  - use `CharArray.full_length` only in the terminator branch where `i = n` matters
  - call helper lemmas instead of expanding the fixpoint in every witness

## Round 2

- First compile failure was parser-level, not semantic:
  - file: `coq/generated/string_all_lowercase_proof_manual.v`
  - location: helper lemmas near the `destruct (Z_lt_dec ...); [lia |].` lines
  - error: `Syntax error: ']' expected after [for_each_goal]`
- Cause hypothesis:
  - this Coq/Ltac parser rejects the compact branch form with an intentionally empty second branch
- Fix direction:
  - rewrite those `destruct` steps into explicit named branches
  - keep the proof structure and helper lemmas unchanged

## Round 3

- After the syntax fix, the next stable failure moved to `proof_of_string_all_lowercase_entail_wit_2`.
- Compile error:
  - `Cannot find any non-recursive equality over l.`
- This means `subst l` is too optimistic for the exact generated context shape.
- Fix direction:
  - replace `subst l` with an explicit `rewrite` on the hypothesis `l = app ...`
  - make the same change in the two return witnesses that use the same prefix/suffix equality pattern

## Round 4

- After switching from `subst` to `rewrite`, the preservation proof still had two semantic gaps:
  - `entailer!` left `i + 1 <= n` open
  - the generated bounds on the current character stayed in `Znth 0 ...` form until normalized explicitly
- The successful repair sequence was:
  - derive `Zlength l = n` from `CharArray.full_length`
  - prove `i < n` before constructing the next invariant witness
  - normalize the head-of-suffix bounds with `change (Znth 0 ((x :: xs) ++ 0 :: nil) 0) with x`
  - apply the helper lemmas directly instead of trying to recover them through a brittle `match goal`
- The return witnesses then needed only context-alignment fixes:
  - use the actual post-`entailer!` equality hypothesis for each theorem
  - feed the spec-preservation hypothesis, not the prefix-length hypothesis, into the bad-character helper lemmas
- Final result:
  - `proof_manual.v` compiled
  - `goal_check.v` compiled
  - no `Admitted.` remains in `proof_manual.v`

## Round 5

- Final cleanup and validation:
  - compiled `original/<name>.v`
  - compiled `goal.v`
  - compiled `proof_auto.v`
  - compiled `proof_manual.v`
  - compiled `goal_check.v`
  - deleted all non-`.v` files under `coq/`
- No experience document update was necessary for this run because the issues were already covered by the existing verify experience notes.
