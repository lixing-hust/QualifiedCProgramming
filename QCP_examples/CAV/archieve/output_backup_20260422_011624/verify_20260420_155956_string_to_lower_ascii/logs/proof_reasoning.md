# Proof Reasoning

## Round 1: five manual witnesses after symexec

- `symexec` succeeded on the active annotated C and generated `string_to_lower_ascii_goal.v`, `string_to_lower_ascii_proof_auto.v`, `string_to_lower_ascii_proof_manual.v`, and `string_to_lower_ascii_goal_check.v`.
- The manual file contains five admitted obligations: `proof_of_string_to_lower_ascii_entail_wit_1`, `proof_of_string_to_lower_ascii_entail_wit_2_1`, `proof_of_string_to_lower_ascii_entail_wit_2_2`, `proof_of_string_to_lower_ascii_entail_wit_2_3`, and `proof_of_string_to_lower_ascii_return_wit_1`.
- The closest reusable proof pattern is `examples/string_to_upper_ascii/coq/generated/string_to_upper_ascii_proof_manual.v`; the invariant and witness shape are the same, except the character range is `65..90` and the replacement is `x - 65 + 97`.
- Planned helper lemmas:
  - append and length preservation for `string_to_lower_ascii_spec`
  - range case lemmas for `lower_ascii_char`
  - a current-head lookup lemma after the transformed prefix
  - a replacement lemma for the uppercase branch
  - a preservation lemma for non-uppercase branches
- Expected proof shape:
  - the initial invariant witness extracts `CharArray.full_length`, chooses `nil` and `l`, and discharges list length arithmetic
  - the three preservation witnesses destruct `l2`, expose the current head, and either rewrite the replacement or preserve the list
  - the return witness first proves `i = n` from the zero read and the no-internal-zero precondition, then reduces the suffix to `nil`

## Round 2: first compile failure in initialization witness

- Compile command reached `string_to_lower_ascii_proof_manual.v` and failed at line 131 with `Error: No such goal.`
- Location: `proof_of_string_to_lower_ascii_entail_wit_1`, immediately after `entailer!`.
- Cause: in this generated goal, unlike the older upper-case example, `entailer!` already closes the initialization witness after choosing `nil` and `l`; the following length-rewrite script is therefore applied when no subgoal remains.
- Fix plan: remove the three post-`entailer!` lines from this witness only, then rerun the full compile chain with shell `set -e` so later compile steps do not mask an earlier failure.

## Round 3: generated hypothesis names differ from the upper-case example

- After the initialization fix, compilation failed in `proof_of_string_to_lower_ascii_entail_wit_2_1` at line 137 with `Error: Found no subterm matching "Zlength nil" in H7.`
- `coqtop` showed that this task's invariant includes an explicit `Zlength l = n`, so the generated hypothesis names are shifted relative to the older `string_to_upper_ascii` proof:
  - for `entail_wit_2_1`, suffix length is `H8`, prefix length is `H7`
  - for `entail_wit_2_2`, suffix length is `H7`, prefix length is `H6`
  - for `entail_wit_2_3`, suffix length is `H8`, prefix length is `H7`
  - for `return_wit_1`, split is `H3`, prefix length is `H5`, suffix length is `H6`, and the nonzero facts are `H7` / `H11`
- Fix plan: update only these generated-hypothesis references and rerun the full compile chain.

## Round 4: return witness hypothesis names and final compile

- The next compile failures were the same generated-name issue in `entail_wit_2_3` and `return_wit_1`.
- `coqtop` showed that `return_wit_1` uses `H2` for `l = app(l1, l2)`, `H4` for `Zlength(l1) = i`, `H5` for `Zlength(l2) = n - i`, and `H10` for the preserved nonzero fact.
- Updated those references in the proof script.
- Final compile result: `original/string_to_lower_ascii.v`, `string_to_lower_ascii_goal.v`, `string_to_lower_ascii_proof_auto.v`, `string_to_lower_ascii_proof_manual.v`, and `string_to_lower_ascii_goal_check.v` all compiled successfully. `proof_manual.v` has no `Admitted.` and no added `Axiom`.
