# Proof Reasoning

## Round 1

- Read `string_all_lowercase_goal.v`, `string_all_lowercase_proof_auto.v`, and `string_all_lowercase_goal_check.v`.
- Manual obligations generated in `string_all_lowercase_proof_manual.v`:
  - `proof_of_string_all_lowercase_entail_wit_2`
  - `proof_of_string_all_lowercase_entail_wit_3`
  - `proof_of_string_all_lowercase_return_wit_1`
  - `proof_of_string_all_lowercase_return_wit_2`
  - `proof_of_string_all_lowercase_return_wit_3`
- First classification:
  - `entail_wit_2` is the loop-preservation step for extending the processed lowercase prefix from `i` to `i + 1`
  - `entail_wit_3` is the loop-exit bridge and should mainly need `i = n`
  - the three `return_wit_*` obligations are pure list/spec lemmas:
    - first bad character greater than `122` implies spec `0`
    - first bad character less than `97` implies spec `0`
    - all characters lowercase implies spec `1`
- Initial proof plan:
  - prove `entail_wit_2` and `entail_wit_3` directly with `entailer!` plus arithmetic and list-length facts
  - add helper lemmas over `string_all_lowercase_spec` for:
    - all-elements-lowercase lists
    - a first out-of-range element forcing result `0`
  - keep the witness proofs short and use those helper lemmas instead of redoing the recursion in every theorem

## Round 2

- Added two helper lemmas to `string_all_lowercase_proof_manual.v`:
  - `string_all_lowercase_spec_all`
  - `string_all_lowercase_spec_bad_at`
- These compiled far enough to confirm the overall proof direction is sound:
  - `return_wit_1` and `return_wit_2` can be reduced to "there exists a first bad index"
  - `return_wit_3` can be reduced to "all indices satisfy the lowercase range"
- The main friction in this round was Coq syntax compatibility in this environment:
  - `induction ... as [| ...]`
  - bracketed tactical forms like `[lia |]`
  - compact nested bullet patterns
- I rewrote those pieces into a more conservative style and recompiled after each change.

## Round 3

- First stable proof blocker after syntax cleanup:
  - `proof_of_string_all_lowercase_entail_wit_2`
- What is already established:
  - `symexec` generated the expected witness shape from the revised invariant
  - the helper lemmas for the three return witnesses are present in the manual proof file
  - non-`.v` files under `coq/` were cleaned after the compile attempts
- Current failing point:
  - the branch proving the new processed index `k = i` still needs a stable way to recover the current character bounds from the post-`entailer!` proof state
  - compile failure at the end of this run:
    - file: `coq/generated/string_all_lowercase_proof_manual.v`
    - location: the `match goal with ...` block inside `proof_of_string_all_lowercase_entail_wit_2`
    - error class: `No matching clauses for match`
- Diagnosis:
  - this is no longer an annotation-layer problem
  - the remaining issue is proof-state fragility: the exact pure hypotheses available after `entailer!` are not matching the current proof script shape consistently enough
- If continuing from this workspace, the next step should be:
  - inspect the exact post-`entailer!` context for `string_all_lowercase_entail_wit_2` with an interactive `coqtop` session
  - then rewrite that witness proof without assumption-name guesses or fragile `match goal` patterns
