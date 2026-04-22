# Proof Reasoning

## Round 1

- Read `string_length_goal.v`, `string_length_proof_auto.v`, and `string_length_goal_check.v`.
- The generated `proof_manual.v` contains exactly two unresolved theorems:
  - `proof_of_string_length_entail_wit_2`
  - `proof_of_string_length_return_wit_1`
- Initial classification:
  - `entail_wit_2` is a loop-preservation arithmetic goal
  - `return_wit_1` is the standard string-scan exit goal where the real bridge is proving `i = n`
- Reusable pattern from nearby verified examples:
  - use `CharArray.full_length` to recover `Zlength l = n`
  - reason by cases on `i < n` versus `i >= n`
  - refute the bad branch with the contract-level nonzero-prefix fact and the generated equality/inequality about `Znth i (l ++ [0])`
- Planned proof shape:
  - keep the scripts conservative with `pre_process`, one explicit length fact, one arithmetic case split, and `entailer!`
  - avoid introducing helper lemmas unless the first compile pass shows a real side-condition gap

## Round 2

- The first `coqc` pass failed at `proof_of_string_length_entail_wit_2` with:
  - `Error: No such goal.`
- Localization:
  - after proving `i < n`, the `entailer!` call already discharged the remaining arithmetic goal
  - the trailing `lia` was therefore acting on an empty proof state
- Fix direction:
  - delete the redundant trailing `lia`
  - rerun the full compile chain before changing any proof content
