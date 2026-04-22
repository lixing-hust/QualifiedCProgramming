# Verify Issues

## Fingerprint Initialization

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the workspace was bootstrapped before this manual verify continuation.
- Location: `output/verify_20260420_032842_string_count_not_char/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled in a concrete semantic description and controlled keywords for a string counting loop with preserved input memory.
- Result: the fingerprint now has non-empty semantic metadata, and after verification it records `goal_check_passed` and `proof_check_passed`.

## Missing Loop Invariant

- Phenomenon: the active annotated C was identical to the input C and had no invariant for the `while (1)` string scan.
- Trigger: `string_count_not_char` repeatedly reads `s[i]`, conditionally increments `count`, and exits on the zero terminator; `symexec` needs an invariant at the loop head to preserve the processed-prefix semantics.
- Location: `annotated/verify_20260420_032842_string_count_not_char.c`, immediately before the `while (1)`.
- Fix: added a prefix/suffix invariant with `l == app(l1, l2)`, `Zlength(l1) == i`, `count == string_count_not_char_spec(l1, c)`, preserved `s == s@pre` and `c == c@pre`, the no-internal-zero fact, and `CharArray::full`.
- Result: this invariant gave the loop enough state to generate prefix-step and loop-exit witnesses.

## Parser Rejected `sublist`

- Phenomenon: the first `symexec` attempt failed before usable VC generation with `Use of undeclared identifier 'sublist'`.
- Trigger: the initial invariant used `string_count_not_char_spec(sublist(0, i, l), c)`.
- Location: `logs/qcp_run.log` from the first run and `annotated/verify_20260420_032842_string_count_not_char.c`.
- Fix: replaced the `sublist` expression with existential lists `l1` and `l2`, following the accepted string-scan pattern from `string_contains_char`.
- Result: the clean rerun of `symexec` succeeded and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Manual Proof Iteration

- Phenomenon: `string_count_not_char_proof_manual.v` contained five admitted generated lemmas: one safety witness and four entailment witnesses.
- Trigger: the count accumulator and prefix/suffix list step required manual arithmetic and list reasoning.
- Location: `output/verify_20260420_032842_string_count_not_char/coq/generated/string_count_not_char_proof_manual.v`.
- Fix: added helper lemmas for the spec range and append-one behavior, then proved:
  - the increment safety bound from `string_count_not_char_spec_range`;
  - invariant initialization with `l1 = nil` and `l2 = l`;
  - both loop-step cases by moving the head of `l2` into `l1`;
  - the loop-exit assertion by proving `i = n` from the terminator read and no-internal-zero precondition.
- Result: `proof_manual.v` now contains no `Admitted.` and no new `Axiom`.

## Proof Script Compatibility Fixes

- Phenomenon: several compile iterations failed in the manual proof:
  - `Cannot find witness` in the base case of `string_count_not_char_spec_range`;
  - an index mismatch after `app_Znth2` while deriving a contradiction from the terminator cell;
  - a wrong post-`entailer!` bullet order in the loop-step witness;
  - a Ltac parser error for a chained inequality inside `match goal`;
  - the exit witness rewrote `i` through `Zlength l1` instead of through `i = n`.
- Trigger: Coq simplification and generated witness proof states were slightly different from the initially copied `string_contains_char` pattern.
- Location: `logs/compile.log` across failed compile attempts and `logs/proof_reasoning.md` for the detailed proof-state notes.
- Fix: made `Zlength_nil` explicit, normalized actual `Znth` index expressions by pattern, reordered semantic/length bullets after `entailer!`, loosened the Ltac match premise, and rewrote with `Hi_eq_n` before the final separation-logic entailment.
- Result: the final ordered Coq compile chain completed successfully through `string_count_not_char_goal_check.v`.

## Compile And Cleanup

- Phenomenon: successful Coq compilation produced `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` intermediate files in `coq/generated/`.
- Trigger: normal `coqc` output.
- Location: `output/verify_20260420_032842_string_count_not_char/coq/generated/`.
- Fix: removed all non-`.v` files under the workspace `coq/` directory after the successful compile.
- Result: `coq/` now contains only `.v` files.
