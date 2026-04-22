# Proof Reasoning

## Round 1

- Read `string_equal_goal.v`, `string_equal_proof_auto.v`, and `string_equal_goal_check.v`.
- The generated `proof_manual.v` contains eleven unfinished lemmas:
  - `proof_of_string_equal_entail_wit_2`
  - `proof_of_string_equal_entail_wit_3_1`
  - `proof_of_string_equal_entail_wit_3_2`
  - `proof_of_string_equal_entail_wit_4_1`
  - `proof_of_string_equal_entail_wit_4_2`
  - `proof_of_string_equal_return_wit_1`
  - `proof_of_string_equal_return_wit_2`
  - `proof_of_string_equal_return_wit_3`
  - `proof_of_string_equal_return_wit_4`
  - `proof_of_string_equal_return_wit_5`
  - `proof_of_string_equal_return_wit_6`
- Classification:
  - `entail_wit_2` is the loop-preservation step after reading equal nonzero characters
  - `entail_wit_3_*` and `entail_wit_4_*` are the loop-exit bridge goals that turn the first seen `0` into exact index equalities and then into `na = nb`
  - the `return_wit_*` goals are pure list/string-spec obligations over `string_equal_spec`
- Planned helper-lemma set:
  - one equality lemma for `string_equal_spec`
  - one mismatch lemma for the first unequal index
  - one or two “one string ends while the other still has a nonzero character” lemmas
- Proof strategy:
  - keep witness scripts short with `pre_process`, `entailer!`, explicit length facts from `CharArray.full_length`, and calls into helper lemmas
  - only add extra local lemmas if the first compile pass shows a real side-condition gap

## Round 2

- The first manual-proof pass against the original generated VC exposed a real annotation problem rather than a pure proof problem.
- Stable blocker:
  - `entail_wit_4_1` / `entail_wit_4_2` tried to derive `na = nb` from two observed zero characters without carrying the contract facts that all earlier characters are nonzero.
- Diagnosis:
  - the post-loop and branch-local assertions in the annotated C file had dropped those nonzero-prefix facts
  - this made the generated witness genuinely underpowered
- Action:
  - stop proof iteration
  - return to the annotation layer
  - add the preserved nonzero-prefix facts to the invariant, the loop-exit assertion, and the `return 1` branch assertion
  - rerun `symexec` from a clean generated directory

## Round 3

- After regenerating the VC, the key exit witnesses were now in the expected shape:
  - `entail_wit_4_1` and `entail_wit_4_2` both retained the nonzero-prefix assumptions
  - `return_wit_3` and `return_wit_4` also retained them, making the “zero versus nonzero at the same index” proof path viable
- New proof plan:
  - add reusable helper lemmas for:
    - `Znth` at the final appended terminator
    - “first zero is at the logical end” reasoning
    - `string_equal_spec` equality and mismatch cases
    - the shorter-string case where one side reaches `0` while the other still has a nonzero character
  - then discharge each witness with short scripts instead of proving list semantics inline

## Round 4

- The helper-lemma layer now compiles partway, but the full manual proof still fails before reaching `goal_check`.
- Current stable blocker:
  - the witness proofs were first written with `unfold ...; intros ...`, but these generated entailment theorems need the repository’s `pre_process`-style proof shape
  - after switching direction, the helper lemmas still needed several compatibility fixes for this Coq build (`induction ... as ...` parsing, `Znth` rewrites, explicit side conditions)
- Current status:
  - the regenerated VC is meaningful
  - the active `string_equal_proof_manual.v` contains substantial helper-lemma progress and no remaining `Admitted.`
  - but `coqc` still fails inside the manual proof file, so the verification task is not complete
- Next proof step if work continues:
  - rewrite the witness proofs from `proof_of_string_equal_entail_wit_1` onward into the same conservative `pre_process` pattern used by `examples/string_length`
  - then replay `proof_manual.v` and `goal_check.v` again
