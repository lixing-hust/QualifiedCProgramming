# Verify Issues

## Fingerprint initially had empty semantic fields

- Phenomenon: `logs/workspace_fingerprint.json` was still at the script
  placeholder state, with `"semantic_description": ""` and `"keywords": {}`.
- Trigger: the workspace had only `original/` inputs and initial Codex logs.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_005007_array_intersection_count_sorted/logs/workspace_fingerprint.json`.
- Fix action: read the repository-level `doc/retrieval/INDEX.md`, then filled
  a nonempty semantic description and used only controlled-vocabulary keyword
  keys and values.  After final `goal_check`, added
  `verification_status: ["goal_check_passed", "proof_check_passed"]`.
- Result: the fingerprint now describes the sorted-array two-pointer counting
  task and uses only controlled vocabulary.

## Missing loop invariant in the initial annotated C

- Phenomenon: the active annotated C initially had no `Inv` before the loop:

```c
int i = 0;
int j = 0;
int count = 0;
while (i < n && j < m) {
    ...
}
```

- Trigger: `symexec` needs a loop-head assertion for every loop path and also
  needs a semantic relationship between `count` and the remaining suffix
  problem.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260422_005007_array_intersection_count_sorted.c`.
- Fix action: added a loop invariant preserving index bounds, parameter
  equalities, list lengths, sortedness facts, both `IntArray::full` resources,
  and the semantic equation:

```c
count + array_intersection_count_sorted_spec(sublist(i, n, la), sublist(j, m, lb)) ==
  array_intersection_count_sorted_spec(la, lb)
```

- Result: a clean `symexec` run succeeded and generated fresh `goal`,
  `proof_auto`, `proof_manual`, and `goal_check` files.

## Manual proof obligations after successful symexec

- Phenomenon: `coq/generated/array_intersection_count_sorted_proof_manual.v`
  contained six generated admissions:

```coq
proof_of_array_intersection_count_sorted_entail_wit_1
proof_of_array_intersection_count_sorted_entail_wit_2_1
proof_of_array_intersection_count_sorted_entail_wit_2_2
proof_of_array_intersection_count_sorted_entail_wit_2_3
proof_of_array_intersection_count_sorted_return_wit_1
proof_of_array_intersection_count_sorted_return_wit_2
```

- Trigger: the generated VCs required pure list/spec reasoning over suffixes
  such as `sublist i n la` and `sublist j m lb`; `entailer!` alone cannot
  unfold the recursive two-list spec through those suffix decompositions.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_005007_array_intersection_count_sorted/coq/generated/array_intersection_count_sorted_proof_manual.v`.
- Fix action: added helper lemmas for nonempty suffix decomposition,
  nil-right behavior, and equal/less-than/greater-than recursive spec
  advancement.  The branch witnesses rewrite the relevant helper and finish
  with `entailer!`; the return witnesses normalize an empty suffix and derive
  `count = array_intersection_count_sorted_spec la lb`.
- Result: `array_intersection_count_sorted_proof_manual.v` compiles and has no
  `Admitted.` or top-level `Axiom`.

## Coq parser rejected compact proof-script syntax

- Phenomenon: the first manual proof compile stopped at the helper lemma:

```text
File ".../array_intersection_count_sorted_proof_manual.v", line 38, characters 17-19:
Error:
Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as' (in [as_or_and_ipat]).
```

  A later compile stopped at compact destruct syntax:

```text
File ".../array_intersection_count_sorted_proof_manual.v", line 73, characters 55-57:
Error: Syntax error: ']' expected after [for_each_goal] (in [ltac_expr]).
```

- Trigger: the local Coq/Ltac parser accepted simpler scripts but rejected
  `induction a as [| x xs IH]` and bracketed destruct alternatives like
  `destruct ...; [lia|].` in this file context.
- Localization: `array_intersection_count_sorted_spec_nil_r`,
  `array_intersection_count_sorted_spec_advance_lt`, and
  `array_intersection_count_sorted_spec_advance_gt`.
- Fix action: rewrote the induction as:

```coq
intros a.
induction a; simpl; auto.
```

  and expanded compact destruct alternatives into explicit bullets.
- Result: the helper lemmas compiled and the proof advanced to the return
  witnesses.

## Return witness initially rewrote the wrong numbered hypothesis

- Phenomenon: compile stopped with:

```text
File ".../array_intersection_count_sorted_proof_manual.v", line 134, characters 2-35:
Error: Found no subterm matching "sublist ?M8825 ?M8826 ?M8824" in H13.
```

- Trigger: after `pre_process`, generated hypothesis numbers were not the same
  as the guessed proof script expected.  A `coqtop` probe showed `H13` was the
  sortedness fact for `lb`, while the semantic invariant was:

```coq
H14 :
  count +
  array_intersection_count_sorted_spec (sublist i_3 n_pre la)
    (sublist j_3 m_pre lb) = array_intersection_count_sorted_spec la lb
```

- Localization: `proof_of_array_intersection_count_sorted_return_wit_1` and
  `proof_of_array_intersection_count_sorted_return_wit_2`.
- Fix action: replaced numbered-hypothesis rewrites with `match goal` patterns
  that select the semantic equation by the `array_intersection_count_sorted_spec`
  context and rewrite the appropriate empty suffix.
- Result: both return witnesses compiled, and the final
  `array_intersection_count_sorted_goal_check.v` compile passed.

## Coq build artifacts required cleanup

- Phenomenon: successful `coqc` runs produced `.aux`, `.glob`, `.vo`, `.vok`,
  and `.vos` files under `coq/generated/`.
- Trigger: normal Coq compilation output.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_005007_array_intersection_count_sorted/coq/generated/`.
- Fix action: ran `find coq -type f ! -name '*.v' -delete` inside the workspace.
- Result: `find coq -type f ! -name '*.v'` prints no files; only `.v`
  generated sources remain under `coq/`.
