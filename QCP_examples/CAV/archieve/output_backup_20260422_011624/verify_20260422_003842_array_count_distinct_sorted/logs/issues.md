# Verify Issues

## Workspace fingerprint initially empty

- Phenomenon: `logs/workspace_fingerprint.json` had an empty `semantic_description` and `{}` keywords.
- Trigger: the workspace was freshly initialized before the verify run.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_003842_array_count_distinct_sorted/logs/workspace_fingerprint.json`.
- Fix action: read the repository-level `doc/retrieval/INDEX.md`, then filled a nonempty semantic description and used only controlled-vocabulary keyword keys and values. After successful `goal_check`, added `verification_status` values `goal_check_passed` and `proof_check_passed`.
- Result: the fingerprint now describes the sorted read-only array scan and has controlled keywords only.

## Missing loop invariant for prefix distinct count

- Phenomenon: the active annotated C initially had no invariant on the `while (i < n)` loop, so symbolic execution would have no durable relationship between `count`, `i`, and `array_count_distinct_sorted_spec(l)`.
- Trigger: `array_count_distinct_sorted` scans a prefix and updates `count` conditionally based on adjacent equality.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260422_003842_array_count_distinct_sorted.c`, immediately before the `while (i < n)` loop.
- Fix action: after recording `logs/annotation_reasoning.md`, inserted this invariant:

```c
/*@ Inv
      1 <= i && i <= n &&
      1 <= count && count <= i &&
      a == a@pre &&
      n == n@pre &&
      count == array_count_distinct_sorted_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
```

- Result: `symexec` succeeded on the current annotated file and generated fresh `array_count_distinct_sorted_goal.v`, `array_count_distinct_sorted_proof_auto.v`, `array_count_distinct_sorted_proof_manual.v`, and `array_count_distinct_sorted_goal_check.v`.

## `symexec` option form must use equals for long file options

- Phenomenon: the first manual `symexec` command exited with status `1` before parsing the program. `logs/qcp_run.log` contained:

```text
goal file not specified
Start to symbolic execution on program : (null)
```

- Trigger: the command used space-separated long options such as `--goal-file /path/to/file`.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_003842_array_count_distinct_sorted/logs/qcp_run.log`.
- Fix action: reran `symexec` with equals-form long options:

```text
--goal-file=... --proof-auto-file=... --proof-manual-file=... --goal-check-file=... --input-file=...
```

- Result: `symexec` exited with status `0`; the log ended with `Successfully finished symbolic execution`.

## Manual proof obligations required prefix-extension helper lemmas

- Phenomenon: `coq/generated/array_count_distinct_sorted_proof_manual.v` contained five `Admitted.` stubs:

```coq
proof_of_array_count_distinct_sorted_entail_wit_1
proof_of_array_count_distinct_sorted_entail_wit_2_1
proof_of_array_count_distinct_sorted_entail_wit_2_2
proof_of_array_count_distinct_sorted_return_wit_1
proof_of_array_count_distinct_sorted_return_wit_2
```

- Trigger: the loop invariant uses `array_count_distinct_sorted_spec (sublist 0 i l)`, so Coq needed explicit list lemmas for initializing a one-element prefix, extending a prefix by one element, and turning the full prefix back into `l` at loop exit.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_003842_array_count_distinct_sorted/coq/generated/array_count_distinct_sorted_proof_manual.v`.
- Fix action: added local helper lemmas:
  - `array_count_distinct_sorted_from_app_one`
  - `array_count_distinct_sorted_spec_app_one`
  - `last_sublist_prefix`
  - `array_count_distinct_sorted_spec_sublist_extend`
  - `sublist_0_over_length`
  - `array_count_distinct_sorted_spec_sublist_0_1_one`
- Result: the five manual witness lemmas now end with `Qed.` and the manual proof file contains no `Admitted.` and no `Axiom`.

## Proof script parser and arithmetic stability fixes

- Phenomenon: during compile replay, Coq reported:

```text
Error: Tactic failure: Cannot find witness.
Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'
```

- Trigger: an unused copied bounds helper had fragile arithmetic; a final `reflexivity` in the append-one helper was too syntactic after `Z` simplification; `destruct xs as [| h tl]` parsed poorly under `Local Open Scope sac`; and the empty-array return witness needed an explicit `Zlength_nonneg` fact in the impossible nonempty-list branch.
- Localization: `array_count_distinct_sorted_proof_manual.v`, helper lemmas and `proof_of_array_count_distinct_sorted_return_wit_1`.
- Fix action: removed unused bounds helpers, kept the append-one proof in `1 + from ...` form with explicit `Z.eq_dec` case split and `lia`, changed the destruct syntax to `destruct xs.`, and added `pose proof (Zlength_nonneg l)` before the contradiction in `return_wit_1`.
- Result: the full documented compile replay passed through `array_count_distinct_sorted_goal_check.v`.

## Final compile and cleanup

- Phenomenon: the workflow requires all generated Coq files to compile and non-`.v` Coq artifacts to be removed before success.
- Trigger: successful `coqc` produced `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` files under `coq/generated/`.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_003842_array_count_distinct_sorted/coq/generated/`.
- Fix action: compiled from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the documented base `-R` paths, `-Q "$ORIG" ""`, and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_003842_array_count_distinct_sorted`; then deleted all files under `coq/` whose names do not end in `.v`.
- Result: `original/array_count_distinct_sorted.v`, `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compiled successfully, and `find coq -type f ! -name '*.v'` prints no files.
