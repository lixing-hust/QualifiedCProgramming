# Verification Issues

## Fingerprint completion

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the verify workspace was created before task-specific semantic classification was filled.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_193642_partition_nonnegative/logs/workspace_fingerprint.json`
- Fix: read `doc/retrieval/INDEX.md`, then filled the semantic description for an in-place two-pointer partition and used only controlled-vocabulary keys and values: `two_pointers`, `while_loop`, `if`, `array`, `pointer`, `in_place_update`, `loop_invariant`, `case_split`, `range_bound`, `heap_reasoning`, `nonnegative_input`, `int_range`, and `empty_loop_possible`.
- Result: the fingerprint is non-empty and after final compile was updated with `verification_status: goal_check_passed`.

## Missing loop invariant

- Phenomenon: the active annotated C file initially had no invariant for the loop:

```c
while (i <= j) {
    if (a[i] < 0) {
        i++;
    } else {
        tmp = a[i];
        a[i] = a[j];
        a[j] = tmp;
        j--;
    }
}
```

- Trigger: the postcondition requires a final `l0` satisfying `Permutation(l, l0)`, negative prefix, nonnegative suffix, and `IntArray::full(a, n, l0)`. Without a loop-head invariant, symbolic execution has no durable record of the two classified regions or the current array list after swaps.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_193642_partition_nonnegative.c`
- Fix: added a loop invariant with existential `l_cur`, bounds `0 <= i <= n@pre`, `-1 <= j < n@pre`, crossing relation `i <= j + 1`, unchanged parameters `n == n@pre && a == a@pre`, `Permutation(l, l_cur)`, prefix negativity, suffix nonnegativity, and `IntArray::full(a, n@pre, l_cur)`.
- Result: a clean `symexec` run succeeded and generated fresh Coq files for the current annotated source.

## Symexec invocation

- Phenomenon: generated Coq artifacts had to be regenerated after adding the invariant.
- Trigger: the verify workflow requires rerunning symbolic execution after every annotation edit and clearing stale generated files first.
- Localization: `logs/qcp_run.log` and `logs/symexec_status.log`
- Fix: removed stale generated targets and ran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` with explicit `--goal-file`, `--proof-auto-file`, `--proof-manual-file`, `--goal-check-file`, `--input-file=/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_193642_partition_nonnegative.c`, `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`, `--coq-logic-path=SimpleC.EE.CAV.verify_20260421_193642_partition_nonnegative`, and `--no-exec-info`.
- Result: `logs/qcp_run.log` ends with `Successfully finished symbolic execution`, and `coq/generated/` contains `partition_nonnegative_goal.v`, `partition_nonnegative_proof_auto.v`, `partition_nonnegative_proof_manual.v`, and `partition_nonnegative_goal_check.v`.

## Manual swap proof obligations

- Phenomenon: fresh `coq/generated/partition_nonnegative_proof_manual.v` contained two admitted obligations:

```coq
Lemma proof_of_partition_nonnegative_entail_wit_1 : partition_nonnegative_entail_wit_1.
Proof. Admitted.

Lemma proof_of_partition_nonnegative_entail_wit_2_1 : partition_nonnegative_entail_wit_2_1.
Proof. Admitted.
```

- Trigger: initialization of the invariant and preservation through the nonnegative swap branch require pure list/permutation reasoning that the generated auto file did not discharge.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_193642_partition_nonnegative/coq/generated/partition_nonnegative_proof_manual.v`
- Fix: added local helper lemmas for `replace_nth`, `replace_Znth`, `partition_nonnegative_swap`, swap `Znth` facts, and `partition_nonnegative_swap_perm`. Proved initialization with `Exists l; entailer!`. Proved the swap branch by choosing `partition_nonnegative_swap l_cur_2 i j`, unfolding it for the heap goal, using `store_int_undef_store_int` for `tmp`, splitting the new suffix case at `q = j`, and composing the old permutation with the swap permutation.
- Result: `partition_nonnegative_proof_manual.v` compiles and contains no `Admitted.` or top-level `Axiom`.

## Proof helper compile failures

- Phenomenon: the first manual proof compile failed in a helper with:

```text
Error: Not an inductive definition.
```

- Trigger: the helper `partition_nonnegative_nth_replace_nth_other` used numeric binders named `a` and `b`; after `induction l`, Coq shadowed `a` with the list head of type `T`, so `destruct a` was not destructing a natural number.
- Fix: renamed the numeric binders to `m` and `n`, then destructed those names.
- Result: the helper advanced to later list-swap proof obligations.

- Phenomenon: subsequent helper failures reported `Cannot find witness` in length and `Znth` side conditions around `partition_nonnegative_swap_split_eq`.
- Trigger: compact rewrites such as `rewrite !Zlength_app, !Zlength_cons; lia` did not normalize nested `Z.succ` and nested app lengths enough, and some `rewrite app_Znth2 by lia` calls tried to rewrite multiple occurrences with different side conditions.
- Fix: made length normalization explicit with repeated `Zlength_app` / `Zlength_cons` rewrites and `unfold Z.succ`; added `Zlength_nonneg` facts; rewrote specific `app_Znth1` / `app_Znth2` occurrences with explicit arguments; split the unchanged-index proof into prefix, middle, and tail cases.
- Result: `partition_nonnegative_swap_split_eq` and `partition_nonnegative_swap_perm` compile.

## Compile replay and cleanup

- Phenomenon: verification is not complete until all generated Coq files compile through `goal_check.v`, and compiled intermediates must be removed.
- Trigger: workflow completion criteria require `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile under the workspace load path and `coq/` to contain no non-`.v` intermediates.
- Localization: `logs/compile.log`
- Fix: compiled from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with the documented `BASE` load path and `EXTRA=(-Q "$ORIG" "" -R "$GEN" SimpleC.EE.CAV.verify_20260421_193642_partition_nonnegative)`, then deleted all non-`.v` files under `coq/`.
- Result: full compile replay exited successfully, `partition_nonnegative_goal_check.v` compiled, `rg -n "Admitted\\.|^Axiom\\b" coq/generated/partition_nonnegative_proof_manual.v` returned no matches, and `find coq -type f ! -name '*.v'` returned no files.
