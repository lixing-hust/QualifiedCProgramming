# Verify Issues

## Issue 1: Initial annotated file lacked the scan invariant

- Phenomenon: the active annotated file initially contained the target contract and implementation but no `Inv` for the `while (i + 1 < n)` scan. Without an invariant, symbolic execution would not retain the fact that every candidate index before the current `i` had already been tested and was not a peak.
- Trigger: `array_first_peak` returns early when `a[i] >= a[i - 1] && a[i] >= a[i + 1]`; the postcondition for both the early return and the final `-1` return needs a prefix fact about all earlier interior indices.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260422_010902_array_first_peak.c`, around the loop:

```c
int i = 1;
while (i + 1 < n) {
    if (a[i] >= a[i - 1] && a[i] >= a[i + 1]) {
        return i;
    }
    i++;
}
return -1;
```

- Fix: added a loop invariant at the real while control point. It records `1 <= i && i <= n + 1`, unchanged `a` and `n`, `IntArray::full(a, n, l)`, and the processed-prefix semantic fact:

```c
(forall (j: Z),
  (0 < j && j < i) =>
    (l[j] < l[j - 1] || l[j] < l[j + 1]))
```

- Result: the invariant supplies the early-return prefix property for `0 < j < i` and gives the final return enough semantic information once combined with the loop exit condition.

## Issue 2: Loop condition safety needed an explicit `i + 1` integer-range fact

- Phenomenon: the first successful `symexec` generated a manual safety witness `array_first_peak_safety_wit_2`. The goal required proving the while-condition expression `i + 1` is in signed-int range:

```coq
|-- [| i + 1 <= INT_MAX |] && [| INT_MIN <= i + 1 |]
```

but the invariant at that time only had `1 <= i && i <= n_pre + 1` and `n_pre <= INT_MAX`, which is too weak because it admits unreachable states such as `i = n_pre + 1`.

- Trigger: the C loop condition is `i + 1 < n`, so symbolic execution must prove `i + 1` is safe before evaluating the condition at every loop head.
- Location: generated witness `array_first_peak_safety_wit_2` in `coq/generated/array_first_peak_goal.v` from the first symexec run, caused by the invariant in `annotated/verify_20260422_010902_array_first_peak.c`.
- Fix: strengthened the invariant and loop-exit assertion with:

```c
i + 1 <= INT_MAX
```

This initializes because `i == 1`, and it is preserved because the loop body only executes under `i + 1 < n`; after `i++`, the next loop-head expression is `i_old + 2 <= n <= INT_MAX`.

- Result: after clearing generated files and rerunning `symexec`, the manual safety obligation disappeared. The new `proof_manual.v` contained only `array_first_peak_entail_wit_3`.

## Issue 3: Loop-exit assertion generated one pure entailment witness

- Phenomenon: after the final `symexec`, `coq/generated/array_first_peak_proof_manual.v` contained:

```coq
Lemma proof_of_array_first_peak_entail_wit_3 :
  array_first_peak_entail_wit_3.
Proof. Admitted.
```

The generated goal had the invariant universal over `0 < j < i`, while the loop-exit assertion needed the postcondition range `0 < j < n_pre - 1`.

- Trigger: the loop-exit assertion intentionally bridges the final `-1` return from the processed-prefix invariant to the full interior range. The required arithmetic step is `j < n_pre - 1` and `i + 1 >= n_pre` imply `j < i`.
- Location: `coq/generated/array_first_peak_goal.v`, definition `array_first_peak_entail_wit_3`; proof completed in `coq/generated/array_first_peak_proof_manual.v`.
- Fix: replaced the generated `Admitted.` with:

```coq
Lemma proof_of_array_first_peak_entail_wit_3 : array_first_peak_entail_wit_3.
Proof.
  unfold array_first_peak_entail_wit_3.
  intros.
  Intros.
  entailer!.
  intros j [? ?].
  apply H3.
  lia.
Qed.
```

- Result: `array_first_peak_proof_manual.v` compiled successfully, and `array_first_peak_goal_check.v` compiled successfully afterward.

## Issue 4: Coq compilation artifacts needed cleanup

- Phenomenon: compiling generated Coq files produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `output/verify_20260422_010902_array_first_peak/coq/generated/`.
- Trigger: normal `coqc` compilation of `array_first_peak_goal.v`, `array_first_peak_proof_auto.v`, `array_first_peak_proof_manual.v`, and `array_first_peak_goal_check.v`.
- Location: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010902_array_first_peak/coq/generated/`.
- Fix: ran:

```bash
find /home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260422_010902_array_first_peak/coq -type f ! -name '*.v' -delete
```

- Result: `find .../coq -type f ! -name '*.v'` returned no files; only generated `.v` sources remain in the workspace `coq/` tree.
