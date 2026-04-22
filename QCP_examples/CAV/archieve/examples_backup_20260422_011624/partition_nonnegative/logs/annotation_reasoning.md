# Annotation Reasoning

## Initial loop invariant plan

- Program point: the only loop, `while (i <= j)`, in `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_193642_partition_nonnegative.c`.
- Current blocker: the active annotated file has no `Inv` for the loop, but the postcondition requires a final array list `l0` such that `Permutation(l, l0)`, all elements before the returned split index are negative, all elements from the split index to `n` are nonnegative, and `IntArray::full(a, n, l0)` holds. Without a loop-head invariant, symbolic execution cannot preserve the current array contents, the permutation relation after swaps, or the two classified regions across loop iterations.
- Pre-edit C fragment:

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

- Planned invariant: introduce `exists l_cur` for the current heap array. Keep bounds `0 <= i && i <= n@pre`, `-1 <= j && j < n@pre`, and `i <= j + 1`; keep unchanged inputs `n == n@pre && a == a@pre`; keep `Permutation(l, l_cur)` and `IntArray::full(a, n@pre, l_cur)`; state the processed prefix property `(forall p, 0 <= p && p < i => l_cur[p] < 0)`; and state the processed suffix property `(forall q, j < q && q < n@pre => l_cur[q] >= 0)`.
- Why initialization holds: before the first loop test, `i == 0` and `j == n - 1`. The prefix range `[0, i)` is empty, and the suffix range `(j, n)` is also empty. `i <= j + 1` becomes `0 <= n`, which follows from the precondition. The current list can be the input list `l`, so `Permutation(l, l_cur)` is reflexive and the initial `IntArray::full(a, n, l)` supplies the heap.
- Why the negative branch preserves it: inside the loop, `i <= j`, so `i` is a valid index. If `a[i] < 0`, incrementing `i` extends the negative prefix by exactly the old `a[i]`, while the array list and suffix are unchanged. The boundary `i <= j + 1` remains true after the increment because the old loop guard gives `i <= j`.
- Why the nonnegative branch preserves it: if `a[i] >= 0`, the code swaps `a[i]` and `a[j]`, then decrements `j`. The prefix `[0, i)` is unchanged because `i` is not advanced. The new suffix starts at the old `j`; the element placed there is the old `a[i]`, known nonnegative from the branch condition, and the old suffix already satisfied the nonnegative property. The swap changes the current list but should preserve `Permutation(l, l_cur)` through a later manual proof obligation.
- Why exit can prove the postcondition: loop exit gives `i > j`, while the invariant gives `i <= j + 1`, so `i == j + 1`. Therefore the processed prefix `[0, i)` and processed suffix `(j, n)` combine exactly into `[0, i)` and `[i, n)`, matching the two `forall` clauses in the postcondition with return value `i`.

Post-edit target fragment:

```c
    /*@ Inv
          exists l_cur,
            0 <= i && i <= n@pre &&
            -1 <= j && j < n@pre &&
            i <= j + 1 &&
            n == n@pre && a == a@pre &&
            Permutation(l, l_cur) &&
            (forall (p: Z),
              (0 <= p && p < i) => l_cur[p] < 0) &&
            (forall (q: Z),
              (j < q && q < n@pre) => l_cur[q] >= 0) &&
            IntArray::full(a, n@pre, l_cur)
    */
    while (i <= j) {
```
