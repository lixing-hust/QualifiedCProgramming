# Annotation Reasoning

## Initial loop invariant plan

- Program point: outer `for (i = 0; i < n; ++i)` in `annotated/verify_20260421_173306_selection_sort.c`.
- Current blocker: the input contract requires the final array list to be both `sorted_z` and a `Permutation` of the original `l`, but the active annotated file has no loop invariants, so symbolic execution has no way to preserve heap shape or sorting/permutation facts across the nested loops and swap.
- Planned outer invariant: carry an existential current array list `l_outer` with `IntArray::full(a, n@pre, l_outer)`, `Permutation(l, l_outer)`, unchanged parameters `n == n@pre` and `a == a@pre`, bounds `0 <= i <= n@pre`, sorted processed prefix `sorted_z(sublist(0, i, l_outer))`, and a partition ordering fact saying every processed-prefix element is `<=` every suffix element.
- Why this should establish the postcondition: when the outer loop exits, `i == n@pre`; the sorted prefix covers the full array, the permutation fact relates the final list to the original input list, and the heap predicate supplies the final `IntArray::full`.

## Inner loop invariant plan

- Program point: inner `for (j = i + 1; j < n; ++j)`.
- Current blocker: selection sort needs to remember that `min_idx` identifies the minimum element in the scanned suffix interval `[i, j)`. Without this fact, the later swap cannot prove that the new prefix element is less than or equal to the remaining suffix.
- Planned inner invariant: carry an existential current array list `l_inner` with the outer invariant facts, bounds `0 <= i < n@pre`, `i + 1 <= j <= n@pre`, `i <= min_idx < j`, and a minimum fact `(forall k, i <= k < j => l_inner[min_idx] <= l_inner[k])`.
- Why this should be preserved: initially `j == i + 1` and `min_idx == i`, so the scanned interval contains only `i`. If `a[j] < a[min_idx]`, assigning `min_idx = j` makes the newly read element the minimum of `[i, j + 1)`; otherwise the old `min_idx` remains a minimum after adding `j`.
- Expected swap bridge: after the inner loop exits with `j == n@pre`, `min_idx` is minimum in the whole suffix. Swapping `a[i]` and `a[min_idx]` should preserve permutation and extend the sorted prefix by one element because all old prefix elements are already `<=` all suffix elements.
