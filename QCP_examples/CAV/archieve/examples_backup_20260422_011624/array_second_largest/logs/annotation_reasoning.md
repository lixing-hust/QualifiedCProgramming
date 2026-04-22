# Annotation Reasoning

## 2026-04-19T23:09:41+0800: loop invariant for second-largest scan

The current annotated C file has no loop invariant before the `for (i = 2; i < n; ++i)` scan. That loop starts after `max1` and `max2` have been initialized to the larger and smaller of `l[0]` and `l[1]`. At the loop head, `i` is the next array index to process, so the already-consumed prefix is `sublist(0, i, l)` and the unprocessed suffix is `sublist(i, n, l)`.

The postcondition requires `max2 == second_largest_list(l)` at return while preserving `IntArray::full(a, n, l)`. A weak invariant such as only `2 <= i <= n` would not preserve the semantic relationship between the two local maxima and the original list. The loop body exactly matches the recursive step of `second_largest_acc`: if `a[i] > max1`, the accumulator becomes `(a[i], max1)`; otherwise, if `a[i] > max2`, it becomes `(max1, a[i])`; otherwise it remains unchanged. Therefore the invariant should record:

- `2 <= i && i <= n` for loop bounds and suffix well-formedness.
- `n == n@pre` and `a == a@pre` because the postcondition mentions the original full array and the function does not mutate parameters.
- `IntArray::full(a, n, l)` because the array is read-only and must be preserved.
- `second_largest_acc(max1, max2, sublist(i, n, l)) == second_largest_list(l)` to state that continuing the accumulator over the remaining suffix yields the target full-list result.

This annotation refers directly to `second_largest_acc`, which is defined in `input/array_second_largest.v`. The annotation parser still needs an `Extern Coq` declaration for that symbol, so the annotated file must add `/*@ Extern Coq (second_largest_acc : Z -> Z -> list Z -> Z) */` before the existing `second_largest_list` declaration. After these edits, the next step is to clear stale generated Coq files in this workspace and rerun `symexec`.
