## Round 1

- Program point: the `for (i = 0; i < n; ++i)` loop in `annotated/verify_20260420_120451_array_last_positive.c` has no invariant, so symbolic execution has no preserved summary for `ans` or for the read-only `IntArray::full(a, n, l)` ownership across iterations.
- Loop meaning: at the loop head, `i` is the next index to inspect and `[0, i)` is the processed prefix.
- Required semantic summary: after scanning a prefix, either `ans == -1` and every processed element is nonpositive, or `ans` is a valid processed index with `l[ans] > 0` and every later processed index in the processed prefix is nonpositive.
- Stable facts to preserve: `0 <= i && i <= n`, unchanged parameters `a == a@pre` and `n == n@pre`, bound facts `-1 <= ans && ans < i`, and `IntArray::full(a, n, l)` because the function only reads the array.
- Initialization check: before the first loop test, `i == 0` and `ans == -1`; the processed-prefix universal property over `[0,0)` is vacuous and `ans < i` is `-1 < 0`.
- Preservation check: if `a[i] > 0`, assigning `ans = i` makes the positive-index case true for `[0,i+1)` and the later-index universal fact is vacuous. If `a[i] <= 0`, the existing no-positive/last-positive facts extend to `[0,i+1)` using the current read at index `i`.
- Exit use: on loop exit, `i == n`, so the processed-prefix summary is exactly the full-array postcondition. A small exit `Assert` immediately after the loop will restate `i == n` and the whole-range implication form before `return ans`.

## Planned edit

- Add one loop invariant before the `for` loop with bounds, unchanged parameters, array ownership, and implication-form last-positive prefix facts.
- Add one loop-exit `Assert` immediately after the loop to bridge from `i == n` to the function postcondition.

