## 2026-04-20 annotation plan

The unannotated `for (i = 0; i < n; ++i)` loop cannot expose the final array relation required by `Ensure`. The postcondition needs a witness list `l0` of length `n` such that each original negative element from `l` has become `0`, and each original nonnegative element is preserved. Since the function updates `a` in place, the loop invariant must describe the current heap contents, not a separate output buffer.

At the loop guard, `i` is the next index to process. The invariant will split the current array contents into `app(l1, l2)`: `l1` has length `i` and already satisfies the replacement relation against the original list `l`; `l2` has length `n@pre - i` and is still equal to the original suffix `sublist(i, n@pre, l)`, expressed pointwise as `l2[t] == l[i + t]`. It also preserves `a == a@pre`, `n == n@pre`, and the original length fact `n@pre == Zlength(l)`.

Initialization should hold with `i == 0`, `l1 == nil`, and `l2 == l`. Preservation should hold because each iteration reads `a[i]`; if the original/current element is negative, the branch writes `0`, otherwise it leaves the element unchanged. In both cases the processed prefix grows by one element satisfying the postcondition relation. On loop exit, `i == n@pre`, so `l2` is empty and `app(l1, l2)` gives a full result list matching the required `exists l0` witness.
