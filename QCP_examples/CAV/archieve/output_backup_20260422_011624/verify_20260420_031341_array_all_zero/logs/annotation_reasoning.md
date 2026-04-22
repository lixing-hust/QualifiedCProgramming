## 2026-04-20 03:14:29 +0800

Program point: the `for (i = 0; i < n; ++i)` loop in `array_all_zero`.

The unannotated loop scans `a[0..n)` from left to right. If it sees `a[i] != 0`, the immediate return value 0 satisfies the existential branch of the postcondition using the current index as witness. If the loop exits normally, the function returns 1, so the proof needs a universal fact that every element in the whole range is zero.

The loop invariant must therefore describe the already-scanned prefix: `0 <= i <= n`, the parameters `a` and `n` are unchanged from pre-state, the prefix fact `(forall j, 0 <= j && j < i => l[j] == 0)`, and the unchanged array ownership `IntArray::full(a, n, l)`. Initialization holds because the prefix is empty at `i = 0`. Preservation holds because the loop only continues past the `if (a[i] != 0)` when `a[i] == 0`, extending the all-zero prefix from `i` to `i + 1`. Exit usability holds because loop exit gives `i == n`; adding a minimal loop-exit `Assert` after the loop fixes `i == n` and rewrites the prefix fact into the full-range fact needed by the return-1 branch.

Planned annotation changes: add the above `Inv` immediately before the `for` loop and add the loop-exit `Assert` immediately after the loop and before `return 1`.
