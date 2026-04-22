## 2026-04-20 17:20:38 +0800

Program point: the `for (i = 0; i < n; ++i)` loop in `array_all_less_than_k`.

The unannotated loop scans `a[0..n)` from left to right. If it sees `a[i] >= k`, the immediate return value 0 should satisfy the existential branch of the postcondition with the current index `i` as witness. If the loop exits normally, the function returns 1, so the proof needs a universal fact that every element in the whole array is less than `k`.

The loop invariant should therefore describe the already-scanned prefix: `0 <= i <= n`, the parameters `a`, `n`, and `k` are unchanged from pre-state, the prefix fact `(forall j, 0 <= j && j < i => l[j] < k)`, and the unchanged array ownership `IntArray::full(a, n, l)`. Initialization holds at `i = 0` because the prefix is empty. Preservation holds because the loop only continues past the `if (a[i] >= k)` branch when `a[i] < k`, extending the checked prefix from `i` to `i + 1`. Exit usability holds because loop exit gives `i == n`; a minimal assertion immediately after the loop fixes `i == n` and turns the prefix fact into the full-range fact required by the return-1 branch.

Planned annotation changes: add the above `Inv` immediately before the `for` loop and add the loop-exit `Assert` immediately after the loop and before `return 1`.
