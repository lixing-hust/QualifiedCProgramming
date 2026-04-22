# Annotation Reasoning

## Round 1

- Current program point: the only loop is `for (i = 0; i < n; ++i)`, and the unannotated copy gives no loop invariant for `symexec` to preserve the relation between `cnt` and the processed array prefix.
- Loop shape: at the loop head, `i` is the next unread index, so the processed region is exactly `sublist(0, i, l)`.
- Required postcondition: after the loop, the verifier must prove `cnt == array_count_greater_than_k_spec(l, k)` and preserve `IntArray::full(a, n, l)`.
- Stable facts needed across the loop: `a == a@pre`, `n == n@pre`, `k == k@pre`, bounds `0 <= i && i <= n`, and unchanged full-array ownership `IntArray::full(a, n, l)`.
- Semantic invariant: `cnt == array_count_greater_than_k_spec(sublist(0, i, l), k)`. This matches initialization because `i == 0` and `cnt == 0`, and `sublist(0, 0, l)` is empty. It matches preservation because each iteration reads `a[i]`, branches on `a[i] > k`, and increments `cnt` exactly when the recursive spec contributes one for the newly included element.
- Exit usefulness: when the loop condition is false, the invariant gives `i == n`; together with `Zlength(l) == n`, the prefix summary over `sublist(0, i, l)` should rewrite to the full-list summary required by the postcondition.

## Planned edit

- Add one loop invariant before the `for` loop carrying bounds, unchanged parameters, the prefix-count summary, and the full array predicate.
- Add one loop-exit `Assert` immediately after the loop to fix `i == n` and expose `cnt == array_count_greater_than_k_spec(l, k)` for the return witness.
