# Contract reasoning: array_find_last_equal

## Source semantics

The target function scans an integer array `a` of logical length `n` from left to right. It maintains `ans`, initially `-1`, and updates `ans` to the current index whenever `a[i] == k`. Therefore the return value is:

- `-1` if no index in `[0, n)` stores `k`;
- otherwise the greatest index `j` such that `0 <= j < n` and `a[j] == k`.

The implementation does not write through `a`, so the array contents and ownership predicate must be preserved by the postcondition.

## Boundary conditions

- `n == 0`: the loop body is skipped and the function returns `-1`.
- `n > 0` with no match: `ans` remains `-1`.
- Multiple matches: each later match overwrites `ans`, so the final result is the last matching index.
- Match at index `0` or `n - 1`: both are covered by the same greatest-index postcondition.

## Memory model

The input pointer `a` is specified by `IntArray::full(a, n, l)` with `Zlength(l) == n`. This gives the function read access to exactly the logical array segment described by `l`.

Because the function only reads `a`, the postcondition restores `IntArray::full(a, n, l)` with the same logical list.

## Contract choice

No extra Coq file is needed. The last-match property is directly expressible in the C contract using first-order quantification over indices:

- the `-1` branch says every valid element differs from `k`;
- the success branch says the returned index is valid, stores `k`, and every later valid index differs from `k`.

This is a complete external semantic specification for "last equal" and does not require a task-specific recursive Coq function.

## Verification-stage boundary

This contract intentionally does not include loop invariants, assertions, bridge assertions, or loop-exit assertions. Those belong to the Verify stage.
