# Contract Reasoning: array_has_adjacent_equal

## Source Semantics

The target function scans an integer array `a` of length `n` from left to right, starting at index `1`. At each index `i`, it compares `a[i]` with `a[i - 1]`.

- If any adjacent pair is equal, the function returns `1` immediately.
- If the scan finishes without finding such a pair, the function returns `0`.
- The input array is read-only and must be preserved by the postcondition.
- When `n` is `0` or `1`, there is no adjacent pair, so the loop does not find a match and the function returns `0`.

## Boundary Conditions

- Require `0 <= n`.
- Bind the logical contents of the array as `l`.
- Require `Zlength(l) == n`.
- Require `IntArray::full(a, n, l)` for memory safety and value semantics.
- The loop starts at `i = 1`, so all reads `a[i]` and `a[i - 1]` are within bounds whenever `i < n`.
- No write occurs, so the same `IntArray::full(a, n, l)` resource is restored in the postcondition.

## Postcondition Shape

The return value is specified by cases:

- `__return == 1` iff there exists an index `i` with `1 <= i < n` and `l[i] == l[i - 1]`.
- `__return == 0` iff every index `i` with `1 <= i < n` satisfies `l[i] != l[i - 1]`.

This directly captures the natural-language behavior and also enforces the promised boolean return range because only `0` and `1` are admitted by the two disjuncts.

## Coq Dependency Decision

No `input/array_has_adjacent_equal.v` file is needed. The specification only uses standard integer comparisons, quantifiers, logical connectives, list length, list indexing, and `IntArray::full`; these are already available through the standard headers and array definitions used by existing CAV array contracts.

## Phase Boundary

The contract output contains only the target function, its precondition, its postcondition, and the required memory resource. Intermediate proof annotations are intentionally left for the later verification phase.
