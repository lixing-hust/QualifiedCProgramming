# Contract Reasoning: array_is_strictly_increasing

## Source Semantics

The target function scans an integer array `a` of length `n` from left to right, starting at index `1`. At each index `i`, it compares the adjacent pair `a[i - 1]` and `a[i]`.

- If any adjacent pair satisfies `a[i - 1] >= a[i]`, the function returns `0` immediately.
- If the scan finishes without finding such a pair, the function returns `1`.
- The input array is read-only and must be preserved by the postcondition.
- Empty arrays and single-element arrays are strictly increasing because there is no adjacent pair that can violate the condition.

## Boundary Conditions

- Require `0 <= n`.
- Bind the logical contents of the array as `l`.
- Require `Zlength(l) == n`.
- Require `IntArray::full(a, n, l)` for memory safety and value semantics.
- The loop starts at `i = 1`, so all reads `a[i - 1]` and `a[i]` are within bounds whenever `i < n`.
- No write occurs, so the same `IntArray::full(a, n, l)` resource is restored in the postcondition.

## Postcondition Shape

The return value is specified by cases:

- `__return == 1` iff every index `i` with `1 <= i < n` satisfies `l[i - 1] < l[i]`.
- `__return == 0` iff there exists an index `i` with `1 <= i < n` and `l[i - 1] >= l[i]`.

This directly captures the natural-language behavior and also enforces the boolean return range because only `0` and `1` are admitted by the two disjuncts.

## Coq Dependency Decision

No `input/array_is_strictly_increasing.v` file is needed. The specification only uses standard integer comparisons, quantifiers, logical connectives, list length, list indexing, and `IntArray::full`; these are already available through the standard headers and array definitions used by existing CAV array contracts.

## Phase Boundary

The contract output contains only the target function, its precondition, its postcondition, and the required memory resource. Intermediate proof annotations are intentionally left for the later verification phase.
