## Function

`array_last(int n, int *a)` is a read-only array function that returns the last element of the input array.

## Semantics

- Original semantics: `return a[n - 1];`
- No interface rewrite is needed.
- The function does not modify the array.

## Boundary Analysis

- The raw statement guarantees `n >= 1`.
- To read `a[n - 1]` safely, the contract must guarantee that the logical array length is exactly `n`.
- With `1 <= n` and `Zlength(l) == n`, the index `n - 1` is within bounds of `l`.
- No arithmetic overflow precondition is needed beyond the nonempty-array condition because the function only performs the index computation `n - 1` and an array read.

## Memory Analysis

- The function reads from caller-provided array memory.
- `IntArray::full(a, n, l)` is the appropriate ownership and value predicate.
- Because the function is read-only, the same `IntArray::full(a, n, l)` resource should be preserved in the postcondition.

## Coq Dependency Decision

- No extra mathematical abstraction is needed.
- The result can be expressed directly as the last logical element: `__return == l[n - 1]`.
- Therefore `input/array_last.v` is unnecessary.

## Contract Shape

- `With`: logical list `l`
- `Require`: nonempty length, exact logical length, and full array ownership
- `Ensure`: returned value is the last element of `l`, and the array ownership is preserved

## Verify-Phase Exclusions

- No loop invariants are needed because there is no loop.
- No assertions, bridge assertions, `which implies`, or loop-exit annotations should appear in the contract file.
