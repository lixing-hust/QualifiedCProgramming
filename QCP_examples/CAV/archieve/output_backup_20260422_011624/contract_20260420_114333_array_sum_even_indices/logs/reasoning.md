# Contract reasoning: array_sum_even_indices

## Source summary

- Raw task: given an integer array `a` of length `n`, return the sum of elements at even indices `0, 2, 4, ...`.
- Input domain: `n >= 0`; `a` has exactly `n` elements.
- Side effects: the function only reads `a`; it does not modify the array.
- Original implementation: scans `i` from `0` to `n - 1`, adds `a[i]` exactly when `i % 2 == 0`, and returns the accumulator.

## Mathematical semantics

The natural result is the sum of list elements whose zero-based index is even. This is not the existing plain `sum(l)` over all elements, so the contract uses a task-specific Coq function:

- `array_sum_even_indices_spec : list Z -> Z`

The function can be defined structurally over the list by taking the head, skipping the next element, and recursing on the remaining tail. This matches even positions in the original list.

## Preconditions

The contract binds the input array contents as logical list `l`.

Required facts:

- `0 <= n`, matching the problem statement.
- `n <= INT_MAX`, so loop comparisons and increments remain in signed-int range.
- `Zlength(l) == n`, matching the exact array length.
- Every element of `l` is in signed-int range. This is the value domain represented by `IntArray::full` and supports safe arithmetic operands.
- Every prefix even-index sum is in signed-int range:
  `forall k, 0 <= k <= n => INT_MIN <= array_sum_even_indices_spec(sublist(0, k, l)) <= INT_MAX`.

The prefix-sum bound is needed because the accumulator is updated during the loop. A bound only on the final sum would be too weak when array values can be negative and positive, since an intermediate partial sum might overflow even if the final result is in range.

## Postcondition

The postcondition states:

- `__return == array_sum_even_indices_spec(l)`.
- `IntArray::full(a, n, l)` is preserved, since the function does not write to `a`.

No Verify-stage proof annotations or intermediate proof facts are included.

## Coq dependency decision

An `input/array_sum_even_indices.v` file is needed. The existing public `sum(l)` function cannot express the even-index filter directly without an additional task-specific definition. The `.v` file contains only this small semantic helper.
