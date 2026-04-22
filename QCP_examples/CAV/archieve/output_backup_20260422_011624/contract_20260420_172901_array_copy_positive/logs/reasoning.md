# Contract reasoning: array_copy_positive

## Source semantics

The target function receives an integer length `n`, an input integer array `a`, and an output integer array `out`.

For each index `i` with `0 <= i < n`:

- if `a[i] > 0`, the function writes `out[i] = a[i]`;
- otherwise, the function writes `out[i] = 0`.

The function does not modify `a`.

## Boundary conditions

- The problem states `n >= 0`.
- Both arrays have exactly length `n`.
- If `n == 0`, the loop body does not execute and both array predicates are still consumed and restored with length zero.

## Memory model

The contract uses `IntArray::full(a, n, la)` for the input array and `IntArray::full(out, n, lo)` for the caller-provided output buffer.

The separating conjunction requires the input and output array regions to be disjoint. This matches the intended "input array plus output array" interface and keeps the postcondition simple: `a` is restored with the original list `la`, while `out` is restored with a result list `lr`.

## Result specification

The postcondition introduces `lr`, the final contents of `out`.

It requires:

- `Zlength(lr) == n`;
- for every valid index `i`, if `la[i] > 0` then `lr[i] == la[i]`;
- for every valid index `i`, if `la[i] <= 0` then `lr[i] == 0`;
- `a` remains `la`;
- `out` becomes `lr`.

No arithmetic overflow precondition is needed: the implementation only copies existing `int` values or writes the constant `0`.

## Coq dependency judgment

No task-specific Coq definitions are needed. The desired semantics can be expressed directly with list length, indexed access, quantification, and integer comparisons in the C contract.
