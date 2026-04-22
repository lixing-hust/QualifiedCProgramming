## Function semantics

Target function: `array_max(int n, int *a)`.

The function scans a length-`n` integer array and returns the maximum element. It reads the array only and preserves the full array ownership/content relation.

## Boundary conditions

- The problem statement requires `n >= 1`.
- The implementation reads `a[0]` before entering the loop, so `n == 0` must be excluded in the precondition.
- No arithmetic beyond assignment/comparison is performed on array elements, so there is no additional overflow-side condition like the one needed for `array_sum`.

## Memory model

- Use `With l` plus `IntArray::full(a, n, l)` to describe readable ownership of the entire array.
- Use `Zlength(l) == n` to connect the logical list length with the concrete array length.
- Because the function does not modify `a`, the postcondition preserves `IntArray::full(a, n, l)`.

## Coq dependency judgment

The repository already exposes list length and array predicates, but it does not provide a reusable list maximum function. This task therefore needs a small dedicated `input/array_max.v` file.

The C contract will import a Coq function:

- `max_list_nonempty : list Z -> Z`

and use it directly in the postcondition:

- `__return == max_list_nonempty(l)`

This stays within contract scope: it captures only final functional semantics and does not introduce verify-stage assertions or invariants.
