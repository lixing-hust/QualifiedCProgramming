## Function semantics

Target function: `array_min(int n, int *a)`.

The function scans a length-`n` integer array and returns the minimum element. It only reads the array and preserves the full array ownership/content relation.

## Boundary conditions

- The problem statement requires `n >= 1`.
- The implementation reads `a[0]` before the loop, so `n == 0` must be excluded in the precondition.
- The loop only performs comparisons and assignments on existing `int` values, so there is no arithmetic-overflow side condition to add.

## Memory model

- Use `With l` together with `IntArray::full(a, n, l)` to describe ownership and contents of the readable array.
- Use `Zlength(l) == n` to connect the logical list length to the concrete array length.
- Because the function does not modify `a`, the postcondition preserves `IntArray::full(a, n, l)`.

## Coq dependency judgment

The repository already provides list length and integer-array predicates, but no reusable nonempty-list minimum function was found in the current inputs. Following the existing `array_max` pattern, this task should use a small task-local Coq definition in `input/array_min.v`.

The C contract will import:

- `min_list_nonempty : list Z -> Z`

and use it directly in the postcondition:

- `__return == min_list_nonempty(l)`

This keeps the contract focused on final functional semantics only and avoids adding verify-stage assertions or invariants.
