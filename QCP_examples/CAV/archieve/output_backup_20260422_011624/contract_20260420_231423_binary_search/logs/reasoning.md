# Contract reasoning: binary_search

## Source semantics

- Target function: `binary_search`
- Inputs:
  - `n`: logical length of the array, with `n >= 0`.
  - `a`: integer array of exactly length `n`.
  - `target`: searched integer value.
- Array precondition: `a` is nondecreasing, expressed pointwise as:
  - for every `i`, if `0 <= i` and `i + 1 < n`, then `l[i] <= l[i + 1]`.
- The function does not write to `a`.

## Result semantics

The source problem allows returning any index whose value equals `target`.

The postcondition therefore has two cases:

- Success: return value is a valid index in `[0, n)` and `l[__return] == target`.
- Failure: return value is `-1` and no valid index contains `target`.

The contract intentionally does not require the first or last matching index, because the original problem says any matching index is acceptable.

## Boundary cases

- `n == 0`: `right` becomes `-1`, the loop is skipped, and the function returns `-1`. The universal failure condition is vacuous.
- `n == 1`: `mid == 0`; the function either returns `0` or `-1`.
- Duplicate target values: any matching position satisfies the success postcondition.

## Memory

- The only memory resource is `IntArray::full(a, n, l)`.
- The function only reads `a[mid]`, so the same full array predicate is restored in every postcondition branch.
- `Zlength(l) == n` records that the logical list matches the declared array length.

## Arithmetic and overflow

- `0 <= n` is required before computing `n - 1`.
- During the algorithm, `left` and `right` are intended to stay within the search interval bounds used by binary search.
- The midpoint expression uses `left + (right - left) / 2`, avoiding the direct `left + right` overflow pattern.
- Since `n` is an `int` parameter and all index values are derived from `0`, `n - 1`, `mid - 1`, and `mid + 1`, no extra result arithmetic specification is needed in the contract.

## Coq dependency decision

No `input/binary_search.v` is needed. The required semantics are expressible directly with first-order quantifiers over the list model:

- sortedness of the input list,
- valid success index,
- absence of the target on failure.

There is no reusable mathematical function or task-specific bridge predicate needed at the Contract stage.
