## Semantics

Target function: `array_first`.

Raw intent is direct: given an integer array `a` of length `n`, return its first element and do not modify the array. The implementation is `return a[0];`, so the contract only needs to guarantee that index `0` is valid and that read-only ownership of the array is available.

## Boundary Conditions

- `n >= 1` is required so `a[0]` is in bounds.
- The logical list representing the array must satisfy `Zlength(l) == n`.
- No extra numeric overflow precondition is needed because the function only reads and returns one `int` already stored in the array.

## Memory Shape

Use `IntArray::full(a, n, l)` to express ownership of the whole input array and its logical contents `l`. Since the function does not write through `a`, the same predicate is preserved in the postcondition.

## Postcondition Choice

The result is the first logical element of the array, expressed as `l[0]`. This keeps the spec simple and avoids introducing an extra Coq helper for a nonempty-head operation.

## Coq Dependency Decision

No dedicated `input/array_first.v` file is needed.

Reason:

- the semantics can be expressed directly in the C contract,
- no problem-specific logical wrapper or helper relation is required,
- existing list notation is sufficient for the first-element property.
