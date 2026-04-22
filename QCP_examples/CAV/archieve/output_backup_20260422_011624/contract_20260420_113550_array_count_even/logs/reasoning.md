# Contract reasoning: array_count_even

## Source semantics

- The raw program scans indices `0` through `n - 1` of an integer array `a`.
- It initializes `cnt` to `0`.
- For each element, it checks `a[i] % 2 == 0`.
- It increments `cnt` exactly for elements satisfying that predicate.
- It returns `cnt`.

## Input domain and memory

- The problem states `n >= 0`.
- The array length is exactly `n`.
- The function only reads `a`; it does not modify array contents.
- The contract represents the input array as a logical list `l` with `Zlength(l) == n`.
- The memory predicate is `IntArray::full(a, n, l)` in both precondition and postcondition, preserving the input array unchanged.

## Result semantics

- The result is the number of elements of `l` whose C remainder by `2` is `0`.
- This is expressed by a task-specific Coq function `array_count_even_spec : list Z -> Z`.
- The Coq definition uses `Z.rem x 2 = 0`, matching the source-level `% 2 == 0` test.

## Boundary cases

- If `n == 0`, then `l` is empty, the loop is skipped, and the result is `0`.
- Negative array elements are allowed. The evenness check is based on remainder equality to zero, so negative even values are counted.
- The counter is bounded by the array length. Since `n` is a C `int` parameter and the counter increases at most once per iteration, the implementation does not require an extra semantic bound beyond the array length/domain constraints used by the existing array-count contracts.

## Coq dependency decision

- The repository has close examples for array counting predicates (`array_count_zero`, `count_positive`) that use a small task-specific `.v` file.
- There is no existing public Coq function in the input contract language that directly names this parity-count result.
- Therefore `input/array_count_even.v` is needed, and it should contain only the recursive list specification.

## Contract shape

- `With l` binds the logical array contents needed by the postcondition.
- `Require` states nonnegative length, list length agreement, and full ownership of the input array.
- `Ensure` states that the return value equals `array_count_even_spec(l)` and restores the same `IntArray::full(a, n, l)`.
- No verification-phase loop annotations are included in the contract input.
