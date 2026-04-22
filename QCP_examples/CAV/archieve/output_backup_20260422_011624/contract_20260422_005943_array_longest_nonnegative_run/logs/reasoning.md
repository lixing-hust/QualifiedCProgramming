# Contract reasoning: array_longest_nonnegative_run

## Source semantics

The raw task defines `array_longest_nonnegative_run(int n, int *a)` over an integer
array segment of length `n`. The function returns the maximum length of any
contiguous segment whose elements are all nonnegative (`a[i] >= 0`). If no such
element exists, or if the array is empty, the result is `0`.

The supplied implementation is a single left-to-right scan:

- `current` is the length of the current suffix run of nonnegative values
- `best` is the maximum run length observed so far
- each negative element resets `current` to `0`

The original interface is already verification-friendly: it has no I/O, no
allocation, and only reads the caller-provided array.

## Boundary and memory conditions

The natural input domain is `n >= 0` with `a` owning at least `n` integer cells.
The contract uses `IntArray::full(a, n, l)` to bind the input contents as a Coq
list `l` and to preserve the array segment in the postcondition.

The implementation increments `i` and `current` only up to `n`, so the contract
includes `n <= INT_MAX` as an explicit integer-safety bound. No data-value
overflow precondition is needed because array values are only compared with `0`;
they are never added, subtracted, or written.

For `n = 0`, the loop is skipped and the result is `0`, which is exactly the
empty-list specification.

## Postcondition choice

The postcondition states the semantic result through a task-local Coq function:

`__return == array_longest_nonnegative_run_spec(l)`

The array is read-only at the C level, so the postcondition also restores the
same `IntArray::full(a, n, l)` predicate. The contract does not include loop
invariants, assertions, processed-prefix facts, or loop-exit facts; those belong
to the Verify stage.

## Coq dependency decision

The repository does not provide a shared mathematical definition for the longest
contiguous nonnegative run of a `list Z`. A small task-specific `.v` file is
therefore needed. It defines an accumulator-style function matching the C scan:

- on a nonnegative element, increment the current run and update the best run
- on a negative element, reset the current run to `0`
- the final best value is the specification result

No additional pre/spec wrapper is needed beyond this direct list function.
