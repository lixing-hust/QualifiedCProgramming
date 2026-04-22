# Contract Reasoning: array_any_equal_sum

## Source semantics

The raw task defines `array_any_equal_sum(int n, int *a, int x, int y)`.
It computes `target = x + y`, scans the `n` elements of `a`, returns `1` if any element equals `target`, and returns `0` otherwise.

The array is read-only and the return value is boolean-like: only `0` or `1`.

## Interface decision

The original interface is verification-friendly:

- `n` gives the array length.
- `a` is caller-provided memory.
- `x` and `y` are scalar inputs.
- The function has no I/O, allocation, global state, or hidden side effects.

No interface rewrite is needed.

## Preconditions

The contract uses a logical list `l` for the contents of `a`.

Required facts:

- `0 <= n`
- `Zlength(l) == n`
- `IntArray::full(a, n, l)`
- `INT_MIN <= x + y && x + y <= INT_MAX`

The overflow bound is needed because the implementation computes `int target = x + y`.

## Postconditions

The postcondition preserves the input array shape and contents:

- `IntArray::full(a, n, l)`

The return semantics are expressed directly:

- return `1` iff there exists `i` with `0 <= i < n` and `l[i] == x + y`
- return `0` iff every valid element differs from `x + y`

No verification-stage annotations are included in the contract input.

## Coq dependency decision

No task-specific `.v` file is needed. The property is simple enough to express directly in the C contract using quantifiers over the list contents.
