# Contract Reasoning: array_all_zero

## Source Semantics

The raw problem defines a function:

```c
int array_all_zero(int n, int *a)
```

It scans the first `n` elements of integer array `a`.

- `n >= 0`
- the logical array length is exactly `n`
- the function does not modify the array
- it returns `1` iff every element is `0`
- it returns `0` if there exists at least one nonzero element

The original implementation uses a forward scan and returns early on the first nonzero element. If the loop finishes, every checked element was zero and the function returns `1`.

## Interface Decision

The original interface is verification-friendly:

- the array is passed by pointer
- the length is explicit
- there is no I/O, global state, allocation, or hidden side effect
- the function returns a scalar boolean-like result

No interface rewrite is needed.

## Memory Contract

Use `IntArray::full(a, n, l)` to describe the input array contents.

The precondition binds logical list `l` with:

- `0 <= n`
- `Zlength(l) == n`
- `IntArray::full(a, n, l)`

The function is read-only, so the postcondition restores:

- `IntArray::full(a, n, l)`

## Result Contract

The result can be expressed directly in the C contract with quantifiers:

- return `1` means every index in range contains `0`
- return `0` means there exists an index in range whose value is not `0`

This mirrors the early-return implementation and avoids introducing a separate Coq helper.

## Coq Dependency Decision

No `input/array_all_zero.v` is needed.

Reason: the full semantic property is simple enough to state directly using first-order quantifiers over the logical array list. There is no recursive numeric function, reusable list computation, or problem-specific semantic bridge required.
