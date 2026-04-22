# Contract Reasoning: array_first_negative

## Source Semantics

The function scans the integer array `a` from index `0` to `n - 1`.
It returns immediately when it finds the first element whose value is negative.
If no negative element is present in the whole array, it returns `-1`.

The implementation does not write to `a`.

## Interface

The original interface is verification-friendly:

```c
int array_first_negative(int n, int *a)
```

No interface rewrite is needed.

## Preconditions

The problem states `n >= 0` and that `a` has exactly length `n`.
The contract represents the array contents with a logical list `l`.

Required assumptions:

- `0 <= n`
- `Zlength(l) == n`
- `IntArray::full(a, n, l)`

No additional arithmetic overflow bound is needed beyond memory safety, because the loop index ranges from `0` to `n` and the return value is either an in-range index or `-1`.

## Postconditions

The result has two cases:

1. `__return == -1`: every element in the array is nonnegative.
2. `0 <= __return < n`: the returned element is negative, and every earlier element is nonnegative.

The array is read-only, so the postcondition restores `IntArray::full(a, n, l)`.

## Coq Dependency Decision

No task-specific Coq definition is needed.
The first-negative semantics can be stated directly with quantifiers in the C contract, following the existing direct-spec style used by array search contracts.
