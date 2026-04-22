# Contract reasoning: array_move_zeroes_to_end

## Source semantics

The raw implementation performs an in-place stable compaction of nonzero
elements:

1. Scan the original array from left to right.
2. Copy every nonzero value to the next write position.
3. Fill the remaining suffix with zeroes.

The relative order of all nonzero elements is preserved. The final array is
the list of original nonzero values followed by enough zeroes to restore the
original length.

## Interface decision

The original interface is already verification-friendly:

```c
void array_move_zeroes_to_end(int n, int *a)
```

No I/O, allocation, global state, or test scaffold is present. The function
mutates only the caller-provided integer array. The interface is therefore
kept unchanged.

## Preconditions

The contract requires:

- `0 <= n`, because the loops interpret `n` as an array length.
- `n <= INT_MAX`, to make the integer loop bounds explicit.
- `Zlength(l) == n`, connecting the logical input list to the C length.
- `IntArray::full(a, n, l)`, giving ownership of a writable integer array of
  length `n` with initial contents `l`.

No stronger value bounds are added beyond the array predicate. The algorithm
only copies existing integer values and writes the literal `0`.

## Postcondition

The postcondition gives back the same array ownership with contents
`move_zeroes_to_end_spec(l)`.

The logical result is defined as:

- all elements `x` of `l` with `x != 0`, in their original order;
- followed by one `0` for each original zero element.

This directly captures both required user-visible properties:

- stable preservation of nonzero elements;
- zero-filled suffix with unchanged total length.

## Coq dependency decision

The desired postcondition is a list transformation, not a pointwise
replacement. It is clearer and more reusable to define this transformation in
`input/array_move_zeroes_to_end.v` and import it from the C contract.

No additional verification-stage assertions, invariants, bridge assertions, or
loop-exit assertions are included in the contract input.
