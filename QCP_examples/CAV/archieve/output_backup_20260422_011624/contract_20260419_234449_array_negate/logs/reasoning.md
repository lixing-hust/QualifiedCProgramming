# Contract Reasoning: array_negate

## Source Semantics

The raw task defines:

- `n >= 0`.
- `a` is an input integer array of length `n`.
- `out` is an output integer array of length `n`.
- The function returns no value.
- For every index `i` with `0 <= i < n`, after execution `out[i] == -a[i]`.

The provided implementation is a single forward loop:

```c
for (i = 0; i < n; ++i) {
    out[i] = -a[i];
}
```

This is already a verification-friendly interface because all memory is supplied by the caller and the function has no I/O, allocation, global state, or helper calls.

## Memory Model

Use `IntArray::full(a, n, la)` for the input array and `IntArray::full(out, n, lo)` for the output array. The separating conjunction between them requires distinct owned regions, matching the statement's two-array input/output shape.

The precondition binds:

- `la`: the original contents of `a`.
- `lo`: the original contents of `out`, needed only to own the writable output buffer before the loop.

The postcondition preserves `a` unchanged and replaces the output ownership with a result list `lr`.

## Bounds and Overflow

The loop indexes `0 <= i < n`, so `n >= 0` plus full array ownership is enough for memory safety.

C unary negation over `int` is undefined for `INT_MIN`. The contract therefore requires each mathematical result `-la[i]` to fit in signed 32-bit integer range:

```c
-2147483648 <= -la[i] && -la[i] <= 2147483647
```

This excludes exactly the problematic `INT_MIN` case while allowing all other input values.

## Postcondition Shape

The output list `lr` has length `n`, and each element satisfies:

```c
lr[i] == -la[i]
```

No loop invariants, assertions, bridge assertions, or verify-stage comments are added in the contract file.

## Coq Dependency Decision

No task-specific Coq definition is needed. The elementwise relationship is expressible directly with `Zlength`, quantified indexing, and `IntArray::full`, following the existing `array_scale` / `array_add` contract style. Therefore `input/array_negate.v` is not created.
