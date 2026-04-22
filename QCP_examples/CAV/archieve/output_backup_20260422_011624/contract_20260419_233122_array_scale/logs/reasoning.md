# Contract Reasoning: array_scale

## Source

- Raw markdown: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/raw/array_scale.md`
- Target function: `array_scale`
- Output C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/array_scale.c`

## Semantics

`array_scale` receives:

- `n`: array length, with `n >= 0`
- `a`: input integer array of length `n`
- `k`: scalar multiplier
- `out`: output integer array of length `n`

The function writes `a[i] * k` into `out[i]` for every index `i` satisfying `0 <= i < n`. The function returns no value.

The input array `a` is read-only from the function's semantic perspective and must be preserved by the postcondition. The output array `out` is fully overwritten with the scaled values.

## Boundary Conditions

- If `n == 0`, the loop body is not executed. Both arrays have logical length zero, and the postcondition is satisfied by an output list of length zero.
- For `n > 0`, every valid index is processed exactly once by the loop.
- The prompt states both arrays have length exactly `n`; this is represented with `Zlength(la) == n`, `Zlength(lo) == n`, and corresponding `IntArray::full` predicates.

## Memory Model

The contract binds:

- `la` for the initial contents of `a`
- `lo` for the initial contents of `out`

The precondition owns both arrays:

- `IntArray::full(a, n, la)`
- `IntArray::full(out, n, lo)`

The separating conjunction requires the arrays to be represented by disjoint owned memory regions in the standard project style. The postcondition restores `a` with `la` and describes `out` with a result list `lr`.

## Integer Safety

Because the implementation computes `a[i] * k` using C `int` arithmetic, the contract includes a per-element overflow precondition:

```c
(forall (i: Z),
  (0 <= i && i < n) =>
  (-2147483648 <= la[i] * k && la[i] * k <= 2147483647))
```

This preserves the original program semantics while making C signed multiplication defined for every loop iteration.

## Coq Dependency Judgment

No task-specific Coq definitions are required. The postcondition can express the result directly using `Zlength`, indexed list access, quantification, and integer multiplication:

```c
exists lr,
  Zlength(lr) == n &&
  (forall (i: Z), (0 <= i && i < n) => lr[i] == la[i] * k) &&
  ...
```

Therefore `input/array_scale.v` is not created.
