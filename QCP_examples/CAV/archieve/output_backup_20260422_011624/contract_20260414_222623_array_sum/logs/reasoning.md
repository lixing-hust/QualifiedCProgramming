# reasoning

## task
- target function: `array_sum`
- raw input: `raw/array_sum.md`
- required output: `input/array_sum.c`
- optional output: `input/array_sum.v`

## semantic understanding
- Function returns the sum of first `n` elements of array `a`.
- It only reads `a[0..n-1]` and does not modify array contents.
- Boundary allows `n = 0`, so empty prefix sum should be `0`.

## contract design
- Use `With l` and `IntArray::full(a, n, l)` to model readable contiguous array memory.
- Use `sum(l)` as post-state mathematical result, because `int_array_def.h` already exposes `sum`.
- Keep ownership/shape unchanged in postcondition since function is read-only.
- Add domain constraints from statement:
  - `0 <= n <= 10000`
  - per-element range: `-10000 <= l[i] <= 10000`
  - overall sum in 32-bit int range
- Add `Zlength(l) == n` explicitly to align list length with loop bound.

## c/v split decision
- No extra Coq bridge is required:
  - `sum`, `sublist`, `IntArray::full` already exist in shared defs.
  - Contract is directly expressible in C annotation.
- Therefore do **not** create `input/array_sum.v`.
