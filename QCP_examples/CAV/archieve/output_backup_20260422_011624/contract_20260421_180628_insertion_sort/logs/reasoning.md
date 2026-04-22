# Contract reasoning: insertion_sort

## Source semantics

The raw task defines:

- Target function: `void insertion_sort(int n, int *a)`
- Input domain: `n >= 0`
- Memory: `a` points to exactly `n` integer elements
- Effect: sort `a` in place into nondecreasing order
- Algorithm: standard insertion sort; for each `i` from `1` to `n - 1`, save `a[i]` as `key`, shift larger preceding elements one cell to the right, and write `key` at the insertion position.

The C implementation can be kept with the same interface and control flow. No I/O, allocation, globals, or test harness need to be removed.

## Boundary and safety choices

- Keep `n >= 0`.
- Add `n <= 2000`, matching existing local sort contracts, to keep arithmetic and list reasoning within the toolchain's usual bounded array shape.
- Require `IntArray::full(a, n, l)` so the whole array is readable and writable.
- The loop index arithmetic uses `i`, `j`, `j + 1`, and `i - 1`; under `0 <= n <= 2000` all values stay within C `int` range.
- For `n = 0` or `n = 1`, the outer loop does not execute and the postcondition is satisfied by the unchanged array.

## Mathematical postcondition

The observable result is a final list `l0` stored in the same array such that:

- `sorted_z(l0)` holds, meaning `l0` is nondecreasing.
- `Permutation(l, l0)` holds, so the output contains exactly the original elements with multiplicities preserved.
- `IntArray::full(a, n, l0)` describes the final in-place array contents.

This matches the existing `selection_sort` and `bubble_sort` contract shape.

## Coq dependency decision

`Permutation` is provided by Coq's standard sorting library and is imported through the task-local `.v` file. The repository does not expose a shared public `sorted_z` definition for these contracts, and existing sort inputs define it in their own `<name>.v`.

Therefore `input/insertion_sort.v` is needed, but only for the task-local `sorted_z` predicate and standard imports. No algorithm-specific helper lemmas belong in Contract output.

## Verify-stage boundary

No proof-stage annotations or intermediate proof hints are added here. Those belong to the Verify stage.
