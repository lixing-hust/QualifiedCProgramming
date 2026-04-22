# Contract Reasoning: array_count_transitions

## Source semantics

The raw task defines `array_count_transitions(int n, int *a)` for an integer array of length `n`. The function scans adjacent pairs and increments the result once for every index `i` with `1 <= i < n` and `a[i] != a[i - 1]`. It does not modify the array.

For `n == 0` and `n == 1`, there are no adjacent pairs, so the result is `0`.

## Interface decision

The original interface is already verification friendly:

- `n` is an integer length parameter.
- `a` is a caller-provided input array.
- the function returns the computed count.
- no I/O, allocation, globals, or platform behavior are involved.

No interface rewrite is needed.

## Memory contract

The contract uses `IntArray::full(a, n, l)` and `Zlength(l) == n` to connect the C array to its logical list contents. Because the implementation only reads from `a`, the postcondition preserves the same `IntArray::full(a, n, l)` resource.

The task states `n >= 0`, so the precondition includes `0 <= n`. The loop reads `a[i]` and `a[i - 1]` only when `1 <= i < n`, which is covered by the full-array predicate and the length equality.

## Mathematical specification

There is no existing public Coq function for counting adjacent transitions. A task-local Coq definition is therefore needed:

`array_count_transitions_spec : list Z -> Z`

The Coq file defines a structurally recursive helper `array_count_transitions_from prev rest`, then exposes `array_count_transitions_spec l`. The public spec returns `0` for an empty list and otherwise counts differences between the head and the remaining suffix.

## Contract shape

The C contract imports the task-local Coq file and states:

- precondition: `0 <= n`, `Zlength(l) == n`, and ownership of the full array.
- postcondition: `__return == array_count_transitions_spec(l)` and the array resource is preserved.

No verification-stage annotation is included in the contract output.
