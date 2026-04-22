# Contract reasoning: array_all_less_than_k

## Source semantics

The raw task defines `array_all_less_than_k(int n, int *a, int k)`.

- `n >= 0`.
- `a` has exactly `n` integer elements.
- The empty array satisfies the predicate.
- The function does not modify `a`.
- The result is `1` iff every element of `a[0..n-1]` is strictly less than `k`; otherwise the result is `0`.

The implementation scans from left to right and returns `0` as soon as it finds an element `a[i] >= k`. If the loop finishes, every scanned element is `< k`, so it returns `1`.

## Interface decision

The original interface is verification-friendly:

- no I/O,
- no allocation,
- no global state,
- single target function,
- input array is represented directly by an `IntArray::full` predicate.

No interface rewrite is needed.

## Contract shape

Use `With l` to bind the logical list backing the input array.

Precondition:

- `0 <= n`;
- `Zlength(l) == n`;
- `IntArray::full(a, n, l)`.

Postcondition:

- if `__return == 1`, all indices in `[0, n)` satisfy `l[i] < k`;
- if `__return == 0`, there exists an index in `[0, n)` with `l[i] >= k`;
- `IntArray::full(a, n, l)` is restored unchanged, expressing that the function does not modify the array.

The empty-array case is covered by the universal quantifier over an empty range, so return `1` is allowed and no special case is needed.

## Memory and integer safety

The loop variable starts at `0` and only ranges while `i < n`. The precondition `0 <= n` and `IntArray::full(a, n, l)` provide the array bounds needed for reads `a[i]`.

The function performs no arithmetic on array values and does not write memory. The only integer increment is `++i`; no extra value-bound precondition is introduced at Contract stage because existing CAV array scan contracts use the same loop/index shape with `0 <= n` and list length equality.

## Coq dependency decision

No `input/array_all_less_than_k.v` is needed. The specification can be expressed directly in the C contract using first-order quantifiers over `l`; there is no recursive count, transformed list, or problem-specific helper relation to bridge.
