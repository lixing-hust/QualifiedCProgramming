# Annotation Reasoning

## Round 1

- Program point: the `for (i = 0; i < n; ++i)` loop in `annotated/verify_20260420_115922_array_first_negative.c` currently has no invariant, so symbolic execution will not have a preserved fact describing why any returned index is the first negative element or why the final `-1` path means every element is nonnegative.
- Loop meaning: `i` is the next unread array index; the processed prefix is exactly indices `0 <= j < i`.
- Required semantic fact: before each iteration, every processed element is nonnegative, expressed as `(forall (j: Z), (0 <= j && j < i) => l[j] >= 0)`.
- Stable facts to preserve: `0 <= i && i <= n`, `a == a@pre`, `n == n@pre`, and `IntArray::full(a, n, l)` because the function only reads the array.
- Initialization: when the first loop test is reached, `i == 0`, so the quantified prefix fact is vacuous.
- Preservation: if `a[i] < 0`, the function returns immediately with current `i`, and the invariant supplies nonnegativity of all earlier indices. If the branch is not taken, then `a[i] >= 0`, so the processed-prefix fact extends to the next loop head after `++i`.
- Exit: when the loop exits, `i == n`; restating the invariant with `i == n` gives the final return path condition that every index in `[0, n)` is nonnegative.

## Planned edit

- Add a loop invariant before the `for` statement carrying bounds, unchanged-parameter facts, the prefix nonnegativity property, and `IntArray::full(a, n, l)`.
- Add a minimal loop-exit `Assert` immediately after the loop fixing `i == n` and restating the full-range nonnegativity property before `return -1`.
