# Annotation Reasoning

## Round 1

- Program point: the `for (i = 0; i < n; ++i)` loop in `array_any_equal_sum`.
- Current issue before annotation: the loop has no invariant, but the final `return 0` must prove the universal postcondition `(forall (i: Z), (0 <= i && i < n) => l[i] != x + y)`. That fact is accumulated by scanning the array and is not available unless the loop invariant records the processed prefix.
- Loop meaning: at the loop head, `i` is the next unread index and the processed region is the prefix `0 <= j < i`.
- Required semantic fact: before each iteration, every processed element differs from `target`; if a current element equals `target`, the function returns `1` immediately and the existential postcondition is witnessed by the current index.
- Stable facts to preserve in the invariant: `0 <= i && i <= n`, unchanged parameters `a == a@pre`, `n == n@pre`, `x == x@pre`, `y == y@pre`, stable local `target == x + y`, integer range for `target`, and `IntArray::full(a, n, l)`.
- Initialization: when the loop starts with `i == 0`, the quantified prefix fact over `0 <= j < 0` is vacuous.
- Preservation: on the non-return path from `if (a[i] == target)`, the branch condition gives `l[i] != target`, extending the prefix fact from `< i` to `< i + 1`.
- Exit usefulness: after loop exit, `i == n` plus the prefix fact gives the exact universal condition needed by the `return 0` postcondition.

## Planned edit

- Add a loop invariant before the `for` loop containing bounds, unchanged parameters, target equality, target integer range, prefix non-membership, and `IntArray::full(a, n, l)`.
- Add one loop-exit `Assert` immediately after the loop to fix `i == n` and restate the universal fact over the full range before `return 0`.
