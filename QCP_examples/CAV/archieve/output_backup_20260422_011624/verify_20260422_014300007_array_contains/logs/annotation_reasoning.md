# Annotation Reasoning

## Round 1

- Loop shape: `i` is the next unread index, so at the loop head the processed region is the prefix `sublist(0, i, l)`.
- Required postcondition: on either return path we need `__return == array_contains_spec(l, k)` while preserving `IntArray::full(a, n, l)`.
- The loop returns immediately on the first hit, so the loop invariant should not try to summarize a mutable accumulator. The stable semantic fact before each iteration is instead:
  - every processed element is different from `k`
- Stable facts that should stay in the invariant:
  - bounds `0 <= i && i <= n`
  - unchanged parameters `a == a@pre`, `n == n@pre`, and `k == k@pre`
  - memory ownership `IntArray::full(a, n, l)`
  - prefix non-membership `(forall (j: Z), (0 <= j && j < i) => l[j] != k)`
- Initialization check: before the first loop test, `i == 0`, so the quantified prefix fact is vacuous.
- Preservation expectation:
  - in the `a[i] == k` branch, the function returns immediately, so the invariant does not need to describe the next loop head
  - in the fallthrough branch, we have just established `l[i] != k`, so the prefix non-membership fact should extend from `< i` to `< i + 1`
- Exit usefulness: when the loop exits with `i == n`, the quantified fact becomes “all indices in the full list differ from `k`”, which is the exact semantic shape needed for the final `return 0`.

## Planned edit

- Add one loop invariant carrying the unchanged-parameter facts plus the prefix non-membership property.
- Add one loop-exit `Assert` fixing `i == n` and restating the full-list non-membership fact before `return 0`.
