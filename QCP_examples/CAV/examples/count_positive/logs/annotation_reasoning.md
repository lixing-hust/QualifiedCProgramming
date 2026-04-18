# Annotation Reasoning

## Round 1

- Loop shape: `i` is the next unread index, so the loop head naturally summarizes the processed prefix `sublist(0, i, l)`.
- Required postcondition: on exit we need `cnt == count_positive_spec(l)` while preserving `IntArray::full(a, n, l)`.
- Stable facts to preserve across iterations:
  - bounds `0 <= i && i <= n`
  - unchanged parameters `a == a@pre` and `n == n@pre`
  - memory ownership `IntArray::full(a, n, l)`
  - semantic summary `cnt == count_positive_spec(sublist(0, i, l))`
- Initialization check: before the first test, `i == 0` and `cnt == 0`, so the summary reduces to the empty-prefix case `count_positive_spec(sublist(0, 0, l)) == 0`.
- Preservation expectation: after reading `a[i]`, the next state should summarize `sublist(0, i + 1, l)`. The branch `if (a[i] > 0) cnt++;` matches the recursive definition of `count_positive_spec`.
- Exit usefulness: when `i == n`, the prefix becomes the full list, so one small loop-exit assertion should be enough to align the invariant with the postcondition.

## Planned edit

- Add one loop invariant carrying the prefix-count summary.
- Add one loop-exit `Assert` fixing `i == n` and rewriting the prefix summary to the full-list summary.
