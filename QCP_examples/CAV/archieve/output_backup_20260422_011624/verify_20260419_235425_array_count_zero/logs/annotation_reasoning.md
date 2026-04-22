# Annotation Reasoning

## Iteration 1: Prefix-count invariant for the array scan

- Program point:
  - the `for (i = 0; i < n; ++i)` loop in `array_count_zero`
- Current issue:
  - the unannotated loop does not preserve a relation between the scalar `count` and the already processed prefix of `l`
  - the postcondition requires `__return == array_count_zero_spec(l)`, so the verifier needs a loop invariant strong enough to rewrite the final `count` into the specification over the whole list
- Planned annotation:
  - add an invariant before the loop with `0 <= i && i <= n`
  - preserve unchanged parameters with `a == a@pre` and `n == n@pre`
  - preserve the full array resource as `IntArray::full(a, n, l)`
  - state the semantic accumulator relation `count == array_count_zero_spec(sublist(0, i, l))`
  - add a loop-exit assertion after the loop that fixes `i == n` and rewrites the accumulator to `array_count_zero_spec(l)`
- Why this should work:
  - initialization holds because `i == 0`, `count == 0`, and the spec over the empty prefix is zero
  - the body either increments `count` when `a[i] == 0` or leaves it unchanged, matching the recursive specification when the prefix is extended by one element
  - on loop exit, `i == n`, `Zlength(l) == n`, and `sublist(0, n, l)` is the full list, so the return value can satisfy the postcondition while preserving the unchanged array resource
