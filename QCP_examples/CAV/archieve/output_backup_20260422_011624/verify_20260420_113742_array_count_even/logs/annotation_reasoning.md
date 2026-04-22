# Annotation Reasoning

## Iteration 1: Prefix-count invariant for even elements

- Program point:
  - the `for (i = 0; i < n; ++i)` loop in `array_count_even`
- Current issue:
  - the unannotated loop updates `cnt` based on each array element but gives the verifier no persistent relation between `cnt` and the already processed prefix of `l`
  - the postcondition requires `__return == array_count_even_spec(l)`, so loop exit must connect the final counter to the specification over the entire list
- Planned annotation:
  - add an invariant immediately before the loop with `0 <= i && i <= n`
  - preserve unchanged parameters with `a == a@pre` and `n == n@pre`
  - preserve the full read-only array resource as `IntArray::full(a, n, l)`
  - state `cnt == array_count_even_spec(sublist(0, i, l))`, meaning `cnt` is exactly the count for the processed prefix
  - add a minimal loop-exit assertion after the loop fixing `i == n` and rewriting the accumulator to `array_count_even_spec(l)`
- Why this should work:
  - initialization holds because before the first loop test the processed prefix is empty and `cnt` is zero
  - preservation matches the recursive spec: when `a[i] % 2 == 0`, the branch increments `cnt`; otherwise it leaves `cnt` unchanged
  - on exit, `i == n` and `Zlength(l) == n` let the processed prefix `sublist(0, i, l)` denote the whole list, while the array resource is unchanged
