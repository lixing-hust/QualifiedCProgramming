# Annotation Reasoning

## Round 1

- Program point: the single `for (i = 1; i <= n; ++i)` loop in `annotated/verify_20260421_045730_count_multiples.c`.
- Current issue: the active annotated C has no loop invariant. The postcondition requires `__return == count_multiples_spec(n@pre, k@pre)`, but without a loop-head invariant the verifier has no durable relation between `cnt` and the already processed integers.
- Loop-state interpretation: at the loop head, `i` is the next integer to test, so the processed prefix is the inclusive range `1..i-1`. Therefore `cnt` should equal `count_multiples_spec(i - 1, k)` at that control point.
- Stable facts to preserve:
  - `1 <= i && i <= n + 1`, because the loop starts at `1` and exits immediately after incrementing past `n`.
  - `n == n@pre` and `k == k@pre`, because the postcondition is stated over pre-state parameters and the loop does not assign either parameter.
  - `1 <= n && n < INT_MAX && 1 <= k`, because modulo safety and increment safety depend on these integer facts.
  - `0 <= cnt && cnt <= i - 1`, because `cnt++` must stay in the signed integer range and the count cannot exceed the number of processed candidates.
  - `cnt == count_multiples_spec(i - 1, k)`, because this is the semantic summary needed at loop exit.
- Initialization check: immediately before the first loop test, `i == 1` and `cnt == 0`, so the semantic summary becomes `count_multiples_spec(0, k)`, which should reduce to zero from the input Coq definition.
- Preservation expectation: if `i % k == 0`, the branch increments `cnt`, matching the next counted element in `count_multiples_spec(i, k)`; otherwise `cnt` stays unchanged, matching the non-divisible case. After the `++i` loop step, the invariant again describes `count_multiples_spec(i - 1, k)` for the new `i`.
- Exit usefulness: when the loop exits, the invariant gives `i <= n + 1` and the failed loop condition gives `i > n`, hence `i == n + 1`. A small loop-exit assertion should bridge the semantic summary to `cnt == count_multiples_spec(n, k)` before the return.

## Planned edit

- Add one loop invariant before the `for` loop with the bounds, unchanged parameter facts, accumulator range, and prefix-count summary above.
- Add one post-loop `Assert` that fixes `i == n + 1`, preserves parameter equality, and rewrites the prefix summary to the full `count_multiples_spec(n, k)` required by the postcondition.
