# Contract reasoning: count_multiples

## Source semantics

- Target function: `count_multiples`.
- Inputs are scalar integers `n` and `k`.
- Natural-language domain: `n >= 1` and `k >= 1`.
- The program initializes `cnt = 0`, iterates `i` from `1` through `n`, increments `cnt` exactly when `i % k == 0`, and returns `cnt`.
- The function has no heap input, no heap output, and no side effects.

## Boundary and safety choices

- Keep the original interface `int count_multiples(int n, int k)`.
- Keep the original loop implementation.
- Add `n < INT_MAX` to avoid signed overflow in the `for` loop increment when the final iteration has `i == n`.
- Require `1 <= k` so `% k` is defined and matches the problem statement.
- Under `1 <= n && n < INT_MAX`, the counter never exceeds `n`, so `cnt++` remains within signed `int`.

## Mathematical specification

- The result is the number of integers `i` in `1..n` such that `i` is divisible by `k`.
- Although this is equivalent to `n / k` for positive `n` and `k`, the loop computes the value by enumeration.
- Use a problem-specific Coq recursive function `count_multiples_spec` to express the enumerating semantics directly:
  - `count_multiples_upto k fuel` counts multiples of `k` among positive integers represented by the natural fuel range.
  - `count_multiples_spec n k` instantiates that count with `Z.to_nat n`.

## Coq dependency decision

- A dedicated `input/count_multiples.v` is justified because the postcondition needs a stable logical counting function that mirrors the loop.
- No public Coq definition for this exact scalar counting problem was identified in the required contract-reading pass.
- The `.v` file contains only task-specific definitions and no proof script.

## Contract shape

- `Require`: scalar input domain and empty heap.
- `Ensure`: returned integer equals `count_multiples_spec(n@pre, k@pre)` and heap remains empty.
- No invariants, assertions, bridge assertions, or verify-stage comments are included.
