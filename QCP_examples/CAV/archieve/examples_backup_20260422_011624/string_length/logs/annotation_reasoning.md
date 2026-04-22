# Annotation Reasoning

## Round 1

- Loop shape: `i` is the next character index to inspect, so at the loop head the processed region is exactly the prefix of length `i`.
- Required postcondition: on loop exit and return, prove `i == n` while preserving `CharArray::full(s, n + 1, app(l, cons(0, nil)))`.
- Stable facts that should remain true at every loop head:
  - `0 <= i <= n`
  - `s == s@pre`
  - the contract-level nonzero-prefix fact `forall (k: Z), (0 <= k && k < n) => l[k] != 0`
  - the original full string ownership `CharArray::full(s, n + 1, app(l, cons(0, nil)))`
- Initialization check:
  - at function entry `i == 0`, so the bounds hold immediately
  - `s` is unchanged
  - the contract facts and full-array ownership come directly from the precondition
- Preservation expectation:
  - on the continue branch, `s[i] != 0`
  - because the string is still modeled by `app(l, cons(0, nil)))`, the current position cannot be past `n`
  - after `i++`, the next loop head still satisfies `0 <= i <= n`
  - all other invariant facts are unchanged because the function does not write through `s`
- Exit usefulness:
  - on the break branch, `s[i] == 0`
  - combined with the invariant's full-array fact, this means the logical string element at position `i` is `0`
  - the contract-level fact says every position `k < n` is nonzero, so `i < n` is impossible
  - the invariant already gives `i <= n`, hence the only remaining case is `i == n`

## Planned edit

- Add a single loop invariant with the four stable facts above.
- Do not add `Assert` or `which implies` yet; this loop should be simple enough to test with invariant-only symbolic execution first.

## Round 2

- The first `symexec` run reached the parser and produced:
  - `fatal error: Expected loop after loop invariant.`
- Localization:
  - the invariant was written after `while (1)` and before the loop body
  - existing repository examples place `/*@ Inv ... */` immediately before the loop statement itself
- This means the issue is not the invariant content yet; it is the invariant attachment point.
- Fix direction:
  - move the invariant comment so it precedes the `while (1)` statement
  - keep the invariant formula unchanged for the next symbolic-execution probe
