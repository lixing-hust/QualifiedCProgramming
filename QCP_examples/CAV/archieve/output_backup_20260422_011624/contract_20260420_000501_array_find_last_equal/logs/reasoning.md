# Contract Reasoning

## Source Semantics

- Target function: `array_find_last_equal`.
- Inputs: an integer length `n`, an integer array pointer `a`, and an integer key `k`.
- Precondition from the statement: `n >= 0`, `a` points to exactly `n` integer elements, and the function must not modify the array.
- Implementation scans `i` from `0` to `n - 1` and maintains `ans` as the most recent index where `a[i] == k`.
- If no element equals `k`, `ans` remains `-1`.

## Boundary Cases

- `n == 0`: the loop body is not executed, so the result is `-1`; the universal no-match postcondition is vacuous.
- Single match: result is that index.
- Multiple matches: result is the greatest index satisfying `a[index] == k`.
- No match: result is `-1`.

## Memory Contract

- The array is read-only.
- Use `IntArray::full(a, n, l)` in both precondition and postcondition to preserve the complete array contents.
- Bind logical list `l` with `With l`, and require `Zlength(l) == n`.

## Result Specification

The postcondition can be expressed directly in C contract logic without an auxiliary Coq function:

- No-match case: `__return == -1` and every valid index contains a value different from `k`.
- Match case: `0 <= __return < n`, `l[__return] == k`, and every later valid index contains a value different from `k`.

This exactly states that the result is the last matching index.

## Coq Dependency Decision

- No existing public Coq function is required.
- No task-specific recursive function or bridge predicate is necessary because the last-match semantics are compactly expressible with bounded quantifiers over `l`.
- Do not create `input/array_find_last_equal.v`.

## Verify-Stage Boundary

- Do not add loop invariants, assertions, bridge assertions, or loop-exit assertions in Contract output.
- The C file should contain only includes, the target function, and its complete `Require` / `Ensure` contract.
