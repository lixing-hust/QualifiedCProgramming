# Annotation Reasoning

## Round 1

- Current program point: the `for (i = 0; i < n; ++i)` loop in `array_any_negative`.
- Without a loop invariant, the verifier has no persistent semantic fact about the already scanned prefix when execution reaches the final `return 0`, and no stable frame facts connecting the current parameters back to the pre-state.
- Loop variable role: `i` is the next unread array index. At each loop head, the processed region is exactly indices `0 <= j < i`.
- Required postcondition:
  - the early `return 1` path needs an existential witness showing some in-bounds index has a negative value;
  - the final `return 0` path needs the universal fact that every index in `[0,n)` is nonnegative;
  - both paths must preserve `IntArray::full(a, n, l)`.
- Planned invariant:
  - bounds `0 <= i && i <= n`;
  - unchanged parameters `a == a@pre` and `n == n@pre`;
  - prefix semantic fact `(forall (j: Z), (0 <= j && j < i) => l[j] >= 0)`;
  - memory ownership `IntArray::full(a, n, l)`.
- Initialization check: before the first loop test, `i == 0`, so the prefix universal fact is vacuous.
- Preservation check: if `a[i] < 0`, the function returns immediately and does not need the next loop-head invariant. On the fallthrough path, the branch condition establishes the current element is nonnegative, so the prefix fact extends from `< i` to `< i + 1`.
- Exit usefulness: when the loop exits, the invariant plus the negated loop guard gives `i == n`; restating the invariant with `i == n` gives exactly the full-range universal fact needed before `return 0`.

## Planned edit

- Add the loop invariant immediately before the `for` statement.
- Add a minimal loop-exit `Assert` immediately after the loop and before `return 0`, fixing `i == n` and restating the full-range nonnegative property.
