## Round 1

- Program point: the `for (i = 0; i < n; ++i)` loop currently has no invariant, so `symexec` would not have a stable summary for the mutable accumulator `ans` or the preserved array ownership across loop iterations.
- Loop meaning: at the loop head, `i` is the next index to inspect and `[0, i)` is the processed prefix.
- Required semantic summary: after scanning a prefix, either `ans == -1` and no processed element equals `k`, or `ans` is a valid processed index with `l[ans] == k` and every later processed index differs from `k`.
- Stable facts to preserve: `0 <= i && i <= n`, unchanged parameters `a == a@pre`, `n == n@pre`, `k == k@pre`, and `IntArray::full(a, n, l)` because the function only reads the array.
- Initialization check: before the first loop test, `i == 0` and `ans == -1`; the no-match quantified fact over `[0,0)` is vacuous.
- Preservation check: if `a[i] == k`, assigning `ans = i` makes the last-match case true for `[0,i+1)` with the later-index condition vacuous. If `a[i] != k`, the existing last-match/no-match fact extends to `[0,i+1)` using the just-read inequality at index `i`.
- Exit use: when the loop exits, `i == n`, so the prefix summary becomes exactly the required postcondition over the whole range `[0,n)`. A small loop-exit assertion should restate `i == n` and the whole-range disjunction before `return ans`.

## Planned edit

- Add one loop invariant before the `for` loop with bounds, unchanged parameters, array ownership, and the processed-prefix last-match disjunction.
- Add one exit `Assert` immediately after the loop to bridge from `i == n` to the function postcondition.

## Round 2

- Observed failure: rerunning `symexec` after Round 1 failed at `annotated/verify_20260420_000745_array_find_last_equal.c:43:4` with `The number of now assertions and loop inv pre assertions does not match.` The generated directory had partial files, but the symbolic execution log stopped immediately after entering `array_find_last_equal`, so those files are stale partial output and must be regenerated after the annotation fix.
- Diagnosis: the loop invariant used a top-level semantic disjunction for the two accumulator states (`ans == -1` versus `0 <= ans`). Existing stable loop examples avoid top-level disjunction in `Inv`; this verifier front end can split the invariant into a different number of assertion branches at the loop head.
- Repair direction: keep the same semantics but encode it as conjunctive bounds plus implications: `-1 <= ans && ans < i`, `ans == -1 => no processed match`, and `0 <= ans => ans is a processed match and all later processed indices differ from k`. This avoids top-level disjunction while preserving the same prefix summary.
- The loop-exit assertion will use the same implication form with `i == n`, leaving the final disjunctive postcondition to the generated return witness/manual proof instead of forcing a disjunctive `Assert` in the annotation layer.

