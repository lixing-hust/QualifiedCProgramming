# Annotation Reasoning

## 2026-04-20 Retry: add missing DP loop invariant

Current blocker: the workspace has no generated Coq files yet, and the active annotated file is still identical to the input C. The function contains a `for (i = 2; i < n; ++i)` loop with two rolling dynamic-programming states, so symbolic execution needs an invariant at the loop guard. Without an invariant, the verifier cannot preserve the semantic relationship between `prev2`, `prev1`, the untouched `cost` array, and the final postcondition `__return == min_cost_two_steps_z(l)`.

Program point: immediately before the `for` loop. At that point, because the earlier `if (n == 1)` returned, the loop path has `2 <= n`, `prev2 == cost[0]`, and `prev1 == cost[0] + cost[1]`. The Coq spec gives `min_cost_two_steps_z(sublist(0, 1, l)) == l[0]` and `min_cost_two_steps_z(sublist(0, 2, l)) == l[0] + l[1]`, so the natural loop guard invariant for next index `i` is:

- `2 <= i && i <= n`;
- `n == n@pre` and `cost == cost@pre`;
- `prev2 == min_cost_two_steps_z(sublist(0, i - 1, l))`;
- `prev1 == min_cost_two_steps_z(sublist(0, i, l))`;
- nonnegative/range facts for `prev2` and `prev1`, bounded by the corresponding prefix sums, to support integer overflow obligations for additions;
- `IntArray::full(cost, n, l)` because the loop only reads the array and must preserve the postcondition memory predicate.

The loop body reads `cost[i]`, assigns `cur` to either `prev1 + cost[i]` or `prev2 + cost[i]`, then shifts `prev2 = prev1` and `prev1 = cur`. This corresponds to the Coq recurrence in `min_cost_two_steps_acc` through `Z.min prev1 prev2 + l[i]`. The explicit numeric bounds are expected to make `cur` fit in the signed int range using nonnegative array elements and `sum(l) <= 2147483647`.

After the loop exits, `i < n` is false and the invariant has `i <= n`, so `i == n`; the exit assertion records that fact and rewrites the prefix expression to the whole-list postcondition shape `prev1 == min_cost_two_steps_z(l)` while preserving `IntArray::full(cost, n, l)`.

## 2026-04-20 Retry: remove loop-exit assertion after local cleanup failure

First `symexec` attempt after adding the invariant failed with `Fail to Remove Memory Permission of cur:105` at the assertion immediately after the `for` loop in `annotated/verify_20260420_222721_min_cost_two_steps.c`. This matches the known assertion-placement failure mode where a loop-exit assertion after the loop interferes with local variable cleanup. The invariant already gives `i <= n` and the false loop condition gives `n <= i`, so the proof phase can derive `i == n` and `sublist(0, n, l) = l` without an explicit C-level exit assertion. The next annotation change removes only the post-loop `Assert` and keeps the loop invariant unchanged.
