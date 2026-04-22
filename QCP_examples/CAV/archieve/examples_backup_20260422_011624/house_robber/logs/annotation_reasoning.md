# Annotation Reasoning

## 2026-04-21 initial loop invariant

Program point: the `for (i = 0; i < n; ++i)` loop in `annotated/verify_20260421_134943_house_robber.c`.

The unannotated loop cannot establish the postcondition because the verifier has no relation between the scalar state `prev2`/`prev1` and the imported Coq recurrence `house_robber_spec`. At the loop test, `i` is the number of processed array elements and the next element to read. The intended state is:

- `prev1` equals `house_robber_acc(0, 0, sublist(0, i, l))`, the result for the processed prefix.
- `prev2` equals the previous-prefix result when `i >= 1`; at `i == 0`, the previous prefix does not exist, so `prev2` is just the initialized zero.
- `n`, `a`, and the full array permission are preserved so the loop can read `a[i]` and the function can return the same `IntArray::full(a, n, l)`.
- Range facts are needed because `take = prev2 + a[i]` must stay within `int`; nonnegative elements and `sum(l) <= INT_MAX` should allow `prev1`, `prev2`, and `take` to be bounded by appropriate prefix sums.

Planned annotation: add an `Inv` before the loop with `0 <= i <= n`, `n == n@pre`, `a == a@pre`, `IntArray::full(a, n, l)`, `prev1 == house_robber_acc(0, 0, sublist(0, i, l))`, split implications for `prev2` at `i == 0` and `1 <= i`, and nonnegative/sum upper bounds for both accumulators. This should make initialization immediate, preservation follow the Coq recurrence over `sublist(0, i + 1, l)`, and loop exit at `i == n` imply the return condition because `house_robber_spec(l)` is `house_robber_acc 0 0 l`.

## 2026-04-21 first symexec failure: undeclared Coq function

Observed failure: the first clean `symexec` run stopped at the invariant with `Use of undeclared identifier 'house_robber_acc'` in `annotated/verify_20260421_134943_house_robber.c:38:4`. The input contract only declares `house_robber_spec` as an `Extern Coq` symbol; although `house_robber_acc` is defined in `input/house_robber.v`, it is not available to the annotation parser by name.

Next annotation change: rewrite the invariant to use the declared function `house_robber_spec(sublist(...))` for both prefix states. This keeps the same semantic content because `house_robber_spec(xs)` is defined as `house_robber_acc 0 0 xs`, avoids changing the formal contract, and should allow the frontend to parse the annotation.

## 2026-04-21 second symexec failure: implication shape

Observed failure: after switching to `house_robber_spec`, `symexec` failed at the same invariant line with `Cannot unify types Assertion and Prop`. The likely trigger is the pair of implication clauses for the special `i == 0` case and the `1 <= i` case; this frontend is sensitive to assertion-level implication mixed directly into a long invariant conjunction.

Next annotation change: remove the split implications and state `prev2 == house_robber_spec(sublist(0, i - 1, l))` uniformly. At `i == 0`, the previous-prefix slice is the empty slice, which matches the initialized `prev2 == 0`; at `i >= 1`, it is the intended previous processed prefix. This avoids an assertion/proposition type mismatch while preserving the semantic loop state needed by the return witness.
