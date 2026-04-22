# Annotation Reasoning

## Round 1

- `n == 0` returns immediately, so the loop only runs in the nonempty case after `cur = a[0]` and `out[0] = cur`.
- At the loop head, `i` is the next output position to fill. That means the processed region is the prefix `[0, i)`.
- The scalar summary should follow the repository's max-scan pattern exactly: `cur == max_list_nonempty(sublist(0, i, la))`.
- The heap summary for `out` must preserve both parts:
  - the written prefix already satisfies the target prefix-max relation
  - the untouched suffix still contains the old list `lo`
- Keeping `a == a@pre`, `out == out@pre`, and `n@pre == Zlength(...)` in the invariant should prevent later witnesses from rebuilding unchanged-parameter facts.

## Round 2

- I compared this with the existing `array_max` and `array_add` patterns.
- `array_max` shows the right scalar invariant for the running maximum.
- `array_add` shows the stable heap shape for an output array that is filled left-to-right: use an existential prefix list `l1` plus the untouched suffix `sublist(i, n@pre, lo)`.
- That gives the concrete loop-head invariant:
  - `exists l1, Zlength(l1) == i`
  - `forall k < i, l1[k] == max_list_nonempty(sublist(0, k + 1, la))`
  - `IntArray::full(out, n@pre, app(l1, sublist(i, n@pre, lo)))`

## Round 3

- The store `out[i] = cur;` needs the usual local opening around the exact write cell.
- Before the store, the bridge assertion should expose:
  - `a[i]` as a readable cell
  - `out[i]` as the writable cell taken from `app(l1, sublist(i, n@pre, lo))`
- After the optional `cur = a[i]` update and the store, the second bridge should close both arrays back to full form and extend the processed prefix from length `i` to length `i + 1`.
- The new prefix element should simply be `cur`, and the branch invariant should guarantee that this `cur` is exactly `max_list_nonempty(sublist(0, i + 1, la))`.

## Round 4

- Initialization lines up cleanly:
  - after `out[0] = cur`, we have already written the prefix of length `1`
  - `cur == a[0]` should match `max_list_nonempty(sublist(0, 1, la))`
- Exit should also be direct: when `i == n@pre`, the suffix `sublist(i, n@pre, lo)` is empty, so the existential prefix list itself can be chosen as the postcondition witness `lr`.
- I am not adding a separate loop-exit `Assert` in the first pass because the invariant already stores the full output semantics in the form needed for the postcondition.

## Round 5

- The first `symexec` retry failed before checking the loop at all:
  - `unexpected PT_COMMA, expecting PT_REQUIRE`
- This is the same front-end restriction already seen in `array_add`: the annotated working copy cannot keep `With la, lo` even though the input contract was bootstrapped that way.
- Fix direction:
  - keep `Require` and `Ensure` unchanged
  - normalize only the binder syntax from `With la, lo` to `With la lo`
- After this parser-only repair, rerun `symexec` immediately from a clean generated directory so the next failure, if any, reflects the actual VC shape.

## Round 6

- The next `symexec` retry got past parsing and failed at the branch assignment `cur = a[i];`.
- That suggests the pre-branch bridge is too aggressive: I had already opened both `a[i]` and `out[i]` before entering the `if`, but this loop only needs an explicit heap bridge for the write to `out[i]`.
- The input array `a` is read-only and follows the standard scan pattern already used in `array_max` and `count_positive`, where plain `IntArray::full(a, ...)` is enough for `a[i]` reads inside the branch.
- Fix direction:
  - keep `IntArray::full(a, ...)` in the loop invariant across the branch
  - let the `if` update only the scalar fact for `cur`
  - move the only heap-opening bridge to just before `out[i] = cur;`
- This should align the annotations with the real phase boundary: branch computes the new prefix maximum, then the store materializes it into the output array.

## Round 7

- The simplified write bridge still failed, but now the failure text is more specific:
  - at `out[i] = cur;`, the executor complains that it would write a null program value
- The printed state already shows the needed logical fact on the branch:
  - either `la[i] <= cur_old` or, on the other branch, `cur` should become `la[i]`
- That points to a branch-merge issue for the program variable `cur`, not a missing heap opening for `out[i]`.
- Nearby successful patterns like `string_reverse_copy` rely on the loop invariant plus plain stores, without forcing `missing_i` bridges at every write.
- Fix direction:
  - remove the write-specific `which implies` blocks entirely
  - keep the split `out` heap in the invariant
  - add one explicit `Assert` after the `if` to stabilize `cur == max_list_nonempty(sublist(0, i + 1, la))` before the store
- If this works, the remaining obligations should move cleanly into proof generation instead of front-end symbolic execution.

## Round 8

- Proof debugging on `safety_wit_5` showed the current invariant is still missing an explicit signed-int range fact:
  - the generated goal needs `i + 1 <= INT_MAX`
  - from the current invariant, we only know `1 <= i < n@pre`
- This is the same pattern already documented for `is_sorted_nondecreasing`: when the loop head or the next iteration uses `i + 1`, the bound must be preserved explicitly in the annotation layer instead of reconstructed later in Coq.
- To make the next-iteration arithmetic stable, the invariant should carry both:
  - `i + 1 <= INT_MAX`
  - `n <= INT_MAX` together with `n == n@pre`
- The post-`if` assertion should keep the same facts so the store and the later `++i` step can reuse them directly.
- After adding these bounds, I need to clear generated files and rerun `symexec`; the proof script must then be realigned to the new witnesses.
