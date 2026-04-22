# Annotation Reasoning

## Round 1

- Loop shape: `i` is the next destination index to fill, so at the loop head the processed region is the prefix `dst[0..i)`.
- Required postcondition: on exit, `src` must stay unchanged and `dst` must contain `rev(l) ++ [0]`.
- Stable facts that should stay in the invariant:
  - bounds `0 <= i && i <= n`
  - unchanged parameters `src == src@pre`, `dst == dst@pre`, and `n == n@pre`
  - the full source ownership `CharArray::full(src, n + 1, app(l, cons(0, nil)))`
  - a split destination ownership `CharArray::full(dst, n + 1, app(l1, d1))`
- Candidate semantic summary for the written prefix:
  - choose `l1` as the already-written prefix and `d1` as the untouched suffix
  - keep `Zlength(l1) == i`
  - keep `Zlength(d1) == n + 1 - i`
  - keep `(forall (k: Z), (0 <= k && k < i) => Znth(k, l1, 0) == Znth(n - 1 - k, l, 0))`
- Initialization check: at `i == 0`, choose `l1 = nil` and `d1 = d`; the prefix relation is vacuous.
- Preservation expectation: one loop body writes `dst[i] = src[n - 1 - i]`, so the new written prefix should be the old one extended by exactly the mirrored source element required by the invariant.
- Exit usefulness: when the `for` loop stops, `i == n`; the invariant then says the whole non-terminator prefix of `dst` matches the reversed source characters pointwise. After `dst[n] = 0`, the remaining proof obligation should be pure list reasoning, not missing memory shape.

## Planned edit

- Add one loop invariant carrying the destination split and the pointwise reverse-prefix relation.
- Add one loop-exit assertion fixing `i == n` and re-exposing the same destination split just before the terminating store.
- Rerun `symexec` from a clean generated directory after the edit.

## Round 2

- The first real `symexec` run reached symbolic execution and failed at the final statement `dst[n] = 0`.
- Diagnosis:
  - the loop-body stores were acceptable under the invariant
  - the failure only appeared after the explicit loop-exit `Assert`
  - nearby successful char-array examples (`string_copy`, `string_set_a`) let the verifier derive the final writable cell directly from loop exit instead of forcing a stronger full-array exit assertion first
- This suggests the exit assertion is over-constraining the state right before the final store rather than helping it.
- Fix direction:
  - remove the explicit loop-exit assertion
  - keep the loop invariant unchanged
  - rerun `symexec` and only add a more local bridge if the final write still fails
