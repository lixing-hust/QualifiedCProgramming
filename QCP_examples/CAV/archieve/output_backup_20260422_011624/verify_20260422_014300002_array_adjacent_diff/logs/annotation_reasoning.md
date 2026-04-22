# Annotation Reasoning

## Round 1

- The current program has a single `for` loop, but the first `symexec` failure happens before loop analysis starts, so there is no evidence yet that an `Inv`, `Assert`, `which implies`, or loop-exit assertion is semantically required.
- The failure is parser-level at the contract header: this front end rejects comma-separated binders in `With`, even when the contract meaning is otherwise correct.
- The minimal safe edit is therefore to normalize only the active annotated copy from `With la, lo` to `With la lo`.
- This keeps the contract semantics unchanged, stays within Verify-stage permissions, and is the cheapest way to reach a real symbolic-execution signal before deciding whether any loop annotations are needed.

## Round 2

- After the binder fix, `symexec` reached the function body and failed with `Lack of assertions in some paths for the loop!`, so the real missing piece is now a loop-head summary.
- The loop index `i` is the next output position to write. At the loop head, positions `0 .. i - 1` of `out` should already contain adjacent differences, while positions `i .. n - 2` should still be the old contents from `lo`.
- The input array `a` is read-only, and the postcondition requires it to remain exactly `la`, so the invariant should keep `a == a@pre`, `out == out@pre`, `n == n@pre`, and `IntArray::full(a, n@pre, la)`.
- For `out`, the stable heap shape is a full array of length `n@pre - 1` split as `app(l1, l2)` where:
  - `Zlength(l1) == i`
  - `Zlength(l2) == (n@pre - 1) - i`
  - processed cells satisfy `l1[k] == la[k + 1] - la[k]`
  - untouched cells satisfy `l2[k] == lo[i + k]`
- The store itself should use a local bridge that opens `out[i]` as the current untouched cell `lo[i]`, then recloses the array with a one-element-longer processed prefix after the assignment.
- This invariant should make loop exit cheap: when the condition is false, `i + 1 >= n@pre`; combined with `i <= n@pre - 1`, that yields `i == n@pre - 1`, so the untouched suffix becomes empty and the processed prefix already has the postcondition shape.

## Round 3

- The first loop-step attempt still failed in the post-store `which implies`. The failure shape showed the symbolic state retained `replace_Znth(..., app(l1, l2))`, while my target introduced a second existential suffix `l2'`; that left the solver with unnecessary shape reconstruction work.
- To reduce that burden, I am switching the invariant to the more direct suffix form `app(l1, sublist(i, n@pre - 1, lo))`, matching the stable update pattern already used by other array-write examples in this repo.
- This keeps the semantic content unchanged:
  - `l1` still records the processed adjacent differences
  - the untouched suffix is now fixed canonically by `lo`
- The expected benefit is that after writing `out[i]`, the post-store target only needs to extend the processed prefix to `l1'` and shift the untouched suffix from `sublist(i, ...)` to `sublist(i + 1, ...)`, which should align better with the built-in array rules.

## Round 4

- The simplified suffix shape still failed specifically inside the post-store `which implies`, and the failure trace showed the front end already had the right `replace_Znth` update available in the symbolic heap.
- That means the problem is not lack of semantic information, but that the explicit bridge is asking the front end to complete a list-normalization step it does not need to finish before VC generation.
- The next adjustment is therefore to remove both loop-body `which implies` blocks entirely and keep only:
  - the loop invariant
  - the final loop-exit assertion
- This should allow `symexec` to proceed, with any remaining list-equality work deferred to generated Coq obligations instead of being forced at the annotation layer.

## Round 5

- Proof inspection later showed that the loop-exit assertion itself is not actually helping: it generates an `entail_wit_3` goal that must drop the live local `n` store from the left-hand heap.
- That is a classic sign the assertion is attached too late or is trying to repackage state at a control point where local-variable cleanup has not happened yet.
- The invariant already carries the semantic information needed at loop exit:
  - processed prefix values
  - `i <= n@pre - 1`
  - unchanged `a`, `out`, and `n`
- So I am removing the loop-exit assertion entirely and letting `symexec` generate the natural end-of-function witness from the invariant alone.
