# Annotation Reasoning

## Round 1

- The loop index `i` is the next position to write, so the invariant has to describe a processed prefix `0 .. i - 1` and an untouched suffix `i .. n - 1`.
- `a` and `b` are read-only across the whole loop, and the postcondition requires them to remain exactly `la` and `lb`. Those parameter-unchanged facts should stay in the invariant instead of being reconstructed later in witnesses.
- `out` starts as `lo`, then each iteration updates exactly one cell. The stable shape is therefore:
  - processed prefix already equals `la[k] + lb[k]`
  - remaining suffix still equals the old output list `lo`
- A weak invariant like “`out` matches the spec for all processed indices” without preserving the untouched suffix would leave the heap shape under-specified for the next store and for loop exit.

## Round 2

- I compared the expected shape with the existing `copy_array` pattern. The verifier expects the store target to be opened as `IntArray::missing_i(... ) * data_at(...)`, and source reads are also more stable when their current cells are exposed explicitly.
- That means the bridge before `out[i] = a[i] + b[i];` should open:
  - `a[i]` as `data_at(..., la[i])`
  - `b[i]` as `data_at(..., lb[i])`
  - `out[i]` as `data_at(..., lo[i])`
- The post-store bridge can then close the arrays back to full form with the prefix extended to `i + 1`.

## Round 3

- I chose the concrete prefix/suffix expression
  `app(sublist(0, i, map2 Z.add la lb), sublist(i, n@pre, lo))`
  because it matches the desired postcondition exactly at loop exit and keeps the untouched suffix in a canonical form during the loop.
- Exit reasoning is then minimal: when `i == n@pre`, the suffix becomes empty and the full `out` array equals `map2 Z.add la lb`.
- No separate loop-exit `Assert` looks necessary initially because the invariant already lines up with the function postcondition.

## Round 4

- The first parser retry showed two front-end constraints that the higher-level reasoning did not account for:
  - comma-separated binders in `With la, lb, lo` are rejected here, so the annotated copy has to use `With la lb lo`
  - `map2` is not available in C annotations for this front end
- To keep the same semantic content while staying inside supported syntax, I rewrote the invariant to the standard existential prefix/suffix form:
  - `l1` is the processed output prefix with `l1[k] = la[k] + lb[k]`
  - `l2` is the untouched suffix copied from the old output `lo`
- This keeps the heap shape explicit for `missing_i` and should still let loop exit reconstruct the postcondition by taking `lr = l1` once `i == n@pre`.
