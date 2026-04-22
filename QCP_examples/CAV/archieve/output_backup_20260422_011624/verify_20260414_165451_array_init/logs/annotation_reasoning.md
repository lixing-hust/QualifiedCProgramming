# Annotation Reasoning

## Semantic understanding

`array_init` walks the array from index `0` to `n - 1` and overwrites each element with `0`. The trusted contract already states that the input owns a full integer array of length `n` with abstract contents `l`, and the result should own the same array with contents `zeros(n)`.

## Invariant choice

The loop counter `i` is the next index to write. The stable state before each loop test is therefore:

- `0 <= i <= n@pre`
- `a == a@pre`
- `n@pre == Zlength(l)` so the list operators line up with the concrete array length
- `IntArray::full(a, n@pre, app(zeros(i), sublist(i, n@pre, l)))`

This says the processed prefix `[0, i)` has already been zeroed, while the suffix `[i, n)` still carries the original logical contents from `l`.

## Bridge assertions

Inside the loop body we need write permission for `a[i]`, so we open the full-array predicate with:

- `IntArray::missing_i(a, i, 0, n@pre, app(zeros(i), sublist(i, n@pre, l)))`
- `data_at(a + (i * sizeof(int)), int, l[i])`

After writing `0`, we fold back to the updated full-array predicate:

- `IntArray::full(a, n@pre, app(zeros(i + 1), sublist(i + 1, n@pre, l)))`

## Loop exit

When the loop exits, `i == n@pre`. Substituting that into the invariant gives `app(zeros(i), sublist(i, n@pre, l))`, which should normalize to `zeros(n@pre)`. A final exit assertion records that normalization explicitly for the verifier.

## Risk check

- Bounds: the loop guard gives `0 <= i < n`, and the invariant ties `n` to `Zlength(l)`.
- Aliasing: only `a[i]` is written; no additional pointers are introduced.
- Null / invalid memory: already covered by the trusted `IntArray::full(a, n, l)` precondition.
- Integer overflow: the proof only uses `i + 1` under `i < n@pre`, so the arithmetic obligations should be standard loop-index facts.
