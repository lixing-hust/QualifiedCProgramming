# Annotation Reasoning

## Semantic understanding

`copy_array` iterates from `0` to `n - 1`, reads `src[i]`, and writes that value into `dst[i]`. The contract already fixes the intended behavior: `src` remains the same full array `ls`, and `dst` must end as the same list `ls`.

## Why the loop invariant is needed

The body performs one read from `src` and one write to `dst`, so the invariant has to preserve both full-array ownership facts across iterations while recording partial progress in `dst`.

The natural progress statement is:

- indices `0 .. i - 1` of `dst` have already been copied from `ls`
- indices `i .. n - 1` of `dst` still contain their original list `ld`

That gives the value relation:

`IntArray::full(dst, n@pre, app(sublist(0, i, ls), sublist(i, n@pre, ld)))`

This invariant is:

- true initially at `i = 0`, because `sublist(0, 0, ls)` is empty and the whole destination is still `ld`
- preserved by one loop step, because writing `dst[i] = src[i]` extends the copied prefix from length `i` to `i + 1`
- strong enough at exit `i = n@pre`, because the destination list becomes `app(sublist(0, n@pre, ls), sublist(n@pre, n@pre, ld))`, which is exactly `ls`

## Bridge assertions

Before `dst[i] = src[i]`, the tool needs pointwise access to both arrays at index `i`. So the bridge converts the two full-array predicates into:

- `IntArray::missing_i(src, i, 0, n@pre, ls) * data_at(src + (i * sizeof(int)), int, ls[i])`
- `IntArray::missing_i(dst, i, 0, n@pre, app(sublist(0, i, ls), sublist(i, n@pre, ld))) * data_at(dst + (i * sizeof(int)), int, ld[i])`

After the assignment, the same destination cell contains `ls[i]`, and folding it back yields the invariant for `i + 1`.

## Risk check

- No extra overflow conditions are needed because the function only copies integers and does not perform arithmetic on element values.
- The contract already guarantees both arrays have length `n`.
- I am not strengthening or redesigning `Require`/`Ensure`; verify only adds invariant and bridge annotations.
