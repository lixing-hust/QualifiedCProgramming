## Function summary

Target function: `copy_array`

Raw intent: copy the `n` elements of integer array `src` into integer array `dst`.

Concrete implementation:

```c
void copy_array(int n, int *src, int *dst) {
    int i;

    for (i = 0; i < n; ++i) {
        dst[i] = src[i];
    }
}
```

## Semantic decisions

- The function is `void`; the full postcondition is expressed as the final memory state.
- `src` is read-only from the program's perspective, so the postcondition should preserve its abstract list.
- `dst` is fully overwritten element-by-element, so the postcondition should state that its final abstract list equals the pre-state abstract list of `src`.
- No arithmetic overflow condition is needed because the body only loads and stores `int` values without arithmetic.

## Memory model decision

- Use `IntArray::full(src, n, ls)` for the source array.
- Use `IntArray::full(dst, n, ld)` for the destination array.
- Keep both arrays as full arrays in the contract instead of shape-only predicates, because the function's semantic result is exact value equality between `dst` and pre-state `src`.
- Use separating ownership between the two arrays in the contract. This is the most verification-friendly interpretation for a two-buffer copy and avoids alias-sensitive behaviors that are not discussed in the raw statement.

## Logical variables

- `ls`: pre-state abstract contents of `src`
- `ld`: pre-state abstract contents of `dst`

`ld` is only used to describe ownership of the writable destination in the precondition; the postcondition intentionally discards the old destination contents.

## Length and boundary choices

- Keep `0 <= n` from the problem statement.
- Add `Zlength(ls) == n` and `Zlength(ld) == n` explicitly to make later loop reasoning straightforward and consistent with existing array examples.

## Coq dependency decision

- No extra `input/copy_array.v` is needed.
- Existing list and array predicates from `verification_list.h` and `int_array_def.h` are sufficient.
- No custom mathematical function or problem-specific bridge predicate is required.
