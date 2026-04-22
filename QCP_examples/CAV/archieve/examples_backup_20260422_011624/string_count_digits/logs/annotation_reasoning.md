# Annotation reasoning

## 2026-04-20 initial loop invariant

Program point: the `while (1)` loop in `string_count_digits`.

The unannotated loop scans `s` from index `0` until it reads the sentinel `0`. The precondition gives `CharArray::full(s, n + 1, app(l, cons(0, nil)))`, `Zlength(l) == n`, and every element of `l` is nonzero, so the terminator is exactly the first logical zero at index `n`.

The accumulator `cnt` must equal the imported recursive specification on the already processed prefix. To avoid frontend issues with `sublist` in C annotations, the invariant introduces existential `l1 l2` with `l == app(l1, l2)` and `Zlength(l1) == i`, then records `cnt == string_count_digits_spec(l1)`.

Initialization holds with `i == 0`, `cnt == 0`, and an empty processed prefix. Preservation follows because a nonzero read means the current element belongs to `l`; the branch `s[i] >= 48 && s[i] <= 57` is the same digit classification used by `string_count_digits_spec`, so after optionally incrementing `cnt` and then incrementing `i`, the processed-prefix relation is restored for one more character.

Exit needs the terminator branch to yield `i == n`, after which the processed prefix is all of `l`. The assertion immediately after the loop records `i == n`, unchanged pointer/heap, and `cnt == string_count_digits_spec(l)` so the return postcondition can consume it.
