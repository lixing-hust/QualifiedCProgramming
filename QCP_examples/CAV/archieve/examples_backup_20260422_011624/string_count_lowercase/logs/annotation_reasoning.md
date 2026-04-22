# Annotation reasoning

## 2026-04-20 initial loop invariant

Program point: the `while (1)` loop in `string_count_lowercase`.

The unannotated loop scans `s` from index `0` until it reads the sentinel `0`. The formal precondition represents `s` as `CharArray::full(s, n + 1, app(l, cons(0, nil)))`, with every `l[k]` nonzero for `0 <= k < n`; therefore the first zero in this logical string is at index `n`. The accumulator `cnt` is updated exactly when the current character is between `97` and `122`, matching the recursive head case of `string_count_lowercase_spec`.

The invariant should hold at the loop guard/control point, before each read of `s[i]`. It keeps:

- `0 <= i && i <= n` so the read `s[i]` is within the `n + 1` character array and the sentinel index remains available.
- `s == s@pre`, the nonzero-prefix forall, and the full `CharArray::full` heap so the postcondition memory can be recovered unchanged.
- `cnt == string_count_lowercase_spec(sublist(0, i, l))`, meaning the accumulator is the count for the already processed prefix.

Initialization: at `i == 0` and `cnt == 0`, `sublist(0, 0, l)` is empty, so the invariant matches the spec result for `nil`.

Preservation: if `s[i] != 0`, the nonzero-prefix fact and full string representation force `i < n`; after the lowercase branch either increments `cnt` or leaves it unchanged, the recursive definition of `string_count_lowercase_spec` over `sublist(0, i + 1, l)` matches the branch condition for `l[i]`. Then `i++` reestablishes the prefix count invariant at `i + 1`.

Exit: if `s[i] == 0`, the invariant plus nonzero-prefix fact should imply `i == n`. A loop-exit `Assert` immediately after the loop records `i == n`, the unchanged input pointer and heap, and `cnt == string_count_lowercase_spec(l)`, which is the return postcondition.

## 2026-04-20 parser repair: avoid `sublist` in C annotation

Observed failure: the first `symexec` run stopped before generating usable VCs with `Use of undeclared identifier 'sublist'` at the loop invariant line containing `cnt == string_count_lowercase_spec(sublist(0, i, l))`.

This matches the existing `string_count_not_char` experience: the frontend can reject `sublist` in this string-scan annotation context even though similar array examples use it. The semantic shape is still a processed prefix plus unprocessed suffix, so the repair is to introduce existential lists `l1` and `l2` in the invariant, keep `l == app(l1, l2)` and `Zlength(l1) == i`, and track `cnt == string_count_lowercase_spec(l1)`.

The exit assertion remains the same because when the loop exits the proof should derive `i == n`, and then `l1 == l` from `l == app(l1, l2)`, `Zlength(l1) == n`, and `Zlength(l) == n`.
