## 2026-04-20 annotation pass 1

Program point: the `while (1)` loop before reading `s[i]` in `string_remove_char_to_output`.

Current issue: the active annotated C has no loop invariant. The loop scans the input string with `i`, conditionally writes to `out[j]`, and later returns `j`. Without an invariant, symexec cannot preserve either the input string ownership or the relationship between `j` and the filtered output prefix across loop iterations.

Planned annotation: add an invariant immediately before the while loop with existential `l1 l2 d1`. The invariant records `l == app(l1, l2)`, `Zlength(l1) == i`, `j == Zlength(string_remove_char_to_output_spec(l1, c))`, the original input memory unchanged as `CharArray::full(s, n + 1, app(l, cons(0, nil)))`, and the output buffer as `CharArray::full(out, n + 1, app(string_remove_char_to_output_spec(l1, c), d1))` with `Zlength(d1) == n + 1 - j`. This should initialize with `l1 = nil`, keep the invariant in both branches of `s[i] != c`, and make loop exit strong enough to bridge to the postcondition after writing the terminating zero.

## 2026-04-20 annotation pass 2

Observed result after pass 1: `symexec` reached symbolic execution of `string_remove_char_to_output` but failed at the final assignment `out[j] = 0` in `annotated/verify_20260420_190707_string_remove_char_to_output.c:62` with `Assign Exec fail`. The post-loop assertion exposed the output as `app(string_remove_char_to_output_spec(l, c), d1)`, but it did not split `d1` into the exact cell at offset `j` and the remaining tail. Since the write index is exactly `j == Zlength(string_remove_char_to_output_spec(l, c))`, the assignment needs a bridge assertion whose heap list is `app(app(string_remove_char_to_output_spec(l, c), cons(x, nil)), t)`.

Planned change: replace the post-loop assertion with `exists x t` such that `Zlength(t) == n - j` and `CharArray::full(out, n + 1, app(app(string_remove_char_to_output_spec(l, c), cons(x, nil)), t))`. This should give symexec a focused writable cell for the terminator and leave the postcondition tail `t` directly available after the write.

## 2026-04-20 annotation pass 3

Observed result after pass 2: `symexec` still failed at `out[j] = 0`. The bridge assertion focused the heap cell but accidentally omitted the pure bounds on `j` that the invariant had before the assertion. The assignment checker needs the write index to be known in range for an `n + 1` character array.

Planned change: retain the focused `exists x t` heap shape but add `0 <= j && j <= n` to the same post-loop assertion before rerunning `symexec`.
