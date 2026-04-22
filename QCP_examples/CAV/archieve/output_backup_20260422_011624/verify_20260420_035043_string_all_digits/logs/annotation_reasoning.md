# Annotation Reasoning

## Round 1

- Program point: immediately before the `while (1)` loop in the active annotated file.
- Current gap: the plain input contract owns the whole string, but without a loop invariant the verifier has no persistent relationship between loop index `i`, the already-scanned prefix, and `string_all_digits_spec`.
- Loop meaning: at the loop head, `i` is the next character to inspect, and the processed region is the prefix `l1` with `Zlength(l1) == i`.
- Facts to preserve: `0 <= i && i <= n`, `s == s@pre`, the split `l == app(l1, l2)`, `string_all_digits_spec(l1) == 1`, the original nonzero-prefix fact, and `CharArray::full(s, n + 1, app(l, cons(0, nil)))`.
- Initialization: choose `l1 = nil` and `l2 = l`; then `i == 0`, `Zlength(nil) == 0`, and `string_all_digits_spec(nil) == 1` by the Coq definition.
- Continue preservation: when the loop does not break and does not return, path conditions give `s[i] != 0`, `48 <= s[i]`, and `s[i] <= 57`; adding this current digit to a prefix whose spec is already `1` should keep the prefix spec equal to `1`.
- Exit usefulness: on `s[i] == 0`, the invariant plus the contract fact that every element before `n` is nonzero should imply `i == n`, so the processed prefix is the whole logical string and the final return `1` matches `string_all_digits_spec(l)`. On the early return branch, the invariant says prior elements were digits and the current one is outside the digit interval, so the full-list spec should evaluate to `0`.

## Planned edit

- Add one `Inv exists l1 l2, ...` annotation immediately before the `while (1)` loop.
- Do not add bridge assertions yet; if `symexec` reports a concrete assertion gap after this invariant, handle that in a later round.
