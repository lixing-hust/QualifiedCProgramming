# Annotation Reasoning

## Round 1: initial loop invariant

- Program point: the only loop is the `while (1)` immediately after `int i = 0;` in `annotated/verify_20260420_034132_string_replace_char.c`.
- Current issue before editing: the active annotated copy has no loop invariant, so symbolic execution has no summary for the in-place prefix already processed by the loop.
- Loop state meaning:
  - `i` is the next character index to inspect.
  - Positions `< i` have already been transformed by `string_replace_char_spec` using `old_c` and `new_c`.
  - Positions `>= i` and `< n` still contain the original suffix from `l`.
  - Position `n` remains the zero terminator.
- Planned invariant shape:
  - keep bounds `0 <= i && i <= n`
  - keep parameter identity `s == s@pre`, `old_c == old_c@pre`, and `new_c == new_c@pre`
  - split the original list as `l == app(l1, l2)` with `Zlength(l1) == i` and `Zlength(l2) == n - i`
  - preserve `Zlength(l) == n` and the contract-level nonzero fact `(forall (k: Z), (0 <= k && k < n) => l[k] != 0)`
  - describe the current buffer as `CharArray::full(s, n + 1, app(app(string_replace_char_spec(l1, old_c, new_c), l2), cons(0, nil)))`
- Initialization check: at `i == 0`, choose `l1 = nil` and `l2 = l`; the buffer is the original `app(l, cons(0, nil))`, matching the invariant after simplifying `string_replace_char_spec(nil, old_c, new_c)`.
- Preservation check:
  - if `s[i] == 0`, the loop exits and no next-iteration invariant is needed.
  - otherwise the nonzero fact and terminator layout imply `i < n`, so the current cell corresponds to the head of `l2`.
  - when `s[i] == old_c`, assigning `new_c` matches the head case of `replace_char`; otherwise leaving the cell unchanged also matches the spec.
  - after `i++`, the next invariant can use `l1 ++ [x]` as the processed prefix and the tail of `l2` as the remaining suffix.
- Exit usefulness: at loop exit, invariant plus `s[i] == 0` should force `i == n`; then `l2` is empty and the heap shape reduces to the required postcondition.
- No separate bridge assertion is planned for the first attempt. If symbolic execution reports a concrete missing bridge, the next edit will add the smallest local assertion at that program point and rerun from clean generated files.
