# Annotation Reasoning

## Round 1: initial loop invariant

- Program point: the single `while (1)` loop immediately after `int i = 0;` in `annotated/verify_20260420_155956_string_to_lower_ascii.c`.
- Current issue before editing: the active annotated copy has no `Inv`, but the loop updates the buffer in place and needs a summary of which prefix has already been transformed.
- Loop state meaning:
  - `i` is the next string index to inspect.
  - Positions `< i` have already been transformed according to `string_to_lower_ascii_spec`.
  - Positions `>= i` and `< n` still contain the original suffix of `l`.
  - Position `n` remains the zero terminator.
- Planned invariant:
  - keep bounds `0 <= i && i <= n`
  - preserve `s == s@pre`
  - split the original list as `l == app(l1, l2)` with `Zlength(l1) == i` and `Zlength(l2) == n - i`
  - preserve the contract facts `Zlength(l) == n` and `(forall (k: Z), (0 <= k && k < n) => l[k] != 0)`
  - describe current memory as `CharArray::full(s, n + 1, app(app(string_to_lower_ascii_spec(l1), l2), cons(0, nil)))`
- Initialization check: at `i == 0`, choose `l1 = nil` and `l2 = l`; the memory is still the original input, which matches the invariant because `string_to_lower_ascii_spec(nil) = nil`.
- Preservation check: if `s[i] != 0`, the nonzero-prefix contract and current memory shape make `i < n` and expose the head of `l2`; the branch either writes `x - 65 + 97` for uppercase ASCII or leaves `x` unchanged, matching `lower_ascii_char x`.
- Exit usefulness: when the loop exits from `s[i] == 0`, the invariant plus the nonzero-prefix contract should imply `i == n`; then `l2` is empty and the memory shape reduces to the required postcondition.
- First attempt does not add a separate loop-exit `Assert`; if symbolic execution or the manual return witness needs a bridge, add the smallest assertion at the actual exit point and rerun `symexec`.
