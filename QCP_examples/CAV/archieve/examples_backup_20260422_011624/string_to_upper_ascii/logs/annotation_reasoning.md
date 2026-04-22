# Annotation Reasoning

## Round 1: initial loop invariant

- Program point: the only loop is the `while (1)` immediately after `int i = 0;` in `annotated/verify_20260419_084727_string_to_upper_ascii.c`.
- Current issue before editing: the active annotated copy has no loop invariant, so `symexec` will not have a stable summary for the processed prefix of the in-place string update.
- Loop state meaning:
  - `i` is the next string index to inspect.
  - Positions `< i` have already been transformed according to `string_to_upper_ascii_spec`.
  - Positions `>= i` and `< n` still contain the original suffix from `l`.
  - Position `n` is the terminator `0`.
- Planned invariant shape:
  - keep bounds `0 <= i && i <= n`
  - keep parameter identity `s == s@pre`
  - preserve the contract-level nonzero fact `(forall (k: Z), (0 <= k && k < n) => l[k] != 0)`
  - split the original input list as `l == app(l1, l2)` with `Zlength(l1) == i` and `Zlength(l2) == n - i`
  - describe the current buffer as `CharArray::full(s, n + 1, app(app(string_to_upper_ascii_spec(l1), l2), cons(0, nil)))`
- Initialization check: at `i == 0`, choose `l1 = nil` and `l2 = l`; the buffer is still the original `app(l, cons(0, nil))`, which is equal to the invariant buffer shape after simplifying `string_to_upper_ascii_spec(nil)`.
- Preservation check:
  - if `s[i] == 0`, the loop exits and no preservation step is required.
  - otherwise `i < n`; the current element is the head of `l2`.
  - the branch assignment either stores `x - 97 + 65` for lowercase ASCII or leaves `x` unchanged, matching `upper_ascii_char x` in the imported Coq spec.
  - after `i++`, the next invariant can use `l1 ++ [x]` as the processed prefix and the tail of `l2` as the remaining suffix.
- Exit usefulness: at loop exit, invariant plus `s[i] == 0` should force `i == n` using the preserved nonzero fact for all `k < n`; then `l2` is empty and the buffer shape reduces to the required postcondition.
- No extra `Assert` or `which implies` is planned for the first attempt; if `symexec` reports a concrete missing bridge, add the smallest bridge around that program point and rerun from clean generated files.
