# Annotation Reasoning

## Round 1

- Loop meaning: at the loop head, `i` is the next character to inspect, so the processed prefix is the first `i` elements of `l`.
- Required postcondition:
  - if the loop exits on `s[i] == 0`, we need the whole logical string to satisfy `string_all_lowercase_spec(l) == 1`
  - if the function returns `0` from the range check, we need the whole logical string to satisfy `string_all_lowercase_spec(l) == 0`
- Stable facts worth preserving at every loop head:
  - `0 <= i && i <= n`
  - `s == s@pre`
  - `l == app(l1, l2)` with `Zlength(l1) == i`
  - `string_all_lowercase_spec(l1) == 1`, meaning every processed character has already passed the lowercase test
  - the original nonzero-prefix contract and full-string ownership
- Initialization check:
  - choose `l1 = nil`, `l2 = l`
  - then `Zlength(l1) == 0 == i`
  - `string_all_lowercase_spec(nil) == 1` by definition
- Preservation check on the continue path:
  - path conditions give `s[i] != 0` and `97 <= s[i] <= 122`
  - from `CharArray::full(s, n + 1, app(l, cons(0, nil)))`, the current element is the head of the suffix `l2`
  - appending one lowercase character to a prefix whose spec is already `1` should preserve `string_all_lowercase_spec` equal to `1`
- Exit usefulness:
  - on `s[i] == 0`, the invariant plus the precondition that every `l[k]` for `k < n` is nonzero should force `i == n`, so `l2 = nil` and the prefix fact becomes the full-list result
  - on the early `return 0` branch, the invariant says all earlier characters are lowercase while the current character is outside `[97, 122]`, which should make the full-list spec evaluate to `0`

## Planned edit

- Add one loop invariant immediately before `while (1)`.
- Start without extra `Assert` or `which implies`; only add them if the first `symexec` result exposes a concrete gap.
