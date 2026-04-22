# Annotation Reasoning

## Round 1

- Loop meaning: at the loop head, `i` is the next index to inspect, so the processed region is exactly `sublist 0 i l`.
- Required return behavior splits into two cases:
  - if the loop hits `s[i] == c`, the function returns `1`, so the invariant should already tell us the earlier prefix contains no `c` and the current element is the first matching point we need
  - if the loop hits `s[i] == 0`, the function returns `0`, so we need to derive `i == n` and then conclude the whole list `l` contains no `c`
- Stable facts worth keeping at every loop head:
  - `0 <= i && i <= n`
  - `s == s@pre`
  - `c == c@pre`
  - `(forall (k: Z), (0 <= k && k < n) => l[k] != 0)`
  - `CharArray::full(s, n + 1, app(l, cons(0, nil)))`
  - `string_contains_char_spec(sublist 0 i l, c) == 0`
- Initialization check:
  - `i == 0`
  - `sublist 0 0 l` is empty, so its spec is `0`
  - all ownership and nonzero-prefix facts come directly from the precondition
- Preservation check on the continue path:
  - the path condition gives `s[i] != 0` and `s[i] != c`
  - from the full-string model, index `i` corresponds to the current logical element of `l`
  - extending a prefix that still avoids `c` with one more non-`c` element should preserve `string_contains_char_spec(sublist 0 (i + 1) l, c) == 0`
- Exit usefulness:
  - on `s[i] == 0`, the invariant plus the nonzero-prefix contract should force `i == n`
  - then `string_contains_char_spec(sublist 0 i l, c) == 0` becomes the full-list result
  - on `s[i] == c`, the invariant already says the earlier prefix has no match, so the full list spec should evaluate to `1`

## Planned edit

- Add one loop invariant before `while (1)`.
- Start with the invariant only; do not add extra `Assert` or `which implies` unless the first `symexec` run shows a specific gap.

## Round 2

- The first `symexec` run failed in the parser before real VC generation.
- `qcp_run.log` reported:
  - `fatal error: bison: syntax error, unexpected PT_NATLIT, expecting PT_RPAREN or PT_COMMA`
  - location: the invariant line `string_contains_char_spec(sublist 0 i l, c) == 0`
- This is a frontend syntax issue rather than an invariant-design issue.
- Nearby verified examples in this repo use the concrete form `sublist(0, i, l)` inside annotations.
- Fix direction:
  - keep the same invariant meaning
  - rewrite the prefix expression to `sublist(0, i, l)`
  - rerun `symexec` from a clean generated directory

## Round 3

- The second `symexec` run still failed before VC generation, now with:
  - `Use of undeclared identifier 'sublist'`
- So this front end is not reliably accepting `sublist` inside this custom string-spec invariant, even though other built-in examples use it.
- A safer repo-established fallback is to replace derived list operators with an existential prefix/suffix split that exposes the processed prefix directly.
- New invariant plan:
  - `exists l1 l2,`
  - `l == app(l1, l2)`
  - `Zlength(l1) == i`
  - `string_contains_char_spec(l1, c) == 0`
  - together with unchanged parameter and heap facts
- This keeps the loop meaning the same while avoiding unsupported annotation syntax.
