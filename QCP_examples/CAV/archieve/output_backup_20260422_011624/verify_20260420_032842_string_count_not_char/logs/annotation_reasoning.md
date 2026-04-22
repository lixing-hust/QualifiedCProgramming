# Annotation Reasoning

## 2026-04-20 03:30:05 +0800 - Initial loop invariant

- Program point: the unannotated `while (1)` loop in `annotated/verify_20260420_032842_string_count_not_char.c`.
- Current blocker: the loop scans `s[i]` until the terminator and updates `count`, so `symexec` needs an invariant before it can justify the repeated character reads and the final return relation. The initial annotated copy is identical to the input and has no invariant.
- State meaning:
  - `i` is the length of the processed prefix of `l`;
  - `count` is the value of `string_count_not_char_spec` on that processed prefix;
  - `s` and `c` are unchanged from the pre-state;
  - the complete `CharArray::full(s, n + 1, app(l, cons(0, nil)))` ownership is preserved because the loop only reads.
- Planned annotation:
  - add a loop invariant immediately before `while (1)` with `0 <= i && i <= n`, `s == s@pre`, `c == c@pre`, `count == string_count_not_char_spec(sublist(0, i, l), c)`, the original no-internal-zero fact, and the full character-array predicate;
  - add a loop-exit assertion immediately after the loop fixing `i == n` and rewriting the prefix spec to the full-list spec before `return count`.
- Why this should work:
  - initialization gives `i == 0`, `count == 0`, and `sublist(0, 0, l)` is empty;
  - the loop guard and the precondition's no-internal-zero fact force `i < n` on non-exit paths, so reading `s[i]` corresponds to `l[i]`;
  - incrementing `count` exactly matches the recursive spec step for the next prefix depending on whether `s[i] == c`;
  - on exit, `s[i] == 0` plus no internal zero and `i <= n` should force `i == n`, making `sublist(0, i, l) == l`.

## 2026-04-20 03:31:02 +0800 - Replace parser-rejected `sublist`

- Observed failure: the first `symexec` run failed before usable VC generation with `Use of undeclared identifier 'sublist'` at the invariant line containing `string_count_not_char_spec(sublist(0, i, l), c)`.
- Trigger: this verifier frontend accepts `sublist(...)` in some array examples but rejects it in this annotated C context, matching the prior `string_contains_char` issue pattern.
- Localization: `annotated/verify_20260420_032842_string_count_not_char.c`, invariant before the `while (1)`.
- Planned annotation repair:
  - replace the `sublist` invariant with existential prefix/suffix lists `l1` and `l2`;
  - keep `l == app(l1, l2)` and `Zlength(l1) == i`;
  - track `count == string_count_not_char_spec(l1, c)`;
  - keep the same no-internal-zero fact and full array ownership.
- Expected effect: the parser should accept this shape because it is the same style used by the verified `string_contains_char` example, while preserving enough semantic information for the final return witness.
