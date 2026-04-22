## 2026-04-20 annotation pass 1

Program point: the unannotated `while (1)` loop in annotated/verify_20260420_162845_string_count_spaces.c before the first read `s[i]`.
Issue: the loop scans an unknown number of characters, so without an invariant the verifier has no persistent relation between `cnt` and the prefix of `l` already processed. The postcondition requires `cnt == string_count_spaces_spec(l)` and preservation of `CharArray::full(s, n + 1, app(l, cons(0, nil)))`.
Observed context: input/string_count_spaces.c has `Zlength(l) == n`, every element of `l` is nonzero, and the actual terminator is the extra trailing 0. The loop exits only when `s[i] == 0`, so the invariant must carry `0 <= i <= n`, a split `l == app(l1, l2)`, `Zlength(l1) == i`, and `cnt == string_count_spaces_spec(l1)`. This makes initialization use `l1 = nil`, preservation append the current character to the processed prefix, and exit force `i == n` because positions before n are nonzero.
Planned edit: add an `Inv exists l1 l2` immediately before the loop with the prefix count relation, unchanged pointer relation `s == s@pre`, the nonzero premise, and the full character array permission. Add a minimal loop-exit `Assert` immediately after the loop to expose `i == n`, `cnt == string_count_spaces_spec(l)`, and the preserved buffer to the return statement.

