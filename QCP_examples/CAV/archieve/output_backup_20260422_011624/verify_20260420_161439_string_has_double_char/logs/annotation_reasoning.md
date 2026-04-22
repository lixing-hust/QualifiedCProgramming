# Annotation Reasoning

## Round 1

- Loop shape: `i` is the left index of the next adjacent pair `(i, i + 1)` to inspect. At the loop head, all adjacent pairs with left index `j < i` have already been checked and found unequal.
- Required postcondition: returning `1` needs an existential witness `i` with `0 <= i`, `i + 1 < n`, and `l[i] == l[i + 1]`; returning `0` needs the universal inequality for every valid adjacent pair, while preserving `CharArray::full(s, n + 1, app(l, cons(0, nil)))`.
- Stable facts needed in the invariant: `0 <= i && i <= n`, `s == s@pre`, the contract fact that every logical string element before `n` is nonzero, the checked-prefix property `(forall (j: Z), (0 <= j && j + 1 < n && j < i) => l[j] != l[j + 1])`, and the full char-array ownership.
- Initialization check: initially `i == 0`, so the checked-prefix property is vacuous and all heap and nonzero facts come from the precondition.
- Preservation expectation: if `s[i] == 0` or `s[i + 1] == 0`, the loop exits. Otherwise the path conditions give both positions are nonzero; if `s[i] == s[i + 1]`, the current `i` is the existential witness for return `1`; if they differ, incrementing `i` extends the checked prefix by one adjacent pair.
- Exit usefulness: if the loop exits at `s[i] == 0`, the invariant and nonzero-prefix fact force `i == n`, so every valid pair has left index `< i`. If the loop exits at `s[i + 1] == 0`, then after the first guard `s[i] != 0` we have `i < n`, and the second guard plus the nonzero-prefix fact force `i + 1 == n`, so again every valid pair has left index `< i`.

## Planned edit

- Add one `Inv` immediately before the `while (1)` loop.
- Do not add a loop-exit `Assert` on the first attempt because the closest adjacent-equality example showed that such assertions can disturb local variable permission cleanup.

## Round 2

- First `symexec` attempt failed before a complete VC set with `Cannot derive the precondition of Memory Read` at `annotated/verify_20260420_161439_string_has_double_char.c:32`, the statement `if (s[i + 1] == 0)`.
- The invariant gives `0 <= i && i <= n` and the full `CharArray`, and the path just passed through `if (s[i] == 0) break`, so semantically `s[i] != 0`. Together with the contract fact that all positions `< n` are nonzero, this should force `i < n`, hence `i + 1 <= n`, making the read of the terminator-inclusive slot valid.
- The failure is a local bridge gap rather than a weak loop invariant: the verifier needs the derived bound at the read point.
- Planned repair: add one `Assert` immediately after the first guard and before reading `s[i + 1]`, restating `i + 1 <= n` together with the preserved heap and processed-prefix facts. Then clear generated files and rerun `symexec`.

## Round 3

- The second `symexec` run succeeded and generated VCs, but inspecting `string_has_double_char_goal.v` showed that `string_has_double_char_safety_wit_4`, `safety_wit_7`, `safety_wit_10`, and `entail_wit_3` were missing the contract facts `0 <= n` and `n < INT_MAX` in their premises.
- The cause is the Round 2 bridge assertion: it restated the local read bound but accidentally omitted the stable integer range facts for `n`, so generated witnesses after that assertion cannot prove `i + 1 <= INT_MAX` or re-establish the loop invariant's range facts after `i++`.
- Planned repair: strengthen the bridge assertion immediately after the first guard by adding `0 <= n && n < INT_MAX`. This is annotation-level information that already comes from the precondition and should be preserved across the loop.
