## Iteration 1: initial loop invariant for last-character scan

Program point: the active annotated file `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_183816_string_ends_with_char.c` has an unannotated `while (1)` loop after the early `if (s[0] == 0) return 0;` branch. At loop head, `i` is intended to point at the current candidate last nonzero character. The loop reads `s[i + 1]`; if that next cell is zero, the loop exits with `i` pointing at the final nonzero character, otherwise it increments `i`.

The contract models `s` as `CharArray::full(s, n + 1, app(l, cons(0, nil)))` and states that every `l[k]` for `0 <= k < n` is nonzero. Therefore the early branch handles `n == 0`; on the fall-through path we need to expose `0 < n` before entering the loop. The loop invariant must preserve `0 <= i && i < n`, the unchanged parameters `s == s@pre` and `c == c@pre`, the nonzero-prefix property, and the full array ownership. The bound `i < n` is needed both to justify reading `s[i + 1]` within the `n + 1` array and to prove that after `s[i + 1] == 0` the only possible sentinel position is `i + 1 == n`.

Planned annotation changes: add a fall-through assertion after the empty-string branch recording `0 < n` and the preserved array facts; add the loop invariant immediately before the `while`; add a minimal loop-exit assertion immediately after the loop recording `i == n - 1` plus preserved parameter and memory facts. This should allow the final `if (s[i] == c)` branches to match the postcondition cases using `l[n - 1]` while keeping the input string memory unchanged.

## Iteration 2: keep the local index through the pre-loop assertion

Observed failure: the first `symexec` run failed at the loop invariant check in the active annotated file at line 38. The log showed the left side of the pre-loop assertion had the stores for `s`, `c`, and the character array, but the invariant right side needed `store(i_84_addr, i_value, signed int)`. The pre-loop `Assert` had recorded `0 < n` and the preserved memory facts, but it did not mention `i == 0`, so the assertion transition discarded the local index permission before the invariant check.

Planned fix: add `i == 0` to the fall-through assertion immediately before the loop invariant. This keeps the `i` local store available and gives the invariant initialization witness `i = 0` together with `0 < n`.

## Iteration 3: retain explicit bounds at loop exit for the final read

Observed failure: after adding `i == 0`, `symexec` passed the loop-invariant initialization but failed at the final `if (s[i] == c)` with `Cannot derive the precondition of Memory Read` at line 53. The loop-exit assertion recorded `i == n - 1` and the full character array, but it did not explicitly retain `0 < n` or `0 <= i && i < n`. The memory-read checker is syntactic enough that relying on arithmetic reconstruction from `i == n - 1` is not robust.

Planned fix: strengthen the loop-exit assertion with `0 < n` and `0 <= i && i < n` while keeping `i == n - 1`. This gives the next read `s[i]` a direct in-bounds fact against `CharArray::full(s, n + 1, ...)`.

## Iteration 4: preserve the original integer upper bound through the loop

Observed failure: after `symexec` succeeded, the first manual proof attempt left `string_ends_with_char_safety_wit_6` with the pure goal `i + 1 <= 2147483647`. The proof state had `0 <= i`, `i < n`, and `0 < n`, but it did not have `n < INT_MAX`. That upper bound was present in the function precondition but was not preserved by the fall-through assertion, loop invariant, or loop-exit assertion, so the generated safety witness lacked the fact needed for the increment/read bound.

Planned fix: add `n < INT_MAX` to the pre-loop assertion, loop invariant, and loop-exit assertion. This is annotation-layer state that should be preserved by the loop, not reconstructed manually in `proof_manual.v`. After this edit, clear the generated Coq files and rerun `symexec`.
