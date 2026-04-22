## Round 1

- Program point: the active annotated file has a `for (i = 0; i < n; ++i)` loop with no invariant, so symbolic execution has no loop summary for `ans`, the processed prefix, or preserved `IntArray::full(a, n, l)`.
- Loop meaning: at the loop head, `i` is the next index to read and `[0, i)` is the processed prefix.
- Required postcondition: the return value is either `-1` with no match in the whole range `[0, n)`, or a valid index whose value equals `k` and all later indices differ from `k`.
- Planned invariant: keep `0 <= i <= n`, unchanged parameters `a == a@pre`, `n == n@pre`, `k == k@pre`, array ownership, and a conjunctive prefix summary for `ans`: `-1 <= ans < i`, `ans == -1` implies no processed match, `0 <= ans` implies `l[ans] == k`, and every processed index after `ans` differs from `k`.
- Why implication form: the same function in `examples/array_find_last_equal` records that a top-level disjunction in `Inv` caused a branch-count mismatch during `symexec`; the implication-based conjunctive form preserves the same semantics while keeping the loop invariant shape stable.
- Initialization check: before the first loop test, `i == 0` and `ans == -1`; `ans < i` holds and quantified facts over `[0,0)` are vacuous.
- Preservation check: if `a[i] == k`, assigning `ans = i` makes `l[ans] == k` true and the later-processed range `(ans, i+1)` empty. If `a[i] != k`, the existing no-match/last-match summary extends through the newly read index.
- Exit use: when the loop exits, `i == n`; an immediate loop-exit `Assert` will restate the prefix summary over `[0,n)` so the return witness can choose the correct disjunctive postcondition branch.

## Planned edit

- Add one `Inv` immediately before the `for` loop.
- Add one loop-exit `Assert` immediately after the loop and before `return ans`.
