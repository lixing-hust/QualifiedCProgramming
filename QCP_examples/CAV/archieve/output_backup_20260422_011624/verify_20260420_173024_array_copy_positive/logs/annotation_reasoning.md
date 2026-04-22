## 2026-04-20 17:31:22 CST - Loop invariant before first symexec

Current annotated file had no loop invariant before the `for (i = 0; i < n; ++i)` loop in `annotated/verify_20260420_173024_array_copy_positive.c`. The postcondition needs a final output list `lr` of length `n` whose every element is selected by a case split on the corresponding original input element `la[i]`, while the input array `a` remains unchanged. Without an invariant, symbolic execution has no persistent description of the partially written output prefix and cannot derive the final existential `lr`.

At the loop head, `i` is the next element to process and also the length of the processed prefix. The invariant should therefore split the output list into `app(l1, l2)`, where `l1` has length `i` and already satisfies the postcondition's positive/nonpositive selection rule for indices `< i`, while `l2` has length `n@pre - i` and still equals the corresponding suffix of the original output list `lo`. The invariant must also keep `a == a@pre`, `out == out@pre`, `n == n@pre`, and the length facts for `la` and `lo`, so the loop body can read `a[i]`, write `out[i]`, and the loop exit state can instantiate `lr` with the final `l1`.

I will add this invariant immediately before the loop. I am not adding a loop-exit `Assert` yet because when the loop exits, the invariant plus `!(i < n)` and `0 <= i <= n@pre` should give `i == n@pre`, making `l2` empty and `app(l1, l2)` usable as the result list.

## 2026-04-20 17:32:10 CST - Parser syntax fix for With binders

The first clean `symexec` run did not reach verification-condition generation. `logs/qcp_run.log` reports `bison: syntax error, unexpected PT_COMMA, expecting PT_REQUIRE` at `annotated/verify_20260420_173024_array_copy_positive.c:6:12`, which is the binder line `With la, lo`. This is the same frontend syntax issue seen in nearby array examples: the parser accepts space-separated binders such as `With la lo`, while the comma form fails before any semantic checking.

I will update only the active annotated copy from `With la, lo` to `With la lo`. This does not change the `Require` or `Ensure` formulas and does not redesign the contract; it only makes the existing binders parseable by the verification frontend. After the edit I will clear generated Coq files and rerun `symexec`.
