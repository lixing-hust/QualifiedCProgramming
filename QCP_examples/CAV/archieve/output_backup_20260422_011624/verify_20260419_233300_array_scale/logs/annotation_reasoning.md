## 2026-04-19 23:33:55 +0800

The active annotated file currently has no loop invariant for the `for (i = 0; i < n; ++i)` loop. At the loop head, `i` is the number of output cells already written and also the next index to process. The postcondition needs a final result list `lr` of length `n` such that every `lr[k]` is `la[k] * k@pre`, while `a` is preserved and `out` contains `lr`.

The invariant should therefore split `out` into a processed prefix and an untouched suffix. I will use witnesses `l1` and `l2`, where `l1` has length `i` and satisfies `l1[t] == la[t] * k@pre` for processed indices, and `l2` has length `n@pre - i` and still corresponds to the original `lo[i + t]` tail. The heap shape remains `IntArray::full(a, n@pre, la) * IntArray::full(out, n@pre, app(l1, l2))`. The invariant must also preserve parameter equalities `a == a@pre`, `out == out@pre`, `n == n@pre`, and `k == k@pre` so the generated return witness can connect the loop state back to the contract variables.

Inside the loop, the next statement reads `a[i]` and writes `out[i]`. Based on the existing `array_add` annotation pattern, I will add a bridge assertion before the assignment that opens the indexed cells via `IntArray::missing_i` and `data_at`. After the assignment, I will add a second bridge assertion that repacks the updated cell into a new prefix witness of length `i + 1`, with the remaining output tail expressed as `sublist(i + 1, n@pre, lo)`. This should make initialization, preservation, and loop exit line up with the postcondition when `i == n@pre`.

## 2026-04-19 23:35:17 +0800

The first `symexec` run failed during parsing before VC generation. `logs/qcp_run.log` reports `syntax error, unexpected PT_COMMA, expecting PT_REQUIRE` at the contract binder line `With la, lo`. Existing verified examples in this repository use space-separated binders, for example `With la lb lo`, so the comma is frontend syntax noise rather than a semantic contract change. I will update only the active annotated copy from `With la, lo` to `With la lo`, keep the `Require` and `Ensure` formulas unchanged, then clear generated files and rerun `symexec`.

## 2026-04-19 23:35:18 +0800

The second `symexec` run parsed the program and reached the loop body, but failed at the post-assignment `which implies` around line 63 of the active annotated file. The partial entailment log shows the assignment cell as `((la[i]) * NULL)` and reports unsolved stack stores for `n` and `k`. This means the manual bridge assertion before the assignment consumed or failed to preserve the local scalar permissions needed to evaluate the right-hand-side variable `k`.

The closest scalar-key examples (`array_contains`, `count_equal_to_k`, and `array_replace_k`) do not manually open array cells around simple indexed reads/writes; they keep scalar equalities in the invariant and let symbolic execution apply the array strategies. I will remove both loop-body bridge assertions and keep only the invariant, then rerun `symexec` from clean generated files. If the next failure identifies a specific missing array split, I will add a narrower assertion that preserves the scalar locals.
