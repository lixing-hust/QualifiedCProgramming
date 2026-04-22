## 2026-04-21 first symexec failure: missing loop assertions

Observed failure: a clean `symexec` run on `annotated/verify_20260421_144632_merge_sorted_arrays.c` failed at line 35 with `Error: Lack of assertions in some paths for the loop!`. The generated Coq files are partial and cannot be reused for completion.

Program point: the first `while (i < n && j < m)` has no invariant. The function also has two later tail-copy loops, so each loop needs its own entry-state invariant.

Invariant plan before editing: model `i` and `j` as consumed prefixes of `la` and `lb`, and `k` as the output prefix length with `k == i + j`. The output memory is split semantically as `app(l1, l2)`, where `l1` has length `k` and equals `merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb))`, while `l2` is the original untouched `lo` suffix from index `k` to `n + m`. The input arrays remain `IntArray::full` with the original `la` and `lb`, and parameter equalities such as `a == a@pre`, `n == n@pre`, and `out == out@pre` are preserved to avoid return witnesses losing the pre-state names.

For the second loop, the first loop has exited with one source exhausted. At entry to `while (i < n)`, the relevant state is `j == m`, `k == i + m`, and the written output prefix equals `merge_sorted_arrays_spec(sublist(0, i, la), lb)`. For the third loop, the state is `i == n`, `k == n + j`, and the prefix equals `merge_sorted_arrays_spec(la, sublist(0, j, lb))`. These invariants should initialize at the true loop entry control points and expose enough information for the final postcondition when both tails are exhausted.

First edit: add only these three loop invariants, without extra `Assert`/`which implies` bridges. If `symexec` next fails at a concrete array read or write, add the smallest local bridge at that program point and rerun from a clean generated directory.

## 2026-04-21 second symexec issue: invariant shape caused frontend blow-up

Observed failure: after adding the first semantic invariants, `symexec` ran for about 50 seconds with zero lines in `logs/qcp_run.log` and zero-byte generated files. The process was still CPU-running and had not reached even the normal startup lines. I stopped that run rather than waiting indefinitely.

Likely cause: the first invariant put the recursive Coq function `merge_sorted_arrays_spec` applied to `sublist(...)` directly inside all three loop invariants, together with quantified sortedness and suffix facts. That shape is much heavier than the array examples that keep invariants mostly as prefix/suffix memory shape and push local element transitions into smaller bridge assertions.

Next edit: simplify the invariants to the memory/bounds skeleton only: preserve `i`, `j`, `k`, parameter equalities, list lengths, sortedness premises, and output split `IntArray::full(out, ..., app(l1, l2))`, but remove the recursive spec equality and suffix-value forall from the invariant. This tests whether the frontend can progress through the loops and identifies the next concrete bridge needed. This may be too weak for final proof, but it should isolate whether the blow-up was caused by the recursive spec in the invariant.

## 2026-04-21 third annotation reduction: isolate memory-shape cost

Observed failure: the reduced prefix/suffix invariant without recursive spec equality still ran for more than 40 seconds without log output. This suggests that even the `exists l1 l2` plus `app(l1, l2)` output split may be too expensive for this three-loop merge function before local bridges are added.

Next edit: reduce each loop invariant to a minimal ownership skeleton with a single existential `lout`: index bounds, `k` relation, parameter equalities, input lengths, `Zlength(lout) == n@pre + m@pre`, and full ownership of `a`, `b`, and `out`. This deliberately drops output-prefix semantics to test whether the verifier can handle the control-flow and memory updates at all. If this succeeds, the semantic facts can be reintroduced incrementally at the exact loop where they are needed.

## 2026-04-21 fourth annotation reduction: avoid pre-state arithmetic in loop ownership

Observed failure: the single-`lout` ownership invariant still ran more than 30 seconds without diagnostics. The remaining suspicious part is pervasive `n@pre + m@pre` arithmetic inside invariant lengths and ownership predicates.

Next edit: keep the same weak ownership invariant but express bounds and array lengths with current `n`, `m`, and `n + m`. The C code never assigns to `n` or `m`, and the invariant still records `a == a@pre`, `b == b@pre`, and `out == out@pre`; this edit is only to make the symbolic executor's invariant matching cheaper. If this produces a normal diagnostic, later semantic strengthening should follow this current-state arithmetic style and add only the pre-state equalities needed by the final return witness.

## 2026-04-21 fifth annotation repair: second loop entry invariant too strong

Observed failure: after switching to current-state arithmetic, `symexec` produced a normal entailment failure while initializing the second loop invariant. The left side had first-loop exit facts `j >= m`, `j <= m`, and `i < n` in the branch displayed by the log, but the verifier had to prove the second loop invariant at the loop-head before the `i < n` guard is consumed in all paths. The previous second invariant required `j == m` and `k == i + m`, which is only guaranteed on paths where the second loop actually executes; if the first loop exited because `i == n`, execution still reaches the second loop head and the invariant must hold even when `j < m`.

Repair: weaken the second loop invariant to the same general index relation as the main loop skeleton: `0 <= i <= n`, `0 <= j <= m`, and `k == i + j`. This is true at first-loop exit regardless of which source is exhausted, and the second loop body preserves it because it increments `i` and `k` together while leaving `j` unchanged. The third loop may still use `i == n` because after the second loop exits, either it copied the remaining `a` elements or `i == n` was already true.
## 2026-04-21 retry: replace whole-array existential invariants with segment invariants

Fresh retry result: running the current weak annotation with the canonical explicit symexec command and a 180-second timeout produced status 124. `logs/qcp_run.log` remained empty and the generated `goal`, `proof_auto`, `proof_manual`, and `goal_check` files were all zero bytes. This reproduces the previous CPU-bound blocker on the current annotated file.

Blocker localization: all three current loop invariants own `IntArray::full(out, n + m, lout)` under an existential `lout`. Even without semantic prefix facts, every loop iteration writes `out[k]`, so the frontend must recover a focused cell and rebuild a whole-array existential across nested control-flow and across the second-loop entry where either source may be exhausted. The closest stable repository example is `QCP_examples/int_array_merge_rel.c`, which avoids whole-array ownership in merge loops and instead keeps processed and remaining ranges as `IntArray::seg` pieces.

Next edit: replace the three weak `IntArray::full` loop invariants with segment-based invariants. The main loop will existentially split `a` into processed and remaining pieces, `b` into processed and remaining pieces, and `out` into written prefix and unwritten suffix. The pure facts keep `la == app(la_done, la_rem)`, `lb == app(lb_done, lb_rem)`, `k == i + j`, and lengths of the processed pieces. The second-loop invariant will use the same segment shape plus `(i == n || j == m)` because the invariant is checked at the loop head before the `i < n` guard is consumed. The third-loop invariant can strengthen to `i == n`. This edit targets only the VC-generation blocker and does not change the function contract or implementation.

## 2026-04-21 retry: concrete sublist segments after initialization failure

Observed failure: the segment-invariant retry completed immediately with `Partial Solve Invariant Error` at `annotated/verify_20260421_144632_merge_sorted_arrays.c:56:4`, the first loop head. This is progress compared with the previous timeout, but the solver could not instantiate the existential remainder lists introduced by the invariant when splitting `IntArray::full(a, n, la)`, `IntArray::full(b, m, lb)`, and `IntArray::full(out, n + m, lo)` into `IntArray::seg` pieces. The checked residual SEP still contained `IntArray.seg(a@pre, 0, Zlength(la), la_rem)` and analogous `b`/`out` goals with the existential witnesses unresolved.

Next edit: keep the segment-based shape, but remove the existential input remainder witnesses. Use concrete `sublist(0, i, la)`, `sublist(i, n, la)`, `sublist(0, j, lb)`, and `sublist(j, m, lb)` for input segments. For the unwritten output suffix use `sublist(k, n + m, lo)`, because all writes are to the processed prefix `0..k`. Leave only `lout_done` existential for the already written output prefix. This should make loop initialization and cell focusing deterministic for the frontend.

## 2026-04-21 retry: use full output with app prefix/suffix instead of seg split

Observed failure: the concrete-sublist segment retry still failed immediately at the first loop invariant initialization. The residual SEP required full-length segment goals such as `IntArray.seg(a@pre, 0, Zlength(la), sublist(0, Zlength(la), la))` from `IntArray.full(a@pre, n, la)`, and the available strategy did not close those segment goals automatically.

Next edit: stop splitting the input arrays in the invariant, and stop splitting output into two segment predicates. Keep `IntArray::full(a, n, la)` and `IntArray::full(b, m, lb)`. For output, use the stable array-example pattern `IntArray::full(out, n + m, app(lout_done, sublist(k, n + m, lo)))`, with `Zlength(lout_done) == k`, so initialization can choose `lout_done = nil` and later writes extend only the prefix list.

## 2026-04-21 retry: add semantic prefix equality after weak return witness

Observed proof-stage blocker: fresh `symexec` succeeded, but `merge_sorted_arrays_return_wit_1` is not provable from the current invariant. At final exit it only knows `IntArray.full(out, n + m, app(lout_done, sublist(k, n + m, lo)))` and `Zlength(lout_done) == k`; there is no fact connecting `lout_done` with `merge_sorted_arrays_spec(la, lb)`. This is not a Coq tactic issue; the annotation is semantically too weak for the postcondition.

Next edit: keep the successful ownership shape `IntArray::full(out, n + m, app(lout_done, sublist(k, n + m, lo)))`, but add the minimal prefix semantics `lout_done == merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb))` to each loop invariant. This avoids the earlier segment/existential initialization problems while giving the return witness a direct path to the postcondition when `i == n`, `j == m`, and `k == n + m`.


## 2026-04-21 annotation repair after proof counterexample

Manual proof of `entail_wit_2_1` exposed a real invariant weakness rather than a local tactic gap. The generated VC asks to prove `lout_done_2 ++ [Znth i_3 la 0] = merge_sorted_arrays_spec (sublist 0 (i_3 + 1) la) (sublist 0 j_3 lb)`. That is not derivable from sortedness and the branch condition `la[i] <= lb[j]` alone unless the invariant also records two-pointer history: every consumed `b[p]` is `<= la[i]` while `i < n`, and every consumed `a[q]` is `<= lb[j]` while `j < m`. These facts are true initially, preserved by the branch conditions plus sorted input arrays, and needed by both tail-copy loops. I will add those cross-boundary pure facts to all loop invariants/loop-exit assertions. I will also add `n == n@pre` and `m == m@pre`, because the return witness must connect current loop-state lengths back to the contract lengths `n_pre` and `m_pre`.

## 2026-04-21 annotation parser repair for cross facts

The first cross-boundary repair failed during `symexec` at `annotated/verify_20260421_144632_merge_sorted_arrays.c:89:4` with `Cannot infer size of array`. The problematic shape was a free access such as `la[i]` guarded by implication `(i < n) => ...`; at a loop head `i` may equal `n`, and the frontend does not use that implication to infer the array access size. I will replace those facts with quantified range forms: consumed `b[p]` is `<= la[q]` for every future `a` index `i <= q < n`, and consumed `a[q]` is `<= lb[p]` for every future `b` index `j <= p < m`. Each array access then has an explicit quantified bound in the same antecedent, matching the contract sortedness style.

## 2026-04-21 annotation variable-name repair

The second cross-boundary form failed after partial VC generation with `The array q_167 of Znth is not a list type. The type is Z`. This points to a frontend parsing/type issue around the bound variable name `q` in indexed expressions such as `la[q]`. The mathematical invariant shape is still the intended repair, so I will keep the quantified range facts but rename the quantified variables to avoid `q` as an index name.

## 2026-04-21 annotation switch to explicit Znth

Renaming the quantified indices did not fix the frontend issue; `symexec` failed with `The array ai_167 of Znth is not a list type. The type is Z`, so bracket notation in these quantified invariant facts is being mis-typed by the frontend. I will switch only the cross-boundary pure facts to explicit Coq-style `Znth(index, list, 0)` calls to avoid array-size inference on ghost lists while retaining the same mathematical ordering facts for manual proof.

## 2026-04-21 strict tie-order repair

A Coq proof probe of `entail_wit_2_1` showed that the cross-boundary invariant also needs to respect the merge spec tie rule. `merge_sorted_arrays_spec` chooses from `a` when values are equal, so an element already consumed from `b` cannot merely be `<=` a future `a` element; it must be strictly `<` that future `a` element. This is preserved by the program because `b[j]` is consumed only in the branch `a[i] > b[j]`, and then sortedness of `a` carries the strict comparison to later `a` indices. I will change only the consumed-b/future-a fact from `<=` to `<` and rerun `symexec`.

## 2026-04-21 retry annotation repair: preserve list lengths for tail-loop proofs

Manual proof reached `proof_of_merge_sorted_arrays_entail_wit_4`, the preservation witness for `while (i < n)` after the main merge loop. The generated VC contains the semantic prefix equality and bounds such as `i < n_pre`, but it does not contain `Zlength(la) == n`, `Zlength(lb) == m`, or `Zlength(lo) == n + m` from the original contract. Those length facts are needed to prove `sublist 0 (i+1) la = sublist 0 i la ++ [Znth i la 0]` and to normalize the output suffix after `replace_Znth`. This is an annotation gap, not a Coq tactic gap: the loop invariants preserve `n == n@pre` and `m == m@pre`, but not the ghost list lengths tied to those bounds. I will add `Zlength(la) == n`, `Zlength(lb) == m`, and `Zlength(lo) == n + m` to each loop invariant / loop-exit assertion immediately after `n + m <= INT_MAX`, preserving the existing semantic and heap shape facts. After this annotation change, I will delete the generated Coq files and rerun `symexec` in the same workspace.

## 2026-04-21 retry annotation repair: preserve sortedness for tail-loop proofs

After preserving list lengths and regenerating VCs, `proof_of_merge_sorted_arrays_entail_wit_4` reached the semantic append proof for the `while (i < n)` tail loop. The VC now has the length facts but still lacks the original sortedness facts for `la` and `lb`. Without sortedness, the proof cannot show that appending `Znth i la 0` to the merged prefix is semantically valid: it must know every prior `la` prefix element is `<= Znth i la 0`, and the analogous `lb` fact is needed for the later `while (j < m)` tail loop. I will add the two original sortedness facts, written with explicit `Znth` to avoid the earlier quantified bracket-notation frontend bug, to each loop invariant / loop-exit assertion after the length facts.
