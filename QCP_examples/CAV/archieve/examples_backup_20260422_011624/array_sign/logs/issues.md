# Verify Issues

## Symexec parser error on `With` binder comma

- Phenomenon: the first `symexec` run exited with status 1 before entering `array_sign`; `logs/qcp_run.log` reported `bison: syntax error, unexpected PT_COMMA, expecting PT_REQUIRE` at `annotated/verify_20260420_174025_array_sign.c:6:12`.
- Trigger: the annotated copy inherited `/*@ With la, lo` from the input contract. Existing verified examples for multi-binder contracts use whitespace-separated binders such as `With la lo`, and this frontend does not parse the comma form.
- Location: `annotated/verify_20260420_174025_array_sign.c`, function contract binder line.
- Fix action: normalize only the annotated working copy from `With la, lo` to `With la lo`. This is a parser-syntax normalization and does not change the Require/Ensure semantics.
- Result after fix: pending rerun of `symexec`.

## Symexec hang after parser normalization

- Phenomenon: after normalizing `With la lo`, the second `symexec` attempt stayed alive for over a minute with `logs/qcp_run.log` containing only the start marker and with zero-byte generated files (`array_sign_goal.v`, `array_sign_proof_auto.v`, `array_sign_proof_manual.v`, `array_sign_goal_check.v`).
- Trigger: the first invariant encoded the three output cases with separate implications for `la[t] > 0`, `la[t] < 0`, and `la[t] == 0`. The implementation also used nested `if`/`else if`, which likely made the frontend's path/pure-clause search much heavier than the nearby two-branch `array_copy_positive` example.
- Location: invariant before the `for` loop in `annotated/verify_20260420_174025_array_sign.c`.
- Fix action: stop the no-progress `symexec` process and simplify the implementation-visible branch structure/annotation shape before rerunning in the same workspace.
- Result after fix: pending next annotation attempt and rerun.

## Branch assertion left an unsolved local `n` store

- Phenomenon: after adding branch-local bridges, `symexec` entered `array_sign` and failed at `annotated/verify_20260420_174025_array_sign.c:71:12` with `Partial Solve Failed for Partial Implies`; the remaining separation item was `store(n_90_addr, Zlength(Z, la_92_free), signed int)`.
- Trigger: the branch-local assertions mentioned the C variable equality `n == n@pre`. In this assertion context the frontend translated that mention in a way that required carrying the local `n` stack cell through the partial implication, but the assertion shape did not include it as a resource.
- Location: in-body bridge assertions inside the loop, especially the first post-assignment assertion after `out[i] = 1`.
- Fix action: remove `n == n@pre` from the in-body bridge assertions and keep all bounds/length facts in terms of `n@pre`. The loop invariant still records `n == n@pre` at the loop boundary.
- Result after fix: pending rerun of `symexec`.

## Removing `n == n@pre` from in-body assertions caused search blow-up

- Phenomenon: after removing `n == n@pre` from the in-body bridge assertions, the next `symexec` attempt produced no output for about two minutes and generated only zero-byte Coq files.
- Trigger: the changed branch assertions avoided the previous explicit local-`n` failure but gave the frontend a less constrained partial implication, returning to a search blow-up.
- Location: in-body bridge assertions in `annotated/verify_20260420_174025_array_sign.c`.
- Fix action: stop the stalled run. The next attempt will avoid the nested `else if` source shape in the annotated working copy and use a verification-stable equivalent with a temporary value and simpler branch tests.
- Result after fix: pending source-shape normalization and rerun.

## Single-write normalized loop dropped scalar `s` before output write

- Phenomenon: after normalizing the loop to compute scalar `s` and then write `out[i] = s`, `symexec` failed at `annotated/verify_20260420_174025_array_sign.c:80:8` with `cannot write null value to memory, maybe you try to read from an uninitialized program variable`.
- Trigger: the `which implies` bridge immediately before `out[i] = s` exposed the focused output cell but did not preserve the pure relation involving `s`. The current assertion shown in the error retained `v == la[i]` and branch facts (`la[i] >= 0`, `la[i] <= 0`) but no fact/store for `s`, so the RHS expression value was unavailable.
- Location: bridge assertion before the single `out[i] = s` write.
- Fix action: include the scalar sign relation for `s` in the target side of that bridge so it remains available at the write point.
- Result after fix: pending rerun of `symexec`.

## Post-write rebuild pulled live `a` local into partial implication

- Phenomenon: after preserving the scalar `s` relation, `symexec` reached the post-write bridge and failed at `annotated/verify_20260420_174025_array_sign.c:84:8` with an unsolved separation remainder containing `store(a_87_addr, a_86_pre, signed int*)` and `IntArray.full(a_86_pre, Zlength(Z, la_92_free), la_92_free)`.
- Trigger: the in-body post-write bridge target used `IntArray::full(a, n@pre, la)`. In this local assertion context, mentioning the live C variable `a` forces the local pointer stack cell to be part of the partial implication.
- Location: post-write `which implies` after `out[i] = s`, and the surrounding in-body bridge assertions.
- Fix action: use preserved pre-state pointers (`a@pre`, `out@pre`) in the in-body heap assertions and keep the live-parameter equalities only in the loop invariant. This avoids asking branch-local partial implications to reconstruct stack-cell resources for unchanged pointer parameters.
- Result after fix: pending rerun of `symexec`.

## Symexec segfault after pre-state pointer heap bridge

- Phenomenon: after changing in-body heap assertions to use `a@pre` and `out@pre`, `symexec` printed many `too many clause` messages and then exited with status 139; `timeout` reported that the monitored command dumped core.
- Trigger: the heap-resource issue was avoided, but the pure sign relation still used three implications at several program points. This appears to trigger a clause explosion severe enough to crash the frontend.
- Location: loop invariant and in-body assertions that repeat `(la[t] > 0 => ...)`, `(la[t] < 0 => ...)`, and `(la[t] == 0 => ...)`.
- Fix action: replace the repeated implication bundle in invariant/assertions with a single disjunctive sign relation over each processed element, leaving the original function postcondition unchanged. The manual proof stage can later derive the postcondition implications from that disjunction if VC generation succeeds.
- Result after fix: pending annotation simplification and rerun.

## Final blocker: no successful VC generation before time budget

- Phenomenon: no `array_sign_goal.v`, `array_sign_proof_auto.v`, `array_sign_proof_manual.v`, or `array_sign_goal_check.v` was successfully generated. Failed attempts either timed out, hit partial implication failures, segfaulted in `symexec`, or rejected the disjunctive simplification with `Multiple cases inside pre- or post-condition`.
- Trigger: the target postcondition and natural loop invariant require a three-way sign relation. Encoding it as chained implications caused `symexec` clause blow-ups; encoding it as disjunction is not accepted in assertion pre/post contexts.
- Location: `annotated/verify_20260420_174025_array_sign.c`, loop invariant and bridge assertions for the sign relation.
- Fix action taken: preserved all reasoning and failed attempts in `annotation_reasoning.md` and this `issues.md`; removed zero-byte generated `.v` files so a future retry starts from a clean generated directory.
- Result: verification did not succeed in this run. A future retry should likely move the sign relation into a small Coq helper/spec function during Contract or use a frontend-supported predicate form instead of inline implications/disjunctions.

## Retry repair: helper extern caused startup segfault, split implications generated VCs

- Phenomenon: in the retry, replacing the inline sign relation with verification-local Coq helpers (`sign_value` and initially `sign_list`) made `symexec` segfault immediately, before its usual `Start to symbolic execution on program` output.
- Trigger: the annotated file introduced new `Extern Coq` / `Import Coq` helper declarations in a workspace whose formal input had no paired `.v`. Even after narrowing to scalar-only `sign_value`, the frontend still crashed before VC generation.
- Location: the helper declarations and helper-based invariant in `annotated/verify_20260420_174025_array_sign.c`; the failed runs are captured by `logs/qcp_run.log` timestamps around `2026-04-20 18:13:11 CST`, `18:13:53 CST`, `18:14:59 CST`, and `18:15:15 CST`.
- Fix action: removed the helper declarations and rewrote the processed-prefix relation as three separate native quantified implications:
  - `(0 <= t && t < i && la[t] > 0) => l1[t] == 1`
  - `(0 <= t && t < i && la[t] < 0) => l1[t] == -1`
  - `(0 <= t && t < i && la[t] == 0) => l1[t] == 0`
- Result after fix: `symexec` completed successfully at `2026-04-20 18:16:27 CST` and generated fresh `array_sign_goal.v`, `array_sign_proof_auto.v`, `array_sign_proof_manual.v`, and `array_sign_goal_check.v`.

## Manual proof had stale bullets after `entailer!`

- Phenomenon: the first manual proof replacement for `proof_of_array_sign_entail_wit_1` failed with `Wrong bullet -: No more goals` at `array_sign_proof_manual.v:28`.
- Trigger: after choosing witnesses `l2 = lo` and `l1 = nil`, `simpl; entailer!` solved the initialization entailment completely, leaving no subgoals for the explicit bullet script.
- Location: `output/verify_20260420_174025_array_sign/coq/generated/array_sign_proof_manual.v`, theorem `proof_of_array_sign_entail_wit_1`.
- Fix action: removed the unnecessary bullet subproofs and kept the minimal script `unfold ...; intros; Exists lo nil; simpl; entailer!.`
- Result after fix: `array_sign_proof_manual.v` compiled successfully, and `array_sign_goal_check.v` compiled successfully afterward.

## Final retry result: verification succeeded

- Phenomenon: after the split-implication annotation and minimal manual proof, all required verification artifacts were present and compiled.
- Trigger: the frontend-friendly invariant avoided both disjunction and helper extern crashes while preserving the original contract semantics.
- Location: active annotated file `annotated/verify_20260420_174025_array_sign.c`; generated Coq files under `output/verify_20260420_174025_array_sign/coq/generated/`.
- Fix action: compiled `array_sign_goal.v`, `array_sign_proof_auto.v`, `array_sign_proof_manual.v`, and `array_sign_goal_check.v` with the documented `COMPILE.md` template; removed all non-`.v` Coq intermediates.
- Result: `goal_check.v` compiled successfully, `proof_manual.v` contains no `Admitted.` and no added `Axiom`, and `coq/` now contains only `.v` files.
