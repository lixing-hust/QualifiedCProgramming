
## 2026-04-20 initial invariant design

Program point: the single `for (i = 0; i < n; ++i)` loop in `annotated/verify_20260420_174025_array_sign.c` currently has no `Inv`, so `symexec` would lack a stable loop state and cannot derive the postcondition for the written output array.

Observed contract need: the postcondition needs an existential result list `lr` with `Zlength(lr) == n` and, for every index in bounds, `lr[i]` equal to `1`, `-1`, or `0` according to the sign of the preserved input list `la[i]`. The input array `a` must remain `la`; only `out` is updated.

Planned annotation: add an invariant before the loop with existential lists `l1` and `l2`. `l1` is the already written prefix of length `i` and satisfies the sign relation against `la` for all `0 <= t < i`. `l2` is the not-yet-written suffix of length `n@pre - i` and still equals the original output suffix `lo[i + t]`. The heap shape is `IntArray::full(a, n@pre, la) * IntArray::full(out, n@pre, app(l1, l2))`, plus parameter preservation facts `a == a@pre`, `out == out@pre`, `n == n@pre`, and length facts for `la`/`lo`.

Why this should fix the loop: initialization uses `l1 = nil` and `l2 = lo`; preservation advances one element from `l2` into `l1` after one of the three assignments; loop exit with `i == n` leaves `l2` empty and `app(l1, l2)` as the final result list satisfying the full postcondition. This mirrors the verified prefix/suffix invariant shape used by `array_copy_positive`, but with three case implications instead of two.

## 2026-04-20 branch-local bridge assertions after symexec timeout

Program point: the invariant-only annotated copy parses, but the bounded `symexec` run was killed by `timeout` after 241 seconds with exit code 124 and zero-byte generated Coq files. The log showed no progress beyond the start marker, which is consistent with the frontend spending too long searching across the nested three-way branch and array ownership reconstruction.

Current blocker: the loop invariant describes the right prefix/suffix state globally, but before `if (a[i] > 0)` the tool must infer both the focused cell `a[i]` for branch tests and the focused cell `out[i]` for writes from two full arrays. After each assignment it must rebuild `IntArray::full(out, n@pre, app(l1', sublist(i + 1, n@pre, lo)))` and show the extended prefix relation. Doing that implicitly in all three branches is too expensive.

Planned annotation change: add a `which implies` bridge at the top of the loop body that exposes `IntArray::missing_i` plus `data_at` for `a[i]` and `out[i]`. Then, after each branch assignment, add a branch-local `which implies` that rebuilds the full arrays and existentially introduces the new processed prefix `l1'` with the sign relation for indices `< i + 1`. This keeps the same invariant and postcondition but makes the ownership and prefix-extension steps explicit at the exact control points where they are needed.

Expected effect: `symexec` should no longer need to search for the same array split/rebuild and list witness shape across the positive, negative, and zero paths. If this still times out, the remaining issue is likely the nested `else if` control-flow shape rather than missing heap bridge facts.

## 2026-04-20 source-shape normalization in annotated copy

Program point: the nested `if / else if / else` performs the output array write inside each branch. With the sign relation in the invariant, this forced the frontend either to rebuild `IntArray::full(out, ...)` in three separate branch-local assertions or to search for those rebuilds implicitly. Both approaches either timed out or hit brittle partial implications.

Planned annotated-copy normalization: introduce scalar locals `v` and `s` inside the annotated working copy, set `v = a[i]`, compute `s` by the same three-way sign branch, and then perform a single `out[i] = s` after the branch. This is semantically equivalent for the target contract: for each iteration the final stored value is still 1 if `a[i] > 0`, -1 if `a[i] < 0`, and 0 otherwise; `a` remains unchanged and only `out[i]` is updated. The formal input contract in `input/array_sign.c` is not modified.

Annotation plan after normalization: keep the loop invariant over `app(l1, l2)`. At the top of the loop expose only the focused input cell for `v = a[i]`. After computing `s`, assert the pure sign relation between `s` and `la[i]` while keeping both full arrays. Before the single output write, expose the focused `out[i]` cell. After the write, use one prefix-extension bridge to rebuild the invariant for the next iteration.

Why this should reduce search: array ownership is split/rebuilt once per iteration instead of once per branch, and the branch reasoning is pure scalar reasoning over `s`, not heap reconstruction.

## 2026-04-20 retry: replace inline sign cases with verification-local spec function

Current blocker from the existing workspace: the latest `logs/qcp_run.log` reports `Multiple cases inside pre- or post-condition` at `annotated/verify_20260420_174025_array_sign.c:57:8`. That line is the first in-body assertion using the disjunctive processed-element relation. The earlier `issues.md` also records that the implication encoding of the same three sign cases caused `too many clause` output and a `symexec` segfault. Therefore the blocker is not array ownership itself, but the repeated inline three-way sign relation in invariants and bridge assertions.

Planned annotation repair: keep the normalized single-write C shape with locals `v` and `s`, but add a verification-local extern `sign_value : Z -> Z`. The loop invariant will keep the original output prefix/suffix shape `IntArray::full(out, n@pre, app(l1, l2))`, but the processed-prefix semantic relation becomes the single equality `l1[t] == sign_value(la[t])` instead of three inline sign cases. After the branch, add a small assertion that `s == sign_value(la[i])`; the proof stage can justify this from the branch facts and the Coq definition, while `symexec` only needs to carry one equality.

Why this should fix the current blocker: the frontend no longer sees either `||` inside assertion pre/post conditions or three nested implications at every processed index. Prefix extension remains the familiar `app(l1, l2)` array shape, and only a scalar uninterpreted equality is carried through symbolic execution. The original function contract's `Require` and `Ensure` remain unchanged; the helper only changes the internal invariant representation.

Immediate retry note: an initial attempt with both a scalar helper and a list-valued helper (`sign_list`) made `symexec` segfault before its normal startup output. That suggests the list-valued extern/import shape itself may trigger a frontend crash in this workspace. The narrowed scalar-only plan avoids that surface.

Second immediate retry note: even the scalar-only extern form made `symexec` segfault before normal startup, so this workspace cannot currently use a verification-local Coq helper in the annotated file. The next narrowed repair removes the extern entirely and rewrites the processed-prefix relation as three separate quantified implications:

- positive inputs imply prefix element `1`
- negative inputs imply prefix element `-1`
- zero inputs imply prefix element `0`

This still avoids `||` and avoids the earlier single bundled implication consequent `((...) && (...) && (...))`, which appeared to be one source of clause explosion.
