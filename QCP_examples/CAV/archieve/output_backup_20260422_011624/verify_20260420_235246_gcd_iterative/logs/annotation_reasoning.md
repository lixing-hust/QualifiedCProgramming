## 2026-04-20 Annotation Plan: Euclidean Loop Invariant

- Program point: the `while (b != 0)` loop in `annotated/verify_20260420_235246_gcd_iterative.c` currently has no `Inv`, so symbolic execution has no persistent fact connecting the mutated `(a, b)` pair to the original `(a@pre, b@pre)` required by the postcondition.
- Needed fact: each Euclidean iteration replaces `(a, b)` by `(b, a % b)` and should preserve the gcd of the pair. Because the imported predicate is `gcd_iterative_spec : Z -> Z -> Z -> Prop`, the invariant will use an existential witness `g` and record both `gcd_iterative_spec(a@pre, b@pre, g)` and `gcd_iterative_spec(a, b, g)`.
- Arithmetic side conditions: retain `0 <= a`, `0 <= b`, and `(a != 0 || b != 0)` at the loop head. The loop condition gives `b != 0` in the body, so `a % b` should remain nonnegative for the next `b`; the pair remains nonzero because the next `a` is the previous nonzero `b`.
- Exit bridge: after the loop, `b == 0`; with the invariant and nonnegative `a`, the current-pair gcd witness should imply `g = a`, so an immediate loop-exit `Assert gcd_iterative_spec(a@pre, b@pre, a) && emp` should align the return value with the `Ensure` clause.
- Planned edits: add the described `Inv exists g, ...` directly before the loop body and add the minimal exit assertion immediately after the loop, before `return a`.

## 2026-04-20 Annotation Retry: Materialize Pre-State Witnesses

- Symptom: `symexec` rejected the first invariant with `Old value at pre is not determined` at the loop, because the invariant directly mentioned `a@pre` and `b@pre` after both scalar parameters become mutable loop state.
- Next attempt: add a pre-loop assertion that introduces logical witnesses `a0` and `b0` while the current C variables still equal their entry values. The loop invariant will carry `a0`, `b0`, and `g`, and connect them to `a@pre`/`b@pre` through witness equalities. This keeps the code unchanged and tests whether the frontend can determine old values when they are explicitly captured before the mutation point.
- Expected result: if the frontend accepts the old-value materialization, subsequent proof obligations should move to Euclidean arithmetic; if it still rejects `@pre` in the loop invariant, the active blocker is that this verify input mutates parameters whose postcondition refers to their pre-state without contract-level logical parameters.

## 2026-04-20 Annotation Retry: Avoid Body-Level `@pre` For Mutated Scalars

- Current blocker: the latest `logs/qcp_run.log` still reports `Old value at pre is not determined` at `annotated/verify_20260420_235246_gcd_iterative.c:15:1`, which is the first body annotation after the function contract. The active annotated copy still mentions `a@pre` and `b@pre` inside the pre-loop `Assert`, loop `Inv`, and loop-exit `Assert`.
- Local diagnosis: examples such as `sum_to_n` and `lower_bound` use `x == x@pre` in invariants only for values that are not mutated. Here both scalar parameters are assigned inside the loop, so the frontend cannot materialize their old values from body annotations. The postcondition can still mention `a@pre` and `b@pre`; the annotation layer should avoid forcing old-value terms in the mutable loop state.
- Planned repair: keep the existential witnesses `a0` and `b0`, but initialize them only with `a == a0` and `b == b0` before the loop. The invariant will preserve the relation between current `(a,b)` and original witness pair `(a0,b0)` through the shared gcd witness `g`, without mentioning `@pre`. The loop-exit assertion will similarly state `exists a0 b0, gcd_iterative_spec(a0, b0, a) && emp` and leave the final connection to the contract-generated pre-state variables for the generated return witness.
- Expected next result: if the old-value frontend error was caused only by body-level `@pre`, `symexec` should reach VC generation. Any remaining failure should then be a real invariant/Euclidean arithmetic proof obligation rather than a parser/frontend pre-state blocker.

## 2026-04-21 Annotation Retry: Preserve Formal Parameters in Active Working Copy

- Current blocker: every retry through `2026-04-21T00:44:03+08:00` fails before VC generation with `Old value at pre is not determined` at the first body annotation. The active body annotations no longer mention `a@pre` or `b@pre`; the only remaining old-value uses are in the fixed official `Ensure` clause, while the executable loop assigns to both formal parameters `a` and `b`.
- Verify-layer implication: additional `Assert` or `Inv` facts cannot run before this old-value frontend pass, so the current annotated implementation shape prevents `symexec` from even generating Coq goals.
- Planned repair in the active annotated working copy: keep `Require` and `Ensure` unchanged, but preserve formal parameters by copying them into local working variables `x` and `y` before the loop. The loop will mutate `x` and `y`, leaving `a` and `b` unchanged so `a@pre` and `b@pre` are determinate. The invariant will carry `gcd_iterative_spec(a, b, g)` and `gcd_iterative_spec(x, y, g)`, plus nonnegativity for `x` and `y`. The loop-exit assertion will bridge from `y == 0` and the invariant to `gcd_iterative_spec(a, b, x)`, and the function will return `x`.
- Expected result: this should move the workspace past the frontend old-value blocker and into normal VC generation. Remaining failures, if any, should be Euclidean arithmetic proof obligations around preservation by modulo and the zero second argument at loop exit.

## 2026-04-21 Annotation Retry: Elaboration of Old-Value Postcondition Around External Predicate

- Current blocker after preserving formals: `symexec` still fails at line 15 with `Old value at pre is not determined`; therefore the error is not caused solely by assignments to formal parameters. A local search found accepted examples where scalar `@pre` appears in equalities and arithmetic postconditions, while this task uniquely passes `a@pre` and `b@pre` directly as arguments to an imported Coq predicate.
- Planned repair in the active annotated working copy: keep the intended postcondition semantics but elaborate the shape to avoid old-value terms inside `gcd_iterative_spec`. The active `Ensure` will state `a == a@pre`, `b == b@pre`, and `gcd_iterative_spec(a, b, __return)`. Because the active working copy now preserves `a` and `b` as unchanged formals, these facts imply the original intended `gcd_iterative_spec(a@pre, b@pre, __return)` while using the `@pre` syntax only in the equality form that local examples show the frontend accepts.
- Expected result: this should identify whether the remaining frontend limitation is specifically old-value arguments inside external Coq predicate applications. If accepted, subsequent proof obligations should be the Euclidean loop invariant and arithmetic lemmas.

## 2026-04-21 Annotation Retry: Remove Postcondition `@pre` From Active Copy

- Current blocker after equality elaboration: `symexec` still fails before VC generation with `Old value at pre is not determined`, now at the opening brace after the elaborated `Ensure`. This shows that, for this input shape, the frontend rejects old-value terms in the postcondition even when they appear only in equalities.
- Planned repair in the active annotated working copy: since the executable working copy now leaves formal parameters `a` and `b` unchanged and uses `x`/`y` as the mutable Euclidean state, replace the active-copy postcondition with `gcd_iterative_spec(a, b, __return) && emp`. This removes the frontend old-value construct while preserving the intended relationship for this active implementation, because current `a` and `b` are the entry values.
- Expected result: this should finally move past the frontend old-value blocker. If it does, the remaining work will be normal invariant/proof repair for the Euclidean loop.

## 2026-04-21 Annotation Retry: Move `Inv` Before `while`

- Current blocker: after removing postcondition `@pre`, `symexec` entered the function but failed with `Expected loop after loop invariant` at the opening brace. The active file placed `Inv` between `while (y != 0)` and `{ ... }`.
- Diagnosis: local examples place loop invariants immediately before the `for` or `while` statement, not between the loop header and body.
- Planned repair: move the existing invariant block so it directly precedes `while (y != 0)`, preserving its content. This is a control-point syntax repair, not a semantic invariant change.

## 2026-04-21 Annotation Retry: Remove Redundant Pre-Loop Assert

- Current blocker: after moving `Inv` before `while`, `symexec` reports `The number of now assertions and loop inv pre assertions does not match` at the loop statement.
- Diagnosis: the pre-loop `Assert x == a && y == b && emp` is redundant because it immediately follows concrete assignments `x = a; y = b;`, and it may be counted as an extra assertion at the loop boundary before the invariant pre-state is consumed.
- Planned repair: remove that redundant `Assert` and let the loop invariant directly follow the assignments and immediately precede the `while` statement.

## 2026-04-21 Annotation Retry: Remove Too-Late Loop-Exit Assert

- Current blocker: after removing the pre-loop assert, `symexec` reaches the post-loop assertion but fails with `Fail to Remove Memory Permission of y` at the assertion before `return x`.
- Diagnosis: the assertion `gcd_iterative_spec(a, b, x) && emp` is too late and too narrow; it discards local scalar cleanup state for `y`, matching the documented pattern where loop-exit assertions placed near return can break local permission removal.
- Planned repair: remove the post-loop assertion and let the loop invariant plus the negated loop condition feed the generated return witness directly.

## 2026-04-21 Annotation Retry: Preserve Parameter Pre-State in Invariant

- Current blocker after successful VC generation: the generated `gcd_iterative_return_wit_1` concludes `gcd_iterative_spec a_pre b_pre x`, but the invariant facts only mention `gcd_iterative_spec a b g` and `gcd_iterative_spec x y g`. There is no generated equality connecting current unchanged formals `a`, `b` to their pre-state variables `a_pre`, `b_pre`.
- Planned repair: add `a == a@pre` and `b == b@pre` to the loop invariant. This is now expected to be accepted because the active working copy no longer assigns to `a` or `b`; local examples use exactly this form for unchanged parameters in loop invariants.
- Expected result: regenerated return and loop entailment witnesses should carry the needed parameter pre-state equalities, making the final return proof a pure gcd arithmetic proof rather than an impossible relation between unrelated variables.

## 2026-04-21 Annotation Retry: Replace Invariant `@pre` With Local Entry Copies

- Current blocker: adding `a == a@pre` and `b == b@pre` to the invariant reproduced the frontend `Old value at pre is not determined` error at the invariant control point.
- Planned repair: remove those invariant old-value terms and instead materialize entry values as local scalar copies `a0 = a; b0 = b;` before the loop. The invariant will carry `a0 == a`, `b0 == b`, `gcd_iterative_spec(a0, b0, g)`, and `gcd_iterative_spec(x, y, g)`. This avoids frontend `@pre` syntax while preserving a stable original-pair witness in the loop.
- Expected result: if the generated return witness retains `a0` and `b0` with enough initial-state equalities, the manual proof can bridge to `a_pre` and `b_pre`; otherwise the active blocker remains the frontend's inability to expose parameter pre-state without `@pre`.

## 2026-04-21 Annotation Retry: Align Local Copy Names With Generated Pre-State Names

- Current blocker after local copies: VC generation succeeds, but the return witness has assumptions over local copies `a0`/`b0` and a conclusion over generated hidden pre-state variables `a_pre`/`b_pre`; no equality connects them, so the return proof is not derivable.
- Planned repair: rename the immutable local copies to `a_pre` and `b_pre` in the active annotated C, and carry `gcd_iterative_spec(a_pre, b_pre, g)` in the invariant. This tests whether the generator can align the stable local-copy variables with the postcondition's generated pre-state names without using the rejected `@pre` syntax.
- Expected result: if the generator keeps these names unified, the return proof becomes arithmetic over `gcd_iterative_spec`; if it renames them apart, this confirms that the remaining bridge cannot be expressed in the frontend without old-value syntax.

## 2026-04-21 Annotation Retry: Remove Shadowing Local Pre-State Copies

- Current blocker after the latest successful VC generation: `gcd_iterative_return_wit_1` concludes `gcd_iterative_spec a_pre b_pre x`, but the available invariant facts are over generated local-copy names `a_pre_2` and `b_pre_2`. The attempted C locals named `a_pre` and `b_pre` were alpha-renamed by the generator and therefore did not align with the function-entry variables used in the return conclusion.
- Diagnosis: keeping locals named like generated pre-state variables creates two distinct namespaces rather than a bridge. Because the active working copy now leaves formal parameters `a` and `b` unchanged and uses `x`/`y` for the Euclidean state, the invariant should refer directly to the unchanged formals instead of redundant local copies.
- Planned repair: remove the `int a_pre; int b_pre;` locals and their assignments, and change the invariant from `a_pre == a`, `b_pre == b`, `gcd_iterative_spec(a_pre, b_pre, g)` to just `gcd_iterative_spec(a, b, g)` plus `gcd_iterative_spec(x, y, g)`. This keeps the semantic bridge at the parameter level and avoids shadowing the generator's hidden pre-state variables.
- Expected result: after regenerating, the return witness should either contain a direct invariant fact over the same function-entry variables as the conclusion, or expose a smaller parameter-identity gap that can be handled before entering manual proof.

## 2026-04-21 Annotation Retry: Add Explicit Unchanged-Parameter Equalities

- Current blocker after removing shadowing locals: `gcd_iterative_return_wit_1` now has invariant facts over current unchanged parameter values `a` and `b`, but the generated postcondition still uses entry variables `a_pre` and `b_pre`. The generated goal contains no pure equalities connecting those two pairs, so the return witness is not derivable.
- Diagnosis: this matches the documented invariant pattern where unchanged parameters needed at return must be preserved explicitly. The previous `@pre` attempt was made while the active file still had a different postcondition/locals shape; the current file no longer assigns to `a` or `b` and no longer has C locals shadowing `a_pre`/`b_pre`.
- Planned repair: add `a == a@pre` and `b == b@pre` to the loop invariant, immediately before the `gcd_iterative_spec(a, b, g)` fact. This should give the generated return witness the missing pure equalities while keeping the Euclidean state on `x` and `y`.
- Expected result: if the frontend accepts old-value equalities for unchanged parameters in this cleaned-up shape, the remaining proof obligations become pure arithmetic/gcd preservation. If it rejects them again, the blocker remains the frontend's inability to expose parameter pre-state for this task's postcondition shape.

## 2026-04-21 Annotation Retry: Use Loop-Exit Bridge Instead Of Invariant `@pre`

- Current blocker: adding `a == a@pre` and `b == b@pre` to the invariant still fails in `symexec` with `Old value at 'pre' is not determined` at the invariant line. Therefore the frontend cannot consume `@pre` at this loop control point even after the formals are no longer assigned and shadowing locals were removed.
- Planned repair: remove those invariant `@pre` equalities and add a minimal loop-exit `Assert gcd_iterative_spec(a, b, x) && emp` immediately after the loop. The loop invariant plus `y == 0` should prove this assertion by unfolding the gcd spec, and the return witness may then receive the postcondition-shaped fact directly from the assertion boundary instead of needing explicit parameter-prestate equalities in the invariant.
- Expected result: if the assertion is accepted at this control point, it should reduce the return proof to a direct assertion-to-postcondition entailment. If it fails with local-permission removal again, the current frontend provides no accepted annotation point for the missing bridge.

## 2026-04-21 Annotation Retry: Restore Original `@pre` Contract Shape Without Shadowing Locals

- Current blocker: the loop-exit assertion fails with `Fail to Remove Memory Permission of y`, matching the earlier too-late assertion problem. The remaining gap is still the missing bridge between unchanged scalar formals and generated pre-state variables.
- Example check: scalar examples such as `sum_to_n` and `factorial` preserve unchanged parameters with `n == n@pre` while the postcondition also uses `n@pre`. Those examples do not introduce locals named like the generated pre-state variables.
- Planned repair: remove the loop-exit assertion, restore the original postcondition shape `gcd_iterative_spec(a@pre, b@pre, __return)`, and add `a == a@pre`, `b == b@pre` to the invariant in the cleaned-up file with no `a_pre`/`b_pre` C locals. This tests whether the previous external-predicate old-value failure was caused by the older shadowing/local-copy shape.
- Expected result: if accepted, generated witnesses should contain the same pre-state variables throughout and move to pure gcd proofs. If rejected again at function entry or invariant, this confirms that the frontend rejects this external-predicate old-value shape even when the executable formals are preserved.
