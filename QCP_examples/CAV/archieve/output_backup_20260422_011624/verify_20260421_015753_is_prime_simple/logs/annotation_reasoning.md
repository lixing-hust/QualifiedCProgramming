## 2026-04-21 annotation plan

The unannotated `for (d = 2; d < n; ++d)` loop cannot preserve the postcondition needed for the final `return 1`: when the loop exits normally, the verifier must know that every integer candidate in the scanned range has been checked and did not divide `n`. The contract for the successful return requires `forall d, 2 <= d && d < n@pre => n@pre % d != 0`, so the loop invariant must carry this checked-prefix property.

At the loop head, `d` is the next candidate divisor to test. The processed range is `[2, d)`. A suitable invariant is `2 <= d && d <= n && n == n@pre && forall i, 2 <= i && i < d => n % i != 0 && emp`. It is initialized by `d = 2`, where the processed range is empty. It is preserved because the loop body returns immediately if `n % d == 0`; the only path that reaches `++d` has `n % d != 0`, extending the checked range to `[2, d + 1)`. On normal loop exit, `!(d < n)` plus `d <= n` gives `d == n`, and the checked-prefix fact becomes the full postcondition range `[2, n)`.

The early return inside the loop should satisfy the failure branch of the postcondition using witness `d`, because the branch condition gives `n % d == 0` and the loop condition gives `d < n`. A minimal assertion in that branch may be needed if `symexec` does not carry the modulo equality into the return witness automatically.

## 2026-04-21 invariant placement repair

The first real `symexec` run using equals-form command-line flags failed before VC generation with `Expected loop after loop invariant` at the opening brace after `for (d = 2; d < n; ++d)`. This shows the invariant was placed after the `for` header, while this frontend expects `/*@ Inv ... */` immediately before the loop statement. The invariant formula itself still describes the loop-head state, so the repair is to move the invariant block above the `for` line without changing its content.

## 2026-04-21 loop-exit assertion removal

After moving the invariant above the loop, `symexec` reached the final `return 1` but failed with `Fail to Remove Memory Permission of d:66` at the return line. The post-loop `Assert` was placed after the loop and before the local variable cleanup, matching the documented failure mode where a late exit assertion disrupts removal of local permissions. The invariant already carries `d <= n`, the loop exit contributes `!(d < n)`, and together they should be enough for the generated return witness to prove the needed `d == n` arithmetic fact in Coq. The repair is to delete the post-loop assertion and rerun `symexec` from clean generated files.
