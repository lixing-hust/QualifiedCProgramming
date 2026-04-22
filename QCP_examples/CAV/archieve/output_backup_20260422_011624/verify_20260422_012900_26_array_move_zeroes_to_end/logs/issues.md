## Issue 1 - invariant referenced helper symbols not exposed to the C annotation parser

Phenomenon: the first `symexec` run after adding loop invariants exited with status 1. `logs/qcp_run.log` reported:

```text
fatal error: Use of undeclared identifier `move_zeroes_nonzeroes` in annotated/verify_20260422_000928_array_move_zeroes_to_end.c:37:4
```

Trigger: the invariant used the helper `move_zeroes_nonzeroes` from `input/array_move_zeroes_to_end.v`, but the active C file only exposed:

```c
/*@ Extern Coq (move_zeroes_to_end_spec: list Z -> list Z) */
/*@ Import Coq Require Import array_move_zeroes_to_end */
```

Fix action: added `Extern Coq` declarations for the two helper functions already defined by the input `.v`:

```c
/*@ Extern Coq (move_zeroes_nonzeroes: list Z -> list Z) */
/*@ Extern Coq (move_zeroes_zeroes: list Z -> list Z) */
```

Result: the next `symexec` run parsed the helper names and advanced to the zero-fill loop assignment.

## Issue 2 - zero-fill assignment needed an explicit `IntArray` cell bridge

Phenomenon: after exposing helper names, `symexec` exited with:

```text
fatal error: Assign Exec fail in annotated/verify_20260422_000928_array_move_zeroes_to_end.c:61:8
```

Location: the failing source statement was:

```c
while (write < n) {
    a[write] = 0;
    write++;
}
```

Cause: at this program point the invariant owned `IntArray::full(a, n@pre, lc)`. The assignment executor needed the target cell exposed as `IntArray::missing_i(...) * data_at(...)`.

Fix action: inserted a local bridge immediately before the assignment:

```c
IntArray::missing_i(a, write, 0, n@pre, lc) *
data_at(a + (write * sizeof(int)), int, lc[write])
```

and inserted a post-assignment bridge that re-closed the array with an existential `lc1` whose prefix still matches `move_zeroes_nonzeroes(l)` and whose zero-filled range extends to `write + 1`.

Result: the assignment itself could execute symbolically, but the first post-write bridge was too strong and caused Issue 3.

## Issue 3 - post-write bridge tried to recreate local variable storage for `n`

Phenomenon: the first post-assignment bridge failed with:

```text
Finish Printing Partial Solve Which Implies Error in annotated/verify_20260422_000928_array_move_zeroes_to_end.c:79:8
Partial Solve Failed for Partial Implies
Sep cannot be fully solved
The Sep is:
SEP[store(n_90_addr , Zlength(Z, l_91_free) , signed int)]
```

Cause: the bridge after `a[write] = 0` included local parameter equalities such as `a == a@pre` and `n == n@pre`. The bridge only needed to re-close the array heap, but these local equalities made the solver try to materialize local storage for `n` on the RHS of a heap reclosure.

Fix action: narrowed the two immediate `which implies` bridges around `a[write] = 0` to heap/list facts only. The surrounding second-loop invariant still preserves `a == a@pre` and `n == n@pre`.

Result: `symexec` completed successfully and generated fresh `array_move_zeroes_to_end_goal.v`, `array_move_zeroes_to_end_proof_auto.v`, `array_move_zeroes_to_end_proof_manual.v`, and `array_move_zeroes_to_end_goal_check.v`.

## Issue 4 - manual proof needed explicit list helper lemmas for compaction semantics

Phenomenon: replacing the generated manual `Admitted.` placeholders with only:

```coq
pre_process.
Exists (replace_Znth write (Znth i lc_2 0) lc_2).
entailer!.
```

left open pure goals in `proof_of_array_move_zeroes_to_end_entail_wit_2_1`, including:

```text
forall k, 0 <= k < write + 1 ->
  Znth k (replace_Znth write (Znth i lc_2 0) lc_2) 0 =
  Znth k (move_zeroes_nonzeroes (sublist 0 (i + 1) l)) 0
write + 1 = Zlength (move_zeroes_nonzeroes (sublist 0 (i + 1) l))
Zlength (replace_Znth write (Znth i lc_2 0) lc_2) = n_pre
```

Fix action: added local helper lemmas in `coq/generated/array_move_zeroes_to_end_proof_manual.v` for `replace_Znth` length/index behavior, singleton extension of `move_zeroes_nonzeroes`, length preservation of `move_zeroes_to_end_spec`, and zero values in `move_zeroes_zeroes`.

Result: the nonzero branch, zero branch, loop transition, and return witness were proved without `Admitted.` or new axioms.

## Issue 5 - `Local Open Scope sac` made singleton list notation ambiguous

Phenomenon: compiling helper lemmas with notation like `[x]` failed with:

```text
The term "[x]" has type "Z -> Prop" while it is expected to have type "list ?A0".
```

Cause: `Local Open Scope sac` causes bracket notation to be parsed as set/assertion notation unless list notations are imported afterward.

Fix action: added:

```coq
Import ListNotations.
```

after `Local Open Scope sac.` in `array_move_zeroes_to_end_proof_manual.v`.

Result: singleton list expressions in helper lemmas parsed as lists and compiled.

## Issue 6 - array bridge proofs needed explicit range facts and stable `sep_apply` bullet order

Phenomenon: `proof_of_array_move_zeroes_to_end_which_implies_wit_1` and `_wit_2` did not close with only `pre_process; entailer!`. Direct inspection showed the required array split/merge side condition:

```coq
0 <= write < n_pre
```

Fix action: proved the range explicitly using:

```coq
pose proof (Zlength_nonneg (move_zeroes_nonzeroes l)); lia.
```

then used:

```coq
sep_apply (IntArray.full_split_to_missing_i a write n_pre lc 0).
sep_apply (IntArray.missing_i_merge_to_full).
```

with the generated bullet order handled explicitly.

Result: both bridge proofs compiled.

## Final verification result

The full compile replay passed for `original/array_move_zeroes_to_end.v`, `array_move_zeroes_to_end_goal.v`, `array_move_zeroes_to_end_proof_auto.v`, `array_move_zeroes_to_end_proof_manual.v`, and `array_move_zeroes_to_end_goal_check.v`. `array_move_zeroes_to_end_proof_manual.v` contains no `Admitted.` and no newly introduced top-level `Axiom`. Non-`.v` files under the workspace `coq/` directory were deleted after the successful compile.
