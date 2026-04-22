## Annotation reasoning - initial invariant plan

Context: target function `array_move_zeroes_to_end` mutates `a` in place. The input contract supplies `0 <= n`, `Zlength(l) == n`, and `IntArray::full(a, n, l)`. The postcondition requires `IntArray::full(a, n, move_zeroes_to_end_spec(l))`, where `move_zeroes_to_end_spec(l) = app (move_zeroes_nonzeroes l) (move_zeroes_zeroes l)` from the input Coq file.

Current unannotated loop snippet:
```c
int write = 0;
int i = 0;
while (i < n) {
    if (a[i] != 0) {
        a[write] = a[i];
        write++;
    }
    i++;
}
while (write < n) {
    a[write] = 0;
    write++;
}
```

First loop control point reasoning: `i` is the number of original positions already scanned, and `write` is the number of nonzero elements found in `sublist(0, i, l)`. Because the assignment target `write` is always `<= i`, the unread suffix `[i,n)` still has original values from `l`, which is necessary to justify the next read `a[i]`. The modified prefix `[0,write)` must equal `move_zeroes_nonzeroes(sublist(0, i, l))`; the middle `[write,i)` can be arbitrary because it will be overwritten or zero-filled later. Therefore the invariant should quantify a logical current list `lc` of length `n@pre`, preserve `a == a@pre` and `n == n@pre`, state `0 <= write <= i <= n@pre`, state `write == Zlength(move_zeroes_nonzeroes(sublist(0, i, l)))`, state the prefix equality for all `k < write`, state the unread suffix equality for all `i <= k < n@pre`, and keep `IntArray::full(a, n@pre, lc)`.

Second loop control point reasoning: after the first loop exits, `i == n@pre`, so the prefix `[0, Zlength(move_zeroes_nonzeroes(l)))` contains exactly the original nonzero elements. The remaining loop turns positions from that boundary up to `write` into zeroes. Since the program reuses the C variable `write`, the invariant records that `Zlength(move_zeroes_nonzeroes(l)) <= write <= n@pre`; positions before that boundary still equal `move_zeroes_nonzeroes(l)`, and positions from the boundary to `write` are zero. The remaining suffix can stay arbitrary. On exit `write == n@pre`, so these facts describe the full final array as nonzero prefix plus a zero suffix; any remaining equality to `move_zeroes_to_end_spec(l)` is expected to become a list/arithmetic proof obligation rather than an annotation-shape problem.

Planned annotated fragments:
```c
/*@ Inv exists lc,
      0 <= i && i <= n@pre &&
      0 <= write && write <= i &&
      a == a@pre &&
      n == n@pre &&
      n@pre == Zlength(l) &&
      Zlength(lc) == n@pre &&
      write == Zlength(move_zeroes_nonzeroes(sublist(0, i, l))) &&
      (forall (k: Z), (0 <= k && k < write) =>
        lc[k] == move_zeroes_nonzeroes(sublist(0, i, l))[k]) &&
      (forall (k: Z), (i <= k && k < n@pre) => lc[k] == l[k]) &&
      IntArray::full(a, n@pre, lc)
*/
while (i < n) { ... }

/*@ Inv exists lc,
      Zlength(move_zeroes_nonzeroes(l)) <= write && write <= n@pre &&
      a == a@pre &&
      n == n@pre &&
      n@pre == Zlength(l) &&
      Zlength(lc) == n@pre &&
      (forall (k: Z), (0 <= k && k < Zlength(move_zeroes_nonzeroes(l))) =>
        lc[k] == move_zeroes_nonzeroes(l)[k]) &&
      (forall (k: Z), (Zlength(move_zeroes_nonzeroes(l)) <= k && k < write) =>
        lc[k] == 0) &&
      IntArray::full(a, n@pre, lc)
*/
while (write < n) { ... }
```

Why this should satisfy the three invariant checks: initialization of the first loop has `i = write = 0`, empty prefix facts, and `lc = l`. Preservation follows by case split on `a[i] != 0`: nonzero appends `l[i]` to the compacted prefix and increments `write`, while zero only advances `i`; in both cases the unread suffix starts at `i + 1`. The first-loop exit gives `i == n@pre` and the compacted prefix for all original nonzeroes. The second-loop invariant initializes from that exit state with an empty zero-filled suffix. Its body writes one zero at index `write`, then advances `write`, preserving the zero-filled range. On second-loop exit, `write == n@pre`, so the logical array is completely described by the nonzero prefix followed by zeroes.

## Annotation reasoning - expose existing Coq helper symbols

Symexec result after the first invariant edit:
```text
fatal error: Use of undeclared identifier `move_zeroes_nonzeroes` in annotated/verify_20260422_000928_array_move_zeroes_to_end.c:37:4
```

This is not an invariant validity failure. The invariant intentionally refers to the helper `move_zeroes_nonzeroes` from `input/array_move_zeroes_to_end.v`, but the active C file only had:
```c
/*@ Extern Coq (move_zeroes_to_end_spec: list Z -> list Z) */
/*@ Import Coq Require Import array_move_zeroes_to_end */
```

The input `.v` already defines both `move_zeroes_nonzeroes` and `move_zeroes_zeroes`; exposing them as `Extern Coq` symbols in the annotated copy does not redesign the contract, but lets the front-end parse loop invariants that state the compacted-prefix and zero-suffix facts. I will add:
```c
/*@ Extern Coq (move_zeroes_nonzeroes: list Z -> list Z) */
/*@ Extern Coq (move_zeroes_zeroes: list Z -> list Z) */
```
next to the existing extern declaration, then clear generated files and rerun symexec.

## Annotation reasoning - bridge second-loop array write

Symexec result after exposing helper symbols:
```text
fatal error: Assign Exec fail in annotated/verify_20260422_000928_array_move_zeroes_to_end.c:61:8
```

The failure is at:
```c
while (write < n) {
    a[write] = 0;
    write++;
}
```

At this program point the second-loop invariant owns `IntArray::full(a, n@pre, lc)`, and the loop guard gives `write < n`, with `n == n@pre`. The assignment executor needs the array cell at `write` exposed explicitly. The fix is a bridge immediately before the assignment:
```c
IntArray::missing_i(a, write, 0, n@pre, lc) *
data_at(a + (write * sizeof(int)), int, lc[write])
```

After the assignment, the cell value is `0`. The post-assignment bridge re-closes the full array by existentially choosing a new logical list `lc1` that has the same nonzero prefix facts and has zeroes on `[Zlength(move_zeroes_nonzeroes(l)), write + 1)`. This is exactly the invariant needed after the subsequent `write++`.

## Annotation reasoning - narrow second-loop post-write bridge

The post-write bridge failed with:
```text
Finish Printing Partial Solve Which Implies Error in annotated/verify_20260422_000928_array_move_zeroes_to_end.c:79:8
Partial Solve Failed for Partial Implies
Sep cannot be fully solved
The Sep is:
SEP[store(n_90_addr , Zlength(Z, l_91_free) , signed int)]
```

The failing bridge after `a[write] = 0` included `a == a@pre` and `n == n@pre` even though the bridge only needs to re-close the array heap. This made the solver try to materialize local storage for `n` inside the RHS of a local heap reclosure. The next edit removes these local-parameter equalities from the two immediate `which implies` bridge assertions around the zero-fill assignment. The surrounding second-loop invariant still preserves `a == a@pre` and `n == n@pre`; the bridge itself will only expose and re-close `IntArray` ownership plus the pure list facts needed for the zero-filled range.

