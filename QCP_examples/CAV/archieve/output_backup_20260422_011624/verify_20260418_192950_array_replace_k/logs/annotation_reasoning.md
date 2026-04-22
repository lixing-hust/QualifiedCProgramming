# Annotation Reasoning

## Iteration 1: choose a prefix-transform invariant

- The loop index `i` is the next position to inspect, so at the loop head the range `[0, i)` is already processed and `[i, n)` is still untouched.
- The postcondition only needs elementwise replacement semantics, so the invariant should keep:
  - `a == a@pre` and `n@pre == Zlength(l)` to avoid rebuilding unchanged parameters later.
  - a processed prefix `l1` of length `i` that already satisfies the replacement rule relative to the original logical list `l`.
  - an untouched suffix `l2` of length `n@pre - i` equal to `sublist(i, n@pre, l)`.
  - `IntArray::full(a, n@pre, app(l1, l2))` so the concrete array always matches the logical split.
- Initialization is direct with `l1 = nil` and `l2 = l`.
- Preservation should work by exposing element `i` with `IntArray::missing_i`, then rebuilding the array with a new prefix element:
  - if `l[i] == old_k`, store `new_k`;
  - otherwise keep `l[i]`.
- This invariant is strong enough for loop exit because `i == n@pre` collapses the untouched suffix to length `0`, leaving a full logical array `l0` that already satisfies the required pointwise replacement relation.

## Iteration 2: place the bridge assertions at the exact control points

- The read `a[i] == old_k` and possible write `a[i] = new_k` need direct access to the focused cell, so a pre-`if` bridge should expose:
  - `IntArray::missing_i(a, i, 0, n@pre, app(l1, l2))`
  - `data_at(a + (i * sizeof(int)), int, l[i])`
- After the `if`, both branches need to rejoin into the invariant shape for the next iteration. A post-`if` bridge should therefore rebuild:
  - `exists l1', Zlength(l1') == i + 1`
  - the processed-prefix replacement property for all `k < i + 1`
  - `IntArray::full(a, n@pre, app(l1', sublist(i + 1, n@pre, l)))`
- This is the minimal branch join that should let `symexec` advance without pushing replacement reasoning into a later proof layer.

## Iteration 3: remove the inline conditional term after a verifier crash

- The first rerun of `symexec` exited with a segmentation fault after creating empty generated files, which means the frontend failed before producing usable obligations.
- The most suspicious construct in the active annotation was the term:
  - `data_at(..., if (l[i] == old_k) then new_k else l[i])`
- Existing verified examples in this repo use branch-local assertions rather than expression-level conditional terms inside separation-logic resources.
- The safer rewrite is:
  - keep the pre-`if` bridge that opens slot `i`;
  - split the program into explicit `if ... else ...`;
  - in each branch, immediately assert the same post-branch shape `exists l1', ... IntArray::full(...)`, with the branch fact deciding whether index `i` contributes `new_k` or `l[i]`.
- This should avoid parser/frontend instability while preserving the same invariant-strength argument.

## Iteration 4: isolate the crashing annotation form

- A control run on the original `input/array_replace_k.c` produced the expected verifier message:
  - `Error: Lack of assertions in some paths for the loop!`
- So the toolchain is healthy on this function, and the crash is caused by the richer active annotations rather than by `array_replace_k` itself.
- The next isolation step is to strip the active file back to:
  - the loop invariant only;
  - no bridge assertions inside the loop body.
- If this reduced file returns the normal missing-assertions error, then the unsupported construct is specifically in the loop-body bridge syntax, not in the invariant itself.
