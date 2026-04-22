# Annotation Reasoning

## Round 1

- Loop shape: `i` is the destination index currently being overwritten, and the loop guard `i + 1 < n` means the unread source position is `i + 1`.
- Stable facts to preserve across iterations:
  - bounds `0 <= i && i <= n - 1`
  - unchanged parameters `a == a@pre` and `n == n@pre`
  - saved head element `first == l[0]`
  - current array contents as the rotated prefix plus untouched suffix:
    `IntArray::full(a, n, app(sublist(1, i + 1, l), sublist(i, n, l)))`
- Initialization check:
  - before the first loop test, `i == 0`
  - `sublist(1, 1, l)` is empty and `sublist(0, n, l)` is `l`, so the invariant reduces to the original `IntArray::full(a, n, l)`
  - `first = a[0]` should expose `first == l[0]`
- Preservation expectation:
  - at loop head, index `i` still stores `l[i]`
  - reading `a[i + 1]` gives `l[i + 1]` because the suffix `sublist(i, n, l)` is still untouched
  - after `a[i] = a[i + 1]`, the array should become
    `app(sublist(1, i + 2, l), sublist(i + 1, n, l))`
- Exit usefulness:
  - when the loop stops, `i == n - 1`
  - the invariant then gives the array shape
    `app(sublist(1, n, l), sublist(n - 1, n, l))`
  - one final bridge around `a[n - 1] = first` should reconstruct a full list `l0` satisfying the postcondition

## Planned edit

- Add one loop invariant carrying the shifted-prefix / untouched-suffix array decomposition.
- Add one bridge assertion before and after the loop-body write.
- Add one loop-exit assertion plus one final-write bridge around `a[n - 1] = first`.

## Round 2

- First rerun blocker: `symexec` failed at `a[i] = a[i + 1]` with `Cannot derive the precondition of Memory Read`.
- Diagnosis:
  - the loop-body bridge changed the state from a full-array view into `IntArray::missing_i(...) * data_at(...)`
  - that is enough to write index `i`, but it hides the separate readable cell at `i + 1`
  - the nearby `bubble_sort` example keeps the same `a[j] = a[j + 1]` statement under a full-array invariant without introducing a single-hole bridge before the assignment
- Change:
  - remove the loop-body `which implies` pair
  - keep the invariant that describes the current logical array contents after each shift step
- Expectation:
  - `symexec` should be able to read `a[i + 1]` and write `a[i]` directly from the invariant-carried `IntArray::full(...)`
  - only the final post-loop write may still need an explicit bridge

## Round 3

- Second rerun blocker: `symexec` failed at `a[n - 1] = first` with `cannot find the program variable n in assertion`.
- Diagnosis:
  - the post-loop bridge only carried `n@pre == Zlength(l)`
  - the assignment itself still mentions the live program variable `n`
  - unlike the loop guard, this statement needs an explicit current-to-pre equality `n == n@pre`
- Change:
  - add `n == n@pre` to the invariant and all post-loop/final-write bridge states
- Expectation:
  - the verifier should now be able to connect the expression `n - 1` in the concrete statement with the pre-state lengths used in the logical array predicates

## Round 4

- Third rerun blocker: the handcrafted final-write bridge caused `a[n - 1] = first` to fail with `cannot write null value to memory`.
- Diagnosis:
  - the custom `missing_i` bridge around the last store distorted the concrete write state instead of helping it
  - the loop exit already preserves a complete `IntArray::full(...)` view of the array, and the surrounding examples show direct array writes are often more stable from a full-array state than from a manually split one
- Change:
  - remove the pre-write and post-write `which implies` blocks around `a[n - 1] = first`
  - keep only a post-write `Assert` that states the required existential result shape
- Expectation:
  - `symexec` should execute the final store directly from the full-array exit state
  - if the final existential summary is still too strong, the next blocker will be a cleaner post-store witness issue instead of a malformed concrete memory state

## Round 5

- Fourth rerun blocker: with the bridge removed, `symexec` still stopped at the last store with `Assign Exec fail`.
- Diagnosis:
  - the loop summary is strong enough for the shift loop itself, but the final overwrite at the fixed index `n - 1` still needs the usual one-hole write shape
  - the earlier bridge failed because it was expressed only in `@pre` names, which confused the concrete write state
- Change:
  - reintroduce the final-store bridge, but express the hole and address using the live variables `a`, `n`, and `n - 1`
  - keep `n == n@pre` only as a pure connection back to the logical list length
- Expectation:
  - the concrete store executor should now recognize the writable cell at `a[n - 1]`
  - after the store, the bridge should reconstruct the existential output list directly

## Round 6

- Fifth rerun blocker: the current-variable bridge still failed at the last store with `cannot write null value to memory`.
- Diagnosis:
  - the array prediction note documents the canonical open-cell shape as `data_at(...) * IntArray::missing_i(...)`
  - my bridge used the reverse order
  - the logic is separation-commutative, but this frontend’s store executor may still be syntactically sensitive at this program point
- Change:
  - reorder the final bridge into the documented `data_at * missing_i` shape
- Expectation:
  - if the executor is pattern-matching on the open-cell shape, this is the smallest remaining normalization to try before treating the final-store failure as a tool limitation on the current annotation path
