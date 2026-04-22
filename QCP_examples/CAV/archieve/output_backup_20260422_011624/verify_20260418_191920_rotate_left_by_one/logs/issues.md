# Verification Issues

## Summary

- Status: blocked
- Blocking stage: `symexec`
- Annotation changes required: yes
- Manual proof required: not reached
- Compile chain status: not reached

## Issue 1: loop needed a semantic invariant for the shifted prefix

- Phenomenon:
  - the initial annotated copy had no loop invariant or loop-exit assertion for the in-place shift loop
- Trigger condition:
  - `rotate_left_by_one` overwrites `a[i]` from `a[i + 1]`, so the logical array contents change on every iteration
- Diagnosis:
  - the loop head needs a summary of the current array contents, not just bounds
  - the stable shape is:
    - shifted prefix `sublist(1, i + 1, l)`
    - untouched suffix `sublist(i, n, l)`
- Fix:
  - added an invariant carrying:
    - `0 <= i && i <= n@pre - 1`
    - `a == a@pre`
    - `n == n@pre`
    - `n@pre == Zlength(l)`
    - `first == l[0]`
    - `IntArray::full(a, n@pre, app(sublist(1, i + 1, l), sublist(i, n@pre, l)))`
  - added a loop-exit assertion fixing `i == n@pre - 1`
- Result:
  - later `symexec` runs advanced through the loop and consistently reached the final store

## Issue 2: single-hole bridge before `a[i] = a[i + 1]` hid the RHS read cell

- Phenomenon:
  - the first rerun failed at the loop body with:
    - `Cannot derive the precondition of Memory Read`
- Trigger condition:
  - I opened the destination slot with:
    - `IntArray::missing_i(a, i, ...) * data_at(...)`
  - but the statement also needs to read `a[i + 1]`
- Diagnosis:
  - the one-hole state was sufficient for writing index `i` but not for exposing the separate readable cell at `i + 1`
  - the repo’s `bubble_sort` example keeps `a[j] = a[j + 1]` under a full-array invariant instead of opening the destination slot first
- Fix:
  - removed the loop-body `which implies` pair
  - kept the stronger full-array invariant only
- Result:
  - the next run passed the loop body and moved on to the post-loop store

## Issue 3: final-store bridge initially lost the live variable `n`

- Phenomenon:
  - the next rerun failed at `a[n - 1] = first` with:
    - `cannot find the program variable n in assertion`
- Trigger condition:
  - the post-loop bridge only mentioned `n@pre`
- Diagnosis:
  - the concrete statement still uses the current variable `n`
  - the bridge needed an explicit live-to-pre equality
- Fix:
  - threaded `n == n@pre` through the invariant and the post-loop assertions
- Result:
  - the failure changed form, confirming the missing current-variable equality had been one real blocker

## Issue 4: final-store execution remained unstable under all tried bridge shapes

- Phenomenon:
  - every subsequent rerun still failed at the final assignment `a[n - 1] = first`
- Trigger conditions and observed variants:
  - no final bridge:
    - `Assign Exec fail`
  - final bridge written only in `@pre` terms:
    - `cannot write null value to memory`
  - final bridge rewritten in current variables `a`, `n`, `n - 1`:
    - still `cannot write null value to memory`
  - final bridge reordered into the documented `data_at(...) * IntArray::missing_i(...)` shape:
    - still `cannot write null value to memory`
- Diagnosis:
  - the shift-loop invariant is strong enough for `symexec` to handle `a[i] = a[i + 1]`
  - the remaining blocker is isolated to the fixed post-loop overwrite of the last slot
  - the available examples and local docs did not provide a verified pattern close enough to this exact state shape
- Fix attempts:
  - kept the loop under a full-array invariant
  - tried the final store from the full-array exit state directly
  - tried `missing_i` bridges using both `n@pre` and current `n`
  - tried both `missing_i * data_at` and `data_at * missing_i`
- Result:
  - `symexec` never completed successfully on the current annotated file
  - proof and compile stages could not start legitimately

## Retrieval result

- Searched `CAV/examples/` and the wider repo for:
  - `rotate_left`
  - fixed final writes like `a[n - 1] = ...`
  - similar shifted-prefix array annotations
- Result:
  - no close verified example was found for this exact “in-place shift loop plus final overwrite” pattern

## Trace Files

- Symexec log:
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_191920_rotate_left_by_one/logs/qcp_run.log`
- Generated files created during failed reruns:
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_191920_rotate_left_by_one/coq/generated/rotate_left_by_one_goal.v`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_191920_rotate_left_by_one/coq/generated/rotate_left_by_one_proof_auto.v`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_191920_rotate_left_by_one/coq/generated/rotate_left_by_one_proof_manual.v`
  - `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_191920_rotate_left_by_one/coq/generated/rotate_left_by_one_goal_check.v`
