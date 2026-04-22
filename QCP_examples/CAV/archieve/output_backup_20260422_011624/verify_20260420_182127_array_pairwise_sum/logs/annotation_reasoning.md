## 2026-04-20 annotation plan

Program point: the single for-loop in annotated/verify_20260420_182127_array_pairwise_sum.c currently has no Inv, so symexec cannot preserve the required postcondition across loop iterations.
Observed state: the contract requires IntArray::full(a,n,la), IntArray::full(b,n,lb), and IntArray::full(out,n,lr) where lr[k] = la[k] + lb[k]. The loop writes out[i] while preserving a and b.
Planned annotation: add a loop invariant with two existential lists l1 and l2 such that l1 is the processed prefix of out and satisfies l1[k] = la[k] + lb[k], while l2 is the unprocessed suffix copied from the original lo at offset i. The heap shape is IntArray::full(out,n@pre,app(l1,l2)) together with unchanged full arrays for a and b.
Bridge assertions: before the assignment, expose element i of a, b, and out using IntArray::missing_i and data_at so the array read/write can consume the focused cells. After the assignment, rebuild full arrays and choose a new processed prefix l1_prime[k] for the next iteration, with the suffix sublist(i+1,n@pre,lo).
Why this should fix it: initialization uses l1=[] and l2=lo; preservation extends the processed prefix by the newly written sum; exit with i=n@pre makes the suffix empty and app(l1,l2) equal to the desired result list.

## 2026-04-20 parser retry

Program point: contract header line 6 of annotated/verify_20260420_182127_array_pairwise_sum.c.
Observed error: symexec reported `bison: syntax error, unexpected PT_COMMA, expecting PT_REQUIRE` at the `With la, lb, lo` binder list before generating any Coq files.
Planned annotation edit: normalize the active annotated working copy header from comma-separated `With la, lb, lo` to the front-end accepted `With la lb lo`; this does not alter Require or Ensure semantics.
Why this should fix it: the close array_add example recorded the same parser issue, and removing commas lets the parser proceed to the actual verification conditions.

