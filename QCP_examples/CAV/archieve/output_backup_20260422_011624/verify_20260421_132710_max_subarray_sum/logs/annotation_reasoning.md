## Annotation round 1: loop invariant for Kadane scan

- Program point: the only loop is `for (i = 1; i < n; ++i)` in the active annotated file `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_132710_max_subarray_sum.c`.
- Current issue before editing: the loop has no `Inv`, so symbolic execution would have no stable summary for the processed prefix, the read-only array ownership, or the relationship between `cur`, `best`, and `max_subarray_sum_spec`.
- Planned invariant: at the loop guard, `i` is the next array index to process, so `sublist(0, i, l)` is the processed nonempty prefix. Keep `n == n@pre`, `a == a@pre`, `IntArray::full(a, n, l)`, and `1 <= i <= n`.
- Semantic facts to add: `cur` is the maximum sum among nonempty subarrays ending exactly at `i`, represented by an existential start index and a universal upper bound over all starts; `best` equals `max_subarray_sum_spec(sublist(0, i, l))` and upper-bounds all nonempty subarray sums inside the processed prefix.
- Why this should fix the next failure: initialization uses `i = 1`, `start = 0`, and `cur = best = a[0]`; the loop body either starts a new suffix at `i` or extends the previous best suffix; after updating `best`, the invariant describes the extended prefix. At exit, `i == n` should make `best == max_subarray_sum_spec(l)` while preserving the full input array.

## Annotation round 2: switch to future-oriented accumulator invariant

- The first invariant let `best == max_subarray_sum_spec(sublist(0, i, l))`. `symexec` succeeded, but the generated branch entailments require proving a direct subarray-maximum characterization of `max_subarray_sum_spec` at every loop step.
- Better annotation shape: keep `cur` as a maximum suffix sum ending at `i` for overflow and branch reasoning, but replace the processed-prefix equality for `best` with `max_subarray_sum_acc(cur, best, sublist(i, n, l)) == max_subarray_sum_spec(l)`.
- Why this is valid: at initialization, `cur = best = l[0]` and the remaining suffix is `sublist(1, n, l)`, which is definitionally the nonempty-list case of `max_subarray_sum_spec(l)`. After each loop body, `cur` and `best` are updated exactly as one step of `max_subarray_sum_acc`; the remaining suffix moves from `sublist(i, n, l)` to `sublist(i + 1, n, l)`. At exit, `i == n` and the suffix is empty, so the accumulator equality directly gives `best == max_subarray_sum_spec(l)`.
- I will remove the processed-prefix `best` equality and all-subarray upper-bound over the prefix from the invariant, keep the suffix maximum facts needed for `cur + a[i]`, clear generated files, and rerun `symexec`.

## Annotation round 3: expose imported accumulator to annotation parser

- The first rerun after switching to `max_subarray_sum_acc(cur, best, sublist(i, n, l))` failed before VC generation.
- `logs/qcp_run.log` reported `Use of undeclared identifier max_subarray_sum_acc` at the invariant line. The identifier is already defined in `input/max_subarray_sum.v` and imported by the active annotated C file, but the C annotation frontend also needs an `Extern Coq` declaration for every Coq symbol referenced in annotations.
- Next edit: add `/*@ Extern Coq (max_subarray_sum_acc : Z -> Z -> list Z -> Z) */` next to the existing spec declaration in the active annotated copy, without changing the function contract or input files, then rerun `symexec` from clean generated files.

