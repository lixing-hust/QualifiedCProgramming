## 2026-04-21 annotation plan

- Program point: the outer `for (i = 1; i < n; ++i)` needs an invariant at the loop condition. The postcondition requires the final array list to be sorted and a permutation of the original list, so the outer invariant must preserve `Permutation(l, l_outer)`, `IntArray::full(a, n@pre, l_outer)`, bounds and unchanged parameters, plus `sorted_z(sublist(0, i, l_outer))`. To make the final sortedness usable, it also records that every processed-prefix element is `<=` every unprocessed-suffix element, matching the successful selection-sort and bubble-sort examples.

- Program point: after `key = a[i]; j = i - 1;`, the inner `while (j >= 0 && a[j] > key)` needs its own invariant. A plain `IntArray::full` with only sorted prefix is not enough because the loop temporarily duplicates shifted elements and keeps `key` in a scalar until the final write. The planned inner invariant introduces a base list `l_base` from the outer-loop state and a current heap list `l_cur`, keeps `key == l_base[i]`, and models the current array as `sublist(0, j + 2, l_base) ++ sublist(j + 1, i, l_base) ++ sublist(i + 1, n@pre, l_base)`, which describes the duplicated value at the current hole and the shifted segment.

- Program point: inner-loop exit before `a[j + 1] = key`. The invariant must preserve that all elements in `(j, i)` from the base prefix are greater than `key`; combined with the negated loop condition (`j < 0` or `a[j] <= key`) and sortedness of `sublist(0, i, l_base)`, the final write should produce a sorted prefix of length `i + 1`. The annotation leaves this as pure list proof obligations for the manual proof phase rather than trying to encode the whole insertion lemma in C annotations.


## 2026-04-21 annotation correction: remove invalid prefix-to-suffix ordering

- Program point: outer `for` loop invariant. Inspection of the generated `insertion_sort_entail_wit_1` showed the copied selection/bubble-sort style invariant required every element of the sorted prefix to be `<=` every unprocessed suffix element already at `i == 1`. That is false for insertion sort on inputs such as `[5, 1]`, because insertion sort only guarantees the prefix is internally sorted, not globally partitioned from the suffix.

- Fix: remove the prefix-to-suffix universal ordering clause from the outer invariant. Also remove the corresponding inherited clause from the inner invariant. Keep `Permutation(l, l_outer/l_base)`, `sorted_z(sublist(0, i, ...))`, bounds, unchanged parameters, and the inner shifted-segment/key facts needed for insertion.

- Expected result: `symexec` should regenerate witnesses whose initialization and return obligations reflect insertion sort semantics. The hard proof obligation should move to showing the final write inserts `key` into the sorted prefix, rather than proving an invalid global partition property.

## 2026-04-21 annotation correction: skipped outer loop boundary

- Program point: outer `for` loop initialization. The regenerated `insertion_sort_entail_wit_1` required proving `1 <= n_pre` from the function precondition `0 <= n_pre`, which fails for the valid boundary case `n == 0`. This happened because the invariant used `i <= n@pre` at the loop condition, but C initializes `i = 1` even when the loop body will be skipped.

- Fix: widen the outer invariant bound to `1 <= i && i <= n@pre + 1`. The inner loop still has `i < n@pre` because it only runs inside the outer loop body. The sorted-prefix assertion remains `sorted_z(sublist(0, i, l_outer))`, which is harmless for skipped loops and should still support the return proof with the array length from `IntArray::full`.

## 2026-04-21 annotation correction: precise outer exit bound

- Program point: function return after the outer loop. The widened bound `i <= n@pre + 1` handles `n == 0`, but by itself leaves the generated `return_wit` with `i >= n_pre` and `i <= n_pre + 1`, which permits `i = n_pre + 1` for nonempty arrays. That is not a real C execution state for this loop, but the invariant did not tell Coq enough to rule it out.

- Fix: strengthen the outer invariant with `(n@pre > 0 => i <= n@pre)`. This keeps the `n == 0` initialization valid while giving the return proof `i == n_pre` whenever the array is nonempty. For `n == 0`, `IntArray::full` length information should make the sortedness postcondition trivial.

## 2026-04-21 annotation correction: carry base-list length through inner invariant

- Program point: inner `while` invariant and outer `for` invariant. During manual proof of `entail_wit_3`, the shifted-hole list normalization needs `Zlength(l_base) == n@pre` to justify that `sublist 0 (j+2) l_base`, `sublist (j+1) i l_base`, and `sublist (i+1) n@pre l_base` cover the intended in-bounds segments. The current invariant only has `IntArray::full(a, n@pre, l_cur)` plus the equation defining `l_cur` from `l_base`; it does not expose the base list length as a pure fact.
- Why this is an annotation issue: `l_base` is the saved outer-loop list. Its length is exactly `n@pre` because it is introduced from an `IntArray::full(a, n@pre, l_outer)` state. Asking the manual proof to reconstruct this fact indirectly from the shifted representation dirties every insertion witness.
- Fix: add `Zlength(l_outer) == n@pre` to the outer invariant and `Zlength(l_base) == n@pre` to the inner invariant. Preserve existing permutation, sorted-prefix, key, range, and heap-shape facts. After this edit, rerun `symexec` and regenerate the Coq files before continuing proof.

## 2026-04-21 retry annotation repair: replace structural sorted_z invariant with adjacent prefix order

Current blocker after the previous retry is not symexec or memory shape: `symexec` succeeds, and the only remaining manual witnesses are `proof_of_insertion_sort_entail_wit_4_1` and `proof_of_insertion_sort_entail_wit_4_2`. Both witnesses must prove `sorted_z (sublist 0 (i + 1) (replace_Znth (j + 1) key l_cur))` directly from the shifted-hole representation. This is correct but makes the proof depend on large structural lemmas about `sorted_z`, `sublist`, append, and insertion.

The program point is the final write after the inner while loop, `a[j + 1] = key;`. The invariant already has the facts that are natural for insertion sort: the base prefix before inserting `key` is ordered, all shifted elements to the right of `j` are greater than `key`, and the guard-false branch gives either `j < 0` or `l_cur[j] <= key`. What is missing is a proof-friendly representation of prefix sortedness.

I will change only the semantic shape of the loop invariants, not the contract: replace the carried `sorted_z(sublist(0, i, ...))` fact with an adjacent-order invariant `forall k, 0 <= k && k + 1 < i => l[k] <= l[k + 1]`. This is equivalent enough for the postcondition because at loop exit a small Coq lemma can derive `sorted_z` from adjacent order over the full prefix. It also makes the final insertion witnesses local: the adjacent pair crossing the insertion point uses `l_cur[j] <= key` in the `j >= 0` branch or the shifted-elements fact in the `j < 0` branch, while pairs away from the insertion point reuse the base adjacent-order invariant.

Expected effect: `symexec` should regenerate final insertion obligations requiring an adjacent-order quantified fact instead of direct `sorted_z`. Existing correct length, permutation, heap-shape, and shifted-hole work remains valid in intent, but the manual proof file must be regenerated and repaired against the new witness shape.
