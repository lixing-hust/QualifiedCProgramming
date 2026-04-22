## Manual proof plan for `array_is_strictly_increasing`

### Round 1: classify generated obligation

Timestamp: 2026-04-20 15:43:04 +0800

After a clean `symexec`, `array_is_strictly_increasing_proof_manual.v` contains one generated manual obligation:

- `proof_of_array_is_strictly_increasing_entail_wit_4`

The obligation is the loop-exit bridge from the invariant prefix property to the assertion after the loop. The precondition contains:

- `i >= n_pre`
- `1 <= i`
- `i <= n_pre + 1`
- `forall j_2, 1 <= j_2 /\ j_2 < i -> Znth (j_2 - 1) l 0 < Znth j_2 l 0`
- `0 <= n_pre`
- `Zlength l = n_pre`
- `IntArray.full a_pre n_pre l`

The conclusion keeps the same bounds and ownership, but needs:

- `forall j, 1 <= j /\ j < n_pre -> Znth (j - 1) l 0 < Znth j l 0`

This is a pure strengthening step: for any such `j`, `j < n_pre` and `i >= n_pre` imply `j < i`, so the invariant hypothesis applies directly. The proof should be `pre_process`, `Intros`, `entailer!`, introduce the postcondition index, apply the invariant hypothesis, and discharge the arithmetic premise with `lia`.
