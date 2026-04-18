# Annotation Reasoning

## Round 1

- Loop shape: `i` is the next unread index, so at the loop head the processed region is the prefix `sublist(0, i, l)`.
- Required postcondition: on exit we need `ret == count_equal_to_k_spec(l, k)` while preserving `IntArray::full(a, n, l)`.
- Stable facts that should stay in the invariant:
  - bounds `0 <= i <= n`
  - unchanged parameters `a == a@pre` and `n == n@pre`
  - memory ownership `IntArray::full(a, n, l)`
  - semantic summary `ret == count_equal_to_k_spec(sublist(0, i, l), k)`
- Initialization check: before the first test, `i == 0` and `ret == 0`, so this reduces to proving `count_equal_to_k_spec(sublist(0, 0, l), k) == 0`.
- Preservation expectation: after reading `a[i]`, the next state should summarize `sublist(0, i + 1, l)`. The branch update on `ret` should match the recursive definition of `count_equal_to_k_spec`.
- Exit usefulness: when `i == n`, `sublist(0, i, l)` should become the full list, so a small loop-exit assertion should be enough to recover the postcondition.

## Planned edit

- Add one loop invariant carrying the prefix-count summary.
- Add one loop-exit `Assert` to fix `i == n` and rewrite the prefix summary to the full-list summary.

## Round 2

- Proof-stage feedback showed `proof_of_count_equal_to_k_return_wit_1` still needed to recover `k_pre` from the current variable `k`.
- This is the exact `@pre`-relation issue described in `INV.md` / `ASSERTION.md`: the invariant kept `a == a@pre` and `n == n@pre`, but it forgot the unchanged scalar parameter `k == k@pre`.
- Why this matters:
  - the function does not modify `k`
  - the postcondition is phrased with `count_equal_to_k_spec(l, k)` from source syntax
  - the generated return witness is phrased with both `k` and `k_pre`, so the proof layer needs the annotation layer to preserve that equality explicitly
- Fix direction:
  - strengthen the loop invariant with `k == k@pre`
  - strengthen the loop-exit assertion with the same equality
  - rerun `symexec` from a clean generated directory before continuing Coq proof work
