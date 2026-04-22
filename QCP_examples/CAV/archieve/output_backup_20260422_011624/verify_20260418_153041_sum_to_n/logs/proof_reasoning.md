## Iteration 1: classify the generated obligations

Read `sum_to_n_goal.v`, `sum_to_n_proof_auto.v`, and `sum_to_n_goal_check.v`.

The generated `sum_to_n_proof_manual.v` contains five unfinished lemmas:

- `sum_to_n_safety_wit_3`
- `sum_to_n_safety_wit_4`
- `sum_to_n_entail_wit_1`
- `sum_to_n_entail_wit_2`
- `sum_to_n_entail_wit_3`

All five are pure arithmetic obligations coming from the loop invariant:

- the two safety witnesses need integer-range facts for `ret + i` and `i + 1`
- `entail_wit_1` is the initialization check
- `entail_wit_2` is preservation of the closed form after one loop step
- `entail_wit_3` is the loop-exit arithmetic normalization to `i = n + 1`

Because there is no heap-shape reconstruction beyond `emp`, the shortest viable plan is:

1. start each proof with `pre_process`
2. use `entailer!` to discharge the separation-logic shell
3. finish the remaining arithmetic with `lia`

If `lia` alone is blocked, the likely issue will be the `÷ 2` notation or a needed normalization of the invariant’s closed form; in that case I will add explicit arithmetic rewriting before rerunning `coqc`.

## Iteration 2: first stable compile failure

The first `coqc` pass failed in `sum_to_n_proof_manual.v` at `proof_of_sum_to_n_safety_wit_3`.

- Stable error: `Cannot find witness.`
- Location: the trailing `lia` after `pre_process; entailer!`

Inspection with `coqtop` showed that `entailer!` left exactly two pure goals:

- `-2147483648 <= ret + i`
- `ret + i <= 2147483647`

The blocker was not missing heap reasoning; it was the triangular closed form still hidden behind
`ret = ((i - 1) * i) / 2`.

That diagnosis also applies to `entail_wit_2`, which needs the same one-step arithmetic normalization.

Updated plan:

1. add a local helper lemma `tri_step` for `((i - 1) * i) / 2 + i = i * (i + 1) / 2`
2. add `tri_nonneg` and `tri_monotone` so the safety witness can use the contract bound directly
3. handle `safety_wit_4` with a concrete numeric contradiction at `n_pre = 65536`, avoiding fragile direct reasoning through division
4. rerun the full compile chain once the five witnesses use those helpers

## Iteration 3: division-notation mismatch in the generated goals

The generated arithmetic uses `÷`, and `Locate "÷"` shows that this notation is `Z.quot`, not `Z.div`.

That explained the failed rewrite attempts with `Z.div_mul` and the earlier “not convertible” / “found no subterm matching” errors.

Fixes applied:

- changed the helper lemmas to reason explicitly about `Z.quot`
- used `Z.quot_div_nonneg` to convert to `Z.div` only in branches where the numerator is known nonnegative
- switched monotonicity and positivity lemmas to `Z.quot_le_mono` / `Z.quot_pos`-compatible forms via that conversion

## Iteration 4: contradiction shape after `vm_compute`

The numeric contradiction for `n_pre > 65535` did not reduce to a plain arithmetic inequality after `vm_compute`.
Instead, Coq normalized it to a proof object of the form `Gt = Gt -> False`.

That means the closing step cannot be a bare `lia`.
The stable closing shape is:

- `exfalso`
- `apply Hcontra`
- `reflexivity`
