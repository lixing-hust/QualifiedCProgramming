# Verification Issues

## Fingerprint initialization

- Phenomenon: `logs/workspace_fingerprint.json` still had an empty `semantic_description` and empty `keywords` at task start.
- Trigger: this workspace was pre-created before the verify workflow was completed.
- Fix: read `doc/retrieval/INDEX.md`, then filled `semantic_description` with the array scan/even-index accumulation semantics and used only controlled vocabulary values for `keywords`.
- Result: the fingerprint now records `algorithm_family: accumulation`, `control_flow: [for_loop, if]`, `data_shape: array`, `semantic_intent: sum_even_series`, and related proof/status dimensions.

## Missing loop invariant

- Phenomenon: the active annotated file initially had a `for (i = 0; i < n; ++i)` loop with no loop invariant or exit assertion.
- Trigger: `array_sum_even_indices` is a prefix scan over an array; without a loop-head summary, `symexec` has no stable relation between `sum`, `i`, and the processed prefix.
- Fix: added an invariant immediately before the `for` loop in `annotated/verify_20260420_114610_array_sum_even_indices.c`:
  - `0 <= i && i <= n`
  - `a == a@pre`
  - `n == n@pre`
  - `sum == array_sum_even_indices_spec(sublist(0, i, l))`
  - `IntArray::full(a, n, l)`
- Fix: added a loop-exit assertion immediately after the loop fixing `i == n`, the full-list spec, unchanged parameters, and preserved array ownership.
- Result: a clean `symexec` run completed successfully and generated fresh `array_sum_even_indices_goal.v`, `array_sum_even_indices_proof_auto.v`, `array_sum_even_indices_proof_manual.v`, and `array_sum_even_indices_goal_check.v`.

## Symexec invocation

- Phenomenon: this workflow requires rerunning `symexec` after every annotation edit and clearing stale generated Coq files first.
- Trigger: the loop invariant and exit assertion changed the VC shape.
- Fix: removed stale generated files for this task and ran `/home/yangfp/QualifiedCProgramming/linux-binary/symexec` with explicit `--goal-file`, `--proof-auto-file`, `--proof-manual-file`, `--input-file`, `-slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE`, `--coq-logic-path=SimpleC.EE.CAV.verify_20260420_114610_array_sum_even_indices`, and `--no-exec-info`.
- Result: `logs/qcp_run.log` ends with `Successfully finished symbolic execution`.

## Manual proof obligations

- Phenomenon: `array_sum_even_indices_proof_manual.v` contained five generated `Admitted.` placeholders:
  - `proof_of_array_sum_even_indices_safety_wit_6`
  - `proof_of_array_sum_even_indices_entail_wit_1`
  - `proof_of_array_sum_even_indices_entail_wit_2_1`
  - `proof_of_array_sum_even_indices_entail_wit_2_2`
  - `proof_of_array_sum_even_indices_entail_wit_3`
- Trigger: preserving the prefix invariant requires list reasoning about extending an even-index sum by one element, split by index parity.
- Fix: added helper lemmas in `array_sum_even_indices_proof_manual.v`:
  - appending one element to an even-length prefix adds that element to `array_sum_even_indices_spec`
  - appending one element to an odd-length prefix leaves `array_sum_even_indices_spec` unchanged
  - sublist-snoc variants instantiate those facts for `sublist 0 i l`
- Result: all five manual witnesses are proved without `Admitted.` or newly added `Axiom`.

## Coq proof iteration details

- Phenomenon: the first manual compile failed on compact destruct syntax: `Syntax error ... expected after 'as'`.
- Trigger: this Coq environment rejects some newer intro/destruct pattern forms.
- Fix: rewrote helper proofs with conservative `destruct` syntax.
- Result: compile advanced to semantic helper proof obligations.

- Phenomenon: one helper proof failed because ordinary list induction supplied an induction hypothesis for the one-cell tail, but `array_sum_even_indices_spec` recurs on the two-cell tail.
- Trigger: the spec clause is `x :: _ :: xs => x + array_sum_even_indices_spec xs`.
- Fix: replaced ordinary induction with guarded recursive proofs that destruct zero, one, or at least two elements and recur on the two-cell tail.
- Result: the append-single helper lemmas matched the spec recursion.

- Phenomenon: concrete modulo contradictions and prefix-length parity side conditions were not fully solved by `lia`.
- Trigger: goals contained concrete `Z.modulo` expressions such as `1 mod 2 = 0` and normalized prefix lengths like `i - 0`.
- Fix: used `cbv in Hmod; discriminate` for concrete impossible modulo cases, replaced nested `Z.succ` lengths with `Zlength l + 2`, and explicitly rewrote `i - 0` to `i`.
- Result: the parity helper lemmas compiled.

- Phenomenon: branch hypotheses from generated C `%` had `Z.rem` shape, while helper lemmas used `Z.modulo`.
- Trigger: C `%` is translated to `Z.rem`; helper arithmetic used Coq `mod`.
- Fix: introduced explicit bridge facts via `Z.rem_mod_nonneg`, using the invariant fact `0 <= i`.
- Result: true and false branch invariant preservation proofs compiled.

- Phenomenon: the loop-exit proof initially rewrote with the wrong generated hypothesis name and then tried to apply `sublist_self` outside the spec context.
- Trigger: generated hypothesis numbering placed `Zlength l = n_pre` at `H5`, not `H4`, and the remaining equality was under `array_sum_even_indices_spec`.
- Fix: rewrote with `H5`, then used `f_equal` before `apply sublist_self`.
- Result: `array_sum_even_indices_proof_manual.v` compiled.

## Final verification

- `goal.v` compiled.
- `proof_auto.v` compiled.
- `proof_manual.v` compiled.
- `goal_check.v` compiled.
- `proof_manual.v` contains no `Admitted.` and no newly added `Axiom`.
- Non-`.v` files under `coq/` were removed after compilation.
