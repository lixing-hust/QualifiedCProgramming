# Proof Reasoning

## Iteration 1: generated manual obligations

- Read `array_equal_goal.v`, `array_equal_proof_auto.v`, `array_equal_proof_manual.v`, and `array_equal_goal_check.v`.
- The generated `proof_manual.v` contains exactly two unfinished lemmas:
  - `proof_of_array_equal_return_wit_1`
  - `proof_of_array_equal_return_wit_2`
- Both obligations are in the pure list-spec layer:
  - the early return must show `array_equal_spec la lb = 0` from a witnessed mismatch at index `i`
  - the loop-exit return must show `array_equal_spec la lb = 1` from full pointwise equality on all valid indices
- This is not an annotation-gap signal:
  - `symexec` already generated the expected prefix-equality witness
  - the remaining work is to connect `Znth`-style index facts to the recursive Coq definition of `array_equal_spec`

## Planned proof structure

- Add one helper lemma `array_equal_spec_mismatch`:
  - inputs: equal lengths, a valid mismatch index, and prefix equality before that index
  - conclusion: `array_equal_spec la lb = 0`
- Add one helper lemma `array_equal_spec_equal`:
  - inputs: equal lengths and pointwise equality for every valid index
  - conclusion: `array_equal_spec la lb = 1`
- Keep the witness proofs short:
  - `entailer!`
  - `symmetry`
  - instantiate the appropriate helper lemma

## Iteration 2: compile compatibility and witness-shape cleanup

- First `coqc` failure in `array_equal_proof_manual.v` was syntax-level:
  - this environment rejected newer proof-script forms such as `induction ... as [...]`
  - fix: rewrite the helper lemmas into the older `induction la.` / plain `destruct` style
- Next failure was a missing induction-hypothesis name:
  - `induction la.` binds the recursive hypothesis as `IHla`, not `IH`
  - fix: update the recursive calls to `apply IHla`
- Next failure was a proof-state mismatch in `return_wit_1`:
  - `lia` on the first helper-lemma premises was less stable than the exact hypotheses produced by `entailer!`
  - fix: use the concrete hypotheses exposed by `coqtop`:
    - `H5` and `H6` for equal lengths
    - `H1` for `0 <= i`
    - `H0` plus `H5` for `i < Zlength la`

## Iteration 3: extracting both array lengths in `return_wit_2`

- The first `return_wit_2` script assumed a generic variable name `l`, which does not exist in the generated theorem context.
- `coqtop` inspection showed the stable context after `Intros`:
  - value lists are named `la` and `lb`
  - the pure equality witness is `H0`
  - length facts must be extracted from the two `IntArray.full` resources
- A plain `prop_apply IntArray.full_length` only targeted the left array resource.
- Fix:
  - apply the length lemma with explicit arguments:
    - `prop_apply (IntArray.full_length a_pre n_pre la). Intros.`
    - `prop_apply (IntArray.full_length b_pre n_pre lb). Intros.`
  - rebuild `Zlength la = n_pre` and `Zlength lb = n_pre` via `Zlength_correct`
  - feed those facts into `array_equal_spec_equal`
- Result:
  - `array_equal_proof_manual.v` compiled successfully
  - the full replay then reached `goal_check.v`

## Final state

- `proof_of_array_equal_return_wit_1` and `proof_of_array_equal_return_wit_2` are both completed.
- `array_equal_proof_manual.v` contains no `Admitted.` and no added `Axiom`.
