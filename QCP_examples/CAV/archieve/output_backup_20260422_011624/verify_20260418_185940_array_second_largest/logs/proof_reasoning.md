## Iteration 1: classify the generated manual goals

Read `array_second_largest_goal.v`, `array_second_largest_proof_auto.v`, and `array_second_largest_goal_check.v`.

The generated `array_second_largest_proof_manual.v` contains ten unfinished lemmas:

- `entail_wit_1_1` and `entail_wit_1_2`: initialization after the first two elements are normalized by the pre-loop swap
- `entail_wit_2_1` through `entail_wit_2_6`: one-step preservation across the three loop branches, duplicated for the two possible initial branch facts `Znth 1 l 0 > Znth 0 l 0` and `<=`
- `return_wit_1` and `return_wit_2`: loop exit

This looks like a pure proof-layer task, not an annotation-layer task:

- the generated contexts already carry `a == a@pre`/`n == n@pre` implicitly through the chosen invariant shape
- there is no missing ownership or malformed witness shape
- the remaining work is to unfold `second_largest_list` / `second_largest_acc` on list prefixes and suffixes

Planned proof structure:

- add a helper lemma turning `sublist i n l` into `Znth i l 0 :: sublist (i + 1) n l`
- add two helper lemmas for the two initialization cases of `second_largest_list`
- use the sublist-step lemma plus case-specific branch inequalities to prove each `entail_wit_2_*`
- prove both return witnesses by deriving `i_2 = n_pre`, rewriting `sublist n_pre n_pre l` to `nil`, and simplifying `second_largest_acc`

## Iteration 2: first compile blocker is Coq syntax, not logic

The first `coqc` pass failed at `second_largest_list_init_gt` before entering semantic proof checking.

- File: `coq/generated/array_second_largest_proof_manual.v`
- Error: `Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'`
- Cause: this environment rejects the newer `destruct l as [| x1 l']; [...]` style with inline branches.

Next action:

- rewrite those destructs into the older stable style used elsewhere in the repository
- recompile before changing any actual proof content

## Iteration 3: guessed sublist helper name was wrong

After the syntax fix, the next compile failure was:

- `The variable sublist_0_cons_cons was not found in the current environment.`

So the proof idea was still fine, but I had used a non-existent library lemma name while simplifying `sublist 2 n (x1 :: x2 :: xs)`.

Next action:

- replace that guessed lemma with an explicit two-step use of the available `sublist_cons2`
- finish the simplification with `sublist_self`

## Iteration 4: initialization proofs reached the real Coq-state shape

Using `coqtop` with the repository load-path showed the key intermediate state for the initialization helper:

- after the first `sublist_cons2`, the goal is not yet `sublist 1 ...`
- it is literally `sublist (2 - 1) (Zlength (x1 :: x2 :: xs) - 1) (x2 :: xs) = xs`

That explained why several earlier rewrites failed by exact matching.

The fix chain that did work:

- prove the first `sublist_cons2` side conditions explicitly instead of `by lia`
- normalize the left index with `replace (2 - 1) with 1 by lia`
- apply the second `sublist_cons2`
- normalize the final suffix length and close with `sublist_self`

## Iteration 5: current stable blocker

After the sublist normalization fixes, compilation progressed through both initialization helpers and then stopped at the contradiction branch in `second_largest_list_init_le`.

- Stable error site: `coq/generated/array_second_largest_proof_manual.v`, line 172 during the impossible `Z_gt_dec x2 x1` branch under the hypothesis `Znth 1 l 0 <= Znth 0 l 0`
- Symptom: contradiction-closing attempts such as `lia`, direct negation synthesis, and branch-local rewrites still end in `Cannot find witness`
- Current judgment: this is still a pure proof-state issue, not an annotation or symexec issue

What was tried before stopping:

- `lia` directly in the impossible branch
- converting the branch to explicit `exfalso`
- using the negated branch fact from `Z_gt_dec`
- simplifying the initialization lemmas enough that only the contradictory comparison remains

Next likely move if continuing:

- inspect the exact branch-local goal/state in `coqtop` at the failing line
- close it with the precise comparison theorem the environment expects instead of relying on `lia`
