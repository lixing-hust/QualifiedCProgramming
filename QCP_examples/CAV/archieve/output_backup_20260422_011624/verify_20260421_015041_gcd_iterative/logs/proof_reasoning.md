## 2026-04-21 manual proof round 1

After successful `symexec`, the generated manual file contains three admitted obligations:

- `proof_of_gcd_iterative_entail_wit_1`: loop invariant initialization from the function precondition.
- `proof_of_gcd_iterative_entail_wit_2`: loop invariant preservation across `(a,b) := (b, a % b)` under `b <> 0`.
- `proof_of_gcd_iterative_return_wit_1`: return postcondition when the loop exits with `b = 0`.

The available generated context in `gcd_iterative_goal.v` shows that all three obligations are pure/separation-light. The first should instantiate the invariant witness with `Z.gcd a_pre b_pre`. The second should reuse the old invariant witness `g_2`; the missing arithmetic fact is the Euclidean identity `Z.gcd b (a mod b) = Z.gcd a b` for `b <> 0` and nonnegative `b`. The third should unfold `gcd_iterative_spec`, use `b = 0`, and reduce `Z.gcd a 0` to `Z.abs a`; because the invariant also has `0 <= a`, this becomes `a`.

Planned edit: replace only the `Admitted.` placeholders in `coq/generated/gcd_iterative_proof_manual.v` with conservative scripts that start with `pre_process`, instantiate existential witnesses explicitly, unfold `gcd_iterative_spec`, and use standard `Z.gcd` lemmas plus `lia` where possible.

## 2026-04-21 manual proof round 2

First compile result: `gcd_iterative_goal.v` and `gcd_iterative_proof_auto.v` compiled, but `gcd_iterative_proof_manual.v` failed in `proof_of_gcd_iterative_entail_wit_2` at the Euclidean rewrite:

`Error: Found no subterm matching "Zgcd (?M5068 mod ?M5069) ?M5069" in the current goal.`

The remaining pure goal after unfolding is `Z.gcd a b = Z.gcd b (a mod b)`. The first script rewrote in the wrong shape for `Z.gcd_mod`, whose statement is `Z.gcd (a mod b) b = Z.gcd b a` under `b <> 0`. Next edit: first replace `Z.gcd a b` with `Z.gcd b a` by commutativity, rewrite that side using `Z.gcd_mod` in reverse, then finish with commutativity.

Second compile result: the replacement was still attempted directly in the separation-logic entailment goal, where the visible pure subterm is guarded under `[| ... |]`. `coqtop` showed the post-`subst` context contains `H4 : Z.gcd a_pre b_pre = Z.gcd a b` and the entailment goal contains the pure target `Z.gcd a_pre b_pre = Z.gcd b (a % b)`. Next edit: assert that equality as a standalone Coq fact before `entailer!`, also assert `0 <= a % b` using `Z.mod_pos_bound` from `0 <= b` and `b <> 0`.

Third compile result: Coq rejected manual notation `a % b` with `Unknown scope delimiting key b`; in proof scripts, the modulo expression must be written as `a mod b` or with parser-friendly parentheses. Next edit: change only the manual proof script assertions to use `a mod b`.

Fourth compile result: `entailer!` left the heap weakening goal `r |-> value |-- r |->_` plus the two pure facts already asserted. Local examples solve the same heap pattern with `sep_apply store_int_undef_store_int` before `entailer!`. Next edit: apply that lemma, then close the remaining pure bullets with the named assertions.

Fifth compile result: the C remainder expression in generated goals is not definitionally the same as Coq `mod`; the goal expected `a % (b)` while the assertion used `a mod b`. Since the proof context has `0 <= a`, `0 <= b`, and `b <> 0`, `Z.rem_mod_nonneg` bridges C-style remainder to mathematical modulo. Next edit: assert `a % (b) = a mod b`, then state the gcd and nonnegativity facts over `a % (b)`.

Sixth compile result: after adding the C-remainder bridge and `sep_apply store_int_undef_store_int`, `entailer!` solved all remaining goals; the explicit bullets for `Hgcd_step` and `Hmod_nonneg` became stale and caused `Wrong bullet -: No more goals.` Next edit: remove the stale bullets.

Seventh compile result: `proof_of_gcd_iterative_return_wit_1` failed because the script rewrote `Z.gcd_0_r` in `H3`, but `coqtop` showed `H3 : g = Z.gcd a_pre b_pre` and `H4 : g = Z.gcd a 0` after unfolding and substituting `b = 0`. Next edit: rewrite `Z.gcd_0_r` in `H4`, simplify `Z.abs a` using `0 <= a`, derive `a = Z.gcd a_pre b_pre`, then let `entailer!` close the final entailment.

Final proof result: the full compile replay at `2026-04-21T01:58:43+08:00` compiled `original/gcd_iterative.v`, `gcd_iterative_goal.v`, `gcd_iterative_proof_auto.v`, `gcd_iterative_proof_manual.v`, and `gcd_iterative_goal_check.v`. `proof_manual.v` contains no `Admitted.` and no added top-level `Axiom`.
