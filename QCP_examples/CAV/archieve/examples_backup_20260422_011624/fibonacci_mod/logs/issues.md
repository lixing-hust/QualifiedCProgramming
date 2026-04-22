## Issue 1: initial invariant used raw Coq projection syntax

- Phenomenon: the first `symexec` run failed before VC generation.
- Trigger: `annotated/verify_20260421_034752_fibonacci_mod.c` used `fst (fib_mod_pair (Z.to_nat (i - 2)) mod)` and `snd (...)` directly in the loop invariant.
- Location: `annotated/verify_20260421_034752_fibonacci_mod.c:30`.
- Error: `logs/qcp_run.log` reported `bison: syntax error, unexpected PT_IDENT, expecting PT_RPAREN or PT_COMMA`.
- Fix: rewrote the invariant in parser-supported function-call style using the exported `fib_mod_z(i - 2, mod)` and `fib_mod_z(i - 1, mod)` terms, and added explicit `0 <= a < mod` / `0 <= b < mod` range facts for loop-body arithmetic safety.
- Result: after clearing stale generated files and rerunning `/home/yangfp/QualifiedCProgramming/linux-binary/symexec`, symbolic execution completed successfully and generated fresh `fibonacci_mod_goal.v`, `fibonacci_mod_proof_auto.v`, `fibonacci_mod_proof_manual.v`, and `fibonacci_mod_goal_check.v`.

## Issue 2: manual proof helper `%` notation conflicted with `sac` scope

- Phenomenon: compiling `coq/generated/fibonacci_mod_proof_manual.v` failed before entering the generated witnesses.
- Trigger: helper lemmas written after `Local Open Scope sac` used statements such as `fib_mod_z 1 m = 1 % m`.
- Location: `coq/generated/fibonacci_mod_proof_manual.v:30`.
- Error: `compile_proof_manual.log` reported `Error: Unknown scope delimiting key m.`
- Fix: rewrote helper lemma statements to use explicit `Z.rem` instead of `%` notation.
- Result: the helper lemmas parsed and compiled far enough to reach the witness proofs.

## Issue 3: `entailer!` left subgoals in a different order than the annotation text

- Phenomenon: the first manual proof script for `proof_of_fibonacci_mod_entail_wit_1` failed with no matching `fib_mod_z 0` subterm.
- Trigger: after `pre_process; entailer!`, the Fibonacci base equalities had already been solved, and the remaining goals were modulo range facts.
- Location: `coq/generated/fibonacci_mod_proof_manual.v:67`.
- Error: `compile_proof_manual.log` reported `Error: Found no subterm matching "fib_mod_z 0 ?M13717" in the current goal.`
- Fix: inspected the proof state with `coqtop`, then reordered bullets. For `entail_wit_1`, the remaining goals were `1 % mod_pre < mod_pre` and `0 <= 1 % mod_pre`; for `entail_wit_2`, the remaining goals were recurrence equality, shifted `b` equality, modulo upper bound, and modulo lower bound.
- Result: the proof advanced to the recurrence-preservation obligation.

## Issue 4: recurrence proof needed explicit arithmetic normalization

- Phenomenon: the recurrence-preservation proof could not rewrite with the invariant hypothesis for `b`.
- Trigger: after applying the local recurrence lemma, Coq kept the index as `i - 2 + 1` rather than `i - 1`.
- Location: `coq/generated/fibonacci_mod_proof_manual.v:79`.
- Error: `compile_proof_manual.log` reported `Error: Found no subterm matching "fib_mod_z (i - 1) mod_pre" in the current goal.`
- Fix: inserted `replace (i - 2 + 1) with (i - 1) by lia` before rewriting with `H7`.
- Result: `proof_of_fibonacci_mod_entail_wit_2` compiled.

## Issue 5: early return proof needed branch equality substitution

- Phenomenon: `proof_of_fibonacci_mod_return_wit_1` initially tried to rewrite `fib_mod_z 0` while the goal still contained `fib_mod_z n_pre`.
- Trigger: `entailer!` did not substitute the branch hypothesis `n_pre = 0` into the postcondition.
- Location: `coq/generated/fibonacci_mod_proof_manual.v:92`.
- Error: `compile_proof_manual.log` reported `Error: Found no subterm matching "fib_mod_z 0 ?M4187" in the current goal.`
- Fix: added `subst n_pre` before rewriting with `fib_mod_z_0_local`.
- Result: `fibonacci_mod_proof_manual.v` compiled, contains no `Admitted.`, and contains no added `Axiom`.

## Final verification

- `symexec` succeeded on the latest active annotated C file.
- `original/fibonacci_mod.v`, `fibonacci_mod_goal.v`, `fibonacci_mod_proof_auto.v`, `fibonacci_mod_proof_manual.v`, and `fibonacci_mod_goal_check.v` all compiled successfully with the documented load-path template.
- `coq/generated/fibonacci_mod_proof_manual.v` contains no `Admitted.` and no top-level `Axiom` declaration.
- Non-`.v` files under `output/verify_20260421_034752_fibonacci_mod/coq/` were removed after compilation.
