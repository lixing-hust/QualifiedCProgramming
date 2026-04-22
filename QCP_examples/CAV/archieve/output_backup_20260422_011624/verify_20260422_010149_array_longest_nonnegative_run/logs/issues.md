# Verification Issues

## 1. Active annotated copy initially had no loop invariant

- Phenomenon: `annotated/verify_20260422_010149_array_longest_nonnegative_run.c` initially copied the input C exactly and had no `Inv` before the `while (i < n)` loop. For this scanning loop, symexec would not have enough information to preserve the array frame, prove overflow safety for `current++` / `i++`, or derive the postcondition from `best`.
- Trigger: the loop maintains three local state variables:

```c
int best = 0;
int current = 0;
int i = 0;
while (i < n) {
    if (a[i] >= 0) {
        current++;
        if (current > best) {
            best = current;
        }
    } else {
        current = 0;
    }
    i++;
}
```

- Location: active annotated C at `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260422_010149_array_longest_nonnegative_run.c`.
- Fix: added the accumulator helper declaration and a loop-head invariant that records bounds, frame facts, and the residual Coq accumulator equation:

```c
/*@ Extern Coq (array_longest_nonnegative_run_acc : Z -> Z -> list Z -> Z) */

/*@ Inv
      0 <= i && i <= n@pre &&
      0 <= current && current <= i &&
      0 <= best && best <= i &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      array_longest_nonnegative_run_acc(current, best, sublist(i, n@pre, l)) ==
        array_longest_nonnegative_run_spec(l) &&
      IntArray::full(a, n@pre, l)
*/
while (i < n) { ... }
```

- Result: after clearing stale generated targets and running symexec, `logs/qcp_run.log` ended with:

```text
Successfully finished symbolic execution
```

The generated files `array_longest_nonnegative_run_goal.v`, `array_longest_nonnegative_run_proof_auto.v`, `array_longest_nonnegative_run_proof_manual.v`, and `array_longest_nonnegative_run_goal_check.v` were created under `coq/generated/`.

## 2. Manual proof obligations remained after successful symexec

- Phenomenon: fresh `coq/generated/array_longest_nonnegative_run_proof_manual.v` contained five generated `Proof. Admitted.` placeholders:

```coq
proof_of_array_longest_nonnegative_run_entail_wit_1
proof_of_array_longest_nonnegative_run_entail_wit_2_1
proof_of_array_longest_nonnegative_run_entail_wit_2_2
proof_of_array_longest_nonnegative_run_entail_wit_2_3
proof_of_array_longest_nonnegative_run_return_wit_1
```

- Trigger: the loop invariant uses `array_longest_nonnegative_run_acc current best (sublist i n_pre l) = array_longest_nonnegative_run_spec l`. The loop-preservation witnesses need pure list rewriting to expose the next element of `sublist i n_pre l` and then simplify one step of the accumulator.
- Location: `coq/generated/array_longest_nonnegative_run_goal.v`, definitions `array_longest_nonnegative_run_entail_wit_2_1`, `_2_2`, `_2_3`, and `array_longest_nonnegative_run_return_wit_1`.
- Fix: added a local helper in `proof_manual.v`:

```coq
Lemma sublist_head_cons_Z :
  forall (l : list Z) i n,
    0 <= i < n ->
    n <= Zlength l ->
    sublist i n l = Znth i l 0 :: sublist (i + 1) n l.
```

Then each preservation proof rewrites the accumulator premise with this helper, simplifies the recursive definition, splits on `Z_le_dec 0 (Znth i l 0)`, and uses `lia` to normalize the relevant `Z.max` expression. The return witness proves `i = n_pre`, rewrites `sublist n_pre n_pre l` to `nil`, and simplifies the accumulator to `best`.
- Result: `coq/generated/array_longest_nonnegative_run_proof_manual.v` compiles, and `rg "Admitted\\.|\\bAxiom\\b" ..._proof_manual.v` returns no matches.

## 3. Full compile replay and cleanup were required for completion

- Phenomenon: successful manual proof compilation alone is not sufficient; the verify workflow requires the full ordered replay and cleanup of Coq intermediates under `coq/`.
- Trigger: completion criteria require `original/<name>.v`, `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile under the workspace logical path:

```text
SimpleC.EE.CAV.verify_20260422_010149_array_longest_nonnegative_run
```

- Fix: ran the documented compile order from `/home/yangfp/QualifiedCProgramming/SeparationLogic` with `_CoqProject`-style base `-R` flags, `-Q "$ORIG" ""`, and `-R "$GEN" "$LP"`. The replay wrote:

```text
compile_status: 0
```

to `logs/compile_status.tmp`.
- Result: `array_longest_nonnegative_run_goal_check.v` compiled successfully. After compile success, all non-`.v` files under `output/verify_20260422_010149_array_longest_nonnegative_run/coq/` were removed; the remaining `coq/` files are only the four generated `.v` sources.
