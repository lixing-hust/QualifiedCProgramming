# Issues

## 1. Loop header with character literal did not survive the verify frontend

- Symptom:
  - the original `while (src[i] != '\0')` form did not parse reliably in the annotation pipeline
- Trigger:
  - keeping the original loop header and using the generated Verify frontend directly
- Diagnosis:
  - reduced the loop to smaller probe variants and compared parser behavior
- Fix:
  - rewrote the annotated working copy to `while (1) { if (src[i] == 0) break; ... }`
- Result:
  - `symexec` succeeded on the rewritten annotated copy

## 2. `With` binder must use `n`, not `n@pre`, inside the invariant

- Symptom:
  - parser failure when the invariant referred to `n@pre`
- Trigger:
  - treating `n` like a mutable C variable instead of a logical binder from the contract
- Diagnosis:
  - compared probe annotations with `n@pre` and `n`
- Fix:
  - changed the invariant to use `n`
- Result:
  - the annotation parsed and symbolic execution completed

## 3. `entail_wit_2` required explicit list normalization

- Symptom:
  - `proof_manual.v` failed with unfinished bullets and unresolved destination-array entailments
- Trigger:
  - relying on `entailer!` alone after choosing the natural witnesses for the loop-preservation step
- Diagnosis:
  - inspected the full proof state in `coqtop`
  - identified the real obligation as normalization of `replace_Znth` over `l1_2 ++ d1_2`
- Fix:
  - used `replace_Znth_app_r`
  - used `replace_Znth_nothing` on the already-fixed prefix
  - destructed the suffix and simplified the `0` index explicitly
  - reordered the remaining pure goals to match the actual post-`entailer!` goal order
- Result:
  - `proof_of_string_copy_entail_wit_2` now completes

## 4. Current contract leaves `return_wit_1` unprovable

- Symptom:
  - `coqc` stops at `proof_of_string_copy_return_wit_1` with:
    - `Attempt to save an incomplete proof (there are remaining open goals).`
- Trigger:
  - compiling `coq/generated/string_copy_proof_manual.v` after `entail_wit_1` and `entail_wit_2` were completed
- Diagnosis:
  - `coqtop` shows the remaining goal after `entailer!` is:
    - `CharArray.full dst_pre (n + 1) (replace_Znth i 0 (l1 ++ d1)) |-- CharArray.full dst_pre (n + 1) (l ++ [0])`
  - the available hypotheses only constrain:
    - the exit position `i`
    - the copied prefix `l1`
    - the total suffix length `d1`
  - they do not constrain the untouched suffix contents, and they do not imply `i = n`
- Root cause:
  - the contract allows internal `0` values inside `l`
  - therefore `Znth i (l ++ [0]) = 0` does not imply that `i` is the final terminator position
- Consequence:
  - the generated return theorem is not derivable from the current specification
- Result:
  - `goal_check.v` cannot be completed without strengthening the specification or changing the problem statement

## 5. The original invariant was too weak; regenerated VC needed prefix nonzero information

- Symptom:
  - the first version of `return_wit_1` only remembered copied-prefix equality and destination shape
- Trigger:
  - using an invariant that tracked `l1` and `d1`, but did not record that all already-scanned source characters were nonzero
- Diagnosis:
  - revisited the loop semantics instead of staying in Coq
  - observed that the loop branch `if (src[i] == 0) break;` preserves one more semantic fact:
    - every earlier source position was checked and therefore nonzero
- Fix:
  - strengthened the invariant with:
    - `forall (k: Z), (0 <= k && k < i) => l[k] != 0`
  - cleared old generated files
  - reran `symexec`
- Result:
  - the regenerated `goal.v` now carries the nonzero-prefix fact into `entail_wit_2` and `return_wit_1`
  - the previous “pure proof only” diagnosis was corrected; part of the old failure really was an invariant gap

## 6. Strengthened invariant fixes `entail_wit_2` but not the final return theorem

- Symptom:
  - after regenerating the VC, `proof_manual.v` no longer matched the new pure-goal order
- Trigger:
  - reusing the old `entail_wit_2` script unchanged after the new nonzero-prefix hypothesis was inserted
- Diagnosis:
  - `coqc` failed in the old prefix-equality bullet because the first remaining pure goal had changed into the new nonzero-prefix obligation
- Fix:
  - restored `proof_of_string_copy_entail_wit_1`
  - restored `proof_of_string_copy_entail_wit_2`
  - swapped the two pure-goal bullets after `entailer!` so the nonzero-prefix goal is solved before the prefix-equality goal
- Result:
  - `proof_manual.v` now compiles again for the first two lemmas
  - the only remaining blocker is `proof_of_string_copy_return_wit_1`

## 7. The final blocker is a genuine contract counterexample, not a missing tactic

- Symptom:
  - even with the strengthened invariant, `coqtop` reduces `return_wit_1` to:
    - `CharArray.full dst_pre (n + 1) (replace_Znth i 0 (l1 ++ d1)) |-- CharArray.full dst_pre (n + 1) (l ++ [0])`
- Trigger:
  - trying to derive the full destination string after the loop exits on the first observed `0`
- Diagnosis:
  - the strengthened assumptions still do not force `i = n`
  - a concrete counterexample satisfies the theorem hypotheses but falsifies the conclusion:
    - `n = 1`
    - `l = [0]`
    - `i = 0`
    - `l1 = []`
    - `d1 = [42; 99]`
  - then the left side describes destination content `[0; 99]`, while the postcondition requires `[0; 0]`
- Fix:
  - no verify-local fix exists under the current contract
  - this must be escalated back to Contract, e.g. by strengthening the source-string specification to rule out internal `0` before the final terminator
- Result:
  - `proof_manual.v` can compile only with the final lemma absent
  - `goal_check.v` still fails because `proof_of_string_copy_return_wit_1` is not derivable from the current spec

## 8. The old contract-gap diagnosis became stale after the input contract was fixed

- Symptom:
  - the workspace logs still treated `return_wit_1` as fundamentally false
- Trigger:
  - the original analysis was done before the strengthened input contract and before the regenerated VC were aligned
- Diagnosis:
  - after updating `input/string_copy.c` and rerunning `symexec`, the new VC carried the “no internal zero before position `n`” fact into the return theorem
  - under that regenerated VC, the real task was to prove `i = n`, not to escalate back out of verify immediately
- Fix:
  - kept the strengthened contract
  - kept the strengthened invariant
  - cleared old generated files
  - reran `symexec`
- Result:
  - the old “counterexample under current contract” no longer applied to the current workspace state

## 9. `return_wit_1` needed explicit side conditions, not stronger tactics

- Symptom:
  - repeated `Cannot find witness` failures in the final lemma
- Trigger:
  - trying to close length obligations with bare `lia`
- Diagnosis:
  - the stuck goals all had hidden structure:
    - `Zlength (x :: nil) = ...`
    - “tail length is exactly one”
    - “a list of length one must be `x :: nil`”
- Fix:
  - rewrote lengths explicitly with:
    - `Zlength_cons`
    - `Zlength_nil`
    - `Zlength_nonneg`
  - replaced nested bullet-heavy destructs with a single local fact:
    - `Hd1_single : exists x, d1 = x :: nil`
- Result:
  - the one-element tail argument became stable and compilable

## 10. Final normalization required explicit nat-index reduction

- Symptom:
  - after most of `return_wit_1` was complete, one last entailment remained open:
    - destination content was still written as `replace_nth (Z.to_nat (...)) 0 (x :: nil)`
- Trigger:
  - `unfold replace_Znth; simpl` was not enough by itself
- Diagnosis:
  - the residual term would only reduce once the nat index was normalized to `0%nat`
- Fix:
  - added:
    - `replace (Z.to_nat (Zlength l - Zlength l)) with 0%nat by lia`
  - then simplified and finished with `entailer!`
- Result:
  - `string_copy_proof_manual.v` compiled successfully
  - `string_copy_goal_check.v` compiled successfully
