# Issues

## Summary

- Status: complete
- Blocking issues: resolved
- Annotation changes required: yes
- Manual proof required: yes

## Annotation parsing mismatch

- Phenomenon: the first `symexec` retry failed immediately at the contract header with `unexpected PT_COMMA, expecting PT_REQUIRE`.
- Trigger: the active annotated copy inherited `With la, lb, lo`, but this front end rejects comma-separated `With` binders.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260418_173707_array_add.c`
- Fix:
  - normalized only the annotated working copy to `With la lb lo`
  - kept `Require` and `Ensure` unchanged
- Result: parsing moved past the contract header.

## Unsupported annotation helper

- Phenomenon: the next `symexec` retry failed with `Use of undeclared identifier 'map2'`.
- Trigger: the first invariant draft used `map2(Z.add, la, lb)` inside the C annotation, but this annotation front end does not expose `map2`.
- Localization: the loop invariant in `annotated/verify_20260418_173707_array_add.c`
- Fix:
  - rewrote the invariant to the repo’s standard existential prefix/suffix shape
  - tracked processed output values with `l1[k] = la[k] + lb[k]`
  - tracked the untouched suffix with `l2[k] = lo[i + k]`
- Result: `symexec` succeeded and generated fresh Coq obligations.

## Manual proof reduction

- Phenomenon: generated `array_add_proof_manual.v` contained six `Admitted.` placeholders.
- Trigger: the invariant and bridge assertions generate explicit range, existential, return, and `which implies` witnesses that auto proof does not discharge.
- Localization: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_173707_array_add/coq/generated/array_add_proof_manual.v`
- Fix chain:
  - proved `safety_wit_2` by instantiating the contract’s overflow hypothesis at index `i`
  - fixed existential witness order in `entail_wit_1` and `entail_wit_2`
  - proved `return_wit_1` by deriving `i = n_pre`, then `l2 = nil`, and reducing the final heap to `l1`
  - proved `which_implies_wit_1` using explicit `full_split_to_missing_i` steps instead of raw `entailer!`
- Result:
  - five of the six manual witnesses were reduced to proof scripts without `Admitted.`
  - one witness remains blocked

## Final proof blocker

- Phenomenon: `proof_of_array_add_which_implies_wit_2` was the last theorem still failing under `coqc`.
- Trigger: after merging the destination `missing_i + data_at` pair back to `IntArray.full`, the proof still has to normalize the updated output list into the exact target shape
  `app(l1 ++ [la[i] + lb[i]], sublist(i + 1, n_pre, lo))`.
- Localization: `array_add_proof_manual.v`, theorem `proof_of_array_add_which_implies_wit_2`
- Localization details:
  - I already proved `l2 = sublist i n_pre lo`
  - I rewrote the source-array merges through `replace_Znth_Znth`
  - the unresolved step was the destination-array normalization after the final merge
- Fix:
  - normalize the destination list to `l1 ++ (new :: sublist (i + 1) n_pre lo)` before the final `entailer!`
  - prove the resulting two pure goals directly:
    - the prefix pointwise property on `0 <= k < i + 1`
    - the length fact `Zlength (l1 ++ [new]) = i + 1`
- Result:
  - `array_add_proof_manual.v` now compiles
  - `array_add_goal_check.v` now compiles

## Final outcome

- `symexec` succeeded on the current annotated file.
- Verification completed successfully.
- The final blocker was a pure list normalization step in `which_implies_wit_2`, not a contract gap and not an annotation failure.
