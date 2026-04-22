# Annotation Reasoning

## Iteration 1

- The loop processes adjacent pairs `(i, i + 1)` while the guard `i + 1 < n` holds.
- At the loop head for a given `i`, the already processed comparisons are exactly the pairs with left endpoint `< i`, so the semantic summary should be the spec on the already covered prefix of `l`.
- A direct summary `cnt == array_count_increasing_steps_spec(sublist(0, i + 1, l))` matches the nonempty case, but it is awkward at initialization when `n == 0` because the loop exits immediately with `i == 0`.
- To keep one invariant that also covers `n == 0`, use:
  - `cnt == array_count_increasing_steps_spec(sublist(0, Z.min n (i + 1), l))`
- Why this shape is promising:
  - Initialization:
    - if `n == 0`, then `Z.min n (i + 1) == 0`, so the summary becomes the empty-list spec `0`
    - if `n > 0`, then `Z.min n 1 == 1`, and the one-element spec is also `0`
  - Preservation:
    - on any real loop iteration, `i + 1 < n`, so the current prefix length is `i + 1`
    - after processing `a[i]` and `a[i + 1]`, the next loop head should summarize the prefix of length `i + 2`
  - Exit:
    - when the guard is false, `i + 1 >= n`, so `Z.min n (i + 1) == n`
    - the invariant should then reduce directly to `cnt == array_count_increasing_steps_spec(sublist(0, n, l))`, and with `Zlength(l) == n` that should collapse to the full postcondition
- The invariant should also preserve the unchanged parameters and array resource:
  - `a == a@pre`
  - `n == n@pre`
  - `IntArray::full(a, n, l)`
- First annotation pass:
  - add the loop-head invariant with the `Z.min` prefix summary
  - add a minimal loop-exit assertion fixing `i + 1 >= n`, the unchanged parameters, and the postcondition-shaped summary
- If the exit assertion introduces a local-permission artifact, remove it and rely on the invariant plus the generated return witness instead.

## Iteration 2

- The first `symexec` rerun failed before real VC generation with:
  - `Use of undeclared identifier 'Z'`
- Localization:
  - the invariant line using `Z.min(n, i + 1)` in the active annotated copy
- Diagnosis:
  - this annotation frontend does not accept dotted Coq names like `Z.min(...)` inside C-side annotations
  - the underlying invariant idea is still valid; only the surface syntax is incompatible
- Adjustment:
  - replace the `Z.min` summary with an explicit case split already expressible in the annotation language:
    - `n == 0 && cnt == 0`
    - or `0 < n && cnt == array_count_increasing_steps_spec(sublist(0, i + 1, l))`
- Why this should still work:
  - initialization:
    - if `n == 0`, the first branch holds immediately
    - if `n > 0`, then `sublist(0, 1, l)` has length `1`, so its spec is `0`
  - preservation:
    - the loop body only runs when `i + 1 < n`, hence necessarily in the `0 < n` branch
    - after one step, the processed-prefix summary still advances from length `i + 1` to length `i + 2`
  - exit:
    - if `n == 0`, the function should return `0`
    - if `n > 0` and the loop exits, `i + 1 >= n` together with `i <= n` should reduce the summary to the full list

## Iteration 3

- The second `symexec` rerun still failed before useful VC generation with:
  - `The number of now assertions and loop inv pre assertions does not match`
- Diagnosis:
  - the parser accepts `||` in postconditions, but this loop invariant shape is not being consumed stably at the loop head
  - the cheapest next step is to remove the loop-level case split entirely
- New hypothesis:
  - the library `sublist` used throughout this repository behaves as a clamped prefix operator, so `sublist(0, 1, l)` should reduce to `nil` when `l` is empty
  - if that is right, the plain summary
    - `cnt == array_count_increasing_steps_spec(sublist(0, i + 1, l))`
    already handles `n == 0` and `n > 0` without any special syntax
- Why this is worth trying:
  - it matches the successful `count_positive` pattern closely
  - it keeps the invariant in a single conjunction, which this frontend handles more reliably
  - if the edge case is not derivable, the remaining problem should then show up as a genuine witness/proof obligation instead of a parser/control-point mismatch

## Iteration 4

- After `symexec` succeeded and the first proof pass started, the generated `proof_manual.v` exposed a genuine annotation gap:
  - `proof_of_array_count_increasing_steps_safety_wit_3` asks for `i + 1 <= INT_MAX` at the loop head
- Diagnosis:
  - the current invariant only preserves `0 <= i <= n`
  - that is not enough to justify signed safety of evaluating the guard expression `i + 1 < n`
  - the real loop-state fact is stronger:
    - if `n == 0`, the loop never runs and `i` stays `0`
    - otherwise every reachable loop head satisfies `i + 1 <= n`
- Adjustment:
  - strengthen the invariant with the pure fact `i + 1 <= n || n == 0`
- Why this should help:
  - with `n == n@pre` and the stored-int range of `n`, the proof can derive `i + 1 <= INT_MAX`
  - the shape is still a single extra arithmetic disjunction, not a whole alternative state summary
  - the semantic summary of `cnt` over `sublist(0, i + 1, l)` remains unchanged, so the loop-step witness shape should stay close to the current one

## Iteration 5

- The strengthened invariant could not be used in practice.
- `symexec` failed immediately with:
  - `The number of now assertions and loop inv pre assertions does not match`
- Diagnosis:
  - this frontend again rejects loop invariants that contain a top-level disjunctive pure fact, even when the rest of the invariant is unchanged
  - so the natural repair for `safety_wit_3` is semantically right but not frontend-compatible in this workspace
- Consequence:
  - the last `symexec`-accepted annotated copy remains the simpler invariant without the disjunctive guard fact
  - under that accepted VC, `proof_of_array_count_increasing_steps_safety_wit_3` still indicates the loop-head arithmetic fact is too weak
- Conclusion:
  - verification is currently blocked by the combination of:
    - a genuine need for a stronger loop-head arithmetic fact
    - and a frontend limitation that rejects the natural disjunctive form of that fact

## Iteration 6

- Revisited the blocker against nearby verified array scans instead of continuing to encode the full reachable-state relation to `n`.
- New observation:
  - the failing witness `array_count_increasing_steps_safety_wit_3` does not actually need `i + 1 <= n`
  - it only needs the signed-safety fact for evaluating the guard expression:
    - `i + 1 <= INT_MAX`
- Why this is a better invariant candidate:
  - it avoids loop-level disjunction entirely, which is what the frontend previously rejected
  - it matches the style already used in other verified scans such as `array_prefix_max`
  - initialization is immediate at the first loop head:
    - `i == 0`, so `i + 1 == 1 <= INT_MAX`
  - preservation should follow from the branch condition on any real iteration:
    - entering the body gives `i + 1 < n`
    - the stored `int` range for `n` yields `n <= INT_MAX`
    - after `++i`, the next loop head needs `(old i) + 2 <= INT_MAX`, which follows from `(old i) + 1 < n <= INT_MAX`
- Planned retry:
  - keep the existing prefix-summary invariant unchanged
  - add only the pure clause `i + 1 <= INT_MAX`
  - rerun `symexec` and then continue from the next concrete proof or compile blocker

## Iteration 7

- The `i + 1 <= INT_MAX` retry improved the VC shape but exposed a new problem during manual proof:
  - it discharges the old loop-head safety witness
  - but it is not inductive as a loop invariant under the generated step witness
- Concrete evidence from the regenerated `entail_wit_2_1`:
  - after one successful body iteration the next head requires `i + 2 <= INT_MAX`
  - the available pure facts are only:
    - old `i + 1 <= INT_MAX`
    - branch fact `i + 1 < n`
    - no explicit pure upper bound on `n` appears in the entail witness
  - so the proof still gets stuck on the step witness
- Better invariant shape:
  - replace the direct machine-range fact with the reachable-state relation:
    - `0 < n => i + 1 <= n`
- Why this should work better:
  - initialization:
    - if `n == 0`, the implication is vacuous
    - if `n > 0`, then at the first loop head `i == 0`, so `i + 1 == 1 <= n`
  - preservation:
    - the body only executes under `i + 1 < n`
    - after `++i`, the next head needs `0 < n => i + 2 <= n`, which follows directly from the old branch fact
  - safety:
    - in the safety witness, the local `int` cell for `n` should provide `n <= INT_MAX`
    - combining that with the implication gives the needed bound on `i + 1` when `n > 0`
    - and the `n == 0` branch still gives `i == 0` from `0 <= i <= n`
- Retry plan:
  - remove `i + 1 <= INT_MAX` from the invariant
  - add the single implication clause `0 < n => i + 1 <= n`
  - rerun `symexec`
  - continue from the new generated proof obligations
