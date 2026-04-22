# Annotation Reasoning

## Round 1

- Loop shape: `i` is the next character position to compare, so at the loop head the processed region is exactly the common prefix `[0, i)`.
- Required postcondition:
  - returning `1` means both strings end at the same position and all earlier characters are equal
  - returning `0` means either a mismatch occurred before either terminator, or one string terminates earlier than the other
- Stable facts that must survive every iteration:
  - bounds `0 <= i <= na` and `0 <= i <= nb`
  - unchanged parameters `a == a@pre` and `b == b@pre`
  - original string ownership for both inputs
  - semantic prefix fact `(forall (j: Z), (0 <= j && j < i) => la[j] == lb[j])`
- Initialization check:
  - before the first loop test, `i == 0`
  - the prefix-equality fact is vacuous
  - both ownership facts and all contract facts come directly from the precondition
- Preservation expectation:
  - on the break branch, the invariant should still describe the state just before control leaves the loop
  - on the mismatch branch, the current unequal characters witness an immediate `0` result after a matched prefix
  - on the equal-continue branch, `a[i] == b[i]` extends prefix equality from `[0, i)` to `[0, i + 1)`
- Exit usefulness:
  - after the break, we need the explicit fact `(a[i] == 0 || b[i] == 0)` close to the final branch
  - inside the `a[i] == 0 && b[i] == 0` branch, the nonzero-prefix contract should force `i == na` and `i == nb`, turning prefix equality into whole-string equality

## Planned edit

- Add one loop invariant carrying the shared-prefix equality fact, parameter stability, and both `CharArray::full` resources.
- Add one loop-exit assertion recording the break condition.
- Add one branch-local assertion before `return 1` to force `i == na` and `i == nb`.

## Round 2

- First `symexec` failure:
  - `fatal error: Cannot infer size of array`
  - localization: the post-loop `Assert` line that mentioned `a[i] == 0 || b[i] == 0`
- Diagnosis:
  - the failure happened while parsing/verifying the annotation itself, before any useful witness generation
  - this frontend accepts array reads in program code, but plain `Assert` formulas are more stable when they stay in the pure index/list layer instead of re-reading concrete arrays
- Change:
  - replace the break-condition restatement `a[i] == 0 || b[i] == 0` with the semantic consequence `i == na || i == nb`
  - keep the loop invariant and the branch-local `i == na && i == nb` target unchanged
- Expectation:
  - if the invariant really preserves the prefix-equality fact and both string resources, the solver should be able to prove the exit assertion using the contract’s nonzero-prefix assumptions

## Round 3

- Second `symexec` failure:
  - `The array j_107 of Znth is not a list type.`
- Diagnosis:
  - the new run reached symbolic execution and then failed while translating the quantified prefix-equality invariant
  - for this char-array task, the bracket notation `la[j] == lb[j]` inside `forall` is not being normalized robustly
  - the generated Coq side for nearby successful tasks already uses the explicit form `Znth j la 0`, so it is safer to match that surface syntax directly in the annotation
- Change:
  - rewrite every quantified prefix-equality occurrence in the active annotated file to `Znth(j, la, 0) == Znth(j, lb, 0)`
- Expectation:
  - this should remove the frontend translation ambiguity without changing the intended invariant semantics

## Round 4

- Proof-layer inspection of the first generated `goal.v` showed that `entail_wit_4_1` / `entail_wit_4_2` no longer carried the original nonzero-prefix contract facts.
- Diagnosis:
  - those witnesses came from the post-loop and branch-local `Assert` blocks
  - my first version of those assertions kept only bounds, prefix equality, and ownership, so the generated proof obligations had to derive `na = nb` without the key fact that characters before each logical length are nonzero
  - that is an annotation-layer information-loss problem, not a manual-proof problem
- Change:
  - add the two preserved contract facts
    - `forall k < na, Znth(k, la, 0) != 0`
    - `forall k < nb, Znth(k, lb, 0) != 0`
  - to the loop invariant, the post-loop assertion, and the `return 1` branch-local assertion
- Expectation:
  - after rerunning `symexec`, the exit witnesses should retain the exact “first zero is the terminator” facts needed to prove `i = na`, `i = nb`, and finally `na = nb`
