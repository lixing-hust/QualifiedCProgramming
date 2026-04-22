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
  - the preserved contract facts that every logical character before `na` / `nb` is nonzero
  - semantic prefix fact `(forall (j: Z), (0 <= j && j < i) => Znth(j, la, 0) == Znth(j, lb, 0))`
- Initialization check:
  - before the first loop test, `i == 0`
  - the prefix-equality fact is vacuous
  - both ownership facts and all contract facts come directly from the precondition
- Preservation expectation:
  - on the break branch, the invariant should still describe the state just before control leaves the loop
  - on the mismatch branch, the current unequal characters witness an immediate `0` result after a matched prefix
  - on the equal-continue branch, `a[i] == b[i]` extends prefix equality from `[0, i)` to `[0, i + 1)`
- Exit usefulness:
  - after the break, the most stable pure consequence is `i == na || i == nb`
  - inside the `a[i] == 0 && b[i] == 0` branch, the preserved nonzero-prefix facts should force `i == na` and `i == nb`, turning prefix equality into whole-string equality

## Planned edit

- Add one loop invariant carrying the shared-prefix equality fact, parameter stability, both `CharArray::full` resources, and the preserved nonzero-prefix contract facts.
- Add one loop-exit assertion recording the pure break consequence `i == na || i == nb`.
- Add one branch-local assertion before `return 1` to force `i == na` and `i == nb`.
