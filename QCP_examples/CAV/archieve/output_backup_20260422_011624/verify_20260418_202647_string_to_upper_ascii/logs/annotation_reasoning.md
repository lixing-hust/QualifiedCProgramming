# Annotation Reasoning

## Round 1

- Loop role:
  - `i` is the next character index to inspect.
  - At the loop head, positions `0 .. i - 1` have already been rewritten to uppercase form.
  - Positions `i .. n - 1` are still the original suffix from the contract input list `l`.
- Required postcondition:
  - the whole writable string should become `app(string_to_upper_ascii_spec(l), cons(0, nil))`
- Stable facts the loop must preserve:
  - `0 <= i <= n`
  - the pointer identity `s == s@pre`
  - a decomposition of the original logical string as `l = app(l1, l2)`
  - `Zlength(l1) == i`
  - the current memory contents are `app(string_to_upper_ascii_spec(l1), app(l2, cons(0, nil)))`
- Why this shape is the right one:
  - the function updates the array in place, so the invariant must describe both the transformed prefix and the untouched suffix at the same time
  - carrying only the full pre-state string, as in read-only scans like `string_length`, would be too weak to justify the write to `s[i]`
  - carrying only the transformed prefix without tying it back to `l` would be too weak to recover the final postcondition
- Initialization:
  - at entry `i == 0`
  - choose `l1 = nil` and `l2 = l`
  - then `string_to_upper_ascii_spec(l1) = nil`, so the current array content is exactly the precondition string
- Preservation expectation:
  - if `s[i] == 0`, the loop exits and the invariant should already imply that the untouched suffix is empty
  - if `s[i] != 0`, then `l2` must be of the form `cons(x, l2')`
  - after the conditional assignment, cell `i` contains `upper_ascii_char(x)` and the next loop head should use:
    - new processed prefix `app(l1, cons(x, nil))`
    - new untouched suffix `l2'`
- Exit usefulness:
  - when the loop stops on `s[i] == 0`, the invariant says the concrete array is `app(string_to_upper_ascii_spec(l1), app(l2, cons(0, nil)))`
  - seeing `0` at the next unread position means the still-unprocessed suffix `l2` must be `nil`
  - then `l = app(l1, nil)`, hence `l == l1`
  - together with `Zlength(l1) == i` and the contract-level nonzero-prefix fact, this should collapse to `i == n`
  - after that the array content is exactly `app(string_to_upper_ascii_spec(l), cons(0, nil))`

## Planned edit

- Add one loop invariant immediately before `while (1)`.
- Add one loop-exit `Assert` after the loop to fix `i == n` and the final transformed string shape for the return point.
- Do not add `which implies` or extra bridge assertions unless the first `symexec` pass shows a specific gap.
