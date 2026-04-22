# Issues for `tribonacci`

No blocking issues.

Notes:

- The raw problem only states `n >= 0`; the contract narrows this to `0 <= n <= 37` to keep all signed `int` additions and the returned result within the 32-bit signed range.
- A task-specific Coq file is required because no existing shared Tribonacci definition was available in the current input set.
