# Contract reasoning: string_count_not_char

## Source semantics

- The raw program scans a valid C-style string `s` until the first terminator byte `0`.
- For each character before the terminator, it increments `count` exactly when that character is not equal to the input character `c`.
- The function does not modify `s`.
- The return value is the number of positions `i` in the string payload such that `s[i] != c`.

## Interface decision

- The original interface `int string_count_not_char(char *s, char c)` is verification-friendly.
- No I/O, allocation, global state, or test harness is present.
- The implementation is rewritten only in the standard string-scan form:
  `while (1) { if (s[i] == 0) break; ... }`.
  This preserves the original behavior while matching the repository's preferred frontend-stable form.

## Contract shape

- Bind a logical payload list `l` and logical length `n`.
- Require `0 <= n && n < INT_MAX` so `i++` and the return count remain within `int` bounds.
- Require `Zlength(l) == n` to connect the payload list to the explicit length used in bounds.
- Require the payload has no internal terminator:
  `(forall (k: Z), (0 <= k && k < n) => l[k] != 0)`.
  This is needed because the C loop stops at the first `0`, while the postcondition describes the full payload `l`.
- Require ownership of the complete string representation:
  `CharArray::full(s, n + 1, app(l, cons(0, nil)))`.
- Ensure the string memory is restored unchanged and the return equals `string_count_not_char_spec(l, c)`.

## Coq dependency decision

- A task-specific recursive count over `list Z` is needed to express the result cleanly.
- Existing public definitions do not directly express "count elements not equal to this character" without adding an awkward derived expression.
- Therefore `input/string_count_not_char.v` is created with only `string_count_not_char_spec : list Z -> Z -> Z`.

## Boundary notes

- Empty strings are allowed with `n == 0`; the function returns `0`.
- Character values are represented as `Z` in the logic, following existing char-array contracts.
- No Verify-stage intermediate annotations or proof guidance are included in the contract output.
