## Function

`string_equal(char *a, char *b)` compares two valid C strings and returns `1` iff they have the same length and the same character at every position; otherwise it returns `0`.

## Semantic Decisions

- The natural abstract inputs are the two string contents before the final terminator, modeled as lists `la` and `lb`.
- The postcondition is best expressed with a dedicated Coq function `string_equal_spec : list Z -> list Z -> Z`.
- The function is read-only, so both `CharArray::full` assertions are preserved in the postcondition.

## Memory And String Shape

- Both pointers must denote valid null-terminated C strings.
- Following the repository string contract rule, each logical string uses:
  - `CharArray::full(ptr, n + 1, app(l, cons(0, nil)))`
  - plus `(forall (k: Z), (0 <= k && k < n) => l[k] != 0)`
- The explicit no-internal-zero condition is necessary because the implementation stops at the first `0`, and the contract needs that stop point to correspond to the final terminator of the modeled string.

## Implementation Shape

- The original program scans both strings in lockstep.
- I rewrote the loop to `while (1)` with an early break on either terminator to match the project guidance for string scans.
- This rewrite preserves behavior:
  - if a mismatch appears before either terminator, return `0`
  - if the scan stops because one side reaches `0`, return `1` only when both sides reach `0` at that same index

## Coq Dependency Decision

- A dedicated `input/string_equal.v` is needed.
- Reason: there is no existing repository-wide built-in spec name for equality of two string-content lists, and the C postcondition is simpler and more stable when it refers to a single recursive spec function.
