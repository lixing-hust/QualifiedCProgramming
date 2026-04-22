## Semantic summary

Target function: `string_all_lowercase`

Raw semantics:

- Input is a valid C string `s`
- The function reads characters from index `0` until the first terminator `0`
- It returns `1` iff every scanned character is in the lowercase ASCII interval `[97, 122]`
- It does not modify the string

## Verification-oriented rewrite decisions

- Keep the interface unchanged: `int string_all_lowercase(char *s)`
- Rewrite the loop from `while (s[i] != '\0')` to `while (1) { if (s[i] == 0) break; ... }` following `doc/SCOPE.md`
- Use `0` instead of `'\0'` in the implementation
- Keep the per-character range test as `s[i] < 97 || s[i] > 122` to reduce front-end noise from character literals

## Memory and string model

- Model the input as `CharArray::full(s, n + 1, app(l, cons(0, nil)))`
- Add `0 <= n && n < INT_MAX` so the scan index stays within the modeled string length and remains `int`-compatible
- Add `(forall (k: Z), (0 <= k && k < n) => l[k] != 0)` because this is a string-scanning function whose postcondition depends on the whole prefix `l`; the contract must exclude interior terminators
- The function is read-only, so the same `CharArray::full` fact is preserved in `Ensure`

## Result specification choice

- A direct inline `Ensure` would require expressing "all elements of `l` are lowercase implies return 1, otherwise 0"
- Repository practice for similar scan/query functions is to expose a small Coq function over `list Z`
- Therefore this task should use a dedicated Coq helper:
  `string_all_lowercase_spec : list Z -> Z`
- Intended meaning:
  - `0` for `nil` is not appropriate here because the empty string should return `1`
  - Base case should therefore be `1`
  - Recursive case returns `0` on the first non-lowercase element, otherwise continues

## Need for input/string_all_lowercase.v

Yes. Existing public definitions do not appear to provide this exact string predicate/result function, and the list-based result is clearer and more reusable through a small task-local spec function.

## Final contract shape

- `With l n`
- `Require`
  - `0 <= n && n < INT_MAX`
  - no interior `0` in `l`
  - `CharArray::full(s, n + 1, app(l, cons(0, nil)))`
- `Ensure`
  - `__return == string_all_lowercase_spec(l)`
  - input string ownership/value unchanged

## Open risks

- No additional Coq bridge predicates are needed beyond the single recursive spec function
- No interface rewrite beyond loop normalization is necessary
