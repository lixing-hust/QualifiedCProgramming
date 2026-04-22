## Semantic summary

Target function: `string_to_upper_ascii`

Raw semantics:

- Input is a valid writable C string `s`
- The function scans from index `0` until the first terminator `0`
- For each scanned byte, if it is a lowercase ASCII letter in `[97, 122]`, it is rewritten to the corresponding uppercase letter by subtracting `32`
- All other bytes remain unchanged
- The update is in-place and the function returns `void`

## Verification-oriented rewrite decisions

- Keep the interface unchanged: `void string_to_upper_ascii(char *s)`
- Rewrite the loop from `while (s[i] != '\0')` to `while (1) { if (s[i] == 0) break; ... }` following `doc/SCOPE.md`
- Use numeric ASCII bounds `97`, `122`, and `65` to reduce front-end noise from character literals
- Preserve the exact pointwise update rule `s[i] = s[i] - 97 + 65`, which is equivalent to subtracting `32`

## Memory and string model

- Model the initial string as `CharArray::full(s, n + 1, app(l, cons(0, nil)))`
- Add `0 <= n && n < INT_MAX` so the scan index fits the implementation type `int`
- Add `(forall (k: Z), (0 <= k && k < n) => l[k] != 0)` because the program stops at the first `0`, and the postcondition describes the whole logical payload `l`
- The postcondition should describe the same buffer `s` with every lowercase ASCII character converted and the terminator preserved

## Result specification choice

- An inline `Ensure` would require repeating a recursive pointwise character transformation over `l`
- Existing public definitions do not appear to provide this exact list-to-list transformation
- This task therefore needs a small task-local Coq bridge:
  - `upper_ascii_char : Z -> Z`
  - `string_to_upper_ascii_spec : list Z -> list Z`
- Intended meaning:
  - `upper_ascii_char(x)` returns `x - 97 + 65` when `97 <= x <= 122`
  - otherwise it returns `x`
  - `string_to_upper_ascii_spec` maps that function over the list

## Need for input/string_to_upper_ascii.v

Yes. The postcondition needs a transformed string value, not just a scalar result, and no existing repository helper was identified for this exact ASCII uppercase map.

## Final contract shape

- `With l n`
- `Require`
  - `0 <= n && n < INT_MAX`
  - no interior `0` in `l`
  - `CharArray::full(s, n + 1, app(l, cons(0, nil)))`
- `Ensure`
  - `CharArray::full(s, n + 1, app(string_to_upper_ascii_spec(l), cons(0, nil)))`

## Open risks

- No extra bridge predicates or abstract pre/spec layers are needed beyond the list transformer
- No interface rewrite is needed because the original in-place API is already verification-friendly
