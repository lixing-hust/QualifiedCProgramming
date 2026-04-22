# Contract reasoning: string_count_digits

## Source semantics

The raw task defines `string_count_digits(char *s)` over a valid C-style null-terminated string. The function scans from index `0` until the first `0` byte and counts characters whose ASCII value is between `48` and `57`, inclusive. It does not modify the input string.

The original implementation uses `while (s[i] != '\0')`. For verification stability, the output C rewrites this as `while (1)` with an explicit `if (s[i] == 0) break;`. This preserves the same observable behavior while matching the project convention for string scans.

## Contract shape

The contract models the string as a logical list `l` of non-terminator characters followed by a final terminator:

- `Zlength(l) == n`
- all indices `0 <= k < n` satisfy `l[k] != 0`
- `CharArray::full(s, n + 1, app(l, cons(0, nil)))`

The nonzero-prefix condition is necessary because the program stops at the first `0`; without it, the contract could not justify that scanning reaches the final terminator after all of `l`.

The postcondition states:

- the return value equals `string_count_digits_spec(l)`
- the input memory is restored unchanged with the same `CharArray::full` predicate

## Bounds and safety

`0 <= n && n < INT_MAX` keeps `i` within the signed `int` range while scanning indices `0..n` and supports the final increment behavior inside the loop. The count is bounded by `n`, so it also stays within `int` under the same length bound.

## Coq dependency decision

No existing public Coq function for counting digit characters was found. A small problem-specific `input/string_count_digits.v` is therefore needed. It defines only `string_count_digits_spec : list Z -> Z`, following the existing count-string examples, and no extra bridge predicates are introduced.
