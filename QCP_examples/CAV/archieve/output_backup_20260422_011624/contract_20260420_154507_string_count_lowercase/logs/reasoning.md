# Contract Reasoning: string_count_lowercase

## Source Semantics

The target function scans a null-terminated C string `s` from left to right and counts characters in the ASCII lowercase range `a` through `z`.

- The scan starts at index `0`.
- At each nonzero character, the function increments the result exactly when `97 <= s[i] <= 122`.
- The scan stops at the first `0` terminator.
- The input string is read-only and must be restored unchanged in the postcondition.

## Boundary Conditions

- Bind the logical string payload as `l` and its length as `n`.
- Require `0 <= n` and `n < INT_MAX`; the result is at most `n`, so the C `int` counter cannot overflow.
- Require `Zlength(l) == n`.
- Require `(forall (k: Z), (0 <= k && k < n) => l[k] != 0)` so the loop's first zero is the final terminator of `app(l, cons(0, nil))`.
- Use `CharArray::full(s, n + 1, app(l, cons(0, nil)))` to provide readable memory for the whole C string including the terminator.

## Implementation Shape

The raw implementation used `while (s[i] != '\0')` and character constants. Following the project scope guidance for string scans, the generated C uses the verification-friendly equivalent:

- `while (1)` with an explicit `if (s[i] == 0) break;`
- integer character codes `97` and `122`

This preserves the program semantics while reducing frontend noise for later verification.

## Postcondition Shape

The postcondition states that the return value equals `string_count_lowercase_spec(l)`, where the task-specific Coq function recursively counts list elements in the inclusive range `97..122`.

The memory resource is restored as the same `CharArray::full(s, n + 1, app(l, cons(0, nil)))`, capturing that the function does not modify the string.

## Coq Dependency Decision

An `input/string_count_lowercase.v` file is needed. The repository has similar task-specific string counting definitions, but no existing public Coq function directly expresses "count lowercase ASCII characters in a list". The `.v` file therefore contains only the small recursive specification function required by this contract.

## Phase Boundary

The generated C contains only the target function, complete precondition/postcondition, and required imports. It intentionally does not include loop invariants, assertions, bridge assertions, or proof-stage comments.
