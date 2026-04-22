## Semantics

Target function `string_set_a(int n, char *s)` writes `'a'` into `s[0]` through `s[n - 1]`, then writes `'\0'` into `s[n]`.

The original interface is already verification-friendly:

- `n` is an explicit length parameter
- `s` is caller-provided writable storage
- there is no alias-sensitive multi-buffer behavior
- there is no need to redesign ownership or return style

## Boundary Conditions

- The problem states `n >= 0`.
- The buffer must have at least `n + 1` writable bytes because the function writes `n` data bytes and one terminator.
- For repository style and integer safety, use `n < INT_MAX` so `n + 1` stays within signed `int` range.
- When `n == 0`, the loop executes zero times and the function writes only `s[0] = '\0'`.

## Memory Shape

The input buffer content is irrelevant because the function overwrites all `n + 1` written positions. So the precondition should use shape-only writable ownership:

- `CharArray::undef_full(s, n + 1)`

The postcondition should describe the final concrete contents:

- first `n` bytes are `'a'`
- final byte is `0`

This is naturally expressed as:

- `CharArray::full(s, n + 1, app(repeat_Z('a', n), cons(0, nil)))`

## Coq Dependency Judgment

No task-specific `.v` bridge is needed.

Reason:

- shared string guidance already uses `repeat_Z(c, n)` for initialized char buffers
- the desired result is expressible directly in the C contract
- there is no extra abstract relation or custom problem-specific math layer

## Contract Writing Decision

The generated `input/string_set_a.c` should:

- include only the target function and its contract
- avoid Verify-stage annotations such as `Inv` or `Assert`
- keep the original program semantics unchanged
