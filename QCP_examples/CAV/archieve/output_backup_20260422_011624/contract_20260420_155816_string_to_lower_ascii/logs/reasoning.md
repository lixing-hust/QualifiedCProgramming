# Contract reasoning: string_to_lower_ascii

## Source semantics

The raw task defines an in-place update over a valid C-style string `s`.
The function scans from index `0` until the first `0` terminator. For each
non-terminator character:

- if `65 <= s[i] <= 90`, it is converted to `s[i] + 32`;
- otherwise it is preserved.

The terminator itself remains `0`, and the function returns no value.

## Verification-friendly implementation choice

The raw loop `while (s[i] != '\0')` is rewritten as:

```c
while (1) {
    if (s[i] == 0) {
        break;
    }
    ...
}
```

This follows the local string-scanning contract convention and preserves the
program semantics. Character constants are written as integer ASCII codes to
avoid frontend noise.

## Memory and string boundary

The contract models the input as a logical list `l` of length `n`, followed by
one terminator:

```c
CharArray::full(s, n + 1, app(l, cons(0, nil)))
```

The precondition also requires:

- `0 <= n && n < INT_MAX`, so the loop index and `n + 1` stay in the intended
  integer range;
- `Zlength(l) == n`, making the logical prefix length explicit;
- every prefix element before index `n` is nonzero, so the loop's first `0`
  is exactly the final terminator.

This excludes embedded string terminators in the logical prefix, which is
required because the function stops at the first `0` but the postcondition
describes the whole prefix.

## Postcondition semantics

The postcondition keeps the same allocation and terminator, while replacing
the prefix with `string_to_lower_ascii_spec(l)`. That specification maps each
list element through the ASCII uppercase-to-lowercase conversion and leaves all
other values unchanged.

## Coq dependency decision

A task-specific `.v` file is needed because the result is naturally a recursive
list transformation, and there is no checked local public definition for this
exact lowercase ASCII transformer. The `.v` file should contain only:

- `lower_ascii_char : Z -> Z`;
- `string_to_lower_ascii_spec : list Z -> list Z`.

No loop invariants, assertions, bridge assertions, or verification-stage proof
material are included in the contract output.
