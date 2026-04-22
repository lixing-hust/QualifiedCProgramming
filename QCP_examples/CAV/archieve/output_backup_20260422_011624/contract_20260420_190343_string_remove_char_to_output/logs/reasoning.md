# Contract Reasoning: string_remove_char_to_output

## Source Semantics

The raw function scans the input C string `s` from index `0` until the first zero terminator. For each nonzero character read from `s`, it copies the character to `out` exactly when that character is not equal to `c`. The copied characters preserve their original order. After the scan, the function writes a zero terminator at `out[j]` and returns `j`, the number of copied characters.

The implementation does not write through `s`. It writes only to the caller-provided `out` buffer.

## Verification-Friendly Rewrite

The source loop `while (s[i] != '\0')` is rewritten as:

```c
while (1) {
    if (s[i] == 0) {
        break;
    }
    ...
}
```

This preserves the program semantics while matching the repository guidance for string scans. The terminator is written as integer `0` rather than `'\0'`.

## Logical Model

The input string is represented by a list `l` of length `n`, followed in memory by a terminating zero:

```c
CharArray::full(s, n + 1, app(l, cons(0, nil)))
```

Because the program stops at the first zero byte, the contract also requires that the logical string payload has no internal zero:

```c
(forall (k: Z), (0 <= k && k < n) => l[k] != 0)
```

The result content is represented by a task-specific Coq function:

```coq
string_remove_char_to_output_spec : list Z -> Z -> list Z
```

It filters `l`, keeping exactly the elements not equal to `c`, in the original order.

## Preconditions

The contract requires:

- `0 <= n && n < INT_MAX`, so the scan index and result length fit in `int`.
- `Zlength(l) == n`, making the logical payload length explicit.
- no internal zero in `l`, so the loop exit position is the final terminator.
- separate ownership of `s` and `out` via separating conjunction. This captures the problem statement that `s` is not modified and that `out` is a writable caller-provided buffer.
- `out` has length `n + 1`, which is enough because the filtered result length is at most `n`, plus one zero terminator.

## Postconditions

The postcondition preserves the full input string ownership:

```c
CharArray::full(s, n + 1, app(l, cons(0, nil)))
```

For `out`, only the meaningful output prefix is fixed exactly. Since the output buffer has length `n + 1` and the filtered result may be shorter than `n`, the unused suffix after the written terminator is left existentially quantified:

```c
exists t,
  Zlength(t) == n - Zlength(string_remove_char_to_output_spec(l, c)) &&
  CharArray::full(out, n + 1,
    app(app(string_remove_char_to_output_spec(l, c), cons(0, nil)), t))
```

The return value is exactly the filtered output length:

```c
__return == Zlength(string_remove_char_to_output_spec(l, c))
```

## Coq Dependency Decision

A dedicated `.v` file is needed because the C contract needs a task-specific list filter by a runtime character `c`. There is no existing public definition in the checked inputs that directly names this exact string filtering semantics.

The `.v` file contains only the minimal recursive semantic function needed by the C contract.
