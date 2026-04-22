# Contract reasoning: string_count_spaces

## Source semantics

The raw task defines `string_count_spaces(char *s)`, where `s` is a valid C-style string terminated by `0`. The function scans from index `0` until the first terminator and returns the number of ordinary space characters in the scanned prefix. It does not modify the string.

Only ASCII space is counted. Tabs, newlines, and other characters are not counted.

## Verification-friendly implementation shape

The original implementation uses `while (s[i] != '\0')`. Per the project scope guidance for string scans, the generated input uses:

```c
while (1) {
    if (s[i] == 0) {
        break;
    }
    ...
}
```

This preserves the program semantics while giving the verifier a stable explicit branch for the terminator case. The character constant `' '` is represented as integer `32` to avoid front-end character literal noise.

## Contract shape

The string is represented by a logical list `l` of non-terminator characters followed by a final `0` in memory:

```c
CharArray::full(s, n + 1, app(l, cons(0, nil)))
```

The precondition includes:

- `0 <= n && n < INT_MAX` so `n + 1` is a valid positive memory length and the scan index stays in int range.
- `Zlength(l) == n` to connect the abstract string prefix length with the array shape.
- `(forall (k: Z), (0 <= k && k < n) => l[k] != 0)` so the first `0` reached by the program is the final terminator, not an internal terminator in `l`.

The postcondition preserves the same `CharArray::full` predicate because the function only reads `s`. The return value is specified by a task-specific recursive Coq function:

```coq
string_count_spaces_spec : list Z -> Z
```

which counts elements equal to `32`.

## Coq dependency decision

No existing public Coq definition for this exact space-counting string semantics was found. A small `input/string_count_spaces.v` file is therefore needed. It contains only the task-specific recursive specification function and no proof-stage definitions.
