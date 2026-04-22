# Contract reasoning: string_starts_with

## Source semantics

The raw task defines `string_starts_with(char *s, char c)`.

The function reads exactly `s[0]` and returns:

- `1` when the first stored character equals `c`
- `0` otherwise

It does not modify `s`.

## Interface decision

The original interface is already verification-friendly:

- one input pointer to a C-style string
- one scalar character
- scalar integer return value
- no allocation, I/O, global state, or test harness

No interface rewrite is needed.

## Memory model

Use the existing `CharArray::full` string representation:

```c
CharArray::full(s, n + 1, app(l, cons(0, nil)))
```

where `l` is the logical string content before the terminating zero and `n` is its length. The task says `s` is a legal C-style string, so the contract includes the standard no-internal-zero condition:

```c
(forall (k: Z), (0 <= k && k < n) => l[k] != 0)
```

Although this function only reads `s[0]` and does not scan to the terminator, this keeps the input model consistent with the repository's string contracts.

The precondition also includes `0 <= n && n < INT_MAX` so that the array size expression `n + 1` stays in the usual verifier-friendly range.

## Postcondition semantics

The first memory cell is:

- `0` when `n == 0`, because the string is empty and the terminator is at index `0`
- `l[0]` when `0 < n`

Therefore the return condition is expressed directly as four disjoint cases:

- empty string and `c == 0`: return `1`
- empty string and `c != 0`: return `0`
- non-empty string and `l[0] == c`: return `1`
- non-empty string and `l[0] != c`: return `0`

The heap is preserved exactly as `CharArray::full(s, n + 1, app(l, cons(0, nil)))`.

## Coq dependency decision

No extra Coq file is needed. The semantics can be written directly in the C contract using arithmetic, equality, list indexing, and the existing `CharArray::full` predicate.
