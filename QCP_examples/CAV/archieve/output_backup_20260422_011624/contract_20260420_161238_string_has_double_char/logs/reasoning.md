# Contract reasoning: string_has_double_char

## Raw semantics

The task asks for a function over a valid null-terminated C string `s`.
It returns `1` iff there are two adjacent non-terminator characters with
the same value, and returns `0` otherwise.  The function is read-only: it
must preserve the input string memory.

The raw implementation initializes `i = 1` and tests `s[i]` before any
separate empty-string check.  For an empty string represented by `[0]`,
that reads `s[1]`, outside the supplied string object.  The contract input
therefore uses a verification-friendly scan that first checks `s[i] == 0`
and only then inspects `s[i + 1]`.  This implements the intended problem
semantics for all valid C strings, including strings of length `0` and `1`.

## Logical model

Use logical variables:

- `l`: the list of non-terminator character codes.
- `n`: the length of `l`.

The concrete memory is represented as:

```c
CharArray::full(s, n + 1, app(l, cons(0, nil)))
```

The string validity condition also requires that no element of `l` is an
internal terminator:

```c
(forall (k: Z), (0 <= k && k < n) => l[k] != 0)
```

This follows the project experience for C string scans: if the function
stops at the first `0`, the contract must exclude earlier zeroes when the
postcondition speaks about the full logical string.

## Boundary conditions

- `n == 0`: the string is empty, so no adjacent pair exists and the result is `0`.
- `n == 1`: there is only one non-terminator character, so no adjacent pair exists and the result is `0`.
- `n >= 2`: return `1` iff some index `i` satisfies `0 <= i`, `i + 1 < n`,
  and `l[i] == l[i + 1]`; otherwise return `0`.

The precondition includes `n < INT_MAX`.  The loop index is an `int`, and
the implementation can evaluate `i + 1` while scanning up to the terminator;
this bound keeps the relevant integer arithmetic inside the verifier's
expected range.

## Coq dependency decision

No task-specific `input/string_has_double_char.v` is needed.  The result can
be expressed directly with first-order `exists` / `forall` over the list
indices, matching the existing direct contract style for adjacent-equality
array scans.  Adding a recursive Coq specification would not add necessary
expressive power for this task.
