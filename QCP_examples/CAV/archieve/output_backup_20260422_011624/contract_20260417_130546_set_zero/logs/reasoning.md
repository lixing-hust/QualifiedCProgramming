## Function summary

Target function: `set_zero`

Behavior: overwrite every element of the caller-provided integer array `a` of length `n` with `0`.

Source semantics from raw statement:

- `n >= 0`
- the array length is exactly `n`
- update is in place

## Interface decision

The raw interface is already verification-friendly:

- no I/O
- no allocation
- no hidden global state
- caller owns the writable array

So the generated contract keeps the original signature:

```c
void set_zero(int n, int *a)
```

## Memory shape

The natural memory predicate is:

- `IntArray::full(a, n, l)` in the precondition for ownership of the whole array
- `IntArray::full(a, n, zeros(n))` in the postcondition for the fully updated contents

This matches the repository's existing style for in-place array writes and directly captures the full overwrite semantics.

## Logic variables

Use `With l` only in the C contract:

- the precondition needs an abstract list for the incoming array contents
- the postcondition does not need to preserve `l`, because all elements are overwritten

No extra numeric side conditions are needed beyond `0 <= n`, because:

- the raw statement already guarantees exact array length `n`
- the implementation only writes indices `0 .. n - 1`
- there is no arithmetic accumulation or return value that would require overflow bounds

## Coq dependency decision

No custom `input/set_zero.v` is needed.

Reason:

- the post-state is expressible with existing library notation `zeros(n)`
- no problem-specific mathematical function, relation, or bridge predicate is required
- this is the same shape as existing `input/array_init.c`

## Verify-stage guidance kept out of contract

The raw problem suggests a prefix-zero invariant, but per contract-stage rules this is not written into `input/set_zero.c`.

That belongs to Verify, not Contract.
