## Semantics

Target function: `array_contains(int n, int *a, int k)`.

The function performs a left-to-right scan over the first `n` elements of `a`. It returns `1` as soon as it finds an index `i` such that `a[i] == k`; otherwise it returns `0` after the scan completes. The array is read-only.

## Interface And Memory

The original interface is already verification-friendly:

- `n >= 0`
- `a` denotes an integer array of length `n`
- the function does not modify `a`

So the contract can keep the original signature and use `IntArray::full(a, n, l)` with `Zlength(l) == n`.

## Contract Shape

There are two plausible contract styles:

1. Inline logical characterization:
   - return `1` iff there exists an index in bounds whose value is `k`
   - return `0` iff all in-bounds indices differ from `k`
2. A small Coq list-level spec function

This repository already uses the second style for similar array scans such as `count_equal_to_k` and `find_first_equal`. Following that pattern keeps the C contract short and stable.

## Coq Dependency Decision

`input/array_contains.v` is justified here because the result is a boolean-like scan property over a list, and the repository pattern is to expose that through a small recursive Coq function when the result is naturally recursive over the input list.

Planned definition:

- `array_contains_spec : list Z -> Z -> Z`
- returns `1` if some element equals `k`
- returns `0` otherwise

Then the C postcondition can be:

- `__return == array_contains_spec(l, k)`
- `IntArray::full(a, n, l)`

## Boundary Cases

- `n == 0`: the loop body never executes, so the result is `0`
- first element matches: immediate return `1`
- no element matches: final return `0`
- duplicate matches: still returns `1`; only existence matters

## Semantic Preservation

No interface rewrite is needed. The generated C keeps the original control flow and return values exactly.
