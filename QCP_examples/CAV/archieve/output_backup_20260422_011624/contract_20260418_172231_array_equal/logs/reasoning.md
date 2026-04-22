## Function semantics

Target function: `array_equal`

Raw semantics:

- Inputs are two integer arrays `a` and `b`, both of logical length `n`
- The function scans indices from `0` to `n - 1`
- It returns `0` immediately once it finds an index `i` such that `a[i] != b[i]`
- It returns `1` iff all compared positions are equal
- The function does not modify either input array

## Interface and memory model

The original interface is already verification-friendly:

- `n` is an explicit length parameter
- `a` and `b` are caller-owned buffers
- The function is read-only on both arrays

Required memory assumptions:

- `0 <= n`
- `a` owns an integer array of length `n`
- `b` owns an integer array of length `n`

This is captured with two `IntArray::full` predicates and matching `Zlength` constraints.

## Contract shape

The postcondition needs to describe whether two integer lists are pointwise equal and return an `int`-encoded boolean (`1` or `0`).

There is no evident existing shared Coq definition in this repository for this exact two-list specification, so a problem-specific `.v` bridge is justified.

Chosen shape:

- `With la, lb`
- precondition binds logical contents of both arrays
- postcondition states `__return == array_equal_spec(la, lb)`
- both arrays are preserved unchanged

## Coq dependency decision

`input/array_equal.v` is needed.

Reason:

- the function semantics depends on two logical lists at once
- existing nearby array examples use a dedicated `_spec` definition when the result is more than a trivial arithmetic formula
- defining `array_equal_spec : list Z -> list Z -> Z` keeps the C contract compact and stable

## Boundary considerations

- `n == 0` is valid; both arrays have empty logical contents and the function returns `1`
- no arithmetic overflow is introduced by the implementation
- no interface rewrite is needed
- no verify-stage annotations are included here by design
