## Semantic summary

Target function: `array_add`

Source semantics:

- Input: `n`, input arrays `a` and `b`, output array `out`
- Behavior: for each index `i` with `0 <= i < n`, write `a[i] + b[i]` into `out[i]`
- Return: `void`

The implementation is already verification-friendly:

- single loop
- no branching
- no helper definitions needed
- no interface rewrite needed

## Contract decisions

The contract uses three logical lists:

- `la` for the initial contents of `a`
- `lb` for the initial contents of `b`
- `lo` for the initial contents of `out`

Preconditions:

- `0 <= n`
- `Zlength(la) == n`
- `Zlength(lb) == n`
- `Zlength(lo) == n`
- `IntArray::full` ownership for all three arrays
- per-index sum stays within signed 32-bit `int` range

Postconditions:

- `a` remains `la`
- `b` remains `lb`
- `out` becomes some list `lr` of length `n`
- for each valid index `i`, `lr[i] == la[i] + lb[i]`

## Memory and aliasing judgment

I use separating conjunction between the three `IntArray::full` predicates. This matches the repository pattern for read-two/write-one array functions and supports the intended statement that the two input arrays remain unchanged while the output array is filled independently.

## Coq dependency judgment

No `input/array_add.v` is needed.

Reason:

- the function semantics is a direct pointwise relation over lists
- no custom mathematical function or bridge predicate is needed
- existing list/index notation in the C contract is enough
