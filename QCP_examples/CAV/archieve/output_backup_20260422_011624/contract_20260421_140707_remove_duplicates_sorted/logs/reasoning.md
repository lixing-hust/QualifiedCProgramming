# Contract reasoning: remove_duplicates_sorted

## Raw semantics

- Input is an integer array `a` of length `n`.
- The valid domain is `n >= 0`; the array is nondecreasing.
- The function removes duplicates in place by keeping the first element of each equal run.
- The return value is the length of the compressed prefix.
- The implementation may modify the prefix of `a`; values after the returned prefix are not part of the semantic result.

## Boundary cases

- If `n == 0`, the function returns `0` and does not access `a`.
- If `n > 0`, the first array element is always kept, so the compressed length is at least `1`.
- If all elements are equal, the returned length is `1`.
- If all adjacent elements differ, the returned length is `n`.

## Memory model

- Use `IntArray::full(a, n, l)` to bind the input array contents to logical list `l`.
- The post-state array is represented by a fresh list `lr` of length `n`.
- The meaningful output is only the prefix of `lr`; the suffix is unconstrained because the program may leave old values there or overwrite some of them during compression.

## Mathematical specification

- The input sortedness precondition is:
  `(forall (i: Z), (0 <= i && i + 1 < n) => l[i] <= l[i + 1])`.
- A task-specific Coq function `remove_duplicates_sorted_spec : list Z -> list Z` describes the compressed prefix.
- The postcondition states:
  - `__return == Zlength(remove_duplicates_sorted_spec(l))`
  - `0 <= __return && __return <= n`
  - the final array list `lr` is `app(remove_duplicates_sorted_spec(l), t)` for some suffix `t`
  - `IntArray::full(a, n, lr)` holds.

## Coq dependency judgment

- A `.v` file is needed because the result is a list-valued compression of adjacent duplicates, not a simple scalar relation already available in the shared libraries.
- The `.v` file should contain only the task-specific recursive list specification and no proof-stage artifacts.

## Interface decision

- Keep the original C interface and implementation unchanged.
- Add only the verification contract and the imported Coq specification.
