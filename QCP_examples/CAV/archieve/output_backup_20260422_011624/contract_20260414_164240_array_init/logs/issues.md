# Issues

- The local `leetcode` workspace did not yet contain an annotated array example. I used `doc/ANNOTATE.md`, `doc/predict/ARRAY.md`, and `/home/yangfp/QualifiedCProgramming/QCP_examples/sum.c` to confirm the expected array contract shape.
- `/home/yangfp/QualifiedCProgramming/QCP_examples/sum.c` contains a close analogue in `arr_sum_update`, which writes zeros into an existing array and uses `IntArray::full(..., zeros(n))` in the postcondition. That example confirmed the right abstract result without needing a custom `.v` file.
- The raw markdown says the array has length at least `n` and is writable, while the repository predicate vocabulary naturally describes the exact writable prefix being operated on. I encoded that as `IntArray::full(a, n, l)`, which is the conservative repository-native formulation for the accessed region.
- I intentionally did not carry over any loop invariant templates from repository examples because the annotate skill explicitly forbids adding Verify-stage `Inv`, `Assert`, bridge assertions, or `which implies` material here.
- No `input/array_init.v` was created because the specification uses only existing array predicates and the built-in `zeros(n)` helper.
