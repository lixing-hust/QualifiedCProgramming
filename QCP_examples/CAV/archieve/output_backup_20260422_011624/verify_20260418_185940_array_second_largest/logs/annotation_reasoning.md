## Loop reasoning for `array_second_largest`

The scan starts after the first two elements have been loaded and normalized so that `max1 >= max2`.
Because the precondition states that all indices hold pairwise distinct values, those two initialized values are also distinct.
That means after the `if (max2 > max1)` swap, the processed prefix is exactly `sublist(0, 2, l)`, with:

- `max1` equal to the largest value in that prefix
- `max2` equal to the second-largest value in that prefix

The `for` invariant is checked at the loop guard, so it must describe the state before reading `a[i]`.
At that point:

- `i` is the next index to inspect, so `sublist(0, i, l)` is the processed prefix
- `2 <= i <= n` keeps the prefix large enough for `second_largest_list` to be meaningful
- `second_largest_acc(max1, max2, sublist(i, n, l)) == second_largest_list(l)` says the current accumulator pair plus the unprocessed suffix already summarizes the full target result
- `a == a@pre` and `n == n@pre` preserve unchanged parameters explicitly
- `IntArray::full(a, n, l)` keeps the array ownership/value summary available for the body and the final return

Why this invariant should preserve:

- The Coq definition `second_largest_acc` consumes the remaining suffix one element at a time using exactly the same three-way branch as the C loop body.
- If `a[i] > max1`, then the next accumulator state is `(a[i], max1)`.
- Otherwise, if `a[i] > max2`, then the next accumulator state is `(max1, a[i])`.
- Otherwise the accumulator pair stays `(max1, max2)`.

This means preservation can follow the recursive unfolding of `second_largest_acc` on `sublist(i, n, l)` into the head element `l[i]` and the tail `sublist(i + 1, n, l)`.

On exit, `i < n` is false and the invariant gives `i <= n`, so we get `i == n`.
Then `sublist(n, n, l)` is empty, so `second_largest_acc(max1, max2, nil) = max2`, yielding the exact postcondition target `max2 == second_largest_list(l)`.

## Iteration 2: replace the first invariant after frontend rejection

The first attempt used `max1 == max_list_nonempty(sublist(0, i, l))` to record the current maximum explicitly.
That failed before real symbolic execution because this task’s annotated input only declared `second_largest_list`, not `max_list_nonempty`, so the frontend reported `Use of undeclared identifier max_list_nonempty`.

Instead of introducing new list-max machinery into the annotated file, the invariant was simplified to use only `second_largest_acc`, which is already defined in `array_second_largest.v` and matches the loop body structurally.
This keeps the annotation closer to the provided spec and should produce cleaner witnesses.
