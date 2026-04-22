## Annotation iteration 1

- Program point: the `while (i < n)` loop in `array_count_distinct_sorted`, after the function has handled `n == 0`, initialized `count = 1`, and initialized `i = 1`.
- Current issue: the active annotated C file currently has no loop invariant. Without an invariant, symbolic execution has no persistent relationship between the scalar accumulator `count`, the next index `i`, and the Coq postcondition `array_count_distinct_sorted_spec(l)`. It also needs the read-only array resource `IntArray::full(a, n, l)` and unchanged parameters across iterations.
- Relevant unannotated C fragment before this edit:

```c
int count = 1;
int i = 1;
while (i < n) {
    if (a[i] != a[i - 1]) {
        count++;
    }
    i++;
}
return count;
```

- Planned invariant: at the loop condition, `i` is the next index whose adjacency edge `(i - 1, i)` has not yet been processed. Since the `n == 0` case has returned, the prefix `sublist(0, i, l)` is nonempty at initialization. Therefore `count` should equal `array_count_distinct_sorted_spec(sublist(0, i, l))`, which is exactly the distinct-value count for the already processed prefix. The invariant also carries `1 <= count && count <= i` so the verifier has a simple integer-range fact before `count++`, plus `a == a@pre`, `n == n@pre`, and the full array predicate.
- Annotation to insert immediately before the loop:

```c
/*@ Inv
      1 <= i && i <= n &&
      1 <= count && count <= i &&
      a == a@pre &&
      n == n@pre &&
      count == array_count_distinct_sorted_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
while (i < n) {
```

- Initialization reasoning: after the `if (n == 0) return 0;` branch, the remaining path has `n > 0`. With `i == 1`, `count == 1`, and `Zlength(l) == n`, the prefix `sublist(0, 1, l)` contains the first element, so the Coq spec is `1 + array_count_distinct_sorted_from first nil`, i.e. `1`. Bounds `1 <= i && i <= n` and `1 <= count && count <= i` also hold.
- Preservation reasoning: when the loop body runs, `i < n` and `1 <= i`, so both `a[i]` and `a[i - 1]` are in bounds. If `a[i] != a[i - 1]`, the program appends a new distinct run to the scanned prefix and increments `count`; otherwise the prefix distinct count is unchanged. After `i++`, the invariant describes the larger processed prefix `sublist(0, i, l)`.
- Exit reasoning: when the loop exits, the invariant gives `i <= n` and the loop guard gives `!(i < n)`, hence `i == n`. The return witness should then reduce `sublist(0, n, l)` to `l` using `Zlength(l) == n`, so no separate post-loop `Assert` is added. This follows the existing `array_count_transitions` experience where an extra loop-exit assertion caused `Fail to Remove Memory Permission of i`.
