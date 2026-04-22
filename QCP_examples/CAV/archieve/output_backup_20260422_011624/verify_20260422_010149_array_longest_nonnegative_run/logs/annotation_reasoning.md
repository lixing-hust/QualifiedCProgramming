## 2026-04-22 01:02:39 CST - Initial loop invariant for longest nonnegative run

Current annotated C has no invariant at the only loop:

```c
int best = 0;
int current = 0;
int i = 0;
while (i < n) {
    if (a[i] >= 0) {
        current++;
        if (current > best) {
            best = current;
        }
    } else {
        current = 0;
    }
    i++;
}
return best;
```

At the loop head, `i` is the number of elements already scanned and the next array index to read. `current` is the length of the current nonnegative suffix of the processed prefix, and `best` is the best run length seen so far. The postcondition is not a simple prefix-only equation; the imported Coq specification is tail recursive:

```coq
array_longest_nonnegative_run_acc current best remaining
```

The strongest stable loop-head relation is therefore a residual equation:

```c
array_longest_nonnegative_run_acc(current, best, sublist(i, n@pre, l)) ==
  array_longest_nonnegative_run_spec(l)
```

This says that if the Coq accumulator continues from the current C state over the unprocessed suffix, it produces exactly the full-list specification. Initialization holds because `i == 0`, `current == 0`, `best == 0`, and `sublist(0, n, l)` is the whole list under `Zlength(l) == n`. Preservation matches the loop body: when `a[i] >= 0`, the C code increments `current` and updates `best` with the same `Z.max best current'` used by the Coq accumulator; when `a[i] < 0`, both reset the current run to zero and keep/update best through `Z.max best 0`, which should be equal to `best` because `best` is maintained nonnegative. Exit is direct: `i >= n` plus `0 <= i <= n@pre` gives `i == n@pre`, so the suffix is empty and the residual equation reduces to `best == array_longest_nonnegative_run_spec(l)`, matching the return.

The invariant also needs pure bounds and frame facts:

```c
0 <= i && i <= n@pre &&
0 <= current && current <= i &&
0 <= best && best <= i &&
n == n@pre &&
a == a@pre &&
n@pre == Zlength(l) &&
IntArray::full(a, n@pre, l)
```

The `current <= i` and `best <= i` bounds are needed for arithmetic and overflow safety: inside a taken loop iteration `i < n@pre <= INT_MAX`, so `current + 1 <= i + 1 <= INT_MAX`. The `a == a@pre`, `n == n@pre`, and full-array heap fact are needed because the loop only reads from the input array and the ensure clause must return the same `IntArray::full(a, n, l)`.

Planned annotation change:

```c
/*@ Extern Coq (array_longest_nonnegative_run_acc : Z -> Z -> list Z -> Z) */

/*@ Inv
      0 <= i && i <= n@pre &&
      0 <= current && current <= i &&
      0 <= best && best <= i &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      array_longest_nonnegative_run_acc(current, best, sublist(i, n@pre, l)) ==
        array_longest_nonnegative_run_spec(l) &&
      IntArray::full(a, n@pre, l)
*/
while (i < n) { ... }
```
