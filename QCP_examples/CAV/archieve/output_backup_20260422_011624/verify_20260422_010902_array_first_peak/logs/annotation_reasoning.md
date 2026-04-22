## 2026-04-22 01:10:25 +0800 - Initial loop invariant for first interior peak scan

Current program point:

```c
int i = 1;
while (i + 1 < n) {
    if (a[i] >= a[i - 1] && a[i] >= a[i + 1]) {
        return i;
    }
    i++;
}
return -1;
```

The loop scans interior candidate indices from left to right. At the loop test, `i` is the next candidate index. Every interior index `j` with `0 < j < i` has already been tested and was not a peak, so it must satisfy `l[j] < l[j - 1] || l[j] < l[j + 1]`. This is exactly the prefix fact needed by both return paths: the successful return at `i` needs all earlier interior indices to be non-peaks, and the final `-1` return needs all interior indices to be non-peaks after the loop exits.

The invariant must initialize even when `n` is 0 or 1. Since the code initializes `i = 1` before checking the loop condition and the contract only requires `0 <= n`, the bound cannot be `i <= n`. I will use `1 <= i && i <= n + 1`, which holds initially for all `n >= 0`, is preserved by `i++` under the loop condition `i + 1 < n`, and is strong enough with loop exit `!(i + 1 < n)` to derive that every `0 < j < n - 1` also has `j < i`.

Planned annotated fragment:

```c
int i = 1;
/*@ Inv
      1 <= i && i <= n + 1 &&
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z),
        (0 < j && j < i) =>
          (l[j] < l[j - 1] || l[j] < l[j + 1])) &&
      IntArray::full(a, n, l)
*/
while (i + 1 < n) {
    if (a[i] >= a[i - 1] && a[i] >= a[i + 1]) {
        return i;
    }
    i++;
}
/*@ Assert
      i + 1 >= n &&
      1 <= i && i <= n + 1 &&
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z),
        (0 < j && j < n - 1) =>
          (l[j] < l[j - 1] || l[j] < l[j + 1])) &&
      IntArray::full(a, n, l)
*/
return -1;
```

The successful branch is supported by the loop guard `i + 1 < n`, which gives `0 < i` and `i < n - 1`, plus the `if` condition, which gives both peak inequalities. The invariant supplies the first-peak prefix property for all `0 < j < i`.

The failed branch after the loop uses the explicit exit assertion to bridge from the invariant's prefix bound `j < i` to the postcondition's full interior range `j < n - 1`. This assertion is placed immediately after the loop, before local cleanup and before `return -1`, matching the loop-exit assertion guidance.

## 2026-04-22 01:12:16 +0800 - Strengthen invariant for `i + 1` safety

After the first `symexec` run, symbolic execution succeeded but generated a manual safety obligation:

```coq
Definition array_first_peak_safety_wit_2 :=
forall (a_pre n_pre: Z) (l: list Z) (i: Z),
  [| 1 <= i |] &&
  [| i <= n_pre + 1 |] &&
  [| 0 <= n_pre |] &&
  [| n_pre <= INT_MAX |] &&
  ...
|-- [| i + 1 <= INT_MAX |] && [| INT_MIN <= i + 1 |].
```

The current invariant is too weak for this safety check. From `i <= n + 1` and `n <= INT_MAX`, Coq cannot prove `i + 1 <= INT_MAX`; the invariant admits unreachable states such as `i = n + 1`. This is an annotation-strength issue, not a proof trick, because the program must prove the expression `i + 1` is safe every time the while condition is evaluated.

I will add the pure fact `i + 1 <= INT_MAX` to the loop invariant and to the loop-exit assertion:

```c
/*@ Inv
      1 <= i && i <= n + 1 &&
      i + 1 <= INT_MAX &&
      ...
*/
while (i + 1 < n) { ... }
```

Initialization: `i == 1`, so `i + 1 == 2`, and the global integer constants make `2 <= INT_MAX` immediate.

Preservation: at the loop head, if the body runs then the guard gives `i + 1 < n`. After `i++`, the next loop-head expression is `(i_old + 1) + 1`, and integer arithmetic gives `i_old + 2 <= n`. The precondition preserves `n <= INT_MAX`, so the new `i + 1 <= INT_MAX` holds.

Exit usability: the extra safety fact is not needed for the postcondition, but keeping it in the exit assertion makes the assertion match the current state and does not change the semantic bridge from `j < i` to `j < n - 1`.
