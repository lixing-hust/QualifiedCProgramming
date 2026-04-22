# Annotation reasoning

## Round 1: add the loop-head invariant for the array scan

The active annotated C file initially matched `input/longest_increasing_run.c` and had no Verify annotations inside the function body. The only nontrivial control point is:

```c
cur = 1;
best = 1;
for (i = 1; i < n; ++i) {
    if (a[i - 1] < a[i]) {
        cur++;
    } else {
        cur = 1;
    }
    if (best < cur) {
        best = cur;
    }
}
return best;
```

The contract says that for the nonempty case the return value must equal `longest_increasing_run_spec(l)`, where the input Coq file defines:

```coq
Fixpoint longest_increasing_run_acc
  (cur best prev : Z) (l : list Z) : Z :=
  match l with
  | nil => best
  | x :: xs =>
      let cur' := if Z_lt_dec prev x then cur + 1 else 1 in
      longest_increasing_run_acc cur' (Z.max best cur') x xs
  end.
```

At the loop guard of `for (i = 1; i < n; ++i)`, the program has already processed elements `0 .. i-1`; the next element to process is `i`. The C variables `cur`, `best`, and the previous element `Znth(i - 1, l, 0)` are exactly the accumulator state for continuing over `sublist(i, n, l)`. Therefore the strongest useful invariant is a continuation equation:

```c
longest_increasing_run_acc(cur, best, Znth(i - 1, l, 0), sublist(i, n, l)) ==
  longest_increasing_run_spec(l)
```

This is preferable to only saying `best == longest_increasing_run_spec(sublist(0, i, l))`, because the loop body updates `cur` using the adjacent comparison and then updates `best`; the continuation equation mirrors the Coq recursive step exactly. Initialization holds after `cur = 1; best = 1; i = 1` because the nonempty branch has `n > 0`, so the spec for `l` is the accumulator starting from the first element over `sublist(1, n, l)`. Preservation follows by unfolding one recursive step of the accumulator when `i < n`: the branch `a[i - 1] < a[i]` sets `cur` to `cur + 1`, otherwise to `1`, and the second branch sets `best` to `Z.max best cur`. Exit usability is direct: when `i >= n`, the invariant gives `i == n`; then `sublist(n, n, l)` is empty, so the accumulator returns `best`, matching the return expression.

The invariant also keeps the facts needed by the array reads and overflow side conditions:

```c
1 <= i && i <= n &&
n == n@pre &&
a == a@pre &&
n@pre == Zlength(l) &&
1 <= cur && cur <= i &&
1 <= best && best <= i &&
IntArray::full(a, n, l)
```

These bounds allow `a[i - 1]` and `a[i]` when the guard is true, and `cur++` is safe because `cur <= i`, `i < n`, and `n <= INT_MAX` imply `cur + 1 <= INT_MAX`.

## Round 2: declare the imported accumulator helper to the frontend

The first `symexec` attempt used the Round 1 invariant but failed during annotation parsing, before generating verification conditions:

```text
fatal error: Use of undeclared identifier `longest_increasing_run_acc'
in annotated/verify_20260421_202216_longest_increasing_run.c:40:4
```

The input Coq file already defines `longest_increasing_run_acc`, and the annotated C already imports that file with:

```c
/*@ Import Coq Require Import longest_increasing_run */
```

However, the C annotation frontend only has an explicit `Extern Coq` declaration for `longest_increasing_run_spec`, so it rejects direct use of `longest_increasing_run_acc` inside the invariant. The next edit adds exactly this declaration:

```c
/*@ Extern Coq (longest_increasing_run_acc : Z -> Z -> Z -> list Z -> Z) */
```

This does not change the function `Require`/`Ensure` contract. It only makes the existing imported helper function available to the verifier so the loop invariant can state the continuation equation needed for the proof.
