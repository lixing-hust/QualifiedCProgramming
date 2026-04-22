# Annotation Reasoning

## 2026-04-21 20:13:12 +0800 - Initial loop invariant for `majority_candidate`

The unannotated loop is:

```c
int candidate = a[0];
int count = 1;

for (i = 1; i < n; ++i) {
    if (count == 0) {
        candidate = a[i];
        count = 1;
    } else if (a[i] == candidate) {
        count++;
    } else {
        count--;
    }
}

return candidate;
```

The postcondition requires `__return == majority_candidate_spec(l)` and preservation of `IntArray::full(a, n, l)`. The loop does not write to `a`, so the invariant must keep the full array ownership unchanged, plus the parameter equalities `a == a@pre` and `n == n@pre` so the return witness can reuse the original memory predicate.

At the real `for (i = 1; i < n; ++i)` invariant point, initialization has already executed and the next element to process is index `i`. The processed prefix is `sublist(0, i, l)`, and the unprocessed suffix is `sublist(i, n@pre, l)`. Instead of introducing a new Coq function for the pair state after processing a prefix, the invariant records the continuation property:

```c
majority_candidate_acc(candidate, count, sublist(i, n@pre, l)) ==
  majority_candidate_spec(l)
```

This states that the current C state `(candidate,count)`, when continued over the remaining suffix, yields exactly the same final candidate as the full specification. Initialization holds because `candidate == a[0]`, `count == 1`, `i == 1`, `n == Zlength(l)`, and `majority_candidate_spec(l)` unfolds to `majority_candidate_acc(l[0], 1, sublist(1, n, l))` for the nonempty input guaranteed by `1 <= n`.

The preservation argument matches the three branches directly against `majority_candidate_step`:

```coq
majority_candidate_step candidate count x =
  if Z.eq_dec count 0 then (x, 1)
  else if Z.eq_dec x candidate then (candidate, count + 1)
  else (candidate, count - 1)
```

For `count == 0`, after `candidate = a[i]; count = 1`, the new continuation over `sublist(i + 1, n, l)` is the one-step unfolding of the old continuation over `a[i] :: sublist(i + 1, n, l)`. For `count != 0 && a[i] == candidate`, `count++` corresponds to the second branch of `majority_candidate_step`. For `count != 0 && a[i] != candidate`, `count--` corresponds to the third branch. The pure bounds `0 <= count && count <= i` are included because `count++` needs an overflow guard: when the loop body executes, `i < n`, and `count <= i` implies `count + 1 <= n`; since `n` is an `int`, this keeps the increment inside the signed integer range. They also make `count--` safe because the else branch has `count != 0` and the invariant has `0 <= count`.

The invariant to insert immediately before the `for` loop is:

```c
/*@ Inv
      1 <= i && i <= n@pre &&
      0 <= count && count <= i &&
      a == a@pre &&
      n == n@pre &&
      n@pre == Zlength(l) &&
      majority_candidate_acc(candidate, count, sublist(i, n@pre, l)) ==
        majority_candidate_spec(l) &&
      IntArray::full(a, n@pre, l)
*/
for (i = 1; i < n; ++i) {
```

Because the invariant mentions `majority_candidate_acc`, the annotated file also needs an `Extern Coq` declaration for that imported definition. The input `.v` already defines it in `majority_candidate.v`, and the existing annotated file already imports that module for `majority_candidate_spec`, so this is a parser-facing declaration rather than a contract rewrite.

On loop exit, `i < n` is false while the invariant has `i <= n`, so `i == n`; the continuation expression reduces to `majority_candidate_acc(candidate, count, sublist(n, n, l))`, i.e. `candidate`, which is exactly the return value required by the postcondition. If `symexec` cannot make that final suffix-empty step automatically, the next annotation iteration should add a minimal loop-exit `Assert` directly after the loop, but the first attempt keeps the annotation small.
