## Manual proof plan for `is_sorted_nondecreasing`

### Round 1: classify the generated obligations

After `symexec`, the generated `proof_manual.v` contains exactly three `Admitted.` obligations:

- `proof_of_is_sorted_nondecreasing_safety_wit_2`
- `proof_of_is_sorted_nondecreasing_entail_wit_4`
- `proof_of_is_sorted_nondecreasing_return_wit_2`

These are all pure obligations; there is no missing shape or ownership information.

- `safety_wit_2` is an arithmetic side condition proving `i + 1` is still representable as an `int`.
- `entail_wit_4` is the loop-exit strengthening step: from `i + 1 >= n_pre` and the invariant over pairs `< i`, derive the universal property for all pairs `< n_pre`.
- `return_wit_2` is the final postcondition branch for `return 1`; it should be solved by choosing the right disjunct and reusing the already-established universal property.

This means the task is firmly in the proof layer. There is no reason to go back and change annotations unless compilation reveals some hidden side-condition that the current witnesses did not expose.

### Round 2: proof shape to try first

The initial plan is:

- start each theorem with `pre_process` and `Intros`;
- use `entailer!` to separate the pure goal from the spatial frame;
- solve `safety_wit_2` with `lia`;
- solve `entail_wit_4` by introducing an arbitrary `j`, deriving `j < i` from `j + 1 < n_pre` and `i + 1 >= n_pre`, then applying the invariant hypothesis;
- solve `return_wit_2` by choosing the right disjunct, keeping the same array ownership, and reusing the universal property directly.

If `return_wit_2` leaves a witness-format subgoal after `Exists`, I will inspect the exact compile state and then add the minimum explicit `split` / `assert` steps needed.

### Round 3: first proof failure pointed back to annotations

The initial `proof_manual.v` tried to prove `safety_wit_2`, but proof-state inspection showed the real issue was semantic rather than tactical:

- the loop-head witness needed `i + 1` to stay in signed-int range;
- the invariant only preserved `0 <= i <= n`, which is insufficient to conclude `i + 1 <= INT_MAX`.

This was fixed in the annotation layer by adding `i + 1 <= INT_MAX` and rerunning `symexec`.

### Round 4: second proof failure exposed a contract boundary

After regenerating witnesses, `entail_wit_3` required `i + 2 <= INT_MAX` on the continue branch. To make that provable, I tried strengthening the invariant with `n <= INT_MAX` so that `i + 1 < n` would imply the next-head bound.

That change regenerated a new initialization obligation in `entail_wit_1`:

- prove `n_pre <= INT_MAX` from the function precondition alone.

The current contract only states:

- `0 <= n`
- `Zlength(l) == n`
- `IntArray::full(a, n, l)`

and the generated witness for `entail_wit_1` does not retain the local `n` store, so there is no available hypothesis that directly connects `n_pre` to the signed-int upper bound. This means the added `n <= INT_MAX` invariant is not derivable inside Verify from the current formal input.

Conclusion: the remaining blocker is not a proof-script issue. Under the current contract, either:

- the invariant must avoid depending on a global `n <= INT_MAX` fact, or
- the contract input must be strengthened to state the needed bound explicitly.

The second option is a Contract-stage change and is outside Verify permissions.
