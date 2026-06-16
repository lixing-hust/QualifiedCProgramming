# A tutorial for proving goals of the execution predicate $\text{Exec}(\text{Pre}, c, \text{Post})$

This is a tutorial to illustrate how to prove proof goal in the form of the execution predicate $Pre \vdash \text{Exec}(\text{Pre}, c, \text{Post})$

## MANDATORY proof workflow — read this first

Every refinement VC proof MUST follow this structure. Do NOT deviate from it.

### The proof skeleton

```coq
  (* Execution goal — normalize the hypothesis, do NOT reconstruct by hand *)
  unfold wrapper_name in H at 1.
  prog_nf in H.          (* <-- ALWAYS run this after unfolding *)
  (* if loop combinator: *)
  unfold_loop in H.
  prog_nf in H.          (* <-- ALWAYS run this after unfold_loop *)
  (* if branching: *)
  safe_choice_l H.       (* or safe_choice_r H *)
  ...
  dump_pre_spatial.      (* eliminate spatial predicate: trans Pre \vdash \text{Exec}(\text{Pre}, c, \text{Post}) into \text{Exec}(\text{Pre}, c, \text{Post}) *)
  exact H.               (* finish when hypothesis matches goal *)
```

### Mandatory rules

1. **On the execution side, ALWAYS use `prog_nf in H`** after every `unfold` or `unfold_loop`. This is the single most important tactic. It normalizes the program in the hypothesis to a form that can be matched directly or branched on.
2. **Use `safe_choice_l H` or `safe_choice_r H`** when the normalized hypothesis contains a `choice`. Pick the branch that matches the goal based on context.
3. **Finish with `dump_pre_spatial. exact H.`** when the normalized hypothesis matches the goal.

### When `unfold` is allowed in a `safeExec` goal

The restricted unfolding rules apply **only** when the current goal is of the form `Pre |-- [| safeExec ?P prog X |]` and `safeExec ?P prog X`. In that case:
- **`unfold` should be used with `at 1`**
- **You may `unfold` in the goal** only when `prog` is a direct wrapper application, i.e., `some_def arg1 arg2 ...`. This means `prog` is an opaque name applied to arguments — not yet a compound program expression like sequencing (`x <- ... ;; ...`), branching (`choice`), or looping (`repeat_break`).
- **Do NOT `unfold` in the goal** when `prog` is already one of these compound forms. In that case, work in the hypothesis instead.
- **Name alignment:** Sometimes the hypothesis and goal have the same compound structure (both are sequencing, both are looping, etc.) but differ in a component name. For example, the hypothesis has `safeExec ?P (x <- m1 args ;; m2) X` while the goal has `safeExec ?P (x <- m1' args' ;; m2) X`, where `m1' args'` is definitionally equal to `m1 args`. In this case, use `change (m1' args') with (m1 args)` in the goal to align the names, then `exact H`.

For any goal that is **not** of the form `safeExec ?P (...) X` or `safeExec ?P prog X`, you are free to use `unfold` and any standard Rocq tactics without restriction.

### FORBIDDEN patterns — do NOT do these

- **Do NOT use `safeExec_bind_reta`, `safeExec_bind`, or any manual `safeExec` reconstruction lemma.** These are low-level and almost never needed. Use `prog_nf in H` instead — it handles bind reassociation, choice distribution, and ret-bind simplification automatically.
- **Do NOT unfold `safeExec`-related definitions before `split_pure_spatial`.** The unfolding belongs to the execution side, after the spatial side has been separated out. (Spatial definitions may be unfolded before `split_pure_spatial` when needed.)
- **Do NOT skip `prog_nf in H`.** After any `unfold ... in H at 1` or `unfold_loop in H`, you MUST run `prog_nf in H`. Skipping it leads to an unnormalized hypothesis that cannot be matched.
- **Do NOT `assert (Hs : safeExec ...)`** to introduce a new execution fact by hand. The existing hypothesis already contains the correct execution fact — normalize it instead.
- **Do NOT `unfold ... in *`** (star) for definitions involved in `safeExec`. Unfold in the hypothesis `H` or in the goal (when allowed by the rules above), not both at once. When the program in the goal is already a compound form (sequencing, branching, or looping), work in the hypothesis instead.
- **Do NOT use `eapply safeExec_bind_reta`** or similar manual bind manipulation. This is the most common mistake. `prog_nf` does this automatically and correctly.


## Tactics for solving the execution predicate

The execution predicate is a structured pure proposition.  The tactics below are the ONLY tactics you should use for `safeExec` goals.

**IMPORTANT: `prog_nf` is the central tactic for `safeExec` goals. You MUST use it after every `unfold` or `unfold_loop` in a hypothesis. Do NOT skip it. Do NOT substitute manual bind manipulation lemmas for it.**

**Note:** Goals that are NOT of the form `safeExec ?P (...) X` (e.g., arithmetic inequalities, list properties, guard conditions) should be solved with normal Rocq tactics — `unfold`, `auto`, `lia`, `discriminate`, `congruence`, etc. The restrictions below apply only to `safeExec` goals.

1. `unfold`: Rocq's standard tactic to expand a definition, either in the goal or selected hypotheses.

    Example:
    ```
    1 goal
      
    X : list Z -> unit -> Prop
    l3_2 : list Z
    x_data : Z
    l1_new : list Z
    y_data : Z
    l2_new : list Z
    H : x_data < y_data
    H4 : safeExec ATrue (merge_from_mid_rel (x_data :: l1_new) (y_data :: l2_new) l3_2) X
    ============================
    Pre |-- safeExec ATrue (merge_from_mid_rel l1_new (y_data :: l2_new) (l3_2 +:: x_data)) X
    ```
    After `unfold merge_from_mid_rel in H4 at 1.` (NOT `in *`):
    ```
    1 goal
      
    X : list Z -> unit -> Prop
    l3_2 : list Z
    x_data : Z
    l1_new : list Z
    y_data : Z
    l2_new : list Z
    H : x_data < y_data
    H4 : safeExec ATrue (repeat_break merge_body (x_data :: l1_new, y_data :: l2_new, l3_2)) X
    ============================
    Pre |-- safeExec ATrue (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X
    ```

2. `unfold_loop in`: rewrites loop constructors such as `repeat_break` using its unfolding lemma inside the specified hypothesis or goal.

    After `unfold_loop in H4.`:
    ```
    1 goal
      
    X : list Z -> unit -> Prop
    l3_2 : list Z
    x_data : Z
    l1_new : list Z
    y_data : Z
    l2_new : list Z
    H : x_data < y_data
    H4 :
    safeExec ATrue
    (x <- merge_body (x_data :: l1_new, y_data :: l2_new, l3_2) ;;
    match x with
    | by_continue a0 => repeat_break merge_body a0
    | by_break b0 => return b0
    end) X
    ============================
    Pre |-- safeExec ATrue (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X
    ```

3. `prog_nf`: repeatedly reassociates binds, distributes bind over `choice`, and simplifies `ret`-binds to reach a simpler normal form. **This is the most important tactic for execution goals. ALWAYS use it.**

    3.1 with no arguments, normalizes the program inside the execution predicate in the goal.

    3.2 with `in H`, normalizes the program inside the execution predicate in hypothesis `H`.


    After `unfold merge_body in H4 at 1; prog_nf in H4.`:
    ```
    1 goal
      
    X : list Z -> unit -> Prop
    l3_2 : list Z
    x_data : Z
    l1_new : list Z
    y_data : Z
    l2_new : list Z
    H : x_data < y_data
    H4 :
      safeExec ATrue
        (choice
          (assume!! (x_data <= y_data) ;; repeat_break merge_body
                                            (l1_new, y_data :: l2_new, l3_2 +:: x_data))
          (assume!! (y_data <= x_data) ;; repeat_break merge_body
                                            (x_data :: l1_new, l2_new, l3_2 +:: y_data))) X
    ============================
    Pre |--  safeExec ATrue (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X
    ```

4. `safe_choice_l` / `safe_choice_r`: when the program in hypothesis `H` is a `choice` of two `assume!!`-guarded branches, picks the left/right branch and leaves the corresponding `assume!!` proposition as a separate subgoal (it tries `auto` first, but the subgoal often remains).

    Pick the branch whose `assume!!` matches the current context. The basic shape is:

    ```
    H : safeExec ?P (choice (assume!! cond_l ;; prog_l)
                            (assume!! cond_r ;; prog_r)) X
    ============================
    Pre |-- safeExec ?P prog_target X
    ```

    After `safe_choice_l H.` two subgoals appear:
    - **subgoal 1** (execution side): the goal is unchanged (`Pre |-- safeExec ?P prog_target X`), but the hypothesis is now `H : safeExec ?P prog_l X` — close with `dump_pre_spatial. exact H.` when `prog_l` matches `prog_target` (definitionally).
    - **subgoal 2** (the `assume!!` proposition): `cond_l` — a plain Rocq proposition, NOT a `safeExec` goal.

    **Worked example.** Starting from
    ```
    H : x_data < y_data
    H4 :
      safeExec ATrue
        (choice (assume!! (x_data <= y_data) ;; repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data))
                (assume!! (y_data <= x_data) ;; repeat_break merge_body (x_data :: l1_new, l2_new, l3_2 +:: y_data))) X
    ============================
    Pre |-- safeExec ATrue (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X
    ```
    `safe_choice_l H4.` succeeds: subgoal 1 matches `H4`, and subgoal 2 (`x_data <= y_data`) is internally tried with `auto`, which discharges it from `H : x_data < y_data` — so subgoal 2 disappears and only the execution subgoal remains. (In general, if `auto` cannot close the `assume!!` subgoal, it is left for you to discharge manually as described below.) The wrong choice `safe_choice_r H4.` would leave subgoal 1 with `repeat_break merge_body (x_data :: l1_new, l2_new, l3_2 +:: y_data)` — *not* matching the goal — and the unsolvable `y_data <= x_data` as subgoal 2.

    **Solving the `assume!!` subgoal (subgoal 2).** This is a plain Rocq proposition — use normal Rocq tactics freely: `unfold`, `simpl`, `auto`, `lia`, `discriminate`, `congruence`, etc. Typically it is an inequality, a list non-emptiness, or a guard condition.

    ---

    **Prerequisite — make the `assume!!` propositions concrete and decidable.**
    `safe_choice_l/r` is only useful once the `assume!!` arguments are concrete propositions you can read. Two situations require preparation *before* you call `safe_choice_l/r`:

    *(a) Opaque guard wrappers.* When the hypothesis has the shape
    ```
    choice (assume!! (wrapper_name args) ;; ...)
           (assume!! (~ wrapper_name args) ;; ...)
    ```
    the `assume!!` propositions are opaque names. Unfold the guard wrapper and re-normalize first:
    ```coq
    unfold wrapper_name in H at 1.
    prog_nf in H.
    safe_choice_l H.   (* or safe_choice_r H *)
    ```
    After the unfold, `assume!!` carries a concrete proposition (e.g. `x <> 0`, `x <= y`, `l <> nil`).

    *(b) Branch condition not derivable from the current context.* If neither `cond_l` nor `cond_r` follows from the existing hypotheses, the deciding fact is still buried in the spatial part of the precondition (e.g. "`sll p l` with `p <> 0` implies `l <> nil`"). Use `sep_apply_left LEMMA` on the goal `Pre |-- [| safeExec ... |]` to add the pure consequence into `Pre`, then `Intros` it into the context:
    ```coq
    sep_apply_left (sll_not_zero' p l H_p_neq_zero).   (* adds [| l <> nil |] to Pre *)
    Intros.                                            (* moves it into the context *)
    safe_choice_r H.                                   (* or safe_choice_l H *)
    ```
    For more on `sep_apply_left` and a catalog of representative lemmas, see [spatial_proof_tutorial.md](./spatial_proof_tutorial.md).

5. Handling `assert` / `assertS` in the hypothesis. Unlike `assume!!`, an `assert` is a *forward* obligation: solving the lemma extracts the asserted fact for you to use.

    - Lemmas:
      ```coq
      safeExec_assert_seq  : safeExec P (assert  B ;; c) X -> B /\ safeExec P c X.
      safeExec_assertS_seq : safeExec P (assertS B ;; c) X -> safeExec (fun s => B s /\ P s) c X.
      ```

    - `assert B ;; c`: covered by the unified `safe_step H` — peels the prefix and gives a fresh hypothesis `B`.
    - `assertS B ;; c`: no tactic; apply the lemma manually:
      ```coq
      apply safeExec_assertS_seq in H.
      (* H : safeExec (fun s => B s /\ P s) c X *)
      ```

6. Handling state primitives (`get` / `get'` / `update` / `update'`) in the hypothesis. Coverage is uneven — `get` and `update'` have both bare-program and `_bind` lemmas, `get'` has only the bare-program lemma, and the relational `update` has none.

    Bare-program (program *is* a single primitive, possibly under `prog_nf`):
    ```coq
    safeExec_get  : (forall s, P s -> Pa s a) ->
                    safeExec P (get Pa) X  -> safeExec P (ret a) X.
    safeExec_get' : (forall s, P s -> a = f s) ->
                    safeExec P (get' f) X  -> safeExec P (ret a) X.
    safeExec_update' : safeExec P (update' f) X ->
                       safeExec (fun s => exists s0, s = f s0 /\ P s0) (ret tt) X.
    (* no safeExec_update for the relational `update` *)
    ```

    Sequenced (program is `prim ;; c`):
    ```coq
    safeExec_get_bind     : (forall s, P s -> Pa s a) ->
                            safeExec P (a0 <- get Pa ;; c a0) X ->
                            safeExec P (c a) X.
    safeExec_update'_bind : safeExec P (update' f ;; c) X ->
                            safeExec (fun s => exists s0, s = f s0 /\ P s0) c X.
    (* no safeExec_get'_bind, no safeExec_update_bind *)
    ```

    Typical usage:
    ```coq
    (* relational get, sequenced — supply the value `a` and prove Pa s a *)
    apply safeExec_get_bind with (a := the_concrete_value) in H.
    2: { intros s HP; (* prove Pa s the_concrete_value from P s *) ... }
    (* H : safeExec P (c the_concrete_value) X *)

    (* functional update, sequenced — strengthens the precondition *)
    apply safeExec_update'_bind in H.
    (* H : safeExec (fun s => exists s0, s = f s0 /\ P s0) c X *)

    (* functional get, bare — reduces program to `ret a` *)
    apply safeExec_get' with (a := f s_witness) in H. 2: { intros s HP; reflexivity. }
    ```

    For `get' f ;; c` (no `_bind` lemma): rewrite via `safeExec_bind_reta` with `safeExec_get'` as the inner step, or first do `safeExec_get'` after pulling the bind apart with `prog_nf`. For `update P ;; c` (relational update, no lemma at all): consider rewriting to `update' f` if a functional witness `f` exists, otherwise reason at the `safeExec` level directly.

### Default workflow for solving `safeExec` goal

For solving the `safeExec` goal, first identify the hypothesis that carries the execution fact, for example a hypothesis named `H` of the form `safeExec ...`.

Work in that hypothesis first.

This section assumes you are already on the isolated `safeExec` subgoal. If the proof state is still a mixed separation-logic entailment, do not start unfolding the execution hypothesis yet; finish witness selection, call `split_pure_spatial`, discharge the spatial side, then run `split_pure_and_solve` on the pure side to isolate the leftover `safeExec` obligation.

The steps are:

1. `unfold wrapper_name in H at 1.` — unfold only the concrete wrapper, or if a loop combinator `repeat_break` appears, use `unfold_loop in H`
2. **`prog_nf in H.`** — ALWAYS run this. It normalizes binds, distributes choice, simplifies ret-binds.
3. If the hypothesis `H: safeExec P prog X` now matches the goal `Pre |-- safeExec P prog X`: `dump_pre_spatial. exact H.`
4. If the hypothesis contains a `choice`: use `safe_choice_l H` or `safe_choice_r H` to pick the correct branch.

The common patterns are:

```coq
(* for wrapper definitions *)
unfold some_definition in H at 1.
prog_nf in H.
dump_pre_spatial.
exact H.
```

```coq
(* for loop combinators *)
unfold_loop in H.
prog_nf in H.
(* if branching: *)
unfold loop_body_name in H at 1.
prog_nf in H.
safe_choice_l H.  (* or safe_choice_r *)
dump_pre_spatial.
exact H.
```

You may also unfold in the goal when the goal's program is a direct wrapper application (i.e., `safeExec ?P (some_def args) X`). Do NOT unfold in the goal when the program is already a `bind`, `choice`, or `repeat_break`.

In particular:

- do NOT skip `prog_nf in H` once the wrapper or loop has been unfolded
- prefer `prog_nf in H` over manual reconstruction lemmas for `safeExec`
- prefer `exact H` after normalization when the hypothesis already matches the goal
- do NOT introduce a new auxiliary `safeExec` fact unless the normalized existing hypothesis is genuinely insufficient
- subgoals from `safe_choice_l/r` that are plain propositions (not `safeExec`) should be solved with normal Rocq tactics
- Do not introduce an auxiliary statement such as `assert (Hs : safeExec ...)` unless the direct normalization approach fails.

