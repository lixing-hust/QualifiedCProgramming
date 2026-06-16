# A tutorial for proving generated VCs with the execution predicate $\text{Exec}(\text{Pre}, c, \text{Post})$

This is a tutorial to illustrate how to prove program refinement with the execution predicate $\text{Exec}(\text{Pre}, c, \text{Post})$

## MANDATORY proof workflow — read this first

Every refinement VC proof MUST follow this structure. Do NOT deviate from it.

### The proof skeleton

```coq
pre_process.
(* 1. Choose witnesses *)
Exists ... .
(* 2. Optional spatial normalization *)
simpl ... .
(* 3. Split spatial and execution sides *)
split_pure_spatial.
- (* 4. Spatial goal *)
  ...
- (* 5. Execution goal — normalize the hypothesis, do NOT reconstruct by hand *)
  unfold wrapper_name in H at 1.
  prog_nf in H.          (* <-- ALWAYS run this after unfolding *)
  (* if loop combinator: *)
  unfold_loop in H.
  prog_nf in H.          (* <-- ALWAYS run this after unfold_loop *)
  (* if branching: *)
  safe_choice_l H.       (* or safe_choice_r H *)
  ...
  exact H.               (* finish when hypothesis matches goal *)
```

### Mandatory rules

1. **Start with `pre_process.`** — always.
2. **Choose witnesses and call `split_pure_spatial` BEFORE touching any `safeExec` hypothesis.** Do NOT unfold wrappers before `split_pure_spatial`.
3. **After `split_pure_spatial`, solve the spatial side first** (bullet 1), then the execution side (bullet 2).
4. **On the execution side, ALWAYS use `prog_nf in H`** after every `unfold` or `unfold_loop`. This is the single most important tactic. It normalizes the program in the hypothesis to a form that can be matched directly or branched on.
5. **Finish with `exact H`** when the normalized hypothesis matches the goal.
6. **Use `safe_choice_l H` or `safe_choice_r H`** when the normalized hypothesis contains a `choice`. Pick the branch that matches the goal based on context.

### When `unfold` is allowed in a `safeExec` goal

The restricted unfolding rules apply **only** when the current goal is of the form `safeExec ?P prog X`. In that case:
- **`unfold` should be used with `at 1`**
- **You may `unfold` in the goal** only when `prog` is a direct wrapper application, i.e., `some_def arg1 arg2 ...`. This means `prog` is an opaque name applied to arguments — not yet a compound program expression like sequencing (`x <- ... ;; ...`), branching (`choice`), or looping (`repeat_break`).
- **Do NOT `unfold` in the goal** when `prog` is already one of these compound forms. In that case, work in the hypothesis instead.
- **Name alignment:** Sometimes the hypothesis and goal have the same compound structure (both are sequencing, both are looping, etc.) but differ in a component name. For example, the hypothesis has `safeExec ?P (x <- m1 args ;; m2) X` while the goal has `safeExec ?P (x <- m1' args' ;; m2) X`, where `m1' args'` is definitionally equal to `m1 args`. In this case, use `change (m1' args') with (m1 args)` in the goal to align the names, then `exact H`.

For any goal that is **not** of the form `safeExec ?P (...) X`, you are free to use `unfold` and any standard Rocq tactics without restriction.

### FORBIDDEN patterns — do NOT do these

- **Do NOT use `safeExec_bind_reta`, `safeExec_bind`, or any manual `safeExec` reconstruction lemma.** These are low-level and almost never needed. Use `prog_nf in H` instead — it handles bind reassociation, choice distribution, and ret-bind simplification automatically.
- **Do NOT unfold `safeExec`-related definitions before `split_pure_spatial`.** The unfolding belongs to the execution side, after the spatial side is separated. (Spatial definitions may be unfolded before `split_pure_spatial` when needed.)
- **Do NOT skip `prog_nf in H`.** After any `unfold ... in H at 1` or `unfold_loop in H`, you MUST run `prog_nf in H`. Skipping it leads to an unnormalized hypothesis that cannot be matched.
- **Do NOT `assert (Hs : safeExec ...)`** to introduce a new execution fact by hand. The existing hypothesis already contains the correct execution fact — normalize it instead.
- **Do NOT `unfold ... in *`** (star) for definitions involved in `safeExec`. Unfold in the hypothesis `H` or in the goal (when allowed by the rules above), not both at once. When the program in the goal is already a compound form (sequencing, branching, or looping), work in the hypothesis instead.
- **Do NOT use `eapply safeExec_bind_reta`** or similar manual bind manipulation. This is the most common mistake. `prog_nf` does this automatically and correctly.

## Generated VCs are separation-logic entailments: $\forall \vec{a}.\, P(\vec{a}) \vdash Q(\vec{a})$ 

### The syntax of an assertion 

We use linear separation logic assertions with the following grammar (informally):

```
A ::= [| P |]                          (pure proposition)
    | TT                               (true)
    | emp                              (empty heap)
    | e # T |-> v                      (points-to, `T` is the type)
    | Pred e1 ... en                   (user-defined heap predicate)
    | A && A                           (logical conjunction)
    | A || A                           (logical disjunction)
    | A ** A                           (separating conjunction)
    | A -* A                           (separating implication)
    | EX x: T, A                       (existential quantification)
    | ALL x: T, A                      (universal quantification)
```

Here `P` is a pure proposition over program expressions (e.g., equalities and arithmetic),
`e`/`v` are expressions, `T` is a type (e.g., `Int`, `Ptr`), and `Pred` ranges over the
separating predicates defined below (e.g., `sll`, `sllseg`, `dlistrep`, `dllseg`).

## Tactics for solving the execution predicate

The execution predicate is a structured pure proposition. After `split_pure_spatial`, it can be extracted from the right-hand side and appear as a standalone goal. The tactics below are the ONLY tactics you should use for `safeExec` goals.

**IMPORTANT: `prog_nf` is the central tactic for `safeExec` goals. You MUST use it after every `unfold` or `unfold_loop` in a hypothesis. Do NOT skip it. Do NOT substitute manual bind manipulation lemmas for it.**

**Note:** Goals that are NOT of the form `safeExec ?P (...) X` (e.g., arithmetic inequalities, list properties, guard conditions) should be solved with normal Rocq tactics — `unfold`, `auto`, `lia`, `discriminate`, `congruence`, etc. The restrictions below apply only to `safeExec` goals.

1. `unfold`: Rocq's standard tactic to expand a definition, either in the goal or selected hypotheses.

    Example:
    ```proof state
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
    safeExec ATrue (merge_from_mid_rel l1_new (y_data :: l2_new) (l3_2 +:: x_data)) X
    ```
    After `unfold merge_from_mid_rel in H4 at 1.` (NOT `in *`):
    ```proof state
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
    safeExec ATrue (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X
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
    safeExec ATrue (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X
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
      safeExec ATrue
        (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X
    ```

4. `safe_choice_l` or `safe_choice_r`: chooses the left or right branch of the program in hypothesis `H` and extracts the corresponding `assume!!` proposition as a separate subgoal (it tries to solve it with `auto`, but often it remains).

    You should choose the correct branch according to the context.

    After `safe_choice_l H4.`:
    ```
    2 goals
      
      X : list Z -> unit -> Prop
      l3_2 : list Z
      x_data : Z
      l1_new : list Z
      y_data : Z
      l2_new : list Z
      H : x_data < y_data
      H4 :
        safeExec ATrue
          (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X
      ============================
      safeExec ATrue
        (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X

    goal 2 is:
    x_data <= y_data
    ```

    Goal 1 is the execution side — solve it with `exact H4.` since H4 now matches.
    Goal 2 is the `assume!!` proposition — solve it with normal Rocq tactics (see below).

    However, if you choose to `safe_choice_r H4`, then the goal becomes
    ```
    2 goals
  
    X : list Z -> unit -> Prop
    l3_2 : list Z
    x_data : Z
    l1_new : list Z
    y_data : Z
    l2_new : list Z
    H : x_data < y_data
    H4 :
      safeExec ATrue
        (repeat_break merge_body (x_data :: l1_new, l2_new, l3_2 +:: y_data)) X
    ============================
    safeExec ATrue
      (repeat_break merge_body (l1_new, y_data :: l2_new, l3_2 +:: x_data)) X

    goal 2 is:
    y_data <= x_data
    ```
    which is apparently unsolvable.

    **Solving the `assume!!` subgoal:** After `safe_choice_l/r`, the extracted `assume!!` proposition becomes a standalone subgoal (goal 2 in the examples above). This is a plain Rocq proposition — it is NOT a `safeExec` goal. Use normal Rocq tactics freely: `unfold`, `simpl`, `auto`, `lia`, `discriminate`, `congruence`, etc. The proposition may involve definitions that need unfolding — feel free to unfold them. Typically the subgoal is something like an inequality, a list non-emptiness, or a guard condition.

## Proof workflow for mixed goals

A generated VC often splits conceptually into two parts:

- a spatial entailment that reshapes the separation-logic predicates
- a pure `safeExec` obligation that describes the next abstract program state

For generated refinement VCs, the most stable workflow is:

1. choose the existing witnesses that determine the abstract state
2. do lightweight spatial normalization if needed, for example `simpl sllseg`
3. call `split_pure_spatial` early
4. solve the spatial side
5. only after that, solve the isolated `safeExec` side

This is usually better than trying to push the `safeExec` side first. In particular, prefer rewriting the existing `safeExec` hypothesis over constructing a fresh execution fact by hand.

In particular, do **not** unfold a wrapper in the safeExec hypothesis at the beginning of a mixed entailment proof.
That unfolding belongs to the `safeExec` side, after `split_pure_spatial` has separated the spatial cleanup
from the execution obligation.


### Default workflow for solving `safeExec` goal

For solving the `safeExec` goal, first identify the hypothesis that carries the execution
fact, for example a hypothesis named `H` of the form `safeExec ...`.

Work in that hypothesis first.

This section assumes you are already on the isolated `safeExec` subgoal. If the proof state is
still a mixed separation-logic entailment, do not start unfolding the execution hypothesis yet;
finish witness selection, call `split_pure_spatial`, and discharge the spatial side first.

The steps are:

1. `unfold wrapper_name in H at 1.` — unfold only the concrete wrapper, or if a loop combinator `repeat_break` appears, use `unfold_loop in H`
2. **`prog_nf in H.`** — ALWAYS run this. It normalizes binds, distributes choice, simplifies ret-binds.
3. If the hypothesis now matches the goal: `exact H.`
4. If the hypothesis contains a `choice`: use `safe_choice_l H` or `safe_choice_r H` to pick the correct branch.

The common patterns are:

```coq
(* for wrapper definitions *)
unfold some_definition in H at 1.
prog_nf in H.
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
exact H.
```

You may also unfold in the goal when the goal's program is a direct wrapper application (i.e., `safeExec ?P (some_def args) X`). Do NOT unfold in the goal when the program is already a `bind`, `choice`, or `repeat_break`.

In particular:

- do NOT skip `prog_nf in H` once the wrapper or loop has been unfolded
- prefer `prog_nf in H` over manual reconstruction lemmas for `safeExec`
- prefer `exact H` after normalization when the hypothesis already matches the goal
- do NOT introduce a new auxiliary `safeExec` fact unless the normalized existing hypothesis is genuinely insufficient
- subgoals from `safe_choice_l/r` that are plain propositions (not `safeExec`) should be solved with normal Rocq tactics

### Fast path for simple entail-witness goals

Some witness lemmas have a very small spatial component. In that case, the proof often has the following shape:

```coq
pre_process.
Exists ... .
simpl ... .
split_pure_spatial.
- (* spatial goal *) ... 
- (* the execution side  *)
  unfold wrapper in H at 1.
  prog_nf in H.
  unfold_loop in H.
  prog_nf in H.
  ...
  exact H.
```

The key sequencing point is that `unfold wrapper in H` is part of the second bullet, not something
to do immediately after `pre_process`. A script of the form

```coq
pre_process.
unfold wrapper in H.
...
Exists ... .
split_pure_spatial.
```

is usually the wrong shape for these refinement goals.

This pattern is a good default when:

- the right-hand witnesses are already clear
- the spatial side only needs minor cleanup
- the execution goal is expected to match a normalized hypothesis directly

In this situation, do not introduce an auxiliary statement such as
`assert (Hs : safeExec ...)` unless the direct normalization approach fails.


### When not to force the split

Do not treat "solve separation logic first, then solve `safeExec`" as a rigid recipe.

A common failure mode is:

1. choose witnesses too early
2. call `split_pure_spatial`
3. get a `safeExec` goal in the wrong state shape
4. spend many steps trying generic rewrites that do not match the generated program

Another common failure mode is:

1. unfold a wrapper in the execution hypothesis before the `safeExec` side is isolated
2. skip `prog_nf in H`
3. manually rebuild the execution fact with low-level lemmas like `safeExec_bind_reta`
4. end up proving a more complicated statement than the original goal asked for

If that happens, go back and re-check:

- the witness order
- the loop-state tuple
- whether the current goal really matches the unfolded program structure you intend to prove
- whether the existing execution hypothesis would become usable immediately after `prog_nf in H`

Trying to push the `safeExec` proof too early often makes the obligation look more complicated than it really is, because the abstract state usually only matches cleanly after the spatial part has been rewritten.