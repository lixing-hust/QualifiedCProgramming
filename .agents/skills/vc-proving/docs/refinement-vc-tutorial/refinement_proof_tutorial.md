# A tutorial for proving generated VCs with the execution predicate $\text{Exec}(\text{Pre}, c, \text{Post})$

**Generated VCs are separation-logic entailments: $\forall \vec{a}.\, P(\vec{a}) \vdash Q(\vec{a})$**

This is a tutorial to illustrate how to prove refinement VCs which involves the execution predicate $\text{Exec}(\text{Pre}, c, \text{Post})$

## MANDATORY proof workflow — read this first

Every refinement VC proof MUST follow this structure. Do NOT deviate from it.

### The proof skeleton

```coq
pre_process.
(* 0. address equalities *)
subst_eqs.
(* 1. Choose witnesses *)
Exists ... .  (*if cannot find witness, use eExists. *)
(* 2. Split spatial and pure facts sides *)
split_pure_spatial.
- (* 3. Spatial goal of the form Pre |-- Q1 ** Q2 ** ... ** Qn; use allowed spatial tactics such as cancel and sep_apply. *)
  (* solve the spatial side with allowed spatial tactics *)
  ...
- (* 4. pure facts sides (including execution goal) of the form `Pre |-- [| safeExec ... |] && [| ... |] && ... && [| ... |]` *)
  (* 4.1 split each pure conjunct into its own subgoal and discharge the easy ones with auto *)
  split_pure_and_solve.
  (* Any leftover subgoals fall into one of the two shapes below. *)
  (* 4.2 Leftover execution goal Pre |-- [| safeExec ... |] — normalize the hypothesis, do NOT reconstruct by hand *)
  ...
  (* 4.3 Leftover non-execution pure fact Pre |-- [| ... |] — solve with normal Rocq tactics *)
  ...
```

### Mandatory rules

1. **Start with `pre_process.`** — always.
2. **Choose witnesses and call `split_pure_spatial` BEFORE touching any `safeExec` hypothesis.** Do NOT unfold wrappers before `split_pure_spatial`.
3. **After `split_pure_spatial`, solve the spatial side first** (bullet 1), then the pure / execution side (bullet 2).
4. **spatial side Must refer spatial tutorial** in [spatial_proof_tutorial.md](./spatial_proof_tutorial.md)
5. **execution side Must refer execution tutorial** in [safeExec_proof_tutorial.md](./safeExec_proof_tutorial.md)


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
separating predicates defined in [spatial_proof_tutorial.md](./spatial_proof_tutorial.md).

## Preparation tactics 

1. `pre_process`: unfolds the VC and normalizes the assertion; typically used at the start of a VC proof.

    Example:
    ```
    1 goal
  
    ============================
    sll_append_entail_wit_1
    ```
    After `pre_process.`:
    ```
    1 goal

    H : l1 = x :: l0
    y : Z
    ...
    ============================
    &( x_pre # "list" ->ₛ "next") # Ptr |-> y **
    (sll y l0 **
    (&( x_pre # "list" ->ₛ "data") # Int |-> x ** sll y_pre l2_2))
    |-- EX t_next : Z,
        EX l1_2 : list Z,
        EX l2 : list Z,
        EX l3 : list Z,
        EX w : Z,
        [|safeExec ATrue
            (x <- sll_append_M_loop l1_2 l2 l3 w ;;
            sll_append_M_loop_end x) X|] && [|x_pre <> 0|] &&
        [|t_next = y|] && [|l1 = x :: l0|] && [|x_pre <> 0|] &&
        &( x_pre # "list" ->ₛ "next") # Ptr |-> t_next **
        &( x_pre # "list" ->ₛ "data") # Int |-> w ** 
        sll y_pre l1_2 ** sll y l2 ** sllseg x_pre x_pre l3
    ```

2. `subst_eqs`: handles variable equalities (`x = e`) and injective-constructor equalities (`_ :: _ = _ :: _`, `(_,_) = (_,_)`, `Some _ = Some _`) in the context, peeling them to variable equalities and then `subst`-ing. Use at step 0, right after `pre_process`.

    After `subst_eqs.`:
    ```
    1 goal

    y : Z
    ...
    ============================
    &( x_pre # "list" ->ₛ "next") # Ptr |-> y **
    (sll y l0 **
    (&( x_pre # "list" ->ₛ "data") # Int |-> x ** sll y_pre l2_2))
    |-- EX t_next : Z,
        EX l1_2 : list Z,
        EX l2 : list Z,
        EX l3 : list Z,
        EX w : Z,
        [|safeExec ATrue (x <- sll_append_M_loop l1_2 l2 l3 w ;; sll_append_M_loop_end x) X|] && [|x_pre <> 0|] &&
        [|t_next = y|] && [|x :: l0 = x :: l0|] && [|x_pre <> 0|] &&
        &( x_pre # "list" ->ₛ "next") # Ptr |-> t_next **
        &( x_pre # "list" ->ₛ "data") # Int |-> w ** 
        sll y_pre l1_2 ** sll y l2 ** sllseg x_pre x_pre l3
    ```

3. `Exists`: instantiates the first existential on the right-hand side with the given witness.
    
    After `Exists y. Exists l2_2. Exists l0.Exists nil.`:
    ```
    1 goal
    
    ...
    ============================
    &( x_pre # "list" ->ₛ "next") # Ptr |-> y **
    (sll y l0 ** (&( x_pre # "list" ->ₛ "data") # Int |-> x ** sll y_pre l2_2))
    |-- EX w : Z,
        [|safeExec ATrue (x <- sll_append_M_loop l2_2 l0 nil w ;; sll_append_M_loop_end x) X|] &&
        [|x_pre <> 0|] && [|y = y|] && [|x :: l0 = x :: l0|] && [|x_pre <> 0|] &&
        &( x_pre # "list" ->ₛ "next") # Ptr |-> y ** &( x_pre # "list" ->ₛ "data") # Int |-> w **
        sll y_pre l2_2 ** sll y l0 ** sllseg x_pre x_pre nil
    ```

4. `eExists`: like `Exists` but leaves the witness as a fresh evar, to be resolved later by unification. Use when the witness is not yet known at the point of instantiation

    After `eExists.`:
    ```
    1 goal
    
    ...
    ============================
    &( x_pre # "list" ->ₛ "next") # Ptr |-> y **
    (sll y l0 ** (&( x_pre # "list" ->ₛ "data") # Int |-> x ** sll y_pre l2_2))
    |-- [|safeExec ATrue (x <- sll_append_M_loop l2_2 l0 nil ?x ;; sll_append_M_loop_end x) X|] &&
        [|x_pre <> 0|] && [|y = y|] && [|x :: l0 = x :: l0|] && [|x_pre <> 0|] &&
        &( x_pre # "list" ->ₛ "next") # Ptr |-> y ** &( x_pre # "list" ->ₛ "data") # Int |-> ?x **
        sll y_pre l2_2 ** sll y l0 ** sllseg x_pre x_pre nil

    ```

    there `?x` is a fresh evar, which should be instantiated later


5. `split_pure_spatial`: splits the RHS of an entailment of the form `Pre |-- pure_part && spatial_part`  into two independent subgoals — one containing only spatial conjuncts, one containing only the pure `[| ... |]` conjuncts (which include the `safeExec` obligation). 

   Use it at step 2 of the mandatory skeleton, *after* `Exists ...`. 

   `split_pure_spatial.` produces two subgoals:
    ```
    2 goals
    
    ...
    ============================
    (* spatial subgoal *)
    &( x_pre # "list" ->ₛ "next") # Ptr |-> y ** (sll y l0 ** (&( x_pre # "list" ->ₛ "data") # Int |-> x ** sll y_pre l2_2))
    |-- &( x_pre # "list" ->ₛ "next") # Ptr |-> y ** &( x_pre # "list" ->ₛ "data") # Int |-> ?x **
        sll y_pre l2_2 ** sll y l0 ** sllseg x_pre x_pre nil

    goal 2 is:
    (* pure subgoal *)
    &( x_pre # "list" ->ₛ "next") # Ptr |-> y ** (sll y l0 ** (&( x_pre # "list" ->ₛ "data") # Int |-> x ** sll y_pre l2_2))
    |-- [|safeExec ATrue (x <- sll_append_M_loop l2_2 l0 nil ?x ;; sll_append_M_loop_end x) X|] &&
        [|x_pre <> 0|] && [|y = y|] && [|x :: l0 = x :: l0|] && [|x_pre <> 0|]
    ```

6. Manual spatial cleanup: use allowed spatial tactics such as `cancel`, `sep_apply_left`, and `sep_apply_right` to reshape or cancel spatial predicates.

    For the spatial subgoal, after cancelling the matching points-to predicate:
    ```
    1 goal
    
    ...
    ============================
    &( x_pre # "list" ->ₛ "data") # Int |-> x
    |-- &( x_pre # "list" ->ₛ "data") # Int |-> ?x ** sllseg x_pre x_pre nil
    ```

    then this goal can be solved by instantiating the evar, cancelling the matching points-to predicate, and simplifying the empty segment.

7. `split_pure_and_solve`: on a pure RHS of the form `Pre |-- [| P1 |] && [| P2 |] && ... && [| Pn |]`, splits each conjunct into its own subgoal and tries to discharge each with `dump_pre_spatial; auto`. Any conjunct `auto` cannot solve is left as a leftover subgoal for manual handling.

    Use it at step 4.1 of the mandatory skeleton, on the pure side produced by `split_pure_spatial`. The leftover subgoals typically fall into:
    - step 4.2: a `[| safeExec ... |]` execution obligation — see [safeExec_proof_tutorial.md](./safeExec_proof_tutorial.md);
    - step 4.3: other pure facts — discharge with normal Rocq tactics.

    Example. On the pure subgoal produced by `split_pure_spatial` above, `split_pure_and_solve.` leaves only
    ```
    1 goal

    ...
    ============================
    &( x_pre # "list" ->ₛ "next") # Ptr |-> y **
    (sll y l0 ** (&( x_pre # "list" ->ₛ "data") # Int |-> x ** sll y_pre l2_2))
    |-- [|safeExec ATrue (x <- sll_append_M_loop l2_2 l0 nil x ;; sll_append_M_loop_end x) X|]
    ```

## Proof workflow for mixed goals

A generated refinement VC often splits conceptually into two parts:

- a spatial entailment that reshapes the separation-logic predicates
- a pure `safeExec` obligation that describes the next abstract program state

For generated refinement VCs, the most stable workflow is:

0. preparation steps, and address equalities 
1. choose the existing witnesses that determine the abstract state
2. call `split_pure_spatial` to isolate the spatial side from the pure / `safeExec` side
3. solve the spatial side
4. only after that, solve the pure side with `split_pure_and_solve`, and handle any leftover `safeExec` obligation

This is usually better than trying to push the `safeExec` side first. In particular, prefer rewriting the existing `safeExec` hypothesis over constructing a fresh execution fact by hand.

In particular, do **not** unfold a wrapper in the safeExec hypothesis at the beginning of a mixed entailment proof.
That unfolding belongs to the `safeExec` side, after `split_pure_spatial` has separated the spatial cleanup from the execution obligation.

### When not to force the split

Do not treat "solve separation logic first, then solve `safeExec`" as a rigid recipe.

A common failure mode is:

1. choose witnesses too early
2. call `split_pure_spatial`
3. get a `safeExec` goal in the wrong state shape
4. spend many steps trying generic rewrites that do not match the generated program

Another common failure mode is:

1. unfold a wrapper in the execution hypothesis before the `safeExec` side is isolated
2. end up proving a more complicated statement than the original goal asked for

If that happens, go back and re-check:

- the witness order
- the loop-state tuple
- whether the current goal really matches the unfolded program structure you intend to prove

Trying to push the `safeExec` proof too early often makes the obligation look more complicated than it really is, because the abstract state usually only matches cleanly after the spatial part has been rewritten.
