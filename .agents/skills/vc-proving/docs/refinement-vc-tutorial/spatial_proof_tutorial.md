# A tutorial for proving separation-logic entailments $P \vdash Q$

This is a tutorial to illustrate how to separation-logic entailments.

##  Interpretation for user-defined heap predicates

1. `sll p l`: denotes a complete singly linked list starting at address `p`, corresponding in order to all elements of the logical list `l`.
2. `sllseg p q l`: denotes a singly linked list segment from address `p` to address `q`, logically corresponding to the list `l`.
3. `sllbseg x y l`: in memory there exists a singly linked list segment bounded by two second-level pointer endpoints `x` and `y`, and this segment stores all elements of the sequence `l`.
4. `dlistrep p pre l`: denotes a complete doubly linked list starting at address `p`, with predecessor pointer `pre` for the head, and containing all elements of the logical list `l` in order.
5. `dllseg x y xpre ypre l`: denotes a doubly linked list segment from address `x` to address `y`, where the predecessor of `x` is `xpre` and the predecessor of `y` is `ypre`, and the segment logically corresponds to the list `l`.

## Tactics for spatial entailments

The following lists auxiliary tactics, beyond Rocq's standard library, for solving logical entailments.  

1. `pre_process`: unfolds the VC and normalizes the assertion; typically used at the start of a VC proof.

    Example:
    ```
    1 goal
  
    ============================
    sll_strategy18
    ```
    After `pre_process.`:
    ```
    1 goal
    
    l1 : list Z
    p, v1, q : Z
    ============================
    sllbseg p q l1 ** q # Ptr |-> v1
    |-- q # Ptr |-> v1 ** (ALL l2 : list Z, ALL v2 : Z, TT && [|l1 = l2|] && emp ** q # Ptr |-> v2 -* TT && emp ** sllbseg p q l2 ** q # Ptr |-> v2)
    ```

2. Manual spatial cleanup: use allowed spatial tactics such as `cancel`, `sep_apply_left`, and `sep_apply_right` to reshape or cancel spatial predicates.

    After cancelling the matching points-to predicate:
    ```
    1 goal
    
    l1 : list Z
    p, v1, q : Z
    ============================
    sllbseg p q l1
    |-- ALL l2 : list Z, ALL v2 : Z, TT && [|l1 = l2|] && emp ** q # Ptr |-> v2 -* TT && emp ** sllbseg p q l2 ** q # Ptr |-> v2
    ```

3. `Intros_r`: introduces a universally quantified variable from the right-hand side into the context; typically used to instantiate `ALL` in the goal.


    After `Intros_r l2.`:
    ```
    1 goal
    
    l1 : list Z
    p, v1, q : Z
    l2 : list Z
    ============================
    sllbseg p q l1 |-- ALL v2 : Z, TT && [|l1 = l2|] && emp ** q # Ptr |-> v2 -* TT && emp ** sllbseg p q l2 ** q # Ptr |-> v2
    ```

4. `Intros`:

    4.1. with no arguments, it moves a pure proposition from the left-hand assertion into the context.

    4.2. with one argument (e.g., `x`), it instantiates an existential on the left-hand side and introduces the witness into the context.

    Example:
    ```
    1 goal
    
    p, x : Z
    l : list Z
    ============================
    EX x0 : addr, &( p # "list" ->ₛ "data") # Int |-> x ** &( p # "list" ->ₛ "next") # Ptr |-> x0 ** sll x0 l && [|p <> NULL|]
    |-- EX y : Z, (TT && emp ** &( p # "list" ->ₛ "data") # Int |-> x ** &( p # "list" ->ₛ "next") # Ptr |-> y ** sll y l) ** (TT && emp -* TT && emp)
    ```
    After `Intros y.`:
    ```
    1 goal
    
    p, x : Z
    l : list Z
    y : addr
    H : p <> NULL
    ============================
    &( p # "list" ->ₛ "data") # Int |-> x ** (&( p # "list" ->ₛ "next") # Ptr |-> y ** sll y l)
    |-- EX y0 : Z, (TT && emp ** &( p # "list" ->ₛ "data") # Int |-> x ** &( p # "list" ->ₛ "next") # Ptr |-> y0 ** sll y0 l) ** (TT && emp -* TT && emp)
    ```

5. `Exists`: instantiates the first existential on the right-hand side with the given witness.
    
    After `Exists y.`:
    ```
    1 goal
    
    p, x : Z
    l : list Z
    y : addr
    H : p <> NULL
    ============================
    &( p # "list" ->ₛ "data") # Int |-> x ** (&( p # "list" ->ₛ "next") # Ptr |-> y ** sll y l)
    |-- (TT && emp ** &( p # "list" ->ₛ "data") # Int |-> x ** &( p # "list" ->ₛ "next") # Ptr |-> y ** sll y l) ** (TT && emp -* TT && emp)
    ```

6. `cancel P`: eliminates spatial predicates `P` that appear identically on both sides of the entailment; fails if they do not strictly match.

    When the goal is：
    ```
    ...
    ===============================
    sll p l |-- sllseg p p nil ** sll p l
    ```
    After `cancel (sll p l).`：
    ```
    ...
    ===============================
    emp |-- sllseg p p nil
    ```

    **Note**：
    1. The spatial predicate `P` must be strictly (syntactically) identical on both sides; semantic equality is not enough. `cancel` does not perform any simplification.
    2. When the goal reduces to a single identical predicate such as `P |-- P`, `cancel P` closes the goal directly — it does not produce `emp |-- emp`, so there is no need to call `cancel emp` afterwards.


7. `Left` / `Right` / `Split`

    - **`Left`**: turns `P |-- Q || R` into `P |-- Q`
    - **`Right`**: turns `P |-- Q || R` into `P |-- R`
    - **`Split`**: splits `P || Q |-- R` into two subgoals: `P |-- R` and `Q |-- R`

    When the goal is：
    ```
    1 goal

    ===============================
    P |-- Q || R
    ```
    After：`Left.`:
    ```
    1 goal

    ===============================
    P |-- Q
    ```

8. `split_pures.`: splits a conjunction of pure propositions into multiple subgoals so each can be handled individually.

    **Usage**: Always call this at the start of a pure-proposition proof.

    **Example (proof state change)**:

    When the goal is：
    ```
    1 goal 
    ...
    ===============================
    sll p l |-- [| l1 = l2 |] && [| n = 0 |]
    ```
    After`split_pures.`:
    ```
    2 goals 
    ...
    ===============================
    sll p l |-- [| l1 = l2 |]

    goal 2 is:
    sll p l |-- [| n = 0 |]
    ```

9. `dump_pre_spatial`: once all pure-proposition hypotheses are in place, discard the spatial part of the precondition and switch to pure-proposition proof mode. In other words, without changing the hypotheses, transform the proof state from `P |-- [| Q |]` into `Q`.

    When the goal is：
    ```
    1 goal

    ...
    ===============================
    sll p l |-- [| l1 = l2 |]
    ```
    After`dump_pre_spatial.`:
    ```
    1 goal

    ...
    ===============================
    l1 = l2
    ```
    

10. `sep_apply_left`: given a lemma `H : A |-- B`, finds a matching spatial subterm `A` on the **left-hand side** of the entailment, brings it into position, and rewrites it to `B`. This is the forward/weakening direction — it replaces part of the precondition with something it entails.

    When the goal is:
    ```
    1 goal
  
    y, z : addr
    a : Z
    l1, l2 : list Z
    IHl1 : forall x : addr, sllseg x y l1 ** sllseg y z l2 |-- sllseg x z (l1 ++ l2)
    x, z0 : addr
    H : x <> NULL
    ============================
    &( x # "list" ->ₛ "data") # Int |-> a ** (&( x # "list" ->ₛ "next") # Ptr |-> z0 ** (sllseg z0 y l1 ** sllseg y z l2))
    |-- &( x # "list" ->ₛ "data") # Int |-> a ** &( x # "list" ->ₛ "next") # Ptr |-> z0 ** sllseg z0 z (l1 ++ l2) && [|x <> NULL|]
    ```
    After `sep_apply_left IHl1.`
    ```
    1 goal
  
    y, z : addr
    a : Z
    l1, l2 : list Z
    IHl1 : forall x : addr, sllseg x y l1 ** sllseg y z l2 |-- sllseg x z (l1 ++ l2)
    x, z0 : addr
    H : x <> NULL
    ============================
    sllseg z0 z (l1 ++ l2) ** (&( x # "list" ->ₛ "data") # Int |-> a ** &( x # "list" ->ₛ "next") # Ptr |-> z0)
    |-- [|x <> NULL|] && &( x # "list" ->ₛ "data") # Int |-> a ** (&( x # "list" ->ₛ "next") # Ptr |-> z0 ** sllseg z0 z (l1 ++ l2))
    ```

11. `sep_apply_right`: given a lemma `H : A |-- B`, finds a matching subterm `B` on the **right-hand side** of the entailment and replaces it with `A`. This is the backward/strengthening direction — it commits to proving a stronger postcondition.

    Internally, `sep_apply_right` uses `derivable1_trans` + `derivable1_sepcon_mono` (or `derivable1_andp_mono`) rather than setoid-rewriting, so it is robust regardless of what appears on the LHS.

    When the goal is:
    ```
    1 goal
  
    x_pre, t, y : addr
    lprefix_2 : list Z
    v_2 : Z
    ============================
    ... ** sllseg x_pre t lprefix_2 ** &( t # "list" ->ₛ "data") # Int |-> v_2 ** &( t # "list" ->ₛ "next") # Ptr |-> y
    |-- ... ** sllseg x_pre y (lprefix_2 ++ v_2 :: nil)
    ```
    After `sep_apply_right (sllseg_sllseg x_pre t y).`:
    ```
    1 goal
  
    ...
    ============================
    ... ** sllseg x_pre t lprefix_2 ** &( t # "list" ->ₛ "data") # Int |-> v_2 ** &( t # "list" ->ₛ "next") # Ptr |-> y
    |-- ... ** sllseg x_pre t lprefix_2 ** sllseg t y (v_2 :: nil)
    ```
    The RHS `sllseg x_pre y (lprefix_2 ++ v_2 :: nil)` has been replaced by its "pre-image" under `sllseg_sllseg`: the two separate segments `sllseg x_pre t lprefix_2 ** sllseg t y (v_2 :: nil)`, which now cancel against the LHS.

12. `prop_apply_p`: uses a proposition from the precondition to derive a new pure proposition and add it to the precondition. Given a lemma of the form `H: forall x: T, C -> P ** Q |-- [| R |]` and a goal of the form `P ** Q ** M |-- N`, `prop_apply_p (H x C)` adds `[| R |]` to the precondition.

    Note: this tactic requires all variables and hypotheses of the lemma to be explicitly instantiated; otherwise it fails.

    When we have a lemma：
    ```coq
    Lemma sll_not_zero': forall x l,
      x <> NULL ->
      sll x l |-- [| l <> nil |].
    ``` 
    And the goal is：
    ```
    1 goal
    
    p: Z
    l: list
    H: x <> NULL
    ===============================
    sll p l ** Q |-- R
    ```
    After `prop_apply_p (sll_not_zero' p l H).`:
    ```
    1 goal

    p: Z
    l: list
    H: x <> NULL
    ===============================
    [| l <> nil |] && sll p l ** Q |-- R
    ```


#### Representative lemmas for `sep_apply_left`

`sep_apply_left` rewrites a spatial subterm on the LHS using the forward direction of an entailment lemma. You can use Rocq's `Search` to find lemmas for user-defined predicates. Below are representative examples.

0. `store_ptr_undef_store_ptr`

```coq
Lemma store_ptr_undef_store_ptr : p # Ptr |-> v |-- p # Ptr |->_.
```
**sep_apply_left store_ptr_undef_store_ptr**

```
================
p # Ptr |-> v ** M |-- N
```
becomes
```
================
p # Ptr |-> _ ** M |-- N
```


1. `empty_sll`

```coq
Lemma empty_sll : emp |-- sll 0 nil.
```

**sep_apply_left empty_sll**
```
================
emp ** M |-- N
```
becomes
```
================
sll 0 nil ** M |-- N
```

2. `sll_not_zero`

```coq
Lemma sll_not_zero: forall x l,
  x <> NULL ->
  sll x l |--
    EX y a l0,
      [| l = a :: l0 |] &&
      &(x # "list" ->? "data") # Int |-> a **
      &(x # "list" ->? "next") # Ptr |-> y **
      sll y l0.
```

**sep_apply_left (sll_not_zero x l)**
```
H: x <> 0
================
sll x l ** M |-- N
```
becomes
```
H: x <> 0
================
(EX y a l0,
  [| l = a :: l0 |] &&
  &(x # "list" ->? "data") # Int |-> a **
  &(x # "list" ->? "next") # Ptr |-> y **
  sll y l0) ** M |-- N
```

3. `sllseg_sllseg`

```coq
Lemma sllseg_sllseg: forall x y z l1 l2,
  sllseg x y l1 ** sllseg y z l2 |--
  sllseg x z (l1 ++ l2).
```

**sep_apply_left (sllseg_sllseg x y z l1 l2)**
```
================
(sllseg x y l1 ** sllseg y z l2) ** M |-- N
```
becomes
```
================
sllseg x z (l1 ++ l2) ** M |-- N
```

4. `sllbseg_2_sllseg`

```coq
Lemma sllbseg_2_sllseg: forall x y z l,
  sllbseg x y l ** y # Ptr |-> z |--
  EX y': addr, x # Ptr |-> y' ** sllseg y' z l.
```

**sep_apply_left (sllbseg_2_sllseg x y z l)**
```
================
(sllbseg x y l ** y # Ptr |-> z) ** M |-- N
```
becomes
```
================
(EX y': addr, x # Ptr |-> y' ** sllseg y' z l) ** M |-- N
```

5. `sll_zero`

```coq
Lemma sll_zero: forall x l,
  x = NULL ->
  sll x l |-- [| l = nil |] && emp.
```

**sep_apply_left (sll_zero x l eq_refl)** (when `x = 0` is known)
```
================
sll 0 l ** M |-- N
```
becomes
```
================
([| l = nil |] && emp) ** M |-- N
```

Typical use: when the context gives `x = NULL`, turn `sll x l` into a pure fact `l = nil`. Especially useful in return-witness goals where a null tail should correspond to the empty logical list.

6. `sllseg_len1`

```coq
Lemma sllseg_len1: forall x a y,
  x <> NULL ->
  &( x # "list" ->? "data") # Int |-> a **
  &( x # "list" ->? "next") # Ptr |-> y |--
  sllseg x y (a :: nil).
```

Typical use: when one concrete node should become a one-element segment. This often appears before composing that fresh segment with an existing segment.

7. `sllseg_sll`

```coq
Lemma sllseg_sll: forall x y l1 l2,
  sllseg x y l1 ** sll y l2 |--
  sll x (l1 ++ l2).
```

Typical use: after the segment part of the heap has been assembled, convert the segment plus tail list into one complete list. This is a common finishing step when the goal wants a full `sll`.

#### Representative lemmas for `sep_apply_right`

`sep_apply_right` finds the lemma's **RHS** pattern on the goal's RHS and replaces it with the lemma's LHS — the backward/strengthening direction. The same lemmas above can often be used in reverse. Here are the most common patterns.

1. `sllseg_sllseg` (backward)

```coq
Lemma sllseg_sllseg: forall x y z l1 l2,
  sllseg x y l1 ** sllseg y z l2 |--
  sllseg x z (l1 ++ l2).
```

**sep_apply_right (sllseg_sllseg x y z l1 l2)**
```
================
M |-- sllseg x z (l1 ++ l2) ** N
```
becomes
```
================
M |-- (sllseg x y l1 ** sllseg y z l2) ** N
```

Typical use: when the RHS asks for a single concatenated segment but the LHS has two separate segments that should cancel individually.

2. `sllseg_sll` (backward)

```coq
Lemma sllseg_sll: forall x y l1 l2,
  sllseg x y l1 ** sll y l2 |--
  sll x (l1 ++ l2).
```

**sep_apply_right (sllseg_sll x y l1 l2)**
```
================
M |-- sll x (l1 ++ l2) ** N
```
becomes
```
================
M |-- (sllseg x y l1 ** sll y l2) ** N
```

Typical use: when the RHS wants a complete `sll x (l1 ++ l2)` but the LHS has the segment and tail as separate conjuncts.

3. `sllseg_0_sll`

```coq
Lemma sllseg_0_sll: forall x l,
  sllseg x 0 l |-- sll x l.
```

**sep_apply_right (sllseg_0_sll x l)**
```
================
M |-- sll x l ** N
```
becomes
```
================
M |-- sllseg x 0 l ** N
```

Typical use: when the RHS needs `sll x l` but the LHS naturally has `sllseg x 0 l`.

#### List-shape rewrites for `++` and `+::`

Generated VCs often need to reshape list expressions built from `++`, `::`, and the end-append notation `l +:: x`. The two pitfalls below trip up almost every proof that merges two `sllseg` segments.

**Pitfall 1 — `app_assoc` goes the wrong direction for segment merges.** The standard library lemma is

```coq
Lemma app_assoc : forall {A} (l m n : list A), l ++ m ++ n = (l ++ m) ++ n.
```

so `rewrite app_assoc` turns `l ++ m ++ n` into `(l ++ m) ++ n`. When you merge two segments via `sllseg_sllseg`, the resulting spatial term already has the *parenthesized* form `(l1 ++ w :: nil) ++ x :: nil`, while the goal wants the *flat* form `l1 ++ w :: x :: nil`. In that situation `rewrite app_assoc` does nothing useful — you want the reverse direction:

```coq
rewrite <- app_assoc. simpl.
(* (l1 ++ w :: nil) ++ x :: nil   ==>   l1 ++ w :: x :: nil *)
```

Rule of thumb: when you see `(something ++ _ :: nil) ++ _ :: nil` and need a flat `_ :: _ :: nil` tail, use `rewrite <- app_assoc` (followed by `simpl` to reduce `(w :: nil) ++ x :: nil`). Do NOT reach for `rewrite app_assoc` here — it is in the wrong direction and will fail or leave the goal unchanged.

**Pitfall 2 — `+::` vs `++` presentation.** The end-append notation `l +:: x` hides an append, so `app_assoc` may not match syntactically. Use `app_cons_assoc` to switch between the two forms:

```coq
Lemma app_cons_assoc: forall {A} (l1 l2 : list A) x,
  l1 ++ x :: l2 = l1 +:: x ++ l2.
```

Typical repair when the LHS and RHS list expressions differ only by `++` versus `+::` presentation:

```coq
rewrite <- app_cons_assoc.
```

Quick decision guide:

- Goal / hypothesis uses `+::` and `rewrite app_assoc` fails: try `rewrite app_cons_assoc` or `rewrite <- app_cons_assoc`.
- Goal / hypothesis has `(l ++ _ :: nil) ++ _ :: nil` and you want `l ++ _ :: _ :: nil`: use `rewrite <- app_assoc; simpl` (NOT `rewrite app_assoc`).

- if a hypothesis is a form of `x = c` where `c` is a constant such as `0` or `nil`, try `subst x` 
