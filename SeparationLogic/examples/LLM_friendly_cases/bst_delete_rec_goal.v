Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import SimpleC.EE.LLM_friendly_cases.bst_lib.
Import get_right_most.
Import naive_C_Rules.
Local Open Scope sac.
From SimpleC.EE.LLM_friendly_cases Require Import bst_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import bst_strategy_proof.
From SimpleC.EE.LLM_friendly_cases Require Import common_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import common_strategy_proof.

(*----- Function get_pre -----*)

Definition get_pre_safety_wit_1 := 
forall (tr: tree) (l0: tree) (r0: tree) (t: Z) (t_key: Z) (t_value: Z) (t_left: Z) (t_right: Z) ,
  [| (t <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (t_key) (t_value) (r0))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t)
  **  (store_tree t tr )
  **  ((&((t)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition get_pre_entail_wit_1 := 
forall (t_pre: Z) (tr: tree) ,
  [| (t_pre <> 0) |]
  &&  (store_tree t_pre tr )
|--
  EX (t_right: Z)  (t_left: Z)  (l0: tree)  (t_value: Z)  (r0: tree)  (t_key: Z) ,
  [| (t_pre <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (t_key) (t_value) (r0))) |]
  &&  (store_tree t_pre tr )
  **  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
.

Definition get_pre_return_wit_1 := 
forall (t_pre: Z) (tr: tree) (l0: tree) (r0: tree) (t: Z) (t_key: Z) (t_value: Z) (t_left: Z) (t_right: Z) ,
  [| (t_right = 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (t_key) (t_value) (r0))) |]
  &&  (store_tree t tr )
  **  ((&((t)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
|--
  EX (retval_left: Z)  (retval_right: Z)  (pt: partial_tree)  (tr_ret_left: tree)  (retval_key: Z)  (retval_value: Z) ,
  [| (t <> 0) |] 
  &&  [| forall (tr_ret_right: tree) , ((tree_pre_merge (tr) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) |] 
  &&  [| (retval_right = 0) |] 
  &&  [| (INT_MIN <= retval_key) |] 
  &&  [| (retval_key <= INT_MAX) |]
  &&  ((&((t)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((t)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((t)  # "tree" ->ₛ "right")) # Ptr  |-> retval_right)
  **  ((&((t)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt t t_pre pt )
.

Definition get_pre_return_wit_2 := 
forall (t_pre: Z) (tr: tree) (l0: tree) (r0: tree) (t: Z) (t_key: Z) (t_value: Z) (t_left: Z) (t_right: Z) (retval_left_2: Z) (retval_right_2: Z) (pt_2: partial_tree) (tr_ret_left_2: tree) (retval_key_2: Z) (retval_value_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| forall (tr_ret_right: tree) , ((tree_pre_merge (r0) (tr_ret_right)) = (combine_tree (pt_2) ((make_tree (tr_ret_left_2) (retval_key_2) (retval_value_2) (tr_ret_right))))) |] 
  &&  [| (retval_right_2 = 0) |] 
  &&  [| (INT_MIN <= retval_key_2) |] 
  &&  [| (retval_key_2 <= INT_MAX) |] 
  &&  [| (t_right <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (t_key) (t_value) (r0))) |]
  &&  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value_2)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key_2)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> retval_right_2)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left_2)
  **  (store_tree retval_left_2 tr_ret_left_2 )
  **  (store_pt retval t_right pt_2 )
  **  (store_tree t tr )
  **  ((&((t)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
|--
  EX (retval_left: Z)  (retval_right: Z)  (pt: partial_tree)  (tr_ret_left: tree)  (retval_key: Z)  (retval_value: Z) ,
  [| (retval <> 0) |] 
  &&  [| forall (tr_ret_right: tree) , ((tree_pre_merge (tr) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) |] 
  &&  [| (retval_right = 0) |] 
  &&  [| (INT_MIN <= retval_key) |] 
  &&  [| (retval_key <= INT_MAX) |]
  &&  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> retval_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval t_pre pt )
.

Definition get_pre_partial_solve_wit_1_pure := 
forall (tr: tree) (l0: tree) (r0: tree) (t: Z) (t_key: Z) (t_value: Z) (t_left: Z) (t_right: Z) ,
  [| (t_right <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (t_key) (t_value) (r0))) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t)
  **  (store_tree t tr )
  **  ((&((t)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
|--
  [| (t_right <> 0) |]
.

Definition get_pre_partial_solve_wit_1_aux := 
forall (tr: tree) (l0: tree) (r0: tree) (t: Z) (t_key: Z) (t_value: Z) (t_left: Z) (t_right: Z) ,
  [| (t_right <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (t_key) (t_value) (r0))) |]
  &&  (store_tree t tr )
  **  ((&((t)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
|--
  [| (t_right <> 0) |] 
  &&  [| (t_right <> 0) |] 
  &&  [| (t <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (t_key) (t_value) (r0))) |]
  &&  (store_tree t_right r0 )
  **  (store_tree t tr )
  **  ((&((t)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
.

Definition get_pre_partial_solve_wit_1 := get_pre_partial_solve_wit_1_pure -> get_pre_partial_solve_wit_1_aux.

(*----- Function delete -----*)

Definition delete_safety_wit_1 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_pre_v: Z) ,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v tr_low_level_spec )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition delete_safety_wit_2 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) ,
  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree p tr_low_level_spec )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition delete_safety_wit_3 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (retval_left: Z) (retval_right: Z) (pt: partial_tree) (tr_ret_left: tree) (retval_key: Z) (retval_value: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| forall (tr_ret_right: tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) |] 
  &&  [| (retval_right = 0) |] 
  &&  [| (INT_MIN <= retval_key) |] 
  &&  [| (retval_key <= INT_MAX) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval p_left pt )
  **  ((( &( "pre" ) )) # Ptr  |-> retval)
  **  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree p tr_low_level_spec )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition delete_entail_wit_1 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_pre_v: Z) ,
  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v tr_low_level_spec )
|--
  EX (p_right: Z)  (p_left: Z)  (l0: tree)  (p_value: Z)  (r0: tree)  (p_key: Z)  (b_v: Z) ,
  [| (b_pre_v = b_v) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_pre_v tr_low_level_spec )
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
.

Definition delete_return_wit_1 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (retval_left: Z) (retval_right: Z) (pt: partial_tree) (tr_ret_left: tree) (retval_key: Z) (retval_value: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| forall (tr_ret_right: tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) |] 
  &&  [| (retval_right = 0) |] 
  &&  [| (INT_MIN <= retval_key) |] 
  &&  [| (retval_key <= INT_MAX) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval p_left pt )
  **  ((b_pre) # Ptr  |-> p_left)
  **  (store_tree p tr_low_level_spec )
  **  (store_tree p_right r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete (x_pre) (tr_low_level_spec)) )
.

Definition delete_return_wit_2 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) ,
  [| (p_left = 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((b_pre) # Ptr  |-> p_right)
  **  (store_tree p tr_low_level_spec )
  **  (store_tree p_left l0 )
  **  (store_tree p_right r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete (x_pre) (tr_low_level_spec)) )
.

Definition delete_return_wit_3 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (b_callee_v: Z) ,
  [| (x_pre > p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v (tree_delete (x_pre) (r0)) )
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree p tr_low_level_spec )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete (x_pre) (tr_low_level_spec)) )
.

Definition delete_return_wit_4 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_right: Z) (b_callee_v: Z) ,
  [| (x_pre < p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v (tree_delete (x_pre) (l0)) )
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree p tr_low_level_spec )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete (x_pre) (tr_low_level_spec)) )
.

Definition delete_return_wit_5 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_pre_v_2: Z) ,
  [| (b_pre_v_2 = 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((b_pre) # Ptr  |-> b_pre_v_2)
  **  (store_tree b_pre_v_2 tr_low_level_spec )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete (x_pre) (tr_low_level_spec)) )
.

Definition delete_partial_solve_wit_1_pure := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) ,
  [| (x_pre < p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree p tr_low_level_spec )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |]
.

Definition delete_partial_solve_wit_1_aux := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) ,
  [| (x_pre < p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree p tr_low_level_spec )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre < p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree p tr_low_level_spec )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
.

Definition delete_partial_solve_wit_1 := delete_partial_solve_wit_1_pure -> delete_partial_solve_wit_1_aux.

Definition delete_partial_solve_wit_2_pure := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) ,
  [| (x_pre > p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree p tr_low_level_spec )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
.

Definition delete_partial_solve_wit_2_aux := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) ,
  [| (x_pre > p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree p tr_low_level_spec )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (x_pre > p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree p tr_low_level_spec )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
.

Definition delete_partial_solve_wit_2 := delete_partial_solve_wit_2_pure -> delete_partial_solve_wit_2_aux.

Definition delete_partial_solve_wit_3 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) ,
  [| (p_left = 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((b_pre) # Ptr  |-> p_right)
  **  (store_tree p tr_low_level_spec )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  [| (p_left = 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((b_pre) # Ptr  |-> p_right)
  **  (store_tree p tr_low_level_spec )
  **  (store_tree p_left l0 )
  **  (store_tree p_right r0 )
.

Definition delete_partial_solve_wit_4_pure := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) ,
  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((( &( "pre" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree p tr_low_level_spec )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  [| (p_left <> 0) |]
.

Definition delete_partial_solve_wit_4_aux := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) ,
  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree p tr_low_level_spec )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
|--
  [| (p_left <> 0) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  (store_tree p_left l0 )
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree p tr_low_level_spec )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
.

Definition delete_partial_solve_wit_4 := delete_partial_solve_wit_4_pure -> delete_partial_solve_wit_4_aux.

Definition delete_partial_solve_wit_5 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (l0: tree) (r0: tree) (p: Z) (b_v: Z) (p_key: Z) (p_value: Z) (p_left: Z) (p_right: Z) (retval_left: Z) (retval_right: Z) (pt: partial_tree) (tr_ret_left: tree) (retval_key: Z) (retval_value: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| forall (tr_ret_right: tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) |] 
  &&  [| (retval_right = 0) |] 
  &&  [| (INT_MIN <= retval_key) |] 
  &&  [| (retval_key <= INT_MAX) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval p_left pt )
  **  ((b_pre) # Ptr  |-> p_left)
  **  (store_tree p tr_low_level_spec )
  **  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> 0)
  **  (store_tree p_right r0 )
|--
  [| (retval <> 0) |] 
  &&  [| forall (tr_ret_right: tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) |] 
  &&  [| (retval_right = 0) |] 
  &&  [| (INT_MIN <= retval_key) |] 
  &&  [| (retval_key <= INT_MAX) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (p = b_v) |] 
  &&  [| (p <> 0) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr_low_level_spec = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval p_left pt )
  **  ((b_pre) # Ptr  |-> p_left)
  **  (store_tree p tr_low_level_spec )
  **  (store_tree p_right r0 )
.

Definition delete_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (b_pre: Z) (m_high_level_spec: mapping) ,
  EX b_pre_v,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((b_pre) # Ptr  |-> b_pre_v)
  **  (Bst.store_map b_pre_v m_high_level_spec )
|--
EX (tr_low_level_spec: tree) ,
  (EX b_callee_v,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((b_pre) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v tr_low_level_spec ))
  **
  ((EX b_callee_v_2,
  ((b_pre) # Ptr  |-> b_callee_v_2)
  **  (store_tree b_callee_v_2 (tree_delete (x_pre) (tr_low_level_spec)) ))
  -*
  (EX b_pre_v_2,
  ((b_pre) # Ptr  |-> b_pre_v_2)
  **  (Bst.store_map b_pre_v_2 (map_delete (x_pre) (m_high_level_spec)) )))
.

Module Type VC_Correct.

Include bst_Strategy_Correct.
Include common_Strategy_Correct.

Axiom proof_of_get_pre_safety_wit_1 : get_pre_safety_wit_1.
Axiom proof_of_get_pre_entail_wit_1 : get_pre_entail_wit_1.
Axiom proof_of_get_pre_return_wit_1 : get_pre_return_wit_1.
Axiom proof_of_get_pre_return_wit_2 : get_pre_return_wit_2.
Axiom proof_of_get_pre_partial_solve_wit_1_pure : get_pre_partial_solve_wit_1_pure.
Axiom proof_of_get_pre_partial_solve_wit_1 : get_pre_partial_solve_wit_1.
Axiom proof_of_delete_safety_wit_1 : delete_safety_wit_1.
Axiom proof_of_delete_safety_wit_2 : delete_safety_wit_2.
Axiom proof_of_delete_safety_wit_3 : delete_safety_wit_3.
Axiom proof_of_delete_entail_wit_1 : delete_entail_wit_1.
Axiom proof_of_delete_return_wit_1 : delete_return_wit_1.
Axiom proof_of_delete_return_wit_2 : delete_return_wit_2.
Axiom proof_of_delete_return_wit_3 : delete_return_wit_3.
Axiom proof_of_delete_return_wit_4 : delete_return_wit_4.
Axiom proof_of_delete_return_wit_5 : delete_return_wit_5.
Axiom proof_of_delete_partial_solve_wit_1_pure : delete_partial_solve_wit_1_pure.
Axiom proof_of_delete_partial_solve_wit_1 : delete_partial_solve_wit_1.
Axiom proof_of_delete_partial_solve_wit_2_pure : delete_partial_solve_wit_2_pure.
Axiom proof_of_delete_partial_solve_wit_2 : delete_partial_solve_wit_2.
Axiom proof_of_delete_partial_solve_wit_3 : delete_partial_solve_wit_3.
Axiom proof_of_delete_partial_solve_wit_4_pure : delete_partial_solve_wit_4_pure.
Axiom proof_of_delete_partial_solve_wit_4 : delete_partial_solve_wit_4.
Axiom proof_of_delete_partial_solve_wit_5 : delete_partial_solve_wit_5.
Axiom proof_of_delete_derive_high_level_spec_by_low_level_spec : delete_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
