Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_friendly_cases.bst_fp_lib.
Local Open Scope sac.
From SimpleC.EE.LLM_friendly_cases Require Import bst_fp_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import bst_fp_strategy_proof.

(*----- Function replace_min -----*)

Definition replace_min_safety_wit_1 := 
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (fa: Z) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) ,
  [| (ptr_pre <> 0) |] 
  &&  [| (tr = (combine_tree (pt0) (tr0))) |] 
  &&  [| ((min_key (k) (tr)) = (min_key (k) (tr0))) |] 
  &&  [| ((min_value (v) (tr)) = (min_value (v) (tr0))) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0))))) |]
  &&  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  (store_tree b_v fa tr0 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition replace_min_safety_wit_2 := 
forall (ptr_pre: Z) (v: Z) (k: Z) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) ,
  [| (ptr_pre <> 0) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  (store_tree b_v fa tr0 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition replace_min_safety_wit_3 := 
forall (ptr_pre: Z) (v: Z) (k: Z) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) ,
  [| (b_v_left = 0) |] 
  &&  [| (ptr_pre <> 0) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((( &( "to_free" ) )) # Ptr  |-> b_v)
  **  ((( &( "ptr" ) )) # Ptr  |-> ptr_pre)
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  (store_tree b_v fa tr0 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition replace_min_entail_wit_1 := 
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (b_pre_v: Z) ,
  [| (ptr_pre <> 0) |] 
  &&  [| (INT_MIN <= k) |] 
  &&  [| (k <= INT_MAX) |] 
  &&  [| (b_pre_v <> 0) |]
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v ptr_pre tr )
|--
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  [| (ptr_pre <> 0) |] 
  &&  [| (tr = (combine_tree (pt0) (tr0))) |] 
  &&  [| ((min_key (k) (tr)) = (min_key (k) (tr0))) |] 
  &&  [| ((min_value (v) (tr)) = (min_value (v) (tr0))) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0))))) |]
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_ptb b_pre b_pre ptr_pre ptr_pre pt0 )
  **  (store_tree b_v ptr_pre tr0 )
.

Definition replace_min_entail_wit_2 := 
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (fa: Z) (b_v_2: Z) (b: Z) (pt0: partial_tree) (tr0_2: tree) ,
  [| (ptr_pre <> 0) |] 
  &&  [| (tr = (combine_tree (pt0) (tr0_2))) |] 
  &&  [| ((min_key (k) (tr)) = (min_key (k) (tr0_2))) |] 
  &&  [| ((min_value (v) (tr)) = (min_value (v) (tr0_2))) |] 
  &&  [| (b_v_2 <> 0) |] 
  &&  [| ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0_2))))) |]
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((b) # Ptr  |-> b_v_2)
  **  (store_ptb b b_pre fa ptr_pre pt0 )
  **  (store_tree b_v_2 fa tr0_2 )
|--
  EX (b_v_right: Z)  (b_v_left: Z)  (l0: tree)  (b_v_value: Z)  (r0: tree)  (b_v_father: Z)  (b_v_key: Z)  (tr0: tree)  (b_v: Z) ,
  [| (ptr_pre <> 0) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
.

Definition replace_min_entail_wit_3 := 
forall (ptr_pre: Z) (v: Z) (k: Z) (tr0_2: tree) (l0_2: tree) (r0_2: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key_2: Z) (b_v_father_2: Z) (b_v_value_2: Z) (b_v_left_2: Z) (b_v_right_2: Z) ,
  [| (b_v_right_2 <> 0) |] 
  &&  [| (b_v_left_2 = 0) |] 
  &&  [| (ptr_pre <> 0) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key_2) |] 
  &&  [| (b_v_key_2 <= INT_MAX) |] 
  &&  [| (b_v_father_2 = fa) |] 
  &&  [| (tr0_2 = (make_tree (l0_2) (b_v_key_2) (b_v_value_2) (r0_2))) |]
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key_2)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father_2)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value_2)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_2)
  **  (store_tree b_v_left_2 b_v l0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_2)
  **  (store_tree b_v_right_2 b_v r0_2 )
|--
  EX (b_v_right_right: Z)  (b_v_right_left: Z)  (b_v_right_father: Z)  (l0: tree)  (b_v_right_value: Z)  (r0: tree)  (b_v_right_key: Z)  (tr0: tree)  (b_v_right: Z)  (l1: tree)  (b_v_value: Z)  (r1: tree)  (b_v_father: Z)  (b_v_key: Z)  (tr1: tree)  (b_v_left: Z)  (b_v_2: Z) ,
  [| (ptr_pre <> 0) |] 
  &&  [| (b_v = b_v_2) |] 
  &&  [| (b_v_2 <> 0) |] 
  &&  [| (b_v_left = 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (INT_MIN <= b_v_right_key) |] 
  &&  [| (b_v_right_key <= INT_MAX) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) |] 
  &&  [| (b_v_right_father = b_v_2) |]
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_2 fa tr1 )
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_tree b_v_left b_v_2 l1 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r1 )
  **  (store_tree b_v_right b_v_2 tr0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_right_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
.

Definition replace_min_entail_wit_4 := 
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (tr0_2: tree) (l0: tree) (r0: tree) (b: Z) (b_v_2: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) ,
  [| (b_v_left <> 0) |] 
  &&  [| (ptr_pre <> 0) |] 
  &&  [| (b_v_2 <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((b) # Ptr  |-> b_v_2)
  **  (store_tree b_v_2 fa tr0_2 )
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
|--
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  [| (ptr_pre <> 0) |] 
  &&  [| (tr = (combine_tree (pt0) (tr0))) |] 
  &&  [| ((min_key (k) (tr)) = (min_key (k) (tr0))) |] 
  &&  [| ((min_value (v) (tr)) = (min_value (v) (tr0))) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| ((delete_min (tr)) = (combine_tree (pt0) ((delete_min (tr0))))) |]
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> k)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> v)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v)
  **  (store_ptb &((b_v_2)  # "tree" ->ₛ "left") b_pre b_v_2 ptr_pre pt0 )
  **  (store_tree b_v b_v_2 tr0 )
.

Definition replace_min_return_wit_1 := 
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (tr1: tree) (l1: tree) (r1: tree) (tr0: tree) (l0: tree) (r0: tree) (to_free: Z) (b: Z) (b_v: Z) (b_v_left: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_right: Z) (b_v_right_key: Z) (b_v_right_value: Z) (b_v_right_father: Z) (b_v_right_left: Z) (b_v_right_right: Z) ,
  [| (ptr_pre <> 0) |] 
  &&  [| (to_free = b_v) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (b_v_left = 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (INT_MIN <= b_v_right_key) |] 
  &&  [| (b_v_right_key <= INT_MAX) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) |] 
  &&  [| (b_v_right_father = b_v) |]
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((b) # Ptr  |-> b_v_right)
  **  (store_tree b_v fa tr1 )
  **  (store_tree b_v_left b_v l1 )
  **  (store_tree b_v_right b_v r1 )
  **  (store_tree b_v_right b_v tr0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
|--
  EX (b_pre_v: Z)  (ptr_pre_value: Z)  (ptr_pre_key: Z) ,
  [| (ptr_pre_key = (min_key (k) (tr))) |] 
  &&  [| (ptr_pre_value = (min_value (v) (tr))) |] 
  &&  [| (INT_MIN <= ptr_pre_key) |] 
  &&  [| (ptr_pre_key <= INT_MAX) |]
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> ptr_pre_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> ptr_pre_value)
  **  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v ptr_pre (delete_min (tr)) )
.

Definition replace_min_return_wit_2 := 
forall (ptr_pre: Z) (b_pre: Z) (v: Z) (k: Z) (tr: tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) ,
  [| (b_v_right = 0) |] 
  &&  [| (b_v_left = 0) |] 
  &&  [| (ptr_pre <> 0) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((b) # Ptr  |-> b_v_right)
  **  (store_tree b_v fa tr0 )
  **  (store_tree b_v_left b_v l0 )
  **  (store_tree b_v_right b_v r0 )
|--
  EX (b_pre_v: Z)  (ptr_pre_value: Z)  (ptr_pre_key: Z) ,
  [| (ptr_pre_key = (min_key (k) (tr))) |] 
  &&  [| (ptr_pre_value = (min_value (v) (tr))) |] 
  &&  [| (INT_MIN <= ptr_pre_key) |] 
  &&  [| (ptr_pre_key <= INT_MAX) |]
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> ptr_pre_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> ptr_pre_value)
  **  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v ptr_pre (delete_min (tr)) )
.

Definition replace_min_partial_solve_wit_1 := 
forall (ptr_pre: Z) (tr1: tree) (l1: tree) (r1: tree) (tr0: tree) (l0: tree) (r0: tree) (to_free: Z) (b: Z) (b_v: Z) (b_v_left: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_right: Z) (b_v_right_key: Z) (b_v_right_value: Z) (b_v_right_father: Z) (b_v_right_left: Z) (b_v_right_right: Z) ,
  [| (ptr_pre <> 0) |] 
  &&  [| (to_free = b_v) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (b_v_left = 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (INT_MIN <= b_v_right_key) |] 
  &&  [| (b_v_right_key <= INT_MAX) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) |] 
  &&  [| (b_v_right_father = b_v) |]
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((b) # Ptr  |-> b_v_right)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v fa tr1 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r1 )
  **  (store_tree b_v_right b_v tr0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
|--
  [| (ptr_pre <> 0) |] 
  &&  [| (to_free = b_v) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (b_v_left = 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (INT_MIN <= b_v_right_key) |] 
  &&  [| (b_v_right_key <= INT_MAX) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) |] 
  &&  [| (b_v_right_father = b_v) |]
  &&  ((&((to_free)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((to_free)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((to_free)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((to_free)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((to_free)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((b) # Ptr  |-> b_v_right)
  **  (store_tree b_v fa tr1 )
  **  (store_tree b_v_left b_v l1 )
  **  (store_tree b_v_right b_v r1 )
  **  (store_tree b_v_right b_v tr0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
.

Definition replace_min_partial_solve_wit_2 := 
forall (ptr_pre: Z) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) ,
  [| (b_v_right = 0) |] 
  &&  [| (b_v_left = 0) |] 
  &&  [| (ptr_pre <> 0) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((b) # Ptr  |-> b_v_right)
  **  (store_tree b_v fa tr0 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  [| (b_v_right = 0) |] 
  &&  [| (b_v_left = 0) |] 
  &&  [| (ptr_pre <> 0) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((&((ptr_pre)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((ptr_pre)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((b) # Ptr  |-> b_v_right)
  **  (store_tree b_v fa tr0 )
  **  (store_tree b_v_left b_v l0 )
  **  (store_tree b_v_right b_v r0 )
.

(*----- Function Delete -----*)

Definition Delete_safety_wit_1 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_pre_v: Z) ,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "fa" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 tr_low_level_spec )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Delete_safety_wit_2 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) ,
  [| ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition Delete_safety_wit_3 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) ,
  [| ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Delete_safety_wit_4 := 
forall (x_pre: Z) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) ,
  [| (b_v_key >= x_pre) |] 
  &&  [| (x_pre >= b_v_key) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  (store_tree b_v fa tr0 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Delete_safety_wit_5 := 
forall (x_pre: Z) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) ,
  [| (b_v_right = 0) |] 
  &&  [| (b_v_key >= x_pre) |] 
  &&  [| (x_pre >= b_v_key) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((( &( "to_free" ) )) # Ptr  |-> b_v)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  (store_tree b_v fa tr0 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Delete_safety_wit_6 := 
forall (x_pre: Z) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) ,
  [| (b_v_right <> 0) |] 
  &&  [| (b_v_key >= x_pre) |] 
  &&  [| (x_pre >= b_v_key) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  (store_tree b_v fa tr0 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Delete_safety_wit_7 := 
forall (x_pre: Z) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) ,
  [| (b_v_left = 0) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (b_v_key >= x_pre) |] 
  &&  [| (x_pre >= b_v_key) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((( &( "to_free" ) )) # Ptr  |-> b_v)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  (store_tree b_v fa tr0 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition Delete_safety_wit_8 := 
forall (x_pre: Z) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) ,
  [| (b_v_right = 0) |] 
  &&  [| (b_v_left = 0) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (b_v_key >= x_pre) |] 
  &&  [| (x_pre >= b_v_key) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((( &( "to_free" ) )) # Ptr  |-> b_v)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  (store_tree b_v fa tr0 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  [| False |]
.

Definition Delete_entail_wit_1 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_pre_v: Z) ,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 tr_low_level_spec )
|--
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  [| ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) |]
  &&  (store_ptb b_pre b_pre 0 0 pt0 )
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v 0 tr0 )
.

Definition Delete_entail_wit_2 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v_2: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0_2: tree) ,
  [| (b_v_2 <> 0) |] 
  &&  [| ((combine_tree (pt0) ((tree_delete (x_pre) (tr0_2)))) = (tree_delete (x_pre) (tr_low_level_spec))) |]
  &&  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v_2)
  **  (store_tree b_v_2 fa tr0_2 )
|--
  EX (b_v_right: Z)  (b_v_left: Z)  (l0: tree)  (b_v_value: Z)  (r0: tree)  (b_v_father: Z)  (b_v_key: Z)  (tr0: tree)  (b_v: Z) ,
  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
.

Definition Delete_entail_wit_3 := 
forall (x_pre: Z) (tr0_2: tree) (l0_2: tree) (r0_2: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key_2: Z) (b_v_father_2: Z) (b_v_value_2: Z) (b_v_left_2: Z) (b_v_right_2: Z) ,
  [| (b_v_left_2 <> 0) |] 
  &&  [| (b_v_right_2 = 0) |] 
  &&  [| (b_v_key_2 >= x_pre) |] 
  &&  [| (x_pre >= b_v_key_2) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key_2) |] 
  &&  [| (b_v_key_2 <= INT_MAX) |] 
  &&  [| (b_v_father_2 = fa) |] 
  &&  [| (tr0_2 = (make_tree (l0_2) (b_v_key_2) (b_v_value_2) (r0_2))) |]
  &&  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key_2)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father_2)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value_2)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_2)
  **  (store_tree b_v_left_2 b_v l0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_2)
  **  (store_tree b_v_right_2 b_v r0_2 )
|--
  EX (b_v_left_right: Z)  (b_v_left_left: Z)  (l0: tree)  (b_v_left_value: Z)  (r0: tree)  (b_v_left_father: Z)  (b_v_left_key: Z)  (tr0: tree)  (b_v_left: Z)  (l1: tree)  (b_v_value: Z)  (r1: tree)  (b_v_father: Z)  (b_v_key: Z)  (tr1: tree)  (b_v_right: Z)  (b_v_2: Z) ,
  [| (b_v = b_v_2) |] 
  &&  [| (b_v_2 <> 0) |] 
  &&  [| (b_v_right = 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_left <> 0) |] 
  &&  [| (INT_MIN <= b_v_left_key) |] 
  &&  [| (b_v_left_key <= INT_MAX) |] 
  &&  [| (b_v_left_father = b_v_2) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_left_key) (b_v_left_value) (r0))) |]
  &&  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_2 fa tr1 )
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l1 )
  **  (store_tree b_v_right b_v_2 r1 )
  **  (store_tree b_v_left b_v_2 tr0 )
  **  ((&((b_v_left)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_left_father)
  **  ((&((b_v_left)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left l0 )
  **  ((&((b_v_left)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left r0 )
.

Definition Delete_entail_wit_4 := 
forall (x_pre: Z) (tr0_2: tree) (l0_2: tree) (r0_2: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key_2: Z) (b_v_father_2: Z) (b_v_value_2: Z) (b_v_left_2: Z) (b_v_right_2: Z) ,
  [| (b_v_right_2 <> 0) |] 
  &&  [| (b_v_left_2 = 0) |] 
  &&  [| (b_v_right_2 <> 0) |] 
  &&  [| (b_v_key_2 >= x_pre) |] 
  &&  [| (x_pre >= b_v_key_2) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key_2) |] 
  &&  [| (b_v_key_2 <= INT_MAX) |] 
  &&  [| (b_v_father_2 = fa) |] 
  &&  [| (tr0_2 = (make_tree (l0_2) (b_v_key_2) (b_v_value_2) (r0_2))) |]
  &&  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key_2)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father_2)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value_2)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_2)
  **  (store_tree b_v_left_2 b_v l0_2 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_2)
  **  (store_tree b_v_right_2 b_v r0_2 )
|--
  EX (b_v_right_right: Z)  (b_v_right_left: Z)  (l0: tree)  (b_v_right_value: Z)  (r0: tree)  (b_v_right_father: Z)  (b_v_right_key: Z)  (tr0: tree)  (b_v_right: Z)  (l1: tree)  (b_v_value: Z)  (r1: tree)  (b_v_father: Z)  (b_v_key: Z)  (tr1: tree)  (b_v_left: Z)  (b_v_2: Z) ,
  [| (b_v = b_v_2) |] 
  &&  [| (b_v_2 <> 0) |] 
  &&  [| (b_v_left = 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (INT_MIN <= b_v_right_key) |] 
  &&  [| (b_v_right_key <= INT_MAX) |] 
  &&  [| (b_v_right_father = b_v_2) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) |]
  &&  ((b) # Ptr  |-> b_v_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_2 fa tr1 )
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_tree b_v_left b_v_2 l1 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r1 )
  **  (store_tree b_v_right b_v_2 tr0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_right_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
.

Definition Delete_entail_wit_5 := 
forall (x_pre: Z) (tr0_2: tree) (l0_2: tree) (r0_2: tree) (b: Z) (b_v_2: Z) (fa: Z) (b_v_key_2: Z) (b_v_father_2: Z) (b_v_value_2: Z) (b_v_left_2: Z) (b_v_right_2: Z) ,
  [| (b_v_left_2 <> 0) |] 
  &&  [| (b_v_right_2 <> 0) |] 
  &&  [| (b_v_key_2 >= x_pre) |] 
  &&  [| (x_pre >= b_v_key_2) |] 
  &&  [| (b_v_2 <> 0) |] 
  &&  [| (INT_MIN <= b_v_key_2) |] 
  &&  [| (b_v_key_2 <= INT_MAX) |] 
  &&  [| (b_v_father_2 = fa) |] 
  &&  [| (tr0_2 = (make_tree (l0_2) (b_v_key_2) (b_v_value_2) (r0_2))) |]
  &&  ((b) # Ptr  |-> b_v_2)
  **  (store_tree b_v_2 fa tr0_2 )
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value_2)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_2)
  **  (store_tree b_v_left_2 b_v_2 l0_2 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_2)
  **  (store_tree b_v_right_2 b_v_2 r0_2 )
|--
  EX (b_v_right_right: Z)  (b_v_right_left: Z)  (l0: tree)  (b_v_right_value: Z)  (r0: tree)  (b_v_right_father: Z)  (b_v_right_key: Z)  (tr0: tree)  (b_v_right: Z)  (b_v_left: Z)  (l1: tree)  (b_v_value: Z)  (r1: tree)  (b_v_father: Z)  (b_v_key: Z)  (tr1: tree)  (b_v: Z) ,
  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_left <> 0) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (INT_MIN <= b_v_right_key) |] 
  &&  [| (b_v_right_key <= INT_MAX) |] 
  &&  [| (b_v_right_father = b_v) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) |]
  &&  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr1 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r1 )
  **  (store_tree b_v_right b_v tr0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_right_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
.

Definition Delete_entail_wit_6_1 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (tr0_2: tree) (l0: tree) (r0: tree) (b: Z) (b_v_2: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) ,
  [| (b_v_key < x_pre) |] 
  &&  [| (x_pre >= b_v_key) |] 
  &&  [| (b_v_2 <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((b) # Ptr  |-> b_v_2)
  **  (store_tree b_v_2 fa tr0_2 )
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
|--
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  [| ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) |]
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "right") b_pre b_v_2 0 pt0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v)
  **  (store_tree b_v b_v_2 tr0 )
.

Definition Delete_entail_wit_6_2 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (tr0_2: tree) (l0: tree) (r0: tree) (b: Z) (b_v_2: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) ,
  [| (x_pre < b_v_key) |] 
  &&  [| (b_v_2 <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0_2 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((b) # Ptr  |-> b_v_2)
  **  (store_tree b_v_2 fa tr0_2 )
  **  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v_2 l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v_2 r0 )
|--
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  [| ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) |]
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "left") b_pre b_v_2 0 pt0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v)
  **  (store_tree b_v b_v_2 tr0 )
.

Definition Delete_return_wit_1 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (b_v: Z) (b: Z) (fa: Z) (pt0: partial_tree) (tr0: tree) ,
  [| (b_v = 0) |] 
  &&  [| ((combine_tree (pt0) ((tree_delete (x_pre) (tr0)))) = (tree_delete (x_pre) (tr_low_level_spec))) |]
  &&  (store_ptb b b_pre fa 0 pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
.

Definition Delete_return_wit_2 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (tr1: tree) (l1: tree) (r1: tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (b_v_right_key: Z) (b_v_right_father: Z) (b_v_right_value: Z) (b_v_right_left: Z) (b_v_right_right: Z) (b_callee_v: Z) (ptr_callee_value: Z) (ptr_callee_key: Z) ,
  [| (ptr_callee_key = (min_key (b_v_key) (r1))) |] 
  &&  [| (ptr_callee_value = (min_value (b_v_value) (r1))) |] 
  &&  [| (INT_MIN <= ptr_callee_key) |] 
  &&  [| (ptr_callee_key <= INT_MAX) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_left <> 0) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (INT_MIN <= b_v_right_key) |] 
  &&  [| (b_v_right_key <= INT_MAX) |] 
  &&  [| (b_v_right_father = b_v) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) |]
  &&  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> ptr_callee_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> ptr_callee_value)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_callee_v)
  **  (store_tree b_callee_v b_v (delete_min (r1)) )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr1 )
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l1 )
  **  (store_tree b_v_right b_v tr0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_right_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
.

Definition Delete_return_wit_3 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (tr1: tree) (l1: tree) (r1: tree) (tr0: tree) (l0: tree) (r0: tree) (to_free: Z) (b: Z) (b_v: Z) (b_v_left: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_right: Z) (b_v_right_key: Z) (b_v_right_father: Z) (b_v_right_value: Z) (b_v_right_left: Z) (b_v_right_right: Z) ,
  [| (to_free = b_v) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (b_v_left = 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (INT_MIN <= b_v_right_key) |] 
  &&  [| (b_v_right_key <= INT_MAX) |] 
  &&  [| (b_v_right_father = b_v) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) |]
  &&  ((b) # Ptr  |-> b_v_right)
  **  (store_tree b_v fa tr1 )
  **  (store_tree b_v_left b_v l1 )
  **  (store_tree b_v_right b_v r1 )
  **  (store_tree b_v_right b_v tr0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
.

Definition Delete_return_wit_4 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (tr1: tree) (l1: tree) (r1: tree) (tr0: tree) (l0: tree) (r0: tree) (to_free: Z) (b: Z) (b_v: Z) (b_v_right: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_left_key: Z) (b_v_left_father: Z) (b_v_left_value: Z) (b_v_left_left: Z) (b_v_left_right: Z) ,
  [| (to_free = b_v) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (b_v_right = 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_left <> 0) |] 
  &&  [| (INT_MIN <= b_v_left_key) |] 
  &&  [| (b_v_left_key <= INT_MAX) |] 
  &&  [| (b_v_left_father = b_v) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_left_key) (b_v_left_value) (r0))) |]
  &&  ((b) # Ptr  |-> b_v_left)
  **  (store_tree b_v fa tr1 )
  **  (store_tree b_v_left b_v l1 )
  **  (store_tree b_v_right b_v r1 )
  **  (store_tree b_v_left b_v tr0 )
  **  ((&((b_v_left)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_left)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left l0 )
  **  ((&((b_v_left)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
.

Definition Delete_return_wit_5 := 
forall (x_pre: Z) (b_pre: Z) (tr_low_level_spec: tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) ,
  [| (b_v_left = 0) |] 
  &&  [| (b_v_right = 0) |] 
  &&  [| (b_v_key >= x_pre) |] 
  &&  [| (x_pre >= b_v_key) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((b) # Ptr  |-> b_v_left)
  **  (store_tree b_v fa tr0 )
  **  (store_tree b_v_left b_v l0 )
  **  (store_tree b_v_right b_v r0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v 0 (tree_delete (x_pre) (tr_low_level_spec)) )
.

Definition Delete_partial_solve_wit_1 := 
forall (tr1: tree) (l1: tree) (r1: tree) (tr0: tree) (l0: tree) (r0: tree) (to_free: Z) (b: Z) (b_v: Z) (b_v_right: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_left_key: Z) (b_v_left_father: Z) (b_v_left_value: Z) (b_v_left_left: Z) (b_v_left_right: Z) ,
  [| (to_free = b_v) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (b_v_right = 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_left <> 0) |] 
  &&  [| (INT_MIN <= b_v_left_key) |] 
  &&  [| (b_v_left_key <= INT_MAX) |] 
  &&  [| (b_v_left_father = b_v) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_left_key) (b_v_left_value) (r0))) |]
  &&  ((b) # Ptr  |-> b_v_left)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v fa tr1 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l1 )
  **  (store_tree b_v_right b_v r1 )
  **  (store_tree b_v_left b_v tr0 )
  **  ((&((b_v_left)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_left)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left l0 )
  **  ((&((b_v_left)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left r0 )
|--
  [| (to_free = b_v) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (b_v_right = 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_left <> 0) |] 
  &&  [| (INT_MIN <= b_v_left_key) |] 
  &&  [| (b_v_left_key <= INT_MAX) |] 
  &&  [| (b_v_left_father = b_v) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_left_key) (b_v_left_value) (r0))) |]
  &&  ((&((to_free)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((to_free)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((to_free)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((to_free)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((to_free)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((b) # Ptr  |-> b_v_left)
  **  (store_tree b_v fa tr1 )
  **  (store_tree b_v_left b_v l1 )
  **  (store_tree b_v_right b_v r1 )
  **  (store_tree b_v_left b_v tr0 )
  **  ((&((b_v_left)  # "tree" ->ₛ "key")) # Int  |-> b_v_left_key)
  **  ((&((b_v_left)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_left)  # "tree" ->ₛ "value")) # Int  |-> b_v_left_value)
  **  ((&((b_v_left)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left_left)
  **  (store_tree b_v_left_left b_v_left l0 )
  **  ((&((b_v_left)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_left_right)
  **  (store_tree b_v_left_right b_v_left r0 )
.

Definition Delete_partial_solve_wit_2 := 
forall (x_pre: Z) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) ,
  [| (b_v_left = 0) |] 
  &&  [| (b_v_right = 0) |] 
  &&  [| (b_v_key >= x_pre) |] 
  &&  [| (x_pre >= b_v_key) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((b) # Ptr  |-> b_v_left)
  **  (store_tree b_v fa tr0 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r0 )
|--
  [| (b_v_left = 0) |] 
  &&  [| (b_v_right = 0) |] 
  &&  [| (b_v_key >= x_pre) |] 
  &&  [| (x_pre >= b_v_key) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_key) (b_v_value) (r0))) |]
  &&  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((b) # Ptr  |-> b_v_left)
  **  (store_tree b_v fa tr0 )
  **  (store_tree b_v_left b_v l0 )
  **  (store_tree b_v_right b_v r0 )
.

Definition Delete_partial_solve_wit_3 := 
forall (tr1: tree) (l1: tree) (r1: tree) (tr0: tree) (l0: tree) (r0: tree) (to_free: Z) (b: Z) (b_v: Z) (b_v_left: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_right: Z) (b_v_right_key: Z) (b_v_right_father: Z) (b_v_right_value: Z) (b_v_right_left: Z) (b_v_right_right: Z) ,
  [| (to_free = b_v) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (b_v_left = 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (INT_MIN <= b_v_right_key) |] 
  &&  [| (b_v_right_key <= INT_MAX) |] 
  &&  [| (b_v_right_father = b_v) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) |]
  &&  ((b) # Ptr  |-> b_v_right)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v fa tr1 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r1 )
  **  (store_tree b_v_right b_v tr0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
|--
  [| (to_free = b_v) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (b_v_left = 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (INT_MIN <= b_v_right_key) |] 
  &&  [| (b_v_right_key <= INT_MAX) |] 
  &&  [| (b_v_right_father = b_v) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) |]
  &&  ((&((to_free)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((to_free)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((to_free)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((to_free)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  ((&((to_free)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  ((b) # Ptr  |-> b_v_right)
  **  (store_tree b_v fa tr1 )
  **  (store_tree b_v_left b_v l1 )
  **  (store_tree b_v_right b_v r1 )
  **  (store_tree b_v_right b_v tr0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> fa)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
.

Definition Delete_partial_solve_wit_4_pure := 
forall (x_pre: Z) (tr1: tree) (l1: tree) (r1: tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (b_v_right_key: Z) (b_v_right_father: Z) (b_v_right_value: Z) (b_v_right_left: Z) (b_v_right_right: Z) ,
  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_left <> 0) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (INT_MIN <= b_v_right_key) |] 
  &&  [| (b_v_right_key <= INT_MAX) |] 
  &&  [| (b_v_right_father = b_v) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  ((b) # Ptr  |-> b_v)
  **  ((( &( "fa" ) )) # Ptr  |-> fa)
  **  (store_tree b_v fa tr1 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r1 )
  **  (store_tree b_v_right b_v tr0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_right_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
|--
  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_right <> 0) |]
.

Definition Delete_partial_solve_wit_4_aux := 
forall (tr1: tree) (l1: tree) (r1: tree) (tr0: tree) (l0: tree) (r0: tree) (b: Z) (b_v: Z) (fa: Z) (b_v_key: Z) (b_v_father: Z) (b_v_value: Z) (b_v_left: Z) (b_v_right: Z) (b_v_right_key: Z) (b_v_right_father: Z) (b_v_right_value: Z) (b_v_right_left: Z) (b_v_right_right: Z) ,
  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_left <> 0) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (INT_MIN <= b_v_right_key) |] 
  &&  [| (b_v_right_key <= INT_MAX) |] 
  &&  [| (b_v_right_father = b_v) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) |]
  &&  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr1 )
  **  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l1 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r1 )
  **  (store_tree b_v_right b_v tr0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_right_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
|--
  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| (INT_MIN <= b_v_key) |] 
  &&  [| (b_v_key <= INT_MAX) |] 
  &&  [| (b_v_father = fa) |] 
  &&  [| (tr1 = (make_tree (l1) (b_v_key) (b_v_value) (r1))) |] 
  &&  [| (b_v_left <> 0) |] 
  &&  [| (b_v_right <> 0) |] 
  &&  [| (INT_MIN <= b_v_right_key) |] 
  &&  [| (b_v_right_key <= INT_MAX) |] 
  &&  [| (b_v_right_father = b_v) |] 
  &&  [| (tr0 = (make_tree (l0) (b_v_right_key) (b_v_right_value) (r0))) |]
  &&  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> b_v_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> b_v_value)
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right)
  **  (store_tree b_v_right b_v r1 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v fa tr1 )
  **  ((&((b_v)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_father)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_left)
  **  (store_tree b_v_left b_v l1 )
  **  (store_tree b_v_right b_v tr0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "key")) # Int  |-> b_v_right_key)
  **  ((&((b_v_right)  # "tree" ->ₛ "father")) # Ptr  |-> b_v_right_father)
  **  ((&((b_v_right)  # "tree" ->ₛ "value")) # Int  |-> b_v_right_value)
  **  ((&((b_v_right)  # "tree" ->ₛ "left")) # Ptr  |-> b_v_right_left)
  **  (store_tree b_v_right_left b_v_right l0 )
  **  ((&((b_v_right)  # "tree" ->ₛ "right")) # Ptr  |-> b_v_right_right)
  **  (store_tree b_v_right_right b_v_right r0 )
.

Definition Delete_partial_solve_wit_4 := Delete_partial_solve_wit_4_pure -> Delete_partial_solve_wit_4_aux.

Definition Delete_derive_high_level_spec_by_low_level_spec := 
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
  **  (store_tree b_callee_v 0 tr_low_level_spec ))
  **
  ((EX b_callee_v_2,
  ((b_pre) # Ptr  |-> b_callee_v_2)
  **  (store_tree b_callee_v_2 0 (tree_delete (x_pre) (tr_low_level_spec)) ))
  -*
  (EX b_pre_v_2,
  ((b_pre) # Ptr  |-> b_pre_v_2)
  **  (Bst.store_map b_pre_v_2 (map_delete (x_pre) (m_high_level_spec)) )))
.

Module Type VC_Correct.

Include bst_fp_Strategy_Correct.

Axiom proof_of_replace_min_safety_wit_1 : replace_min_safety_wit_1.
Axiom proof_of_replace_min_safety_wit_2 : replace_min_safety_wit_2.
Axiom proof_of_replace_min_safety_wit_3 : replace_min_safety_wit_3.
Axiom proof_of_replace_min_entail_wit_1 : replace_min_entail_wit_1.
Axiom proof_of_replace_min_entail_wit_2 : replace_min_entail_wit_2.
Axiom proof_of_replace_min_entail_wit_3 : replace_min_entail_wit_3.
Axiom proof_of_replace_min_entail_wit_4 : replace_min_entail_wit_4.
Axiom proof_of_replace_min_return_wit_1 : replace_min_return_wit_1.
Axiom proof_of_replace_min_return_wit_2 : replace_min_return_wit_2.
Axiom proof_of_replace_min_partial_solve_wit_1 : replace_min_partial_solve_wit_1.
Axiom proof_of_replace_min_partial_solve_wit_2 : replace_min_partial_solve_wit_2.
Axiom proof_of_Delete_safety_wit_1 : Delete_safety_wit_1.
Axiom proof_of_Delete_safety_wit_2 : Delete_safety_wit_2.
Axiom proof_of_Delete_safety_wit_3 : Delete_safety_wit_3.
Axiom proof_of_Delete_safety_wit_4 : Delete_safety_wit_4.
Axiom proof_of_Delete_safety_wit_5 : Delete_safety_wit_5.
Axiom proof_of_Delete_safety_wit_6 : Delete_safety_wit_6.
Axiom proof_of_Delete_safety_wit_7 : Delete_safety_wit_7.
Axiom proof_of_Delete_safety_wit_8 : Delete_safety_wit_8.
Axiom proof_of_Delete_entail_wit_1 : Delete_entail_wit_1.
Axiom proof_of_Delete_entail_wit_2 : Delete_entail_wit_2.
Axiom proof_of_Delete_entail_wit_3 : Delete_entail_wit_3.
Axiom proof_of_Delete_entail_wit_4 : Delete_entail_wit_4.
Axiom proof_of_Delete_entail_wit_5 : Delete_entail_wit_5.
Axiom proof_of_Delete_entail_wit_6_1 : Delete_entail_wit_6_1.
Axiom proof_of_Delete_entail_wit_6_2 : Delete_entail_wit_6_2.
Axiom proof_of_Delete_return_wit_1 : Delete_return_wit_1.
Axiom proof_of_Delete_return_wit_2 : Delete_return_wit_2.
Axiom proof_of_Delete_return_wit_3 : Delete_return_wit_3.
Axiom proof_of_Delete_return_wit_4 : Delete_return_wit_4.
Axiom proof_of_Delete_return_wit_5 : Delete_return_wit_5.
Axiom proof_of_Delete_partial_solve_wit_1 : Delete_partial_solve_wit_1.
Axiom proof_of_Delete_partial_solve_wit_2 : Delete_partial_solve_wit_2.
Axiom proof_of_Delete_partial_solve_wit_3 : Delete_partial_solve_wit_3.
Axiom proof_of_Delete_partial_solve_wit_4_pure : Delete_partial_solve_wit_4_pure.
Axiom proof_of_Delete_partial_solve_wit_4 : Delete_partial_solve_wit_4.
Axiom proof_of_Delete_derive_high_level_spec_by_low_level_spec : Delete_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
