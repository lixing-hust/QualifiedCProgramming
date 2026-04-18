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
Import naive_C_Rules.
Require Import array_max.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.

(*----- Function array_prefix_max -----*)

Definition array_prefix_max_safety_wit_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lo )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_prefix_max_safety_wit_2 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lo )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_prefix_max_safety_wit_3 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  ((( &( "cur" ) )) # Int  |-> (Znth 0 la 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full out_pre n_pre lo )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_prefix_max_safety_wit_4 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full out_pre n_pre (replace_Znth (0) ((Znth 0 la 0)) (lo)) )
  **  (IntArray.full a_pre n_pre la )
  **  ((( &( "cur" ) )) # Int  |-> (Znth 0 la 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition array_prefix_max_safety_wit_5 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (l1: (@list Z)) (i: Z) (cur: Z) ,
  [| (1 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (cur = (max_list_nonempty ((sublist (0) ((i + 1 )) (la))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (max_list_nonempty ((sublist (0) ((k + 1 )) (la)))))) |]
  &&  (IntArray.full out_pre n_pre (replace_Znth (i) (cur) ((app (l1) ((sublist (i) (n_pre) (lo)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (IntArray.full a_pre n_pre la )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_prefix_max_entail_wit_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full out_pre n_pre (replace_Znth (0) ((Znth 0 la 0)) (lo)) )
  **  (IntArray.full a_pre n_pre la )
|--
  EX (l1: (@list Z)) ,
  [| (1 <= 1) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = 1) |] 
  &&  [| ((Znth 0 la 0) = (max_list_nonempty ((sublist (0) (1) (la))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 1)) -> ((Znth k l1 0) = (max_list_nonempty ((sublist (0) ((k + 1 )) (la)))))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) ((sublist (1) (n_pre) (lo)))) )
.

Definition array_prefix_max_entail_wit_2_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (cur: Z) (l1_2: (@list Z)) (i: Z) ,
  [| ((Znth i la 0) > cur) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| (cur = (max_list_nonempty ((sublist (0) (i) (la))))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth k_2 l1_2 0) = (max_list_nonempty ((sublist (0) ((k_2 + 1 )) (la)))))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1_2) ((sublist (i) (n_pre) (lo)))) )
|--
  EX (l1: (@list Z)) ,
  [| (1 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Znth i la 0) = (max_list_nonempty ((sublist (0) ((i + 1 )) (la))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (max_list_nonempty ((sublist (0) ((k + 1 )) (la)))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) ((sublist (i) (n_pre) (lo)))) )
.

Definition array_prefix_max_entail_wit_2_2 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (cur: Z) (l1_2: (@list Z)) (i: Z) ,
  [| ((Znth i la 0) <= cur) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| (cur = (max_list_nonempty ((sublist (0) (i) (la))))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth k_2 l1_2 0) = (max_list_nonempty ((sublist (0) ((k_2 + 1 )) (la)))))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1_2) ((sublist (i) (n_pre) (lo)))) )
|--
  EX (l1: (@list Z)) ,
  [| (1 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (cur = (max_list_nonempty ((sublist (0) ((i + 1 )) (la))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (max_list_nonempty ((sublist (0) ((k + 1 )) (la)))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) ((sublist (i) (n_pre) (lo)))) )
.

Definition array_prefix_max_entail_wit_3 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (l1_2: (@list Z)) (i: Z) (cur: Z) ,
  [| (1 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| (cur = (max_list_nonempty ((sublist (0) ((i + 1 )) (la))))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth k_2 l1_2 0) = (max_list_nonempty ((sublist (0) ((k_2 + 1 )) (la)))))) |]
  &&  (IntArray.full out_pre n_pre (replace_Znth (i) (cur) ((app (l1_2) ((sublist (i) (n_pre) (lo)))))) )
  **  (IntArray.full a_pre n_pre la )
|--
  EX (l1: (@list Z)) ,
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = (i + 1 )) |] 
  &&  [| (cur = (max_list_nonempty ((sublist (0) ((i + 1 )) (la))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth k l1 0) = (max_list_nonempty ((sublist (0) ((k + 1 )) (la)))))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) ((sublist ((i + 1 )) (n_pre) (lo)))) )
.

Definition array_prefix_max_return_wit_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (cur: Z) (l1: (@list Z)) (i_2: Z) ,
  [| (i_2 >= n_pre) |] 
  &&  [| (1 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| (cur = (max_list_nonempty ((sublist (0) (i_2) (la))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i_2)) -> ((Znth k l1 0) = (max_list_nonempty ((sublist (0) ((k + 1 )) (la)))))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) ((sublist (i_2) (n_pre) (lo)))) )
|--
  EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i lr 0) = (max_list_nonempty ((sublist (0) ((i + 1 )) (la)))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lr )
.

Definition array_prefix_max_return_wit_2 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lo )
|--
  EX (lr: (@list Z)) ,
  [| ((Zlength (lr)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i lr 0) = (max_list_nonempty ((sublist (0) ((i + 1 )) (la)))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lr )
.

Definition array_prefix_max_partial_solve_wit_1 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lo )
|--
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (((a_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 la 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre la )
  **  (IntArray.full out_pre n_pre lo )
.

Definition array_prefix_max_partial_solve_wit_2 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre lo )
|--
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (((out_pre + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i out_pre 0 0 n_pre lo )
  **  (IntArray.full a_pre n_pre la )
.

Definition array_prefix_max_partial_solve_wit_3 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (cur: Z) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (cur = (max_list_nonempty ((sublist (0) (i) (la))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (max_list_nonempty ((sublist (0) ((k + 1 )) (la)))))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) ((sublist (i) (n_pre) (lo)))) )
|--
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (cur = (max_list_nonempty ((sublist (0) (i) (la))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (max_list_nonempty ((sublist (0) ((k + 1 )) (la)))))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i la 0))
  **  (IntArray.missing_i a_pre i 0 n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) ((sublist (i) (n_pre) (lo)))) )
.

Definition array_prefix_max_partial_solve_wit_4 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (cur: Z) (l1: (@list Z)) (i: Z) ,
  [| ((Znth i la 0) > cur) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (cur = (max_list_nonempty ((sublist (0) (i) (la))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (max_list_nonempty ((sublist (0) ((k + 1 )) (la)))))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) ((sublist (i) (n_pre) (lo)))) )
|--
  [| ((Znth i la 0) > cur) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (cur = (max_list_nonempty ((sublist (0) (i) (la))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (max_list_nonempty ((sublist (0) ((k + 1 )) (la)))))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((Zlength (la)) = n_pre) |] 
  &&  [| ((Zlength (lo)) = n_pre) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i la 0))
  **  (IntArray.missing_i a_pre i 0 n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) ((sublist (i) (n_pre) (lo)))) )
.

Definition array_prefix_max_partial_solve_wit_5 := 
forall (out_pre: Z) (a_pre: Z) (n_pre: Z) (lo: (@list Z)) (la: (@list Z)) (l1: (@list Z)) (i: Z) (cur: Z) ,
  [| (1 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (cur = (max_list_nonempty ((sublist (0) ((i + 1 )) (la))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (max_list_nonempty ((sublist (0) ((k + 1 )) (la)))))) |]
  &&  (IntArray.full a_pre n_pre la )
  **  (IntArray.full out_pre n_pre (app (l1) ((sublist (i) (n_pre) (lo)))) )
|--
  [| (1 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| (n_pre = (Zlength (la))) |] 
  &&  [| (n_pre = (Zlength (lo))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| (cur = (max_list_nonempty ((sublist (0) ((i + 1 )) (la))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = (max_list_nonempty ((sublist (0) ((k + 1 )) (la)))))) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i out_pre i 0 n_pre (app (l1) ((sublist (i) (n_pre) (lo)))) )
  **  (IntArray.full a_pre n_pre la )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_prefix_max_safety_wit_1 : array_prefix_max_safety_wit_1.
Axiom proof_of_array_prefix_max_safety_wit_2 : array_prefix_max_safety_wit_2.
Axiom proof_of_array_prefix_max_safety_wit_3 : array_prefix_max_safety_wit_3.
Axiom proof_of_array_prefix_max_safety_wit_4 : array_prefix_max_safety_wit_4.
Axiom proof_of_array_prefix_max_safety_wit_5 : array_prefix_max_safety_wit_5.
Axiom proof_of_array_prefix_max_entail_wit_1 : array_prefix_max_entail_wit_1.
Axiom proof_of_array_prefix_max_entail_wit_2_1 : array_prefix_max_entail_wit_2_1.
Axiom proof_of_array_prefix_max_entail_wit_2_2 : array_prefix_max_entail_wit_2_2.
Axiom proof_of_array_prefix_max_entail_wit_3 : array_prefix_max_entail_wit_3.
Axiom proof_of_array_prefix_max_return_wit_1 : array_prefix_max_return_wit_1.
Axiom proof_of_array_prefix_max_return_wit_2 : array_prefix_max_return_wit_2.
Axiom proof_of_array_prefix_max_partial_solve_wit_1 : array_prefix_max_partial_solve_wit_1.
Axiom proof_of_array_prefix_max_partial_solve_wit_2 : array_prefix_max_partial_solve_wit_2.
Axiom proof_of_array_prefix_max_partial_solve_wit_3 : array_prefix_max_partial_solve_wit_3.
Axiom proof_of_array_prefix_max_partial_solve_wit_4 : array_prefix_max_partial_solve_wit_4.
Axiom proof_of_array_prefix_max_partial_solve_wit_5 : array_prefix_max_partial_solve_wit_5.

End VC_Correct.
