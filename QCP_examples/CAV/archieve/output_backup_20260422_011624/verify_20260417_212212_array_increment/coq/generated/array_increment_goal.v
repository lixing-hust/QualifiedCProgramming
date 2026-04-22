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

(*----- Function array_increment -----*)

Definition array_increment_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i l 0) < INT_MAX)) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_increment_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = ((Znth k l 0) + 1 ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 l 0) < INT_MAX)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.missing_i a_pre i 0 n_pre (app (l1) (l2)) )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (((Znth i l 0) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i l 0) + 1 )) |]
.

Definition array_increment_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i_2 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i_2)) -> ((Znth k l1 0) = ((Znth k l 0) + 1 ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i_2 ))) -> ((Znth k_2 l2 0) = (Znth (i_2 + k_2 ) l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i l 0) < INT_MAX)) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.missing_i a_pre i_2 0 n_pre (app (l1) (l2)) )
  **  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition array_increment_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) (l1': (@list Z)) ,
  [| ((Zlength (l1')) = (i + 1 )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((Znth k_3 l1' 0) = ((Znth k_3 l 0) + 1 ))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = ((Znth k l 0) + 1 ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 l 0) < INT_MAX)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre (app (l1') ((sublist ((i + 1 )) (n_pre) (l)))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_increment_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i l 0) < INT_MAX)) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = 0) |] 
  &&  [| ((Zlength (l2)) = (n_pre - 0 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth k l1 0) = ((Znth k l 0) + 1 ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - 0 ))) -> ((Znth k_2 l2 0) = (Znth (0 + k_2 ) l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i l 0) < INT_MAX)) |]
  &&  (IntArray.full a_pre n_pre (app (l1) (l2)) )
.

Definition array_increment_entail_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l2_2: (@list Z)) (l1_2: (@list Z)) (i_2: Z) (l1': (@list Z)) ,
  [| ((Zlength (l1')) = (i_2 + 1 )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i_2 + 1 ))) -> ((Znth k_3 l1' 0) = ((Znth k_3 l 0) + 1 ))) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1_2)) = i_2) |] 
  &&  [| ((Zlength (l2_2)) = (n_pre - i_2 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i_2)) -> ((Znth k l1_2 0) = ((Znth k l 0) + 1 ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i_2 ))) -> ((Znth k_2 l2_2 0) = (Znth (i_2 + k_2 ) l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i l 0) < INT_MAX)) |]
  &&  (IntArray.full a_pre n_pre (app (l1') ((sublist ((i_2 + 1 )) (n_pre) (l)))) )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| (0 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = (i_2 + 1 )) |] 
  &&  [| ((Zlength (l2)) = (n_pre - (i_2 + 1 ) )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i_2 + 1 ))) -> ((Znth k l1 0) = ((Znth k l 0) + 1 ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - (i_2 + 1 ) ))) -> ((Znth k_2 l2 0) = (Znth ((i_2 + 1 ) + k_2 ) l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i l 0) < INT_MAX)) |]
  &&  (IntArray.full a_pre n_pre (app (l1) (l2)) )
.

Definition array_increment_entail_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i_2: Z) ,
  [| (i_2 >= n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i_2) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i_2 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i_2)) -> ((Znth k_2 l1 0) = ((Znth k_2 l 0) + 1 ))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre - i_2 ))) -> ((Znth k_3 l2 0) = (Znth (i_2 + k_3 ) l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i l 0) < INT_MAX)) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  (IntArray.full a_pre n_pre (app (l1) (l2)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  EX (l0: (@list Z)) ,
  [| ((Zlength (l0)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l0 0) = ((Znth k l 0) + 1 ))) |]
  &&  ((( &( "i" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l0 )
.

Definition array_increment_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l0_2: (@list Z)) (a: Z) ,
  [| ((Zlength (l0_2)) = n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k l0_2 0) = ((Znth k l 0) + 1 ))) |]
  &&  (IntArray.full a n_pre l0_2 )
|--
  EX (l0: (@list Z)) ,
  [| ((Zlength (l0)) = n_pre) |] 
  &&  [| forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i l0 0) = ((Znth i l 0) + 1 ))) |]
  &&  (IntArray.full a_pre n_pre l0 )
.

Definition array_increment_partial_solve_wit_1_pure := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = ((Znth k_3 l 0) + 1 ))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 l 0) < INT_MAX)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre (app (l1) (l2)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = ((Znth k l 0) + 1 ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) l 0))) |]
.

Definition array_increment_partial_solve_wit_1_aux := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = ((Znth k_3 l 0) + 1 ))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 l 0) < INT_MAX)) |]
  &&  (IntArray.full a_pre n_pre (app (l1) (l2)) )
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = ((Znth k l 0) + 1 ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) l 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = ((Znth k_3 l 0) + 1 ))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 l 0) < INT_MAX)) |]
  &&  (IntArray.full a_pre n_pre (app (l1) (l2)) )
.

Definition array_increment_partial_solve_wit_1 := array_increment_partial_solve_wit_1_pure -> array_increment_partial_solve_wit_1_aux.

Definition array_increment_partial_solve_wit_2_pure := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = ((Znth k_3 l 0) + 1 ))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 l 0) < INT_MAX)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.missing_i a_pre i 0 n_pre (app (l1) (l2)) )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> ((Znth i l 0) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = ((Znth k l 0) + 1 ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) l 0))) |]
.

Definition array_increment_partial_solve_wit_2_aux := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = ((Znth k_3 l 0) + 1 ))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 l 0) < INT_MAX)) |]
  &&  (IntArray.missing_i a_pre i 0 n_pre (app (l1) (l2)) )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> ((Znth i l 0) + 1 ))
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = ((Znth k l 0) + 1 ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) l 0))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth k_3 l1 0) = ((Znth k_3 l 0) + 1 ))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre - i ))) -> ((Znth k_4 l2 0) = (Znth (i + k_4 ) l 0))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Znth i_2 l 0) < INT_MAX)) |]
  &&  (IntArray.missing_i a_pre i 0 n_pre (app (l1) (l2)) )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> ((Znth i l 0) + 1 ))
.

Definition array_increment_partial_solve_wit_2 := array_increment_partial_solve_wit_2_pure -> array_increment_partial_solve_wit_2_aux.

Definition array_increment_which_implies_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k l1 0) = ((Znth k l 0) + 1 ))) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre - i ))) -> ((Znth k_2 l2 0) = (Znth (i + k_2 ) l 0))) |]
  &&  (IntArray.full a_pre n_pre (app (l1) (l2)) )
|--
  (IntArray.missing_i a_pre i 0 n_pre (app (l1) (l2)) )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
.

Definition array_increment_which_implies_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (l2: (@list Z)) (l1: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n_pre - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth k_2 l1 0) = ((Znth k_2 l 0) + 1 ))) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre - i ))) -> ((Znth k_3 l2 0) = (Znth (i + k_3 ) l 0))) |]
  &&  (IntArray.missing_i a_pre i 0 n_pre (app (l1) (l2)) )
  **  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> ((Znth i l 0) + 1 ))
|--
  EX (l1': (@list Z)) ,
  [| ((Zlength (l1')) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth k l1' 0) = ((Znth k l 0) + 1 ))) |]
  &&  (IntArray.full a_pre n_pre (app (l1') ((sublist ((i + 1 )) (n_pre) (l)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_increment_safety_wit_1 : array_increment_safety_wit_1.
Axiom proof_of_array_increment_safety_wit_2 : array_increment_safety_wit_2.
Axiom proof_of_array_increment_safety_wit_3 : array_increment_safety_wit_3.
Axiom proof_of_array_increment_safety_wit_4 : array_increment_safety_wit_4.
Axiom proof_of_array_increment_entail_wit_1 : array_increment_entail_wit_1.
Axiom proof_of_array_increment_entail_wit_2 : array_increment_entail_wit_2.
Axiom proof_of_array_increment_entail_wit_3 : array_increment_entail_wit_3.
Axiom proof_of_array_increment_return_wit_1 : array_increment_return_wit_1.
Axiom proof_of_array_increment_partial_solve_wit_1_pure : array_increment_partial_solve_wit_1_pure.
Axiom proof_of_array_increment_partial_solve_wit_1 : array_increment_partial_solve_wit_1.
Axiom proof_of_array_increment_partial_solve_wit_2_pure : array_increment_partial_solve_wit_2_pure.
Axiom proof_of_array_increment_partial_solve_wit_2 : array_increment_partial_solve_wit_2.
Axiom proof_of_array_increment_which_implies_wit_1 : array_increment_which_implies_wit_1.
Axiom proof_of_array_increment_which_implies_wit_2 : array_increment_which_implies_wit_2.

End VC_Correct.
