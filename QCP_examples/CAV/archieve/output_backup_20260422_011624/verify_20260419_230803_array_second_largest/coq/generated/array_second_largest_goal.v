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
Require Import array_second_largest.
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

(*----- Function array_second_largest -----*)

Definition array_second_largest_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  ((( &( "max1" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition array_second_largest_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  ((( &( "max2" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre l )
  **  ((( &( "max1" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition array_second_largest_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "max2" ) )) # Int  |-> (Znth 1 l 0))
  **  ((( &( "max1" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition array_second_largest_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "max2" ) )) # Int  |-> (Znth 0 l 0))
  **  ((( &( "max1" ) )) # Int  |-> (Znth 1 l 0))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition array_second_largest_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i: Z) ,
  [| ((Znth i l 0) <= max2) |] 
  &&  [| ((Znth i l 0) <= max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , forall (j: Z) , ((((((0 <= i_2) /\ (i_2 < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i_2 <> j)) -> ((Znth i_2 l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "max2" ) )) # Int  |-> max2)
  **  ((( &( "max1" ) )) # Int  |-> max1)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_second_largest_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i: Z) ,
  [| ((Znth i l 0) <= max2) |] 
  &&  [| ((Znth i l 0) <= max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , forall (j: Z) , ((((((0 <= i_2) /\ (i_2 < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i_2 <> j)) -> ((Znth i_2 l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "max2" ) )) # Int  |-> max2)
  **  ((( &( "max1" ) )) # Int  |-> max1)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_second_largest_safety_wit_7 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i: Z) ,
  [| ((Znth i l 0) > max2) |] 
  &&  [| ((Znth i l 0) <= max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , forall (j: Z) , ((((((0 <= i_2) /\ (i_2 < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i_2 <> j)) -> ((Znth i_2 l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "max2" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "max1" ) )) # Int  |-> max1)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_second_largest_safety_wit_8 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i: Z) ,
  [| ((Znth i l 0) > max2) |] 
  &&  [| ((Znth i l 0) <= max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , forall (j: Z) , ((((((0 <= i_2) /\ (i_2 < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i_2 <> j)) -> ((Znth i_2 l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "max2" ) )) # Int  |-> (Znth i l 0))
  **  ((( &( "max1" ) )) # Int  |-> max1)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_second_largest_safety_wit_9 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i: Z) ,
  [| ((Znth i l 0) > max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , forall (j: Z) , ((((((0 <= i_2) /\ (i_2 < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i_2 <> j)) -> ((Znth i_2 l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "max2" ) )) # Int  |-> max1)
  **  ((( &( "max1" ) )) # Int  |-> (Znth i l 0))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_second_largest_safety_wit_10 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i: Z) ,
  [| ((Znth i l 0) > max1) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_2: Z) , forall (j: Z) , ((((((0 <= i_2) /\ (i_2 < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i_2 <> j)) -> ((Znth i_2 l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "max2" ) )) # Int  |-> max1)
  **  ((( &( "max1" ) )) # Int  |-> (Znth i l 0))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition array_second_largest_entail_wit_1_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  ([| (2 <= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((second_largest_acc ((Znth 1 l 0)) ((Znth 0 l 0)) ((sublist (2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
  ||
  ([| (2 <= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((second_largest_acc ((Znth 1 l 0)) ((Znth 0 l 0)) ((sublist (2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
.

Definition array_second_largest_entail_wit_1_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  ([| (2 <= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((second_largest_acc ((Znth 0 l 0)) ((Znth 1 l 0)) ((sublist (2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
  ||
  ([| (2 <= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((second_largest_acc ((Znth 0 l 0)) ((Znth 1 l 0)) ((sublist (2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
.

Definition array_second_largest_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| ((Znth i_2 l 0) > max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  ([| (2 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((second_largest_acc ((Znth i_2 l 0)) (max1) ((sublist ((i_2 + 1 )) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
  ||
  ([| (2 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((second_largest_acc ((Znth i_2 l 0)) (max1) ((sublist ((i_2 + 1 )) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
.

Definition array_second_largest_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| ((Znth i_2 l 0) > max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  ([| (2 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((second_largest_acc ((Znth i_2 l 0)) (max1) ((sublist ((i_2 + 1 )) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
  ||
  ([| (2 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((second_largest_acc ((Znth i_2 l 0)) (max1) ((sublist ((i_2 + 1 )) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
.

Definition array_second_largest_entail_wit_2_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| ((Znth i_2 l 0) > max2) |] 
  &&  [| ((Znth i_2 l 0) <= max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  ([| (2 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) ((Znth i_2 l 0)) ((sublist ((i_2 + 1 )) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
  ||
  ([| (2 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) ((Znth i_2 l 0)) ((sublist ((i_2 + 1 )) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
.

Definition array_second_largest_entail_wit_2_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| ((Znth i_2 l 0) > max2) |] 
  &&  [| ((Znth i_2 l 0) <= max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  ([| (2 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) ((Znth i_2 l 0)) ((sublist ((i_2 + 1 )) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
  ||
  ([| (2 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) ((Znth i_2 l 0)) ((sublist ((i_2 + 1 )) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
.

Definition array_second_largest_entail_wit_2_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| ((Znth i_2 l 0) <= max2) |] 
  &&  [| ((Znth i_2 l 0) <= max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  ([| (2 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist ((i_2 + 1 )) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
  ||
  ([| (2 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist ((i_2 + 1 )) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
.

Definition array_second_largest_entail_wit_2_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| ((Znth i_2 l 0) <= max2) |] 
  &&  [| ((Znth i_2 l 0) <= max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  ([| (2 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist ((i_2 + 1 )) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
  ||
  ([| (2 <= (i_2 + 1 )) |] 
  &&  [| ((i_2 + 1 ) <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist ((i_2 + 1 )) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l ))
.

Definition array_second_largest_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| (i_2 >= n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (max2 = (second_largest_list (l))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_second_largest_return_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| (i_2 >= n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (max2 = (second_largest_list (l))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_second_largest_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (((a_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre l )
.

Definition array_second_largest_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (((a_pre + (1 * sizeof(INT) ) )) # Int  |-> (Znth 1 l 0))
  **  (IntArray.missing_i a_pre 1 0 n_pre l )
.

Definition array_second_largest_partial_solve_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l )
.

Definition array_second_largest_partial_solve_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l )
.

Definition array_second_largest_partial_solve_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| ((Znth i_2 l 0) > max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| ((Znth i_2 l 0) > max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l )
.

Definition array_second_largest_partial_solve_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| ((Znth i_2 l 0) > max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| ((Znth i_2 l 0) > max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l )
.

Definition array_second_largest_partial_solve_wit_7 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| ((Znth i_2 l 0) <= max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| ((Znth i_2 l 0) <= max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l )
.

Definition array_second_largest_partial_solve_wit_8 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| ((Znth i_2 l 0) <= max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| ((Znth i_2 l 0) <= max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l )
.

Definition array_second_largest_partial_solve_wit_9 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| ((Znth i_2 l 0) > max2) |] 
  &&  [| ((Znth i_2 l 0) <= max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| ((Znth i_2 l 0) > max2) |] 
  &&  [| ((Znth i_2 l 0) <= max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) <= (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l )
.

Definition array_second_largest_partial_solve_wit_10 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (max1: Z) (max2: Z) (i_2: Z) ,
  [| ((Znth i_2 l 0) > max2) |] 
  &&  [| ((Znth i_2 l 0) <= max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| ((Znth i_2 l 0) > max2) |] 
  &&  [| ((Znth i_2 l 0) <= max1) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| ((second_largest_acc (max1) (max2) ((sublist (i_2) (n_pre) (l)))) = (second_largest_list (l))) |] 
  &&  [| ((Znth 1 l 0) > (Znth 0 l 0)) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((((0 <= i) /\ (i < n_pre)) /\ (0 <= j)) /\ (j < n_pre)) /\ (i <> j)) -> ((Znth i l 0) <> (Znth j l 0))) |]
  &&  (((a_pre + (i_2 * sizeof(INT) ) )) # Int  |-> (Znth i_2 l 0))
  **  (IntArray.missing_i a_pre i_2 0 n_pre l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_second_largest_safety_wit_1 : array_second_largest_safety_wit_1.
Axiom proof_of_array_second_largest_safety_wit_2 : array_second_largest_safety_wit_2.
Axiom proof_of_array_second_largest_safety_wit_3 : array_second_largest_safety_wit_3.
Axiom proof_of_array_second_largest_safety_wit_4 : array_second_largest_safety_wit_4.
Axiom proof_of_array_second_largest_safety_wit_5 : array_second_largest_safety_wit_5.
Axiom proof_of_array_second_largest_safety_wit_6 : array_second_largest_safety_wit_6.
Axiom proof_of_array_second_largest_safety_wit_7 : array_second_largest_safety_wit_7.
Axiom proof_of_array_second_largest_safety_wit_8 : array_second_largest_safety_wit_8.
Axiom proof_of_array_second_largest_safety_wit_9 : array_second_largest_safety_wit_9.
Axiom proof_of_array_second_largest_safety_wit_10 : array_second_largest_safety_wit_10.
Axiom proof_of_array_second_largest_entail_wit_1_1 : array_second_largest_entail_wit_1_1.
Axiom proof_of_array_second_largest_entail_wit_1_2 : array_second_largest_entail_wit_1_2.
Axiom proof_of_array_second_largest_entail_wit_2_1 : array_second_largest_entail_wit_2_1.
Axiom proof_of_array_second_largest_entail_wit_2_2 : array_second_largest_entail_wit_2_2.
Axiom proof_of_array_second_largest_entail_wit_2_3 : array_second_largest_entail_wit_2_3.
Axiom proof_of_array_second_largest_entail_wit_2_4 : array_second_largest_entail_wit_2_4.
Axiom proof_of_array_second_largest_entail_wit_2_5 : array_second_largest_entail_wit_2_5.
Axiom proof_of_array_second_largest_entail_wit_2_6 : array_second_largest_entail_wit_2_6.
Axiom proof_of_array_second_largest_return_wit_1 : array_second_largest_return_wit_1.
Axiom proof_of_array_second_largest_return_wit_2 : array_second_largest_return_wit_2.
Axiom proof_of_array_second_largest_partial_solve_wit_1 : array_second_largest_partial_solve_wit_1.
Axiom proof_of_array_second_largest_partial_solve_wit_2 : array_second_largest_partial_solve_wit_2.
Axiom proof_of_array_second_largest_partial_solve_wit_3 : array_second_largest_partial_solve_wit_3.
Axiom proof_of_array_second_largest_partial_solve_wit_4 : array_second_largest_partial_solve_wit_4.
Axiom proof_of_array_second_largest_partial_solve_wit_5 : array_second_largest_partial_solve_wit_5.
Axiom proof_of_array_second_largest_partial_solve_wit_6 : array_second_largest_partial_solve_wit_6.
Axiom proof_of_array_second_largest_partial_solve_wit_7 : array_second_largest_partial_solve_wit_7.
Axiom proof_of_array_second_largest_partial_solve_wit_8 : array_second_largest_partial_solve_wit_8.
Axiom proof_of_array_second_largest_partial_solve_wit_9 : array_second_largest_partial_solve_wit_9.
Axiom proof_of_array_second_largest_partial_solve_wit_10 : array_second_largest_partial_solve_wit_10.

End VC_Correct.
