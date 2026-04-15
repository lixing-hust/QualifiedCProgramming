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
Require Import coins_11.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import char_array_strategy_goal.
From SimpleC.EE Require Import char_array_strategy_proof.

(*----- Function string_xor -----*)

Definition string_xor_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval < retval_2) |] 
  &&  [| (retval_2 = nb) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (retval = na) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |]
  &&  ((( &( "output" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "n2" ) )) # Int  |-> retval_2)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| False |]
.

Definition string_xor_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (0 <= retval) |] 
  &&  [| (retval <= retval_2) |] 
  &&  [| (retval <= retval) |] 
  &&  [| (retval_2 >= retval) |] 
  &&  [| (retval = nb) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (retval_2 = na) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |]
  &&  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "n1" ) )) # Int  |-> retval_2)
  **  ((( &( "n2" ) )) # Int  |-> retval)
  **  ((( &( "output" ) )) # Ptr  |->_)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((retval + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval + 1 )) |]
.

Definition string_xor_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (0 <= retval_2) |] 
  &&  [| (retval_2 <= retval) |] 
  &&  [| (retval_2 <= retval_2) |] 
  &&  [| (retval >= retval_2) |] 
  &&  [| (retval_2 = nb) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (retval = na) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |]
  &&  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "n2" ) )) # Int  |-> retval_2)
  **  ((( &( "output" ) )) # Ptr  |->_)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_xor_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (0 <= retval_2) |] 
  &&  [| (retval_2 <= retval) |] 
  &&  [| (retval_2 <= retval_2) |] 
  &&  [| (retval >= retval_2) |] 
  &&  [| (retval_2 = nb) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (retval = na) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |]
  &&  (CharArray.undef_full retval_3 (retval_2 + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "n2" ) )) # Int  |-> retval_2)
  **  ((( &( "output" ) )) # Ptr  |-> retval_3)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_xor_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i >= nb) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (nb < na) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> nb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "output" ) )) # Ptr  |-> output)
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (nb + 1 ) )
|--
  [| False |]
.

Definition string_xor_safety_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < nb) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (nb < na) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> nb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "output" ) )) # Ptr  |-> output)
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (nb + 1 ) )
|--
  [| False |]
.

Definition string_xor_safety_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = (Znth i (app (l2) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (i < na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> na)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output" ) )) # Ptr  |-> output)
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition string_xor_safety_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> (Znth i (app (l2) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (i < na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> na)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output" ) )) # Ptr  |-> output)
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  [| (49 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 49) |]
.

Definition string_xor_safety_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> (Znth i (app (l2) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (i < na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  (CharArray.full output (i + 1 ) (app (out_l) ((cons (49) (nil)))) )
  **  (CharArray.undef_seg output (i + 1 ) (na + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> na)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output" ) )) # Ptr  |-> output)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_xor_safety_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = (Znth i (app (l2) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (i < na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  (CharArray.full output (i + 1 ) (app (out_l) ((cons (48) (nil)))) )
  **  (CharArray.undef_seg output (i + 1 ) (na + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> na)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output" ) )) # Ptr  |-> output)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_xor_safety_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i >= na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> na)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "output" ) )) # Ptr  |-> output)
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_xor_entail_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval >= retval_2) |] 
  &&  [| (retval_2 = nb) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (retval = na) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= retval_2) |] 
  &&  [| (retval_2 <= retval) |] 
  &&  [| (retval_2 <= retval_2) |] 
  &&  [| (retval >= retval_2) |] 
  &&  [| (retval_2 = nb) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (retval = na) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition string_xor_entail_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval_2: Z) (retval_3: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= retval_3) |] 
  &&  [| (retval_3 <= retval_2) |] 
  &&  [| (retval_3 <= retval_3) |] 
  &&  [| (retval_2 >= retval_3) |] 
  &&  [| (retval_3 = nb) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (retval_2 = na) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |]
  &&  (CharArray.undef_full retval (retval_3 + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> retval_3)
  **  ((( &( "n1" ) )) # Int  |-> retval_2)
  **  ((( &( "n2" ) )) # Int  |-> retval_3)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  (EX (out_l: (@list Z)) ,
  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (nb < na) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| ((Zlength (out_l)) = 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> nb)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (nb + 1 ) ))
  ||
  (EX (out_l: (@list Z)) ,
  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> na)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (na + 1 ) ))
.

Definition string_xor_entail_wit_3_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = (Znth i (app (l2) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (i < na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l_2) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l_2) (0)) = 49)))) |]
  &&  (CharArray.full output (i + 1 ) (app (out_l_2) ((cons (48) (nil)))) )
  **  (CharArray.undef_seg output (i + 1 ) (na + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> na)
|--
  (EX (out_l: (@list Z)) ,
  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (nb < na) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  ((( &( "n" ) )) # Int  |-> nb)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (i + 1 ) out_l )
  **  (CharArray.undef_seg output (i + 1 ) (nb + 1 ) ))
  ||
  (EX (out_l: (@list Z)) ,
  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  ((( &( "n" ) )) # Int  |-> na)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (i + 1 ) out_l )
  **  (CharArray.undef_seg output (i + 1 ) (na + 1 ) ))
.

Definition string_xor_entail_wit_3_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> (Znth i (app (l2) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (i < na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l_2) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l_2) (0)) = 49)))) |]
  &&  (CharArray.full output (i + 1 ) (app (out_l_2) ((cons (49) (nil)))) )
  **  (CharArray.undef_seg output (i + 1 ) (na + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> na)
|--
  (EX (out_l: (@list Z)) ,
  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (nb < na) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  ((( &( "n" ) )) # Int  |-> nb)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (i + 1 ) out_l )
  **  (CharArray.undef_seg output (i + 1 ) (nb + 1 ) ))
  ||
  (EX (out_l: (@list Z)) ,
  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  ((( &( "n" ) )) # Int  |-> na)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (i + 1 ) out_l )
  **  (CharArray.undef_seg output (i + 1 ) (na + 1 ) ))
.

Definition string_xor_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (i >= na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l_2) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l_2) (0)) = 49)))) |]
  &&  (CharArray.full output (i + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg output (na + 1 ) (na + 1 ) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  (EX (out_l: (@list Z))  (n: Z) ,
  [| (nb < na) |] 
  &&  [| (n = nb) |] 
  &&  [| ((Zlength (out_l)) = n) |] 
  &&  [| (problem_11_spec_z l1 l2 out_l ) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (n + 1 ) (app (out_l) ((cons (0) (nil)))) ))
  ||
  (EX (out_l: (@list Z))  (n: Z) ,
  [| (na <= nb) |] 
  &&  [| (n = na) |] 
  &&  [| ((Zlength (out_l)) = n) |] 
  &&  [| (problem_11_spec_z l1 l2 out_l ) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (n + 1 ) (app (out_l) ((cons (0) (nil)))) ))
.

Definition string_xor_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition string_xor_partial_solve_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) ,
  [| (retval = na) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= (na + 1 )) |] 
  &&  [| (retval = na) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition string_xor_partial_solve_wit_3_pure := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (0 <= retval) |] 
  &&  [| (retval <= retval_2) |] 
  &&  [| (retval <= retval) |] 
  &&  [| (retval_2 >= retval) |] 
  &&  [| (retval = nb) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (retval_2 = na) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |]
  &&  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "n1" ) )) # Int  |-> retval_2)
  **  ((( &( "n2" ) )) # Int  |-> retval)
  **  ((( &( "output" ) )) # Ptr  |->_)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  [| ((retval + 1 ) > 0) |]
.

Definition string_xor_partial_solve_wit_3_aux := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (0 <= retval) |] 
  &&  [| (retval <= retval_2) |] 
  &&  [| (retval <= retval) |] 
  &&  [| (retval_2 >= retval) |] 
  &&  [| (retval = nb) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (retval_2 = na) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((retval + 1 ) > 0) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= retval_2) |] 
  &&  [| (retval <= retval) |] 
  &&  [| (retval_2 >= retval) |] 
  &&  [| (retval = nb) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (retval_2 = na) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition string_xor_partial_solve_wit_3 := string_xor_partial_solve_wit_3_pure -> string_xor_partial_solve_wit_3_aux.

Definition string_xor_partial_solve_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  [| (0 <= (nb + 1 )) |] 
  &&  [| (i < na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  (((a_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i a_pre i 0 (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
.

Definition string_xor_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (nb + 1 )) |] 
  &&  [| (i < na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  [| (0 <= (na + 1 )) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (i < na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  (((b_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l2) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i b_pre i 0 (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
.

Definition string_xor_partial_solve_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = (Znth i (app (l2) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (i < na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = (Znth i (app (l2) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (i < na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  (((output + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i output i i (na + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
.

Definition string_xor_partial_solve_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> (Znth i (app (l2) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (i < na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> (Znth i (app (l2) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (i < na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  (((output + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i output i i (na + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
.

Definition string_xor_partial_solve_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i >= na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| (i >= na) |] 
  &&  [| ((Zlength (l1)) = na) |] 
  &&  [| ((Zlength (l2)) = nb) |] 
  &&  [| (na = nb) |] 
  &&  [| (problem_11_pre_z l1 l2 ) |] 
  &&  [| (na <= nb) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth (k) (l1) (0)) = (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 48)) \/ (((Znth (k) (l1) (0)) <> (Znth (k) (l2) (0))) /\ ((Znth (k) (out_l) (0)) = 49)))) |]
  &&  (((output + (na * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i output na i (na + 1 ) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_xor_safety_wit_1 : string_xor_safety_wit_1.
Axiom proof_of_string_xor_safety_wit_2 : string_xor_safety_wit_2.
Axiom proof_of_string_xor_safety_wit_3 : string_xor_safety_wit_3.
Axiom proof_of_string_xor_safety_wit_4 : string_xor_safety_wit_4.
Axiom proof_of_string_xor_safety_wit_5 : string_xor_safety_wit_5.
Axiom proof_of_string_xor_safety_wit_6 : string_xor_safety_wit_6.
Axiom proof_of_string_xor_safety_wit_7 : string_xor_safety_wit_7.
Axiom proof_of_string_xor_safety_wit_8 : string_xor_safety_wit_8.
Axiom proof_of_string_xor_safety_wit_9 : string_xor_safety_wit_9.
Axiom proof_of_string_xor_safety_wit_10 : string_xor_safety_wit_10.
Axiom proof_of_string_xor_safety_wit_11 : string_xor_safety_wit_11.
Axiom proof_of_string_xor_entail_wit_1 : string_xor_entail_wit_1.
Axiom proof_of_string_xor_entail_wit_2 : string_xor_entail_wit_2.
Axiom proof_of_string_xor_entail_wit_3_1 : string_xor_entail_wit_3_1.
Axiom proof_of_string_xor_entail_wit_3_2 : string_xor_entail_wit_3_2.
Axiom proof_of_string_xor_return_wit_1 : string_xor_return_wit_1.
Axiom proof_of_string_xor_partial_solve_wit_1 : string_xor_partial_solve_wit_1.
Axiom proof_of_string_xor_partial_solve_wit_2 : string_xor_partial_solve_wit_2.
Axiom proof_of_string_xor_partial_solve_wit_3_pure : string_xor_partial_solve_wit_3_pure.
Axiom proof_of_string_xor_partial_solve_wit_3 : string_xor_partial_solve_wit_3.
Axiom proof_of_string_xor_partial_solve_wit_4 : string_xor_partial_solve_wit_4.
Axiom proof_of_string_xor_partial_solve_wit_5 : string_xor_partial_solve_wit_5.
Axiom proof_of_string_xor_partial_solve_wit_6 : string_xor_partial_solve_wit_6.
Axiom proof_of_string_xor_partial_solve_wit_7 : string_xor_partial_solve_wit_7.
Axiom proof_of_string_xor_partial_solve_wit_8 : string_xor_partial_solve_wit_8.

End VC_Correct.
