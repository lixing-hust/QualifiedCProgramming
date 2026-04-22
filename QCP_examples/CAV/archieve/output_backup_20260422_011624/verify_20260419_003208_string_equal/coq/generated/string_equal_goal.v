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
Require Import string_equal.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import char_array_strategy_goal.
From SimpleC.EE Require Import char_array_strategy_proof.

(*----- Function string_equal -----*)

Definition string_equal_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_equal_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> (Znth i (app (lb) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = (Znth i (app (lb) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_equal_safety_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < na)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> na)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> nb)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth nb (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> nb)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth na (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < na)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> na)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (nb = na) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  ((( &( "i" ) )) # Int  |-> nb)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_equal_safety_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| ((Znth nb (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth nb (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> nb)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_13 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| ((Znth na (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth na (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < na)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> na)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_14 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| ((Znth na (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < na)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> na)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_safety_wit_15 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| ((Znth nb (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> nb)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_equal_entail_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= na) |] 
  &&  [| (0 <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < 0)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_entail_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = (Znth i (app (lb) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= na) |] 
  &&  [| ((i + 1 ) <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_entail_wit_3_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < na)) -> ((Znth (k_5) (la) (0)) <> 0)) |] 
  &&  [| forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < nb)) -> ((Znth (k_6) (lb) (0)) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth (j_2) (la) (0)) = (Znth (j_2) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth k_3 la 0) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth k_4 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  ([| (0 <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < na)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  ((( &( "i" ) )) # Int  |-> na)
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
  ||
  ([| (0 <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  ((( &( "i" ) )) # Int  |-> nb)
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
.

Definition string_equal_entail_wit_3_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < na)) -> ((Znth (k_5) (la) (0)) <> 0)) |] 
  &&  [| forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < nb)) -> ((Znth (k_6) (lb) (0)) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth (j_2) (la) (0)) = (Znth (j_2) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth k_3 la 0) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth k_4 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  ([| (0 <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < na)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  ((( &( "i" ) )) # Int  |-> na)
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
  ||
  ([| (0 <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  ((( &( "i" ) )) # Int  |-> nb)
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) ))
.

Definition string_equal_entail_wit_4_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| ((Znth na (app (lb) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth na (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < na)) -> ((Znth (j_2) (la) (0)) = (Znth (j_2) (lb) (0)))) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> na)
|--
  [| (nb = na) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  ((( &( "i" ) )) # Int  |-> nb)
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_entail_wit_4_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| ((Znth nb (app (lb) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth nb (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < nb)) -> ((Znth (j_2) (la) (0)) = (Znth (j_2) (lb) (0)))) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
|--
  [| (nb = na) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> (Znth i (app (lb) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
|--
  [| (0 = (string_equal_spec (la) (lb))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_return_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (nb = na) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (1 = (string_equal_spec (la) (lb))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_return_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| ((Znth nb (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth nb (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
|--
  [| (0 = (string_equal_spec (la) (lb))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_return_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| ((Znth na (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth na (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < na)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
|--
  [| (0 = (string_equal_spec (la) (lb))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_return_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| ((Znth na (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < na)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 = (string_equal_spec (la) (lb))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_return_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| ((Znth nb (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 = (string_equal_spec (la) (lb))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (((a_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (la) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i a_pre i 0 (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_partial_solve_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (((b_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (lb) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i b_pre i 0 (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
.

Definition string_equal_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (((a_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (la) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i a_pre i 0 (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_partial_solve_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (i: Z) ,
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (lb) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= na) |] 
  &&  [| (i <= nb) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (la) (0)) <> 0)) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na < INT_MAX) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb < INT_MAX) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) |]
  &&  (((b_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (lb) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i b_pre i 0 (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
.

Definition string_equal_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < na)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < na)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (((a_pre + (na * sizeof(CHAR) ) )) # Char  |-> (Znth na (app (la) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i a_pre na 0 (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_partial_solve_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| (0 <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (((a_pre + (nb * sizeof(CHAR) ) )) # Char  |-> (Znth nb (app (la) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i a_pre nb 0 (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition string_equal_partial_solve_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| ((Znth nb (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth nb (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= nb) |] 
  &&  [| (nb <= na) |] 
  &&  [| (nb <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < nb)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (((b_pre + (nb * sizeof(CHAR) ) )) # Char  |-> (Znth nb (app (lb) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i b_pre nb 0 (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
.

Definition string_equal_partial_solve_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  [| ((Znth na (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < na)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  [| (0 <= (na + 1 )) |] 
  &&  [| ((Znth na (app (la) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= (nb + 1 )) |] 
  &&  [| (0 <= na) |] 
  &&  [| (na <= na) |] 
  &&  [| (na <= nb) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (la) (0)) <> 0)) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (lb) (0)) <> 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < na)) -> ((Znth (j) (la) (0)) = (Znth (j) (lb) (0)))) |]
  &&  (((b_pre + (na * sizeof(CHAR) ) )) # Char  |-> (Znth na (app (lb) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i b_pre na 0 (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_equal_safety_wit_1 : string_equal_safety_wit_1.
Axiom proof_of_string_equal_safety_wit_2 : string_equal_safety_wit_2.
Axiom proof_of_string_equal_safety_wit_3 : string_equal_safety_wit_3.
Axiom proof_of_string_equal_safety_wit_4 : string_equal_safety_wit_4.
Axiom proof_of_string_equal_safety_wit_5 : string_equal_safety_wit_5.
Axiom proof_of_string_equal_safety_wit_6 : string_equal_safety_wit_6.
Axiom proof_of_string_equal_safety_wit_7 : string_equal_safety_wit_7.
Axiom proof_of_string_equal_safety_wit_8 : string_equal_safety_wit_8.
Axiom proof_of_string_equal_safety_wit_9 : string_equal_safety_wit_9.
Axiom proof_of_string_equal_safety_wit_10 : string_equal_safety_wit_10.
Axiom proof_of_string_equal_safety_wit_11 : string_equal_safety_wit_11.
Axiom proof_of_string_equal_safety_wit_12 : string_equal_safety_wit_12.
Axiom proof_of_string_equal_safety_wit_13 : string_equal_safety_wit_13.
Axiom proof_of_string_equal_safety_wit_14 : string_equal_safety_wit_14.
Axiom proof_of_string_equal_safety_wit_15 : string_equal_safety_wit_15.
Axiom proof_of_string_equal_entail_wit_1 : string_equal_entail_wit_1.
Axiom proof_of_string_equal_entail_wit_2 : string_equal_entail_wit_2.
Axiom proof_of_string_equal_entail_wit_3_1 : string_equal_entail_wit_3_1.
Axiom proof_of_string_equal_entail_wit_3_2 : string_equal_entail_wit_3_2.
Axiom proof_of_string_equal_entail_wit_4_1 : string_equal_entail_wit_4_1.
Axiom proof_of_string_equal_entail_wit_4_2 : string_equal_entail_wit_4_2.
Axiom proof_of_string_equal_return_wit_1 : string_equal_return_wit_1.
Axiom proof_of_string_equal_return_wit_2 : string_equal_return_wit_2.
Axiom proof_of_string_equal_return_wit_3 : string_equal_return_wit_3.
Axiom proof_of_string_equal_return_wit_4 : string_equal_return_wit_4.
Axiom proof_of_string_equal_return_wit_5 : string_equal_return_wit_5.
Axiom proof_of_string_equal_return_wit_6 : string_equal_return_wit_6.
Axiom proof_of_string_equal_partial_solve_wit_1 : string_equal_partial_solve_wit_1.
Axiom proof_of_string_equal_partial_solve_wit_2 : string_equal_partial_solve_wit_2.
Axiom proof_of_string_equal_partial_solve_wit_3 : string_equal_partial_solve_wit_3.
Axiom proof_of_string_equal_partial_solve_wit_4 : string_equal_partial_solve_wit_4.
Axiom proof_of_string_equal_partial_solve_wit_5 : string_equal_partial_solve_wit_5.
Axiom proof_of_string_equal_partial_solve_wit_6 : string_equal_partial_solve_wit_6.
Axiom proof_of_string_equal_partial_solve_wit_7 : string_equal_partial_solve_wit_7.
Axiom proof_of_string_equal_partial_solve_wit_8 : string_equal_partial_solve_wit_8.

End VC_Correct.
