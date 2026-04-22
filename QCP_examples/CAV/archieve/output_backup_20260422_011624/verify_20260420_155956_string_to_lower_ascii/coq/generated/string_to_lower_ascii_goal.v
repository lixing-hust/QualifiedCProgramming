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
Require Import string_to_lower_ascii.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import char_array_strategy_goal.
From SimpleC.EE Require Import char_array_strategy_proof.

(*----- Function string_to_lower_ascii -----*)

Definition string_to_lower_ascii_safety_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_to_lower_ascii_safety_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_to_lower_ascii_safety_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_to_lower_ascii_safety_wit_4 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition string_to_lower_ascii_safety_wit_5 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| (65 <= (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (90 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 90) |]
.

Definition string_to_lower_ascii_safety_wit_6 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| (65 <= (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) - 65 ) + 97 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) - 65 ) + 97 )) |]
.

Definition string_to_lower_ascii_safety_wit_7 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| (65 <= (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) - 65 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) - 65 )) |]
.

Definition string_to_lower_ascii_safety_wit_8 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| (65 <= (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition string_to_lower_ascii_safety_wit_9 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| (65 <= (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition string_to_lower_ascii_safety_wit_10 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| (65 <= (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_to_lower_ascii_safety_wit_11 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| (65 > (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_to_lower_ascii_safety_wit_12 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| (65 <= (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (replace_Znth (i) ((((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) - 65 ) + 97 )) ((app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_to_lower_ascii_entail_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = 0) |] 
  &&  [| ((Zlength (l2)) = (n - 0 )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
.

Definition string_to_lower_ascii_entail_wit_2_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (i: Z) ,
  [| (0 <= (n + 1 )) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1_2))) (l2_2))) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| (65 <= (Znth i (app ((app ((string_to_lower_ascii_spec (l1_2))) (l2_2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1_2))) (l2_2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| ((Zlength (l2_2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (replace_Znth (i) ((((Znth i (app ((app ((string_to_lower_ascii_spec (l1_2))) (l2_2))) ((cons (0) (nil)))) 0) - 65 ) + 97 )) ((app ((app ((string_to_lower_ascii_spec (l1_2))) (l2_2))) ((cons (0) (nil)))))) )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = (i + 1 )) |] 
  &&  [| ((Zlength (l2)) = (n - (i + 1 ) )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
.

Definition string_to_lower_ascii_entail_wit_2_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (i: Z) ,
  [| (65 > (Znth i (app ((app ((string_to_lower_ascii_spec (l1_2))) (l2_2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1_2))) (l2_2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| ((Zlength (l2_2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1_2))) (l2_2))) ((cons (0) (nil)))) )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = (i + 1 )) |] 
  &&  [| ((Zlength (l2)) = (n - (i + 1 ) )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
.

Definition string_to_lower_ascii_entail_wit_2_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (i: Z) ,
  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1_2))) (l2_2))) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| (65 <= (Znth i (app ((app ((string_to_lower_ascii_spec (l1_2))) (l2_2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1_2))) (l2_2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1_2)) = i) |] 
  &&  [| ((Zlength (l2_2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1_2))) (l2_2))) ((cons (0) (nil)))) )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = (i + 1 )) |] 
  &&  [| ((Zlength (l2)) = (n - (i + 1 ) )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
.

Definition string_to_lower_ascii_return_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
|--
  (CharArray.full s_pre (n + 1 ) (app ((string_to_lower_ascii_spec (l))) ((cons (0) (nil)))) )
.

Definition string_to_lower_ascii_partial_solve_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
|--
  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
.

Definition string_to_lower_ascii_partial_solve_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
.

Definition string_to_lower_ascii_partial_solve_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| (65 <= (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
|--
  [| (65 <= (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
.

Definition string_to_lower_ascii_partial_solve_wit_4 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| (65 <= (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| (65 <= (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
.

Definition string_to_lower_ascii_partial_solve_wit_5 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (i: Z) ,
  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| (65 <= (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (CharArray.full s_pre (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
|--
  [| (0 <= (n + 1 )) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| (65 <= (Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) 0) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (l1)) = i) |] 
  &&  [| ((Zlength (l2)) = (n - i )) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app ((app ((string_to_lower_ascii_spec (l1))) (l2))) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_to_lower_ascii_safety_wit_1 : string_to_lower_ascii_safety_wit_1.
Axiom proof_of_string_to_lower_ascii_safety_wit_2 : string_to_lower_ascii_safety_wit_2.
Axiom proof_of_string_to_lower_ascii_safety_wit_3 : string_to_lower_ascii_safety_wit_3.
Axiom proof_of_string_to_lower_ascii_safety_wit_4 : string_to_lower_ascii_safety_wit_4.
Axiom proof_of_string_to_lower_ascii_safety_wit_5 : string_to_lower_ascii_safety_wit_5.
Axiom proof_of_string_to_lower_ascii_safety_wit_6 : string_to_lower_ascii_safety_wit_6.
Axiom proof_of_string_to_lower_ascii_safety_wit_7 : string_to_lower_ascii_safety_wit_7.
Axiom proof_of_string_to_lower_ascii_safety_wit_8 : string_to_lower_ascii_safety_wit_8.
Axiom proof_of_string_to_lower_ascii_safety_wit_9 : string_to_lower_ascii_safety_wit_9.
Axiom proof_of_string_to_lower_ascii_safety_wit_10 : string_to_lower_ascii_safety_wit_10.
Axiom proof_of_string_to_lower_ascii_safety_wit_11 : string_to_lower_ascii_safety_wit_11.
Axiom proof_of_string_to_lower_ascii_safety_wit_12 : string_to_lower_ascii_safety_wit_12.
Axiom proof_of_string_to_lower_ascii_entail_wit_1 : string_to_lower_ascii_entail_wit_1.
Axiom proof_of_string_to_lower_ascii_entail_wit_2_1 : string_to_lower_ascii_entail_wit_2_1.
Axiom proof_of_string_to_lower_ascii_entail_wit_2_2 : string_to_lower_ascii_entail_wit_2_2.
Axiom proof_of_string_to_lower_ascii_entail_wit_2_3 : string_to_lower_ascii_entail_wit_2_3.
Axiom proof_of_string_to_lower_ascii_return_wit_1 : string_to_lower_ascii_return_wit_1.
Axiom proof_of_string_to_lower_ascii_partial_solve_wit_1 : string_to_lower_ascii_partial_solve_wit_1.
Axiom proof_of_string_to_lower_ascii_partial_solve_wit_2 : string_to_lower_ascii_partial_solve_wit_2.
Axiom proof_of_string_to_lower_ascii_partial_solve_wit_3 : string_to_lower_ascii_partial_solve_wit_3.
Axiom proof_of_string_to_lower_ascii_partial_solve_wit_4 : string_to_lower_ascii_partial_solve_wit_4.
Axiom proof_of_string_to_lower_ascii_partial_solve_wit_5 : string_to_lower_ascii_partial_solve_wit_5.

End VC_Correct.
