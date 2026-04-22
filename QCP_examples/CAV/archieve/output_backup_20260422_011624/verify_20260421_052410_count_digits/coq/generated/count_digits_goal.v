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
Require Import count_digits.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function count_digits -----*)

Definition count_digits_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_digits_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_digits_safety_wit_3 := 
forall (n_pre: Z) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "cnt" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_digits_safety_wit_4 := 
forall (n_pre: Z) (cnt: Z) (n: Z) ,
  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| ((cnt + n ) <= n_pre) |] 
  &&  [| ((n = 0) -> (cnt = (count_digits_z (n_pre)))) |] 
  &&  [| ((n > 0) -> ((cnt + (count_digits_z (n)) ) = (count_digits_z (n_pre)))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_digits_safety_wit_5 := 
forall (n_pre: Z) (cnt: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| ((cnt + n ) <= n_pre) |] 
  &&  [| ((n = 0) -> (cnt = (count_digits_z (n_pre)))) |] 
  &&  [| ((n > 0) -> ((cnt + (count_digits_z (n)) ) = (count_digits_z (n_pre)))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  [| ((cnt + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (cnt + 1 )) |]
.

Definition count_digits_safety_wit_6 := 
forall (n_pre: Z) (cnt: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| ((cnt + n ) <= n_pre) |] 
  &&  [| ((n = 0) -> (cnt = (count_digits_z (n_pre)))) |] 
  &&  [| ((n > 0) -> ((cnt + (count_digits_z (n)) ) = (count_digits_z (n_pre)))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # Int  |-> (cnt + 1 ))
|--
  [| ((n <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition count_digits_safety_wit_7 := 
forall (n_pre: Z) (cnt: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| ((cnt + n ) <= n_pre) |] 
  &&  [| ((n = 0) -> (cnt = (count_digits_z (n_pre)))) |] 
  &&  [| ((n > 0) -> ((cnt + (count_digits_z (n)) ) = (count_digits_z (n_pre)))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # Int  |-> (cnt + 1 ))
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition count_digits_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (0 <= 0) |] 
  &&  [| ((0 + n_pre ) <= n_pre) |] 
  &&  [| ((n_pre = 0) -> (0 = (count_digits_z (n_pre)))) |] 
  &&  [| ((n_pre > 0) -> ((0 + (count_digits_z (n_pre)) ) = (count_digits_z (n_pre)))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
.

Definition count_digits_entail_wit_2 := 
forall (n_pre: Z) (cnt: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| ((cnt + n ) <= n_pre) |] 
  &&  [| ((n = 0) -> (cnt = (count_digits_z (n_pre)))) |] 
  &&  [| ((n > 0) -> ((cnt + (count_digits_z (n)) ) = (count_digits_z (n_pre)))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| (0 <= (n ÷ 10 )) |] 
  &&  [| ((n ÷ 10 ) <= INT_MAX) |] 
  &&  [| (0 <= (cnt + 1 )) |] 
  &&  [| (((cnt + 1 ) + (n ÷ 10 ) ) <= n_pre) |] 
  &&  [| (((n ÷ 10 ) = 0) -> ((cnt + 1 ) = (count_digits_z (n_pre)))) |] 
  &&  [| (((n ÷ 10 ) > 0) -> (((cnt + 1 ) + (count_digits_z ((n ÷ 10 ))) ) = (count_digits_z (n_pre)))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
.

Definition count_digits_entail_wit_3 := 
forall (n_pre: Z) (cnt: Z) (n: Z) ,
  [| (n <= 0) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (0 <= cnt) |] 
  &&  [| ((cnt + n ) <= n_pre) |] 
  &&  [| ((n = 0) -> (cnt = (count_digits_z (n_pre)))) |] 
  &&  [| ((n > 0) -> ((cnt + (count_digits_z (n)) ) = (count_digits_z (n_pre)))) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| (n = 0) |] 
  &&  [| (cnt = (count_digits_z (n_pre))) |]
  &&  emp
.

Definition count_digits_return_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| (1 = (count_digits_z (n_pre))) |]
  &&  emp
.

Definition count_digits_return_wit_2 := 
forall (n_pre: Z) (n: Z) (cnt: Z) ,
  [| (n = 0) |] 
  &&  [| (cnt = (count_digits_z (n_pre))) |]
  &&  emp
|--
  [| (cnt = (count_digits_z (n_pre))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_count_digits_safety_wit_1 : count_digits_safety_wit_1.
Axiom proof_of_count_digits_safety_wit_2 : count_digits_safety_wit_2.
Axiom proof_of_count_digits_safety_wit_3 : count_digits_safety_wit_3.
Axiom proof_of_count_digits_safety_wit_4 : count_digits_safety_wit_4.
Axiom proof_of_count_digits_safety_wit_5 : count_digits_safety_wit_5.
Axiom proof_of_count_digits_safety_wit_6 : count_digits_safety_wit_6.
Axiom proof_of_count_digits_safety_wit_7 : count_digits_safety_wit_7.
Axiom proof_of_count_digits_entail_wit_1 : count_digits_entail_wit_1.
Axiom proof_of_count_digits_entail_wit_2 : count_digits_entail_wit_2.
Axiom proof_of_count_digits_entail_wit_3 : count_digits_entail_wit_3.
Axiom proof_of_count_digits_return_wit_1 : count_digits_return_wit_1.
Axiom proof_of_count_digits_return_wit_2 : count_digits_return_wit_2.

End VC_Correct.
