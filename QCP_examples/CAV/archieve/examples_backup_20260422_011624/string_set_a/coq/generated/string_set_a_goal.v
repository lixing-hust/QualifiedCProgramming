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
From SimpleC.EE Require Import char_array_strategy_goal.
From SimpleC.EE Require Import char_array_strategy_proof.

(*----- Function string_set_a -----*)

Definition string_set_a_safety_wit_1 := 
forall (s_pre: Z) (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.undef_full s_pre (n_pre + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_set_a_safety_wit_2 := 
forall (s_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre i (repeat_Z (97) (i)) )
  **  (CharArray.undef_seg s_pre i (n_pre + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition string_set_a_safety_wit_3 := 
forall (s_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (CharArray.full s_pre (i + 1 ) (app ((repeat_Z (97) (i))) ((cons (97) (nil)))) )
  **  (CharArray.undef_seg s_pre (i + 1 ) (n_pre + 1 ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_set_a_safety_wit_4 := 
forall (s_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre i (repeat_Z (97) (i)) )
  **  (CharArray.undef_seg s_pre i (n_pre + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_set_a_entail_wit_1 := 
forall (s_pre: Z) (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (CharArray.undef_full s_pre (n_pre + 1 ) )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (CharArray.full s_pre 0 (repeat_Z (97) (0)) )
  **  (CharArray.undef_seg s_pre 0 (n_pre + 1 ) )
.

Definition string_set_a_entail_wit_2 := 
forall (s_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (CharArray.full s_pre (i + 1 ) (app ((repeat_Z (97) (i))) ((cons (97) (nil)))) )
  **  (CharArray.undef_seg s_pre (i + 1 ) (n_pre + 1 ) )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (CharArray.full s_pre (i + 1 ) (repeat_Z (97) ((i + 1 ))) )
  **  (CharArray.undef_seg s_pre (i + 1 ) (n_pre + 1 ) )
.

Definition string_set_a_return_wit_1 := 
forall (s_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (CharArray.full s_pre (i + 1 ) (app ((repeat_Z (97) (i))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg s_pre (n_pre + 1 ) (n_pre + 1 ) )
|--
  (CharArray.full s_pre (n_pre + 1 ) (app ((repeat_Z (97) (n_pre))) ((cons (0) (nil)))) )
.

Definition string_set_a_partial_solve_wit_1 := 
forall (s_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (CharArray.full s_pre i (repeat_Z (97) (i)) )
  **  (CharArray.undef_seg s_pre i (n_pre + 1 ) )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i s_pre i i (n_pre + 1 ) )
  **  (CharArray.full s_pre i (repeat_Z (97) (i)) )
.

Definition string_set_a_partial_solve_wit_2 := 
forall (s_pre: Z) (n_pre: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (CharArray.full s_pre i (repeat_Z (97) (i)) )
  **  (CharArray.undef_seg s_pre i (n_pre + 1 ) )
|--
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  (((s_pre + (n_pre * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i s_pre n_pre i (n_pre + 1 ) )
  **  (CharArray.full s_pre i (repeat_Z (97) (i)) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_string_set_a_safety_wit_1 : string_set_a_safety_wit_1.
Axiom proof_of_string_set_a_safety_wit_2 : string_set_a_safety_wit_2.
Axiom proof_of_string_set_a_safety_wit_3 : string_set_a_safety_wit_3.
Axiom proof_of_string_set_a_safety_wit_4 : string_set_a_safety_wit_4.
Axiom proof_of_string_set_a_entail_wit_1 : string_set_a_entail_wit_1.
Axiom proof_of_string_set_a_entail_wit_2 : string_set_a_entail_wit_2.
Axiom proof_of_string_set_a_return_wit_1 : string_set_a_return_wit_1.
Axiom proof_of_string_set_a_partial_solve_wit_1 : string_set_a_partial_solve_wit_1.
Axiom proof_of_string_set_a_partial_solve_wit_2 : string_set_a_partial_solve_wit_2.

End VC_Correct.
