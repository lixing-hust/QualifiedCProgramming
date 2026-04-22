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
Require Import coins_63.
Local Open Scope sac.

(*----- Function fibfib -----*)

Definition fibfib_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fibfib_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fibfib_safety_wit_3 := 
forall (n_pre: Z) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fibfib_safety_wit_4 := 
forall (n_pre: Z) ,
  [| (n_pre = 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fibfib_safety_wit_5 := 
forall (n_pre: Z) ,
  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition fibfib_safety_wit_6 := 
forall (n_pre: Z) ,
  [| (n_pre = 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fibfib_safety_wit_7 := 
forall (n_pre: Z) ,
  [| (n_pre <> 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |]
  &&  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fibfib_safety_wit_8 := 
forall (n_pre: Z) ,
  [| (n_pre <> 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |]
  &&  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fibfib_safety_wit_9 := 
forall (n_pre: Z) ,
  [| (n_pre <> 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |]
  &&  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fibfib_safety_wit_10 := 
forall (n_pre: Z) ,
  [| (n_pre <> 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "next" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> 1)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition fibfib_safety_wit_11 := 
forall (n_pre: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (3 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (3 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |] 
  &&  [| (a = (fibfib_z ((i - 3 )))) |] 
  &&  [| (b = (fibfib_z ((i - 2 )))) |] 
  &&  [| (c = (fibfib_z ((i - 1 )))) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "next" ) )) # Int  |->_)
|--
  [| (((a + b ) + c ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((a + b ) + c )) |]
.

Definition fibfib_safety_wit_12 := 
forall (n_pre: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (3 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (3 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |] 
  &&  [| (a = (fibfib_z ((i - 3 )))) |] 
  &&  [| (b = (fibfib_z ((i - 2 )))) |] 
  &&  [| (c = (fibfib_z ((i - 1 )))) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "next" ) )) # Int  |->_)
|--
  [| ((a + b ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (a + b )) |]
.

Definition fibfib_safety_wit_13 := 
forall (n_pre: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (3 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (3 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |] 
  &&  [| (a = (fibfib_z ((i - 3 )))) |] 
  &&  [| (b = (fibfib_z ((i - 2 )))) |] 
  &&  [| (c = (fibfib_z ((i - 1 )))) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> b)
  **  ((( &( "b" ) )) # Int  |-> c)
  **  ((( &( "c" ) )) # Int  |-> ((a + b ) + c ))
  **  ((( &( "next" ) )) # Int  |-> ((a + b ) + c ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition fibfib_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre <> 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |]
  &&  emp
|--
  [| (3 <= 3) |] 
  &&  [| (3 <= (n_pre + 1 )) |] 
  &&  [| (3 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |] 
  &&  [| (0 = (fibfib_z ((3 - 3 )))) |] 
  &&  [| (0 = (fibfib_z ((3 - 2 )))) |] 
  &&  [| (1 = (fibfib_z ((3 - 1 )))) |]
  &&  emp
.

Definition fibfib_entail_wit_2 := 
forall (n_pre: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (3 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (3 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |] 
  &&  [| (a = (fibfib_z ((i - 3 )))) |] 
  &&  [| (b = (fibfib_z ((i - 2 )))) |] 
  &&  [| (c = (fibfib_z ((i - 1 )))) |]
  &&  ((( &( "next" ) )) # Int  |-> ((a + b ) + c ))
|--
  [| (3 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (n_pre + 1 )) |] 
  &&  [| (3 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |] 
  &&  [| (b = (fibfib_z (((i + 1 ) - 3 )))) |] 
  &&  [| (c = (fibfib_z (((i + 1 ) - 2 )))) |] 
  &&  [| (((a + b ) + c ) = (fibfib_z (((i + 1 ) - 1 )))) |]
  &&  ((( &( "next" ) )) # Int  |->_)
.

Definition fibfib_return_wit_1 := 
forall (n_pre: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i > n_pre) |] 
  &&  [| (3 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (3 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |] 
  &&  [| (a = (fibfib_z ((i - 3 )))) |] 
  &&  [| (b = (fibfib_z ((i - 2 )))) |] 
  &&  [| (c = (fibfib_z ((i - 1 )))) |]
  &&  emp
|--
  [| (problem_63_spec_z n_pre c ) |]
  &&  emp
.

Definition fibfib_return_wit_2 := 
forall (n_pre: Z) ,
  [| (n_pre = 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |]
  &&  emp
|--
  [| (problem_63_spec_z n_pre 1 ) |]
  &&  emp
.

Definition fibfib_return_wit_3 := 
forall (n_pre: Z) ,
  [| (n_pre = 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |]
  &&  emp
|--
  [| (problem_63_spec_z n_pre 0 ) |]
  &&  emp
.

Definition fibfib_return_wit_4 := 
forall (n_pre: Z) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_63_pre_z n_pre ) |] 
  &&  [| (fibfib_step_int_range n_pre ) |]
  &&  emp
|--
  [| (problem_63_spec_z n_pre 0 ) |]
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_fibfib_safety_wit_1 : fibfib_safety_wit_1.
Axiom proof_of_fibfib_safety_wit_2 : fibfib_safety_wit_2.
Axiom proof_of_fibfib_safety_wit_3 : fibfib_safety_wit_3.
Axiom proof_of_fibfib_safety_wit_4 : fibfib_safety_wit_4.
Axiom proof_of_fibfib_safety_wit_5 : fibfib_safety_wit_5.
Axiom proof_of_fibfib_safety_wit_6 : fibfib_safety_wit_6.
Axiom proof_of_fibfib_safety_wit_7 : fibfib_safety_wit_7.
Axiom proof_of_fibfib_safety_wit_8 : fibfib_safety_wit_8.
Axiom proof_of_fibfib_safety_wit_9 : fibfib_safety_wit_9.
Axiom proof_of_fibfib_safety_wit_10 : fibfib_safety_wit_10.
Axiom proof_of_fibfib_safety_wit_11 : fibfib_safety_wit_11.
Axiom proof_of_fibfib_safety_wit_12 : fibfib_safety_wit_12.
Axiom proof_of_fibfib_safety_wit_13 : fibfib_safety_wit_13.
Axiom proof_of_fibfib_entail_wit_1 : fibfib_entail_wit_1.
Axiom proof_of_fibfib_entail_wit_2 : fibfib_entail_wit_2.
Axiom proof_of_fibfib_return_wit_1 : fibfib_return_wit_1.
Axiom proof_of_fibfib_return_wit_2 : fibfib_return_wit_2.
Axiom proof_of_fibfib_return_wit_3 : fibfib_return_wit_3.
Axiom proof_of_fibfib_return_wit_4 : fibfib_return_wit_4.

End VC_Correct.
