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
Require Import coins_46.
Local Open Scope sac.

(*----- Function fib4 -----*)

Definition fib4_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fib4_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fib4_safety_wit_3 := 
forall (n_pre: Z) ,
  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fib4_safety_wit_4 := 
forall (n_pre: Z) ,
  [| (n_pre = 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fib4_safety_wit_5 := 
forall (n_pre: Z) ,
  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition fib4_safety_wit_6 := 
forall (n_pre: Z) ,
  [| (n_pre = 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition fib4_safety_wit_7 := 
forall (n_pre: Z) ,
  [| (n_pre <> 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition fib4_safety_wit_8 := 
forall (n_pre: Z) ,
  [| (n_pre = 3) |] 
  &&  [| (n_pre <> 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fib4_safety_wit_9 := 
forall (n_pre: Z) ,
  [| (n_pre <> 3) |] 
  &&  [| (n_pre <> 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fib4_safety_wit_10 := 
forall (n_pre: Z) ,
  [| (n_pre <> 3) |] 
  &&  [| (n_pre <> 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fib4_safety_wit_11 := 
forall (n_pre: Z) ,
  [| (n_pre <> 3) |] 
  &&  [| (n_pre <> 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition fib4_safety_wit_12 := 
forall (n_pre: Z) ,
  [| (n_pre <> 3) |] 
  &&  [| (n_pre <> 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> 2)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fib4_safety_wit_13 := 
forall (n_pre: Z) ,
  [| (n_pre <> 3) |] 
  &&  [| (n_pre <> 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "next" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Int  |-> 2)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition fib4_safety_wit_14 := 
forall (n_pre: Z) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (4 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (4 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (fib4_step_int_range n_pre ) |] 
  &&  [| (a = (fib4_z ((i - 4 )))) |] 
  &&  [| (b = (fib4_z ((i - 3 )))) |] 
  &&  [| (c = (fib4_z ((i - 2 )))) |] 
  &&  [| (d = (fib4_z ((i - 1 )))) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "next" ) )) # Int  |->_)
|--
  [| ((((a + b ) + c ) + d ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((a + b ) + c ) + d )) |]
.

Definition fib4_safety_wit_15 := 
forall (n_pre: Z) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (4 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (4 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (fib4_step_int_range n_pre ) |] 
  &&  [| (a = (fib4_z ((i - 4 )))) |] 
  &&  [| (b = (fib4_z ((i - 3 )))) |] 
  &&  [| (c = (fib4_z ((i - 2 )))) |] 
  &&  [| (d = (fib4_z ((i - 1 )))) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "next" ) )) # Int  |->_)
|--
  [| (((a + b ) + c ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((a + b ) + c )) |]
.

Definition fib4_safety_wit_16 := 
forall (n_pre: Z) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (4 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (4 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (fib4_step_int_range n_pre ) |] 
  &&  [| (a = (fib4_z ((i - 4 )))) |] 
  &&  [| (b = (fib4_z ((i - 3 )))) |] 
  &&  [| (c = (fib4_z ((i - 2 )))) |] 
  &&  [| (d = (fib4_z ((i - 1 )))) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "next" ) )) # Int  |->_)
|--
  [| ((a + b ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (a + b )) |]
.

Definition fib4_safety_wit_17 := 
forall (n_pre: Z) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (4 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (4 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (fib4_step_int_range n_pre ) |] 
  &&  [| (a = (fib4_z ((i - 4 )))) |] 
  &&  [| (b = (fib4_z ((i - 3 )))) |] 
  &&  [| (c = (fib4_z ((i - 2 )))) |] 
  &&  [| (d = (fib4_z ((i - 1 )))) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> b)
  **  ((( &( "b" ) )) # Int  |-> c)
  **  ((( &( "c" ) )) # Int  |-> d)
  **  ((( &( "d" ) )) # Int  |-> (((a + b ) + c ) + d ))
  **  ((( &( "next" ) )) # Int  |-> (((a + b ) + c ) + d ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition fib4_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre <> 3) |] 
  &&  [| (n_pre <> 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  emp
|--
  [| (4 <= 4) |] 
  &&  [| (4 <= (n_pre + 1 )) |] 
  &&  [| (4 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (fib4_step_int_range n_pre ) |] 
  &&  [| (0 = (fib4_z ((4 - 4 )))) |] 
  &&  [| (0 = (fib4_z ((4 - 3 )))) |] 
  &&  [| (2 = (fib4_z ((4 - 2 )))) |] 
  &&  [| (0 = (fib4_z ((4 - 1 )))) |]
  &&  emp
.

Definition fib4_entail_wit_2 := 
forall (n_pre: Z) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (4 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (4 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (fib4_step_int_range n_pre ) |] 
  &&  [| (a = (fib4_z ((i - 4 )))) |] 
  &&  [| (b = (fib4_z ((i - 3 )))) |] 
  &&  [| (c = (fib4_z ((i - 2 )))) |] 
  &&  [| (d = (fib4_z ((i - 1 )))) |]
  &&  ((( &( "next" ) )) # Int  |-> (((a + b ) + c ) + d ))
|--
  [| (4 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (n_pre + 1 )) |] 
  &&  [| (4 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (fib4_step_int_range n_pre ) |] 
  &&  [| (b = (fib4_z (((i + 1 ) - 4 )))) |] 
  &&  [| (c = (fib4_z (((i + 1 ) - 3 )))) |] 
  &&  [| (d = (fib4_z (((i + 1 ) - 2 )))) |] 
  &&  [| ((((a + b ) + c ) + d ) = (fib4_z (((i + 1 ) - 1 )))) |]
  &&  ((( &( "next" ) )) # Int  |->_)
.

Definition fib4_return_wit_1 := 
forall (n_pre: Z) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (i > n_pre) |] 
  &&  [| (4 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (4 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (fib4_step_int_range n_pre ) |] 
  &&  [| (a = (fib4_z ((i - 4 )))) |] 
  &&  [| (b = (fib4_z ((i - 3 )))) |] 
  &&  [| (c = (fib4_z ((i - 2 )))) |] 
  &&  [| (d = (fib4_z ((i - 1 )))) |]
  &&  emp
|--
  [| (problem_46_spec_z n_pre d ) |]
  &&  emp
.

Definition fib4_return_wit_2 := 
forall (n_pre: Z) ,
  [| (n_pre = 3) |] 
  &&  [| (n_pre <> 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  emp
|--
  [| (problem_46_spec_z n_pre 0 ) |]
  &&  emp
.

Definition fib4_return_wit_3 := 
forall (n_pre: Z) ,
  [| (n_pre = 2) |] 
  &&  [| (n_pre <> 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  emp
|--
  [| (problem_46_spec_z n_pre 2 ) |]
  &&  emp
.

Definition fib4_return_wit_4 := 
forall (n_pre: Z) ,
  [| (n_pre = 1) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  emp
|--
  [| (problem_46_spec_z n_pre 0 ) |]
  &&  emp
.

Definition fib4_return_wit_5 := 
forall (n_pre: Z) ,
  [| (n_pre = 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < 100) |] 
  &&  [| (problem_46_pre_z n_pre ) |] 
  &&  [| (fib4_step_int_range n_pre ) |]
  &&  emp
|--
  [| (problem_46_spec_z n_pre 0 ) |]
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_fib4_safety_wit_1 : fib4_safety_wit_1.
Axiom proof_of_fib4_safety_wit_2 : fib4_safety_wit_2.
Axiom proof_of_fib4_safety_wit_3 : fib4_safety_wit_3.
Axiom proof_of_fib4_safety_wit_4 : fib4_safety_wit_4.
Axiom proof_of_fib4_safety_wit_5 : fib4_safety_wit_5.
Axiom proof_of_fib4_safety_wit_6 : fib4_safety_wit_6.
Axiom proof_of_fib4_safety_wit_7 : fib4_safety_wit_7.
Axiom proof_of_fib4_safety_wit_8 : fib4_safety_wit_8.
Axiom proof_of_fib4_safety_wit_9 : fib4_safety_wit_9.
Axiom proof_of_fib4_safety_wit_10 : fib4_safety_wit_10.
Axiom proof_of_fib4_safety_wit_11 : fib4_safety_wit_11.
Axiom proof_of_fib4_safety_wit_12 : fib4_safety_wit_12.
Axiom proof_of_fib4_safety_wit_13 : fib4_safety_wit_13.
Axiom proof_of_fib4_safety_wit_14 : fib4_safety_wit_14.
Axiom proof_of_fib4_safety_wit_15 : fib4_safety_wit_15.
Axiom proof_of_fib4_safety_wit_16 : fib4_safety_wit_16.
Axiom proof_of_fib4_safety_wit_17 : fib4_safety_wit_17.
Axiom proof_of_fib4_entail_wit_1 : fib4_entail_wit_1.
Axiom proof_of_fib4_entail_wit_2 : fib4_entail_wit_2.
Axiom proof_of_fib4_return_wit_1 : fib4_return_wit_1.
Axiom proof_of_fib4_return_wit_2 : fib4_return_wit_2.
Axiom proof_of_fib4_return_wit_3 : fib4_return_wit_3.
Axiom proof_of_fib4_return_wit_4 : fib4_return_wit_4.
Axiom proof_of_fib4_return_wit_5 : fib4_return_wit_5.

End VC_Correct.
