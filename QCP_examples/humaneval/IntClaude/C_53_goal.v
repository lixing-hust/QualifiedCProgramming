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
Require Import coins_53.
Local Open Scope sac.

(*----- Function add -----*)

Definition add_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= (x_pre + y_pre )) |] 
  &&  [| ((x_pre + y_pre ) <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((x_pre + y_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (x_pre + y_pre )) |]
.

Definition add_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= (x_pre + y_pre )) |] 
  &&  [| ((x_pre + y_pre ) <= INT_MAX) |]
  &&  emp
|--
  [| (problem_53_spec x_pre y_pre (x_pre + y_pre ) ) |]
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_add_safety_wit_1 : add_safety_wit_1.
Axiom proof_of_add_return_wit_1 : add_return_wit_1.

End VC_Correct.
