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
Require Import coins_23.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function string_length -----*)

Definition string_length_return_wit_1 := 
forall (str_pre: Z) (n: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = n) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (problem_23_pre_z l ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (retval = n) |] 
  &&  [| (problem_23_spec_z l retval ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition string_length_partial_solve_wit_1 := 
forall (str_pre: Z) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (problem_23_pre_z l ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (problem_23_pre_z l ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_string_length_return_wit_1 : string_length_return_wit_1.
Axiom proof_of_string_length_partial_solve_wit_1 : string_length_partial_solve_wit_1.

End VC_Correct.
