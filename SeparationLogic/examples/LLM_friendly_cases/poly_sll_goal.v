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
Require Import SimpleC.EE.LLM_friendly_cases.poly_sll_lib.
Local Open Scope sac.
From SimpleC.EE.LLM_friendly_cases Require Import common_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import common_strategy_proof.
From SimpleC.EE.LLM_friendly_cases Require Import poly_sll_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import poly_sll_strategy_proof.

(*----- Function reverse -----*)

Definition reverse_safety_wit_1 := 
forall (A: Type) (p_pre: Z) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (sll storeA p_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition reverse_entail_wit_1 := 
forall (A: Type) (p_pre: Z) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) ,
  (sll storeA p_pre l )
|--
  [| (0 = 0) |] 
  &&  [| (p_pre = p_pre) |]
  &&  (sll storeA 0 nil )
  **  (sll storeA p_pre l )
.

Definition reverse_entail_wit_2 := 
forall (A: Type) (p_pre: Z) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) (w: Z) (v: Z) ,
  [| (w = 0) |] 
  &&  [| (v = p_pre) |]
  &&  (sll storeA w nil )
  **  (sll storeA v l )
|--
  EX (l1: (@list A))  (l2: (@list A)) ,
  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll storeA w l1 )
  **  (sll storeA v l2 )
.

Definition reverse_entail_wit_3 := 
forall (A: Type) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) (v: Z) (w: Z) (l1_2: (@list A)) (l2_2: (@list A)) ,
  [| (l = (app ((rev (l1_2))) (l2_2))) |] 
  &&  [| (v <> 0) |]
  &&  (sll storeA w l1_2 )
  **  (sll storeA v l2_2 )
|--
  EX (vnext: Z)  (vdata: Z)  (x: A)  (xs: (@list A))  (l1: (@list A))  (l2: (@list A)) ,
  [| (l = (app ((rev (l1))) (l2))) |] 
  &&  [| (v <> 0) |] 
  &&  [| (l2 = (cons (x) (xs))) |]
  &&  (sll storeA w l1 )
  **  ((&((v)  # "list" ->ₛ "data")) # Ptr  |-> vdata)
  **  (storeA vdata x )
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> vnext)
  **  (sll storeA vnext xs )
.

Definition reverse_entail_wit_4 := 
forall (A: Type) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) (l1_2: (@list A)) (l2_2: (@list A)) (x: A) (xs: (@list A)) (vnext: Z) (vdata: Z) (v: Z) (w: Z) ,
  [| (l = (app ((rev (l1_2))) (l2_2))) |] 
  &&  [| (v <> 0) |] 
  &&  [| (l2_2 = (cons (x) (xs))) |]
  &&  (sll storeA w l1_2 )
  **  ((&((v)  # "list" ->ₛ "data")) # Ptr  |-> vdata)
  **  (storeA vdata x )
  **  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (sll storeA vnext xs )
|--
  EX (l1: (@list A))  (l2: (@list A)) ,
  [| (l = (app ((rev (l1))) (l2))) |]
  &&  (sll storeA v l1 )
  **  (sll storeA vnext l2 )
.

Definition reverse_return_wit_1 := 
forall (A: Type) (l: (@list A)) (storeA: (Z -> (A -> Assertion))) (v: Z) (w: Z) (l1: (@list A)) (l2: (@list A)) ,
  [| (l = (app ((rev (l1))) (l2))) |] 
  &&  [| (v = 0) |]
  &&  (sll storeA w l1 )
  **  (sll storeA v l2 )
|--
  (sll storeA w (rev (l)) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include poly_sll_Strategy_Correct.

Axiom proof_of_reverse_safety_wit_1 : reverse_safety_wit_1.
Axiom proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Axiom proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Axiom proof_of_reverse_entail_wit_3 : reverse_entail_wit_3.
Axiom proof_of_reverse_entail_wit_4 : reverse_entail_wit_4.
Axiom proof_of_reverse_return_wit_1 : reverse_return_wit_1.

End VC_Correct.
