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
Require Import SimpleC.EE.LLM_friendly_cases.sll_lib.
Require Import SimpleC.EE.LLM_friendly_cases.sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope sac.
From SimpleC.EE.LLM_friendly_cases Require Import sll_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import sll_strategy_proof.
From SimpleC.EE.LLM_friendly_cases Require Import safeexec_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import safeexec_strategy_proof.

(*----- Function split_while -----*)

Definition split_while_safety_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (q_v: Z) (p_v: Z) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X_low_level_spec ) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  ((( &( "t" ) )) # Ptr  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition split_while_safety_wit_2 := 
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (l_new: (@list Z)) (x_data: Z) (p_v: Z) (p_v_next: Z) (x: Z) (q_v: Z) ,
  [| (safeExec ATrue (bind ((split_rec_rel (l_new) (l2) ((cons (x_data) (l1))))) (reversepair)) X_low_level_spec ) |] 
  &&  [| (l = (cons (x_data) (l_new))) |] 
  &&  [| (p_v <> 0) |]
  &&  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((p_pre) # Ptr  |-> p_v)
  **  ((&((p_v)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((p_v)  # "list" ->ₛ "next")) # Ptr  |-> p_v_next)
  **  (sll p_v_next l1 )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l_new )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  ((( &( "t" ) )) # Ptr  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition split_while_entail_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p_pre_v: Z) (q_pre_v: Z) ,
  [| (safeExec ATrue (split_rec_rel (l_low_level_spec) (nil) (nil)) X_low_level_spec ) |]
  &&  (sll x_pre l_low_level_spec )
  **  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v nil )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v nil )
|--
  EX (q_v: Z)  (p_v: Z)  (l: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X_low_level_spec ) |]
  &&  (sll x_pre l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
.

Definition split_while_entail_wit_2 := 
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (q_v_2: Z) (p_v_2: Z) (x: Z) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) ,
  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (split_rec_rel (l_2) (l1_2) (l2_2)) X_low_level_spec ) |]
  &&  (sll x l_2 )
  **  ((p_pre) # Ptr  |-> p_v_2)
  **  (sll p_v_2 l1_2 )
  **  ((q_pre) # Ptr  |-> q_v_2)
  **  (sll q_v_2 l2_2 )
|--
  EX (q_v: Z)  (p_v: Z)  (x_next: Z)  (x_data: Z)  (l1_new: (@list Z))  (l: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X_low_level_spec ) |] 
  &&  [| (x <> 0) |] 
  &&  [| (l = (cons (x_data) (l1_new))) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
.

Definition split_while_entail_wit_3 := 
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l1_new: (@list Z)) (x: Z) (x_data_2: Z) (x_next: Z) (p_v_2: Z) (q_v_2: Z) ,
  [| (safeExec ATrue (split_rec_rel (l_2) (l1_2) (l2_2)) X_low_level_spec ) |] 
  &&  [| (x <> 0) |] 
  &&  [| (l_2 = (cons (x_data_2) (l1_new))) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data_2)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> p_v_2)
  **  (sll x_next l1_new )
  **  ((p_pre) # Ptr  |-> x)
  **  (sll p_v_2 l1_2 )
  **  ((q_pre) # Ptr  |-> q_v_2)
  **  (sll q_v_2 l2_2 )
  **  ((( &( "t" ) )) # Ptr  |-> x_next)
|--
  EX (q_v: Z)  (p_v_next: Z)  (p_v: Z)  (l: (@list Z))  (l_new: (@list Z))  (l2: (@list Z))  (x_data: Z)  (l1: (@list Z)) ,
  [| (safeExec ATrue (bind ((split_rec_rel (l_new) (l2) ((cons (x_data) (l1))))) (reversepair)) X_low_level_spec ) |] 
  &&  [| (l = (cons (x_data) (l_new))) |] 
  &&  [| (p_v <> 0) |]
  &&  ((p_pre) # Ptr  |-> p_v)
  **  ((&((p_v)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((p_v)  # "list" ->ₛ "next")) # Ptr  |-> p_v_next)
  **  (sll p_v_next l1 )
  **  (sll x_next l_new )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  ((( &( "t" ) )) # Ptr  |->_)
.

Definition split_while_entail_wit_4 := 
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l_new: (@list Z)) (x_data_3: Z) (p_v_2: Z) (p_v_next: Z) (x: Z) (q_v_2: Z) ,
  [| (x <> 0) |] 
  &&  [| (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_2) ((cons (x_data_3) (l1_2))))) (reversepair)) X_low_level_spec ) |] 
  &&  [| (l_2 = (cons (x_data_3) (l_new))) |] 
  &&  [| (p_v_2 <> 0) |]
  &&  ((p_pre) # Ptr  |-> p_v_2)
  **  ((&((p_v_2)  # "list" ->ₛ "data")) # Int  |-> x_data_3)
  **  ((&((p_v_2)  # "list" ->ₛ "next")) # Ptr  |-> p_v_next)
  **  (sll p_v_next l1_2 )
  **  (sll x l_new )
  **  ((q_pre) # Ptr  |-> q_v_2)
  **  (sll q_v_2 l2_2 )
|--
  EX (x_next: Z)  (q_v: Z)  (p_v: Z)  (x_data_2: Z)  (l1_new: (@list Z))  (l: (@list Z))  (l2: (@list Z))  (x_data: Z)  (l1: (@list Z)) ,
  [| (safeExec ATrue (bind ((split_rec_rel (l) (l2) ((cons (x_data) (l1))))) (reversepair)) X_low_level_spec ) |] 
  &&  [| (x <> 0) |] 
  &&  [| (l = (cons (x_data_2) (l1_new))) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data_2)
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v (cons (x_data) (l1)) )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
.

Definition split_while_entail_wit_5 := 
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l1_new: (@list Z)) (x_data_2: Z) (x: Z) (x_data_3: Z) (p_v_2: Z) (q_v_2: Z) (x_next: Z) ,
  [| (safeExec ATrue (bind ((split_rec_rel (l_2) (l2_2) ((cons (x_data_2) (l1_2))))) (reversepair)) X_low_level_spec ) |] 
  &&  [| (x <> 0) |] 
  &&  [| (l_2 = (cons (x_data_3) (l1_new))) |]
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data_3)
  **  ((p_pre) # Ptr  |-> p_v_2)
  **  (sll p_v_2 (cons (x_data_2) (l1_2)) )
  **  ((q_pre) # Ptr  |-> x)
  **  (sll q_v_2 l2_2 )
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> q_v_2)
  **  (sll x_next l1_new )
  **  ((( &( "t" ) )) # Ptr  |-> x_next)
|--
  EX (p_v: Z)  (q_v_next: Z)  (q_v: Z)  (l: (@list Z))  (l_new: (@list Z))  (x_data: Z)  (l1: (@list Z))  (x_data2: Z)  (l2: (@list Z)) ,
  [| (safeExec ATrue (split_rec_rel (l_new) ((cons (x_data) (l1))) ((cons (x_data2) (l2)))) X_low_level_spec ) |] 
  &&  [| (l = (cons (x_data2) (l_new))) |] 
  &&  [| (q_v <> 0) |]
  &&  ((q_pre) # Ptr  |-> q_v)
  **  ((&((q_v)  # "list" ->ₛ "data")) # Int  |-> x_data2)
  **  ((&((q_v)  # "list" ->ₛ "next")) # Ptr  |-> q_v_next)
  **  (sll q_v_next l2 )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v (cons (x_data) (l1)) )
  **  (sll x_next l_new )
  **  ((( &( "t" ) )) # Ptr  |->_)
.

Definition split_while_entail_wit_6_1 := 
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l_new: (@list Z)) (x_data: Z) (p_v_2: Z) (p_v_next: Z) (x: Z) (q_v_2: Z) ,
  [| (x = 0) |] 
  &&  [| (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_2) ((cons (x_data) (l1_2))))) (reversepair)) X_low_level_spec ) |] 
  &&  [| (l_2 = (cons (x_data) (l_new))) |] 
  &&  [| (p_v_2 <> 0) |]
  &&  ((p_pre) # Ptr  |-> p_v_2)
  **  ((&((p_v_2)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((p_v_2)  # "list" ->ₛ "next")) # Ptr  |-> p_v_next)
  **  (sll p_v_next l1_2 )
  **  (sll x l_new )
  **  ((q_pre) # Ptr  |-> q_v_2)
  **  (sll q_v_2 l2_2 )
|--
  EX (q_v: Z)  (p_v: Z)  (l: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X_low_level_spec ) |]
  &&  (sll x l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
.

Definition split_while_entail_wit_6_2 := 
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l_new: (@list Z)) (x_data: Z) (x_data2: Z) (q_v_2: Z) (q_v_next: Z) (p_v_2: Z) (x: Z) ,
  [| (safeExec ATrue (split_rec_rel (l_new) ((cons (x_data) (l1_2))) ((cons (x_data2) (l2_2)))) X_low_level_spec ) |] 
  &&  [| (l_2 = (cons (x_data2) (l_new))) |] 
  &&  [| (q_v_2 <> 0) |]
  &&  ((q_pre) # Ptr  |-> q_v_2)
  **  ((&((q_v_2)  # "list" ->ₛ "data")) # Int  |-> x_data2)
  **  ((&((q_v_2)  # "list" ->ₛ "next")) # Ptr  |-> q_v_next)
  **  (sll q_v_next l2_2 )
  **  ((p_pre) # Ptr  |-> p_v_2)
  **  (sll p_v_2 (cons (x_data) (l1_2)) )
  **  (sll x l_new )
|--
  EX (q_v: Z)  (p_v: Z)  (l: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X_low_level_spec ) |]
  &&  (sll x l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
.

Definition split_while_return_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (q_v: Z) (p_v: Z) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (x = 0) |] 
  &&  [| (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X_low_level_spec ) |]
  &&  (sll x l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )
|--
  EX (q_pre_v: Z)  (p_pre_v: Z)  (s1: (@list Z))  (s2: (@list Z)) ,
  [| (safeExec ATrue (return ((maketuple (s1) (s2)))) X_low_level_spec ) |]
  &&  ((p_pre) # Ptr  |-> p_pre_v)
  **  (sll p_pre_v s1 )
  **  ((q_pre) # Ptr  |-> q_pre_v)
  **  (sll q_pre_v s2 )
.

Module Type VC_Correct.

Include sll_Strategy_Correct.
Include safeexec_Strategy_Correct.

Axiom proof_of_split_while_safety_wit_1 : split_while_safety_wit_1.
Axiom proof_of_split_while_safety_wit_2 : split_while_safety_wit_2.
Axiom proof_of_split_while_entail_wit_1 : split_while_entail_wit_1.
Axiom proof_of_split_while_entail_wit_2 : split_while_entail_wit_2.
Axiom proof_of_split_while_entail_wit_3 : split_while_entail_wit_3.
Axiom proof_of_split_while_entail_wit_4 : split_while_entail_wit_4.
Axiom proof_of_split_while_entail_wit_5 : split_while_entail_wit_5.
Axiom proof_of_split_while_entail_wit_6_1 : split_while_entail_wit_6_1.
Axiom proof_of_split_while_entail_wit_6_2 : split_while_entail_wit_6_2.
Axiom proof_of_split_while_return_wit_1 : split_while_return_wit_1.

End VC_Correct.
