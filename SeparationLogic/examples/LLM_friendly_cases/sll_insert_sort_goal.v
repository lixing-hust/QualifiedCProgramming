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
Require Import SimpleC.EE.LLM_friendly_cases.sll_lib.
Require Import SimpleC.EE.LLM_friendly_cases.sll_insert_sort_lib.
Local Open Scope sac.
From SimpleC.EE.LLM_friendly_cases Require Import common_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import common_strategy_proof.
From SimpleC.EE.LLM_friendly_cases Require Import sll_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import sll_strategy_proof.

(*----- Function insertion -----*)

Definition insertion_safety_wit_1 := 
forall (node_pre: Z) (p_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (node_pre <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |]
  &&  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((( &( "p2" ) )) # Ptr  |-> p2)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition insertion_entail_wit_1 := 
forall (node_pre: Z) (p_pre: Z) (a: Z) (l: (@list Z)) ,
  [| (node_pre <> 0) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sll p_pre l )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  [| (node_pre <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) ( &( "res" ) ) l1 )
  **  (sll p_pre l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
.

Definition insertion_entail_wit_2 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v_2: Z) (p2: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) ,
  [| (x < a) |] 
  &&  [| (l2_2 = (cons (x) (l0))) |] 
  &&  [| (p2_v_2 <> 0) |] 
  &&  [| (node_pre <> 0) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| (strict_upperbound a l1_2 ) |]
  &&  ((&((p2_v_2)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((p2_v_2)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_2 )
  **  ((p2) # Ptr  |-> p2_v_2)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  EX (p2_v: Z)  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (node_pre <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) &((p2_v_2)  # "list" ->ₛ "next") l1 )
  **  ((&((p2_v_2)  # "list" ->ₛ "next")) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
.

Definition insertion_entail_wit_3_1 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1_3: (@list Z)) (l2: (@list Z)) ,
  [| (p2_v = 0) |] 
  &&  [| (node_pre <> 0) |] 
  &&  [| (l = (app (l1_3) (l2))) |] 
  &&  [| (strict_upperbound a l1_3 ) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_3 )
  **  ((p2) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  (EX (unext: Z)  (l1: (@list Z))  (l0: (@list Z))  (x: Z)  (u: Z) ,
  [| (node_pre <> 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (x >= a) |] 
  &&  [| (l = (app (l1) ((cons (x) (l0))))) |] 
  &&  [| (strict_upperbound a l1 ) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> u)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> unext)
  **  (sll unext l0 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_))
  ||
  (EX (l1_2: (@list Z)) ,
  [| (node_pre <> 0) |] 
  &&  [| (l = (app (l1_2) (nil))) |] 
  &&  [| (strict_upperbound a l1_2 ) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_2 )
  **  ((p2) # Ptr  |-> 0)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_))
.

Definition insertion_entail_wit_3_2 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1_3: (@list Z)) (l2: (@list Z)) (x_2: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (x_2 >= a) |] 
  &&  [| (l2 = (cons (x_2) (l0_2))) |] 
  &&  [| (p2_v <> 0) |] 
  &&  [| (node_pre <> 0) |] 
  &&  [| (l = (app (l1_3) (l2))) |] 
  &&  [| (strict_upperbound a l1_3 ) |]
  &&  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sll y l0_2 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_3 )
  **  ((p2) # Ptr  |-> p2_v)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  (EX (unext: Z)  (l1: (@list Z))  (l0: (@list Z))  (x: Z)  (u: Z) ,
  [| (node_pre <> 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (x >= a) |] 
  &&  [| (l = (app (l1) ((cons (x) (l0))))) |] 
  &&  [| (strict_upperbound a l1 ) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> u)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> unext)
  **  (sll unext l0 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_))
  ||
  (EX (l1_2: (@list Z)) ,
  [| (node_pre <> 0) |] 
  &&  [| (l = (app (l1_2) (nil))) |] 
  &&  [| (strict_upperbound a l1_2 ) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_2 )
  **  ((p2) # Ptr  |-> 0)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_))
.

Definition insertion_entail_wit_4_1 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (l1_3: (@list Z)) (p2: Z) ,
  [| (node_pre <> 0) |] 
  &&  [| (l = (app (l1_3) (nil))) |] 
  &&  [| (strict_upperbound a l1_3 ) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_3 )
  **  ((p2) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> 0)
|--
  (EX (unext: Z)  (resv: Z)  (l1: (@list Z))  (l0: (@list Z))  (x: Z)  (u: Z) ,
  [| (node_pre <> 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (x >= a) |] 
  &&  [| (l = (app (l1) ((cons (x) (l0))))) |] 
  &&  [| (strict_upperbound a l1 ) |]
  &&  ((( &( "res" ) )) # Ptr  |-> resv)
  **  (sllseg resv node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> unext)
  **  (sll unext l0 ))
  ||
  (EX (resv_2: Z)  (l1_2: (@list Z)) ,
  [| (node_pre <> 0) |] 
  &&  [| (l = (app (l1_2) (nil))) |] 
  &&  [| (strict_upperbound a l1_2 ) |]
  &&  ((( &( "res" ) )) # Ptr  |-> resv_2)
  **  (sllseg resv_2 node_pre l1_2 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> 0))
.

Definition insertion_entail_wit_4_2 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (l1_3: (@list Z)) (x_2: Z) (l0_2: (@list Z)) (u_2: Z) (unext_2: Z) (p2: Z) ,
  [| (node_pre <> 0) |] 
  &&  [| (u_2 <> 0) |] 
  &&  [| (x_2 >= a) |] 
  &&  [| (l = (app (l1_3) ((cons (x_2) (l0_2))))) |] 
  &&  [| (strict_upperbound a l1_3 ) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1_3 )
  **  ((p2) # Ptr  |-> node_pre)
  **  ((&((u_2)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((u_2)  # "list" ->ₛ "next")) # Ptr  |-> unext_2)
  **  (sll unext_2 l0_2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> u_2)
|--
  (EX (unext: Z)  (resv: Z)  (l1: (@list Z))  (l0: (@list Z))  (x: Z)  (u: Z) ,
  [| (node_pre <> 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (x >= a) |] 
  &&  [| (l = (app (l1) ((cons (x) (l0))))) |] 
  &&  [| (strict_upperbound a l1 ) |]
  &&  ((( &( "res" ) )) # Ptr  |-> resv)
  **  (sllseg resv node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> unext)
  **  (sll unext l0 ))
  ||
  (EX (resv_2: Z)  (l1_2: (@list Z)) ,
  [| (node_pre <> 0) |] 
  &&  [| (l = (app (l1_2) (nil))) |] 
  &&  [| (strict_upperbound a l1_2 ) |]
  &&  ((( &( "res" ) )) # Ptr  |-> resv_2)
  **  (sllseg resv_2 node_pre l1_2 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> 0))
.

Definition insertion_return_wit_1 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (resv: Z) (l1: (@list Z)) (x: Z) (l0_2: (@list Z)) (u: Z) (unext: Z) ,
  [| (node_pre <> 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (x >= a) |] 
  &&  [| (l = (app (l1) ((cons (x) (l0_2))))) |] 
  &&  [| (strict_upperbound a l1 ) |]
  &&  (sllseg resv node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> unext)
  **  (sll unext l0_2 )
|--
  EX (l0: (@list Z)) ,
  [| (l0 = (insert (a) (l))) |]
  &&  (sll resv l0 )
.

Definition insertion_return_wit_2 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (resv: Z) (l1: (@list Z)) ,
  [| (node_pre <> 0) |] 
  &&  [| (l = (app (l1) (nil))) |] 
  &&  [| (strict_upperbound a l1 ) |]
  &&  (sllseg resv node_pre l1 )
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |-> 0)
|--
  EX (l0: (@list Z)) ,
  [| (l0 = (insert (a) (l))) |]
  &&  (sll resv l0 )
.

Definition insertion_partial_solve_wit_1 := 
forall (node_pre: Z) (a: Z) (l: (@list Z)) (p2_v: Z) (p2: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p2_v <> 0) |] 
  &&  [| (node_pre <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |]
  &&  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  (sll p2_v l2 )
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
|--
  EX (y: Z)  (l0: (@list Z))  (x: Z) ,
  [| (l2 = (cons (x) (l0))) |] 
  &&  [| (p2_v <> 0) |] 
  &&  [| (node_pre <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (strict_upperbound a l1 ) |]
  &&  ((&((p2_v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((p2_v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((node_pre)  # "list" ->ₛ "data")) # Int  |-> a)
  **  (sllbseg ( &( "res" ) ) p2 l1 )
  **  ((p2) # Ptr  |-> p2_v)
  **  ((&((node_pre)  # "list" ->ₛ "next")) # Ptr  |->_)
.

(*----- Function insertion_sort -----*)

Definition insertion_sort_safety_wit_1 := 
forall (x_pre: Z) (l: (@list Z)) ,
  ((( &( "res" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition insertion_sort_safety_wit_2 := 
forall (x_pre: Z) (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (sll res l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition insertion_sort_entail_wit_1 := 
forall (x_pre: Z) (l: (@list Z)) ,
  (sll x_pre l )
|--
  EX (l0: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  (sll 0 l0 )
  **  (sll x_pre l2 )
.

Definition insertion_sort_entail_wit_2 := 
forall (l: (@list Z)) (p: Z) (l0_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (l0_3: (@list Z)) (y: Z) (l0_4: (@list Z)) (retval: Z) ,
  [| (l0_4 = (insert (x) (l0_2))) |] 
  &&  [| (l2_2 = (cons (x) (l0_3))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1_2) (l2_2))) |] 
  &&  [| (Permutation l1_2 l0_2 ) |] 
  &&  [| (increasing l0_2 ) |]
  &&  (sll retval l0_4 )
  **  (sll y l0_3 )
  **  ((( &( "q" ) )) # Ptr  |-> y)
|--
  EX (l0: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((( &( "q" ) )) # Ptr  |->_)
  **  (sll retval l0 )
  **  (sll y l2 )
.

Definition insertion_sort_return_wit_1 := 
forall (l: (@list Z)) (p: Z) (res: Z) (l0_2: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p = 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0_2 ) |] 
  &&  [| (increasing l0_2 ) |]
  &&  (sll res l0_2 )
  **  (sll p l2 )
|--
  EX (l0: (@list Z)) ,
  [| (Permutation l l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  (sll res l0 )
.

Definition insertion_sort_partial_solve_wit_1 := 
forall (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  (sll res l0 )
  **  (sll p l2 )
|--
  EX (y: Z)  (l0_2: (@list Z))  (x: Z) ,
  [| (l2 = (cons (x) (l0_2))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll res l0 )
.

Definition insertion_sort_partial_solve_wit_2_pure := 
forall (x_pre: Z) (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (l2 = (cons (x) (l0_2))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "q" ) )) # Ptr  |-> y)
  **  ((( &( "res" ) )) # Ptr  |-> res)
  **  (sll res l0 )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  [| (p <> 0) |]
.

Definition insertion_sort_partial_solve_wit_2_aux := 
forall (l: (@list Z)) (p: Z) (res: Z) (l0: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (x: Z) (l0_2: (@list Z)) (y: Z) ,
  [| (l2 = (cons (x) (l0_2))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0_2 )
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll res l0 )
|--
  [| (p <> 0) |] 
  &&  [| (l2 = (cons (x) (l0_2))) |] 
  &&  [| (p <> 0) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll res l0 )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  (sll y l0_2 )
.

Definition insertion_sort_partial_solve_wit_2 := insertion_sort_partial_solve_wit_2_pure -> insertion_sort_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_insertion_safety_wit_1 : insertion_safety_wit_1.
Axiom proof_of_insertion_entail_wit_1 : insertion_entail_wit_1.
Axiom proof_of_insertion_entail_wit_2 : insertion_entail_wit_2.
Axiom proof_of_insertion_entail_wit_3_1 : insertion_entail_wit_3_1.
Axiom proof_of_insertion_entail_wit_3_2 : insertion_entail_wit_3_2.
Axiom proof_of_insertion_entail_wit_4_1 : insertion_entail_wit_4_1.
Axiom proof_of_insertion_entail_wit_4_2 : insertion_entail_wit_4_2.
Axiom proof_of_insertion_return_wit_1 : insertion_return_wit_1.
Axiom proof_of_insertion_return_wit_2 : insertion_return_wit_2.
Axiom proof_of_insertion_partial_solve_wit_1 : insertion_partial_solve_wit_1.
Axiom proof_of_insertion_sort_safety_wit_1 : insertion_sort_safety_wit_1.
Axiom proof_of_insertion_sort_safety_wit_2 : insertion_sort_safety_wit_2.
Axiom proof_of_insertion_sort_entail_wit_1 : insertion_sort_entail_wit_1.
Axiom proof_of_insertion_sort_entail_wit_2 : insertion_sort_entail_wit_2.
Axiom proof_of_insertion_sort_return_wit_1 : insertion_sort_return_wit_1.
Axiom proof_of_insertion_sort_partial_solve_wit_1 : insertion_sort_partial_solve_wit_1.
Axiom proof_of_insertion_sort_partial_solve_wit_2_pure : insertion_sort_partial_solve_wit_2_pure.
Axiom proof_of_insertion_sort_partial_solve_wit_2 : insertion_sort_partial_solve_wit_2.

End VC_Correct.
