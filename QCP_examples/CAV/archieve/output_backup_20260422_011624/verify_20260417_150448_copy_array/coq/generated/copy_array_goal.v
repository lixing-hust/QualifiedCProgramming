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
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.

(*----- Function copy_array -----*)

Definition copy_array_safety_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre ld )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition copy_array_safety_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (IntArray.full src_pre n_pre ls )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (IntArray.full dst_pre n_pre (app ((sublist (0) ((i + 1 )) (ls))) ((sublist ((i + 1 )) (n_pre) (ld)))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition copy_array_entail_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre ld )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((sublist (0) (0) (ls))) ((sublist (0) (n_pre) (ld)))) )
.

Definition copy_array_entail_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((sublist (0) ((i + 1 )) (ls))) ((sublist ((i + 1 )) (n_pre) (ld)))) )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((sublist (0) ((i + 1 )) (ls))) ((sublist ((i + 1 )) (n_pre) (ld)))) )
.

Definition copy_array_return_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((sublist (0) (i) (ls))) ((sublist (i) (n_pre) (ld)))) )
|--
  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre ls )
.

Definition copy_array_partial_solve_wit_1_pure := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((sublist (0) (i) (ls))) ((sublist (i) (n_pre) (ld)))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |]
.

Definition copy_array_partial_solve_wit_1_aux := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((sublist (0) (i) (ls))) ((sublist (i) (n_pre) (ld)))) )
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((sublist (0) (i) (ls))) ((sublist (i) (n_pre) (ld)))) )
.

Definition copy_array_partial_solve_wit_1 := copy_array_partial_solve_wit_1_pure -> copy_array_partial_solve_wit_1_aux.

Definition copy_array_partial_solve_wit_2_pure := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (IntArray.missing_i src_pre i 0 n_pre ls )
  **  (((src_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (IntArray.missing_i dst_pre i 0 n_pre (app ((sublist (0) (i) (ls))) ((sublist (i) (n_pre) (ld)))) )
  **  (((dst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |]
.

Definition copy_array_partial_solve_wit_2_aux := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.missing_i src_pre i 0 n_pre ls )
  **  (((src_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
  **  (IntArray.missing_i dst_pre i 0 n_pre (app ((sublist (0) (i) (ls))) ((sublist (i) (n_pre) (ld)))) )
  **  (((dst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (ls)) = n_pre) |] 
  &&  [| ((Zlength (ld)) = n_pre) |]
  &&  (IntArray.missing_i src_pre i 0 n_pre ls )
  **  (((src_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
  **  (IntArray.missing_i dst_pre i 0 n_pre (app ((sublist (0) (i) (ls))) ((sublist (i) (n_pre) (ld)))) )
  **  (((dst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
.

Definition copy_array_partial_solve_wit_2 := copy_array_partial_solve_wit_2_pure -> copy_array_partial_solve_wit_2_aux.

Definition copy_array_which_implies_wit_1 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |]
  &&  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((sublist (0) (i) (ls))) ((sublist (i) (n_pre) (ld)))) )
|--
  (IntArray.missing_i src_pre i 0 n_pre ls )
  **  (((src_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
  **  (IntArray.missing_i dst_pre i 0 n_pre (app ((sublist (0) (i) (ls))) ((sublist (i) (n_pre) (ld)))) )
  **  (((dst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ld 0))
.

Definition copy_array_which_implies_wit_2 := 
forall (dst_pre: Z) (src_pre: Z) (n_pre: Z) (ld: (@list Z)) (ls: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (ls))) |] 
  &&  [| (n_pre = (Zlength (ld))) |]
  &&  (IntArray.missing_i src_pre i 0 n_pre ls )
  **  (((src_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
  **  (IntArray.missing_i dst_pre i 0 n_pre (app ((sublist (0) (i) (ls))) ((sublist (i) (n_pre) (ld)))) )
  **  (((dst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ls 0))
|--
  (IntArray.full src_pre n_pre ls )
  **  (IntArray.full dst_pre n_pre (app ((sublist (0) ((i + 1 )) (ls))) ((sublist ((i + 1 )) (n_pre) (ld)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_copy_array_safety_wit_1 : copy_array_safety_wit_1.
Axiom proof_of_copy_array_safety_wit_2 : copy_array_safety_wit_2.
Axiom proof_of_copy_array_entail_wit_1 : copy_array_entail_wit_1.
Axiom proof_of_copy_array_entail_wit_2 : copy_array_entail_wit_2.
Axiom proof_of_copy_array_return_wit_1 : copy_array_return_wit_1.
Axiom proof_of_copy_array_partial_solve_wit_1_pure : copy_array_partial_solve_wit_1_pure.
Axiom proof_of_copy_array_partial_solve_wit_1 : copy_array_partial_solve_wit_1.
Axiom proof_of_copy_array_partial_solve_wit_2_pure : copy_array_partial_solve_wit_2_pure.
Axiom proof_of_copy_array_partial_solve_wit_2 : copy_array_partial_solve_wit_2.
Axiom proof_of_copy_array_which_implies_wit_1 : copy_array_which_implies_wit_1.
Axiom proof_of_copy_array_which_implies_wit_2 : copy_array_which_implies_wit_2.

End VC_Correct.
