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
Require Import GmpAux GmpNumber.
Import Aux.
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

(*----- Function gmp_abs -----*)

Definition gmp_abs_safety_wit_1 := 
forall (x_pre: Z) ,
  [| (x_pre < 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (x_pre <> (INT_MIN)) |]
.

Definition gmp_abs_return_wit_1_1 := 
forall (x_pre: Z) ,
  [| (x_pre < 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  emp
|--
  [| ((-x_pre) = (Zabs (x_pre))) |]
  &&  emp
.

Definition gmp_abs_return_wit_1_2 := 
forall (x_pre: Z) ,
  [| (x_pre >= 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  emp
|--
  [| (x_pre = (Zabs (x_pre))) |]
  &&  emp
.

(*----- Function gmp_max -----*)

Definition gmp_max_return_wit_1_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <= b_pre) |]
  &&  emp
|--
  [| (b_pre = (Z.max (a_pre) (b_pre))) |]
  &&  emp
.

Definition gmp_max_return_wit_1_2 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre > b_pre) |]
  &&  emp
|--
  [| (a_pre = (Z.max (a_pre) (b_pre))) |]
  &&  emp
.

(*----- Function gmp_cmp -----*)

Definition gmp_cmp_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre >= b_pre) |] 
  &&  [| (a_pre <= b_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((0 - 0 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 - 0 )) |]
.

Definition gmp_cmp_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < b_pre) |] 
  &&  [| (a_pre <= b_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((0 - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 - 1 )) |]
.

Definition gmp_cmp_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre >= b_pre) |] 
  &&  [| (a_pre > b_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((1 - 0 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (1 - 0 )) |]
.

Definition gmp_cmp_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < b_pre) |] 
  &&  [| (a_pre > b_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| False |]
.

Definition gmp_cmp_return_wit_1_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre >= b_pre) |] 
  &&  [| (a_pre > b_pre) |]
  &&  emp
|--
  ([| (a_pre < b_pre) |] 
  &&  [| ((1 - 0 ) = (-1)) |]
  &&  emp)
  ||
  ([| (a_pre = b_pre) |] 
  &&  [| ((1 - 0 ) = 0) |]
  &&  emp)
  ||
  ([| (a_pre > b_pre) |] 
  &&  [| ((1 - 0 ) = 1) |]
  &&  emp)
.

Definition gmp_cmp_return_wit_1_2 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < b_pre) |] 
  &&  [| (a_pre <= b_pre) |]
  &&  emp
|--
  ([| (a_pre < b_pre) |] 
  &&  [| ((0 - 1 ) = (-1)) |]
  &&  emp)
  ||
  ([| (a_pre = b_pre) |] 
  &&  [| ((0 - 1 ) = 0) |]
  &&  emp)
  ||
  ([| (a_pre > b_pre) |] 
  &&  [| ((0 - 1 ) = 1) |]
  &&  emp)
.

Definition gmp_cmp_return_wit_1_3 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre >= b_pre) |] 
  &&  [| (a_pre <= b_pre) |]
  &&  emp
|--
  ([| (a_pre < b_pre) |] 
  &&  [| ((0 - 0 ) = (-1)) |]
  &&  emp)
  ||
  ([| (a_pre = b_pre) |] 
  &&  [| ((0 - 0 ) = 0) |]
  &&  emp)
  ||
  ([| (a_pre > b_pre) |] 
  &&  [| ((0 - 0 ) = 1) |]
  &&  emp)
.

(*----- Function mpn_copyi -----*)

Definition mpn_copyi_safety_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) ,
  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.full s_pre n_pre l )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (UIntArray.undef_full d_pre n_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_copyi_safety_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (((d_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.undef_ceil d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition mpn_copyi_entail_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) ,
  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full s_pre n_pre l )
  **  (UIntArray.undef_full d_pre n_pre )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full d_pre 0 (sublist (0) (0) (l)) )
  **  (UIntArray.undef_ceil d_pre 0 n_pre )
  **  (UIntArray.full s_pre n_pre l )
.

Definition mpn_copyi_entail_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (((d_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.undef_ceil d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
  **  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full d_pre (i + 1 ) (sublist (0) ((i + 1 )) (l)) )
  **  (UIntArray.undef_ceil d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
.

Definition mpn_copyi_return_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_ceil d_pre i n_pre )
  **  (UIntArray.full s_pre n_pre l )
|--
  (mpd_store_Z UINT_MOD s_pre val n_pre )
  **  (mpd_store_Z UINT_MOD d_pre val n_pre )
.

Definition mpn_copyi_partial_solve_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) ,
  (mpd_store_Z UINT_MOD s_pre val n_pre )
  **  (UIntArray.undef_full d_pre n_pre )
|--
  (mpd_store_Z UINT_MOD s_pre val n_pre )
  **  (UIntArray.undef_full d_pre n_pre )
.

Definition mpn_copyi_partial_solve_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_ceil d_pre i n_pre )
  **  (UIntArray.full s_pre n_pre l )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (((s_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.missing_i s_pre i 0 n_pre l )
  **  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_ceil d_pre i n_pre )
.

Definition mpn_copyi_partial_solve_wit_3 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (val: Z) (l: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full s_pre n_pre l )
  **  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
  **  (UIntArray.undef_ceil d_pre i n_pre )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (((d_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_ceil d_pre (i + 1 ) n_pre )
  **  (UIntArray.full s_pre n_pre l )
  **  (UIntArray.full d_pre i (sublist (0) (i) (l)) )
.

Definition mpn_copyi_which_implies_wit_1 := 
forall (val: Z) (n: Z) (s: Z) ,
  (mpd_store_Z UINT_MOD s val n )
|--
  EX (l: (@list Z)) ,
  [| ((Zlength (l)) = n) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full s n l )
.

(*----- Function mpn_cmp -----*)

Definition mpn_cmp_safety_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  [| ((n_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - 1 )) |]
.

Definition mpn_cmp_safety_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_cmp_safety_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  [| ((Znth n l1 0) <= (Znth n l2 0)) |] 
  &&  [| ((Znth n l1 0) <> (Znth n l2 0)) |] 
  &&  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  [| (1 <> (INT_MIN)) |]
.

Definition mpn_cmp_safety_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  [| ((Znth n l1 0) <= (Znth n l2 0)) |] 
  &&  [| ((Znth n l1 0) <> (Znth n l2 0)) |] 
  &&  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition mpn_cmp_safety_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  [| ((Znth n l1 0) > (Znth n l2 0)) |] 
  &&  [| ((Znth n l1 0) <> (Znth n l2 0)) |] 
  &&  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition mpn_cmp_safety_wit_6 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  [| ((Znth n l1 0) = (Znth n l2 0)) |] 
  &&  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  [| ((n - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n - 1 )) |]
.

Definition mpn_cmp_safety_wit_7 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  [| (n < 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l1 )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_cmp_entail_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  [| ((-1) <= (n_pre - 1 )) |] 
  &&  [| ((n_pre - 1 ) < n_pre) |] 
  &&  [| ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
.

Definition mpn_cmp_entail_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  [| ((Znth n l1 0) = (Znth n l2 0)) |] 
  &&  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  [| ((-1) <= (n - 1 )) |] 
  &&  [| ((n - 1 ) < n_pre) |] 
  &&  [| ((sublist (((n - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n - 1 ) + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
.

Definition mpn_cmp_return_wit_1_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  [| ((Znth n l1 0) <= (Znth n l2 0)) |] 
  &&  [| ((Znth n l1 0) <> (Znth n l2 0)) |] 
  &&  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  ([| (val1 < val2) |] 
  &&  [| ((-1) = (-1)) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
  ||
  ([| (val1 = val2) |] 
  &&  [| ((-1) = 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
  ||
  ([| (val1 > val2) |] 
  &&  [| ((-1) = 1) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
.

Definition mpn_cmp_return_wit_1_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  [| ((Znth n l1 0) > (Znth n l2 0)) |] 
  &&  [| ((Znth n l1 0) <> (Znth n l2 0)) |] 
  &&  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full bp_pre n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
|--
  ([| (val1 < val2) |] 
  &&  [| (1 = (-1)) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
  ||
  ([| (val1 = val2) |] 
  &&  [| (1 = 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
  ||
  ([| (val1 > val2) |] 
  &&  [| (1 = 1) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
.

Definition mpn_cmp_return_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  [| (n < 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  ([| (val1 < val2) |] 
  &&  [| (0 = (-1)) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
  ||
  ([| (val1 = val2) |] 
  &&  [| (0 = 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
  ||
  ([| (val1 > val2) |] 
  &&  [| (0 = 1) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre ))
.

Definition mpn_cmp_partial_solve_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  [| (0 <= n_pre) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
|--
  [| (0 <= n_pre) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 n_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 n_pre )
.

Definition mpn_cmp_partial_solve_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  (((ap_pre + (n * sizeof(UINT) ) )) # UInt  |-> (Znth n l1 0))
  **  (UIntArray.missing_i ap_pre n 0 n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
.

Definition mpn_cmp_partial_solve_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (l1: (@list Z)) (l2: (@list Z)) (n: Z) ,
  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full ap_pre n_pre l1 )
  **  (UIntArray.full bp_pre n_pre l2 )
|--
  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |]
  &&  (((bp_pre + (n * sizeof(UINT) ) )) # UInt  |-> (Znth n l2 0))
  **  (UIntArray.missing_i bp_pre n 0 n_pre l2 )
  **  (UIntArray.full ap_pre n_pre l1 )
.

Definition mpn_cmp_which_implies_wit_1 := 
forall (val2: Z) (val1: Z) (n: Z) (ap: Z) (bp: Z) ,
  (mpd_store_Z_compact UINT_MOD ap val1 n )
  **  (mpd_store_Z_compact UINT_MOD bp val2 n )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| ((list_to_Z (UINT_MOD) (l1)) = val1) |] 
  &&  [| ((last (l1) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l1 ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l2)) = val2) |] 
  &&  [| ((last (l2) (1)) >= 1) |] 
  &&  [| (list_within_bound UINT_MOD l2 ) |] 
  &&  [| (n = (Zlength (l1))) |] 
  &&  [| (n = (Zlength (l2))) |]
  &&  (UIntArray.full ap n l1 )
  **  (UIntArray.full bp n l2 )
.

(*----- Function mpn_cmp4 -----*)

Definition mpn_cmp4_safety_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre <> bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |]
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition mpn_cmp4_safety_wit_2 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  [| (an_pre < bn_pre) |] 
  &&  [| (an_pre <> bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |]
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  [| (1 <> (INT_MIN)) |]
.

Definition mpn_cmp4_safety_wit_3 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  [| (an_pre < bn_pre) |] 
  &&  [| (an_pre <> bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |]
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition mpn_cmp4_return_wit_1_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre <> bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  ([| (val1 < val2) |] 
  &&  [| (1 = (-1)) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  ([| (val1 = val2) |] 
  &&  [| (1 = 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  ([| (val1 > val2) |] 
  &&  [| (1 = 1) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
.

Definition mpn_cmp4_return_wit_1_2 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  [| (an_pre < bn_pre) |] 
  &&  [| (an_pre <> bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  ([| (val1 < val2) |] 
  &&  [| ((-1) = (-1)) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  ([| (val1 = val2) |] 
  &&  [| ((-1) = 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  ([| (val1 > val2) |] 
  &&  [| ((-1) = 1) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
.

Definition mpn_cmp4_return_wit_2_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (retval: Z) ,
  [| (val1 > val2) |] 
  &&  [| (retval = 1) |] 
  &&  [| (an_pre = bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  ([| (val1 < val2) |] 
  &&  [| (retval = (-1)) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  ([| (val1 = val2) |] 
  &&  [| (retval = 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  ([| (val1 > val2) |] 
  &&  [| (retval = 1) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
.

Definition mpn_cmp4_return_wit_2_2 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (retval: Z) ,
  [| (val1 = val2) |] 
  &&  [| (retval = 0) |] 
  &&  [| (an_pre = bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  ([| (val1 < val2) |] 
  &&  [| (retval = (-1)) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  ([| (val1 = val2) |] 
  &&  [| (retval = 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  ([| (val1 > val2) |] 
  &&  [| (retval = 1) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
.

Definition mpn_cmp4_return_wit_2_3 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (retval: Z) ,
  [| (val1 < val2) |] 
  &&  [| (retval = (-1)) |] 
  &&  [| (an_pre = bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
|--
  ([| (val1 < val2) |] 
  &&  [| (retval = (-1)) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  ([| (val1 = val2) |] 
  &&  [| (retval = 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
  ||
  ([| (val1 > val2) |] 
  &&  [| (retval = 1) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre ))
.

Definition mpn_cmp4_partial_solve_wit_1_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  [| (an_pre = bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |]
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  [| (0 <= an_pre) |]
.

Definition mpn_cmp4_partial_solve_wit_1_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) ,
  [| (an_pre = bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 bn_pre )
|--
  [| (0 <= an_pre) |] 
  &&  [| (an_pre = bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ap_pre val1 an_pre )
  **  (mpd_store_Z_compact UINT_MOD bp_pre val2 an_pre )
.

Definition mpn_cmp4_partial_solve_wit_1 := mpn_cmp4_partial_solve_wit_1_pure -> mpn_cmp4_partial_solve_wit_1_aux.

(*----- Function mpn_normalized_size -----*)

Definition mpn_normalized_size_safety_wit_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_ceil xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_normalized_size_safety_wit_2 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_ceil xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  [| ((n - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n - 1 )) |]
.

Definition mpn_normalized_size_safety_wit_3 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_ceil xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition mpn_normalized_size_safety_wit_4 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_ceil xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_normalized_size_safety_wit_5 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  [| ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) = 0) |] 
  &&  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_ceil xp_pre n n_pre )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  [| ((n - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n - 1 )) |]
.

Definition mpn_normalized_size_entail_wit_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) ,
  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
  **  (UIntArray.full xp_pre n_pre l )
|--
  [| (n_pre <= INT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
  **  (UIntArray.full xp_pre n_pre l )
.

Definition mpn_normalized_size_entail_wit_2 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) ,
  [| (n_pre <= INT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full xp_pre n_pre l )
|--
  [| (n_pre >= 0) |] 
  &&  [| (n_pre <= n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l)))) = val) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full xp_pre n_pre (sublist (0) (n_pre) (l)) )
  **  (UIntArray.undef_ceil xp_pre n_pre n_pre )
.

Definition mpn_normalized_size_entail_wit_3 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  [| ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) = 0) |] 
  &&  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_ceil xp_pre n n_pre )
|--
  [| ((n - 1 ) >= 0) |] 
  &&  [| ((n - 1 ) <= n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) ((n - 1 )) (l)))) = val) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full xp_pre (n - 1 ) (sublist (0) ((n - 1 )) (l)) )
  **  (UIntArray.undef_ceil xp_pre (n - 1 ) n_pre )
.

Definition mpn_normalized_size_return_wit_1_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  [| (n <= 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_ceil xp_pre n n_pre )
|--
  [| (0 <= n) |] 
  &&  [| (n <= n_pre) |]
  &&  (mpd_store_Z_compact UINT_MOD xp_pre val n )
  **  (UIntArray.undef_ceil xp_pre n n_pre )
.

Definition mpn_normalized_size_return_wit_1_2 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  [| ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) <> 0) |] 
  &&  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_ceil xp_pre n n_pre )
|--
  [| (0 <= n) |] 
  &&  [| (n <= n_pre) |]
  &&  (mpd_store_Z_compact UINT_MOD xp_pre val n )
  **  (UIntArray.undef_ceil xp_pre n n_pre )
.

Definition mpn_normalized_size_partial_solve_wit_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) ,
  [| (0 <= n_pre) |]
  &&  (mpd_store_Z UINT_MOD xp_pre val n_pre )
|--
  [| (0 <= n_pre) |]
  &&  (mpd_store_Z UINT_MOD xp_pre val n_pre )
.

Definition mpn_normalized_size_partial_solve_wit_2 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (l: (@list Z)) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |]
  &&  (UIntArray.full xp_pre n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_ceil xp_pre n n_pre )
|--
  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (n) (l)))) = val) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |]
  &&  (((xp_pre + ((n - 1 ) * sizeof(UINT) ) )) # UInt  |-> (Znth (n - 1 ) (sublist (0) (n) (l)) 0))
  **  (UIntArray.missing_i xp_pre (n - 1 ) 0 n (sublist (0) (n) (l)) )
  **  (UIntArray.undef_ceil xp_pre n n_pre )
.

Definition mpn_normalized_size_which_implies_wit_1 := 
forall (val: Z) (n: Z) (xp: Z) ,
  (mpd_store_Z UINT_MOD xp val n )
|--
  EX (l: (@list Z)) ,
  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| ((Zlength (l)) = n) |]
  &&  (UIntArray.full xp n l )
.

(*----- Function mpn_add_1 -----*)

Definition mpn_add_1_safety_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= UINT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "b" ) )) # UInt  |-> b_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_add_1_safety_wit_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  [| ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) >= b_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= UINT_MAX) |]
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  (UIntArray.undef_ceil rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "b" ) )) # UInt  |-> 0)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| ((0 + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + 1 )) |]
.

Definition mpn_add_1_safety_wit_3 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  [| ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) < b_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= UINT_MAX) |]
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  (UIntArray.undef_ceil rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "b" ) )) # UInt  |-> 1)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| ((0 + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + 1 )) |]
.

Definition mpn_add_1_safety_wit_4 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < UINT_MOD) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l')) = val2) |] 
  &&  [| (list_within_bound UINT_MOD l' ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b )) (32)))
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b )) (32)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # UInt  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre i l' )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition mpn_add_1_safety_wit_5 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < UINT_MOD) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l')) = val2) |] 
  &&  [| (list_within_bound UINT_MOD l' ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b )) (32)))
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b )) (32)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # UInt  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre i l' )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition mpn_add_1_entail_wit_1_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  [| ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) < b_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= UINT_MAX) |]
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  (UIntArray.undef_ceil rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (l': (@list Z))  (val1: Z)  (val2: Z) ,
  [| (1 <= (0 + 1 )) |] 
  &&  [| ((0 + 1 ) <= n_pre) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 < UINT_MOD) |] 
  &&  [| ((val2 + (1 * (Z.pow (UINT_MOD) ((0 + 1 ))) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = (0 + 1 )) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l)))) = val1) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l')) = val2) |] 
  &&  [| (list_within_bound UINT_MOD l' ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre (0 + 1 ) l' )
  **  (UIntArray.undef_ceil rp_pre (0 + 1 ) n_pre )
.

Definition mpn_add_1_entail_wit_1_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  [| ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) >= b_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= UINT_MAX) |]
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)))
  **  (UIntArray.undef_ceil rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (l': (@list Z))  (val1: Z)  (val2: Z) ,
  [| (1 <= (0 + 1 )) |] 
  &&  [| ((0 + 1 ) <= n_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 < UINT_MOD) |] 
  &&  [| ((val2 + (0 * (Z.pow (UINT_MOD) ((0 + 1 ))) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = (0 + 1 )) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l)))) = val1) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l')) = val2) |] 
  &&  [| (list_within_bound UINT_MOD l' ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre (0 + 1 ) l' )
  **  (UIntArray.undef_ceil rp_pre (0 + 1 ) n_pre )
.

Definition mpn_add_1_entail_wit_2_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l'_2: (@list Z)) (val1_2: Z) (val2_2: Z) (b: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < UINT_MOD) |] 
  &&  [| ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre )) |] 
  &&  [| ((Zlength (l'_2)) = i) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l'_2)) = val2_2) |] 
  &&  [| (list_within_bound UINT_MOD l'_2 ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b )) (32)))
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l'_2 )
|--
  EX (l': (@list Z))  (val1: Z)  (val2: Z) ,
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 < UINT_MOD) |] 
  &&  [| ((val2 + (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = (i + 1 )) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) = val1) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l')) = val2) |] 
  &&  [| (list_within_bound UINT_MOD l' ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre (i + 1 ) l' )
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
.

Definition mpn_add_1_entail_wit_2_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l'_2: (@list Z)) (val1_2: Z) (val2_2: Z) (b: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < UINT_MOD) |] 
  &&  [| ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre )) |] 
  &&  [| ((Zlength (l'_2)) = i) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l'_2)) = val2_2) |] 
  &&  [| (list_within_bound UINT_MOD l'_2 ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b )) (32)))
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l'_2 )
|--
  EX (l': (@list Z))  (val1: Z)  (val2: Z) ,
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 < UINT_MOD) |] 
  &&  [| ((val2 + (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = (i + 1 )) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) = val1) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l')) = val2) |] 
  &&  [| (list_within_bound UINT_MOD l' ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre (i + 1 ) l' )
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
.

Definition mpn_add_1_return_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < UINT_MOD) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l')) = val2) |] 
  &&  [| (list_within_bound UINT_MOD l' ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
  **  (UIntArray.undef_ceil rp_pre i n_pre )
|--
  EX (val': Z) ,
  [| ((val' + (b * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val + b_pre )) |]
  &&  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val' n_pre )
.

Definition mpn_add_1_partial_solve_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) ,
  [| (n_pre > 0) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= UINT_MAX) |]
  &&  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  [| (n_pre > 0) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= UINT_MAX) |]
  &&  (mpd_store_Z UINT_MOD ap_pre val n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_add_1_partial_solve_wit_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= UINT_MAX) |]
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= UINT_MAX) |]
  &&  (((ap_pre + (0 * sizeof(UINT) ) )) # UInt  |-> (Znth 0 l 0))
  **  (UIntArray.missing_i ap_pre 0 0 n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_add_1_partial_solve_wit_3 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  [| ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) < b_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= UINT_MAX) |]
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  [| ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) < b_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= UINT_MAX) |]
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_ceil rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
.

Definition mpn_add_1_partial_solve_wit_4 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) ,
  [| ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) >= b_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= UINT_MAX) |]
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  [| ((unsigned_last_nbits (((Znth 0 l 0) + b_pre )) (32)) >= b_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (0 <= b_pre) |] 
  &&  [| (b_pre <= UINT_MAX) |]
  &&  (((rp_pre + (0 * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_ceil rp_pre 1 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
.

Definition mpn_add_1_partial_solve_wit_5 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < UINT_MOD) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l')) = val2) |] 
  &&  [| (list_within_bound UINT_MOD l' ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
  **  (UIntArray.undef_ceil rp_pre i n_pre )
|--
  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < UINT_MOD) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l')) = val2) |] 
  &&  [| (list_within_bound UINT_MOD l' ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (((ap_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l 0))
  **  (UIntArray.missing_i ap_pre i 0 n_pre l )
  **  (UIntArray.full rp_pre i l' )
  **  (UIntArray.undef_ceil rp_pre i n_pre )
.

Definition mpn_add_1_partial_solve_wit_6 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < UINT_MOD) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l')) = val2) |] 
  &&  [| (list_within_bound UINT_MOD l' ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
  **  (UIntArray.undef_ceil rp_pre i n_pre )
|--
  [| ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < UINT_MOD) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l')) = val2) |] 
  &&  [| (list_within_bound UINT_MOD l' ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
.

Definition mpn_add_1_partial_solve_wit_7 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val: Z) (l: (@list Z)) (l': (@list Z)) (val1: Z) (val2: Z) (b: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < UINT_MOD) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l')) = val2) |] 
  &&  [| (list_within_bound UINT_MOD l' ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
  **  (UIntArray.undef_ceil rp_pre i n_pre )
|--
  [| ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b < UINT_MOD) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l')) = val2) |] 
  &&  [| (list_within_bound UINT_MOD l' ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.full rp_pre i l' )
.

Definition mpn_add_1_which_implies_wit_1 := 
forall (val: Z) (n: Z) (ap: Z) ,
  (mpd_store_Z UINT_MOD ap val n )
|--
  EX (l: (@list Z)) ,
  [| ((Zlength (l)) = n) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l)) = val) |] 
  &&  [| (list_within_bound UINT_MOD l ) |]
  &&  (UIntArray.full ap n l )
.

(*----- Function mpn_add_n -----*)

Definition mpn_add_n_safety_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_b: (@list Z)) (l_a: (@list Z)) ,
  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_add_n_safety_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_b: (@list Z)) (l_a: (@list Z)) ,
  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_add_n_safety_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 1 ))
  **  (UIntArray.full rp_pre i l_r )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition mpn_add_n_safety_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 0 ))
  **  (UIntArray.full rp_pre i l_r )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition mpn_add_n_safety_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 1 ))
  **  (UIntArray.full rp_pre i l_r )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition mpn_add_n_safety_wit_6 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 0 ))
  **  (UIntArray.full rp_pre i l_r )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition mpn_add_n_entail_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) ,
  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = 0) |] 
  &&  [| ((val_r + (0 * (Z.pow (UINT_MOD) (0)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (UIntArray.full rp_pre 0 l_r )
  **  (UIntArray.undef_ceil rp_pre 0 n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_entail_wit_2_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2) |] 
  &&  [| (list_within_bound UINT_MOD l_r_2 ) |] 
  &&  [| ((Zlength (l_r_2)) = i) |] 
  &&  [| ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r_2 )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= (1 + 0 )) |] 
  &&  [| ((1 + 0 ) <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = (i + 1 )) |] 
  &&  [| ((val_r + ((1 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (UIntArray.full rp_pre (i + 1 ) l_r )
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_entail_wit_2_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2) |] 
  &&  [| (list_within_bound UINT_MOD l_r_2 ) |] 
  &&  [| ((Zlength (l_r_2)) = i) |] 
  &&  [| ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r_2 )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= (1 + 1 )) |] 
  &&  [| ((1 + 1 ) <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = (i + 1 )) |] 
  &&  [| ((val_r + ((1 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (UIntArray.full rp_pre (i + 1 ) l_r )
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_entail_wit_2_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2) |] 
  &&  [| (list_within_bound UINT_MOD l_r_2 ) |] 
  &&  [| ((Zlength (l_r_2)) = i) |] 
  &&  [| ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r_2 )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= (0 + 0 )) |] 
  &&  [| ((0 + 0 ) <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = (i + 1 )) |] 
  &&  [| ((val_r + ((0 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (UIntArray.full rp_pre (i + 1 ) l_r )
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_entail_wit_2_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2) |] 
  &&  [| (list_within_bound UINT_MOD l_r_2 ) |] 
  &&  [| ((Zlength (l_r_2)) = i) |] 
  &&  [| ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r_2 )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= (0 + 1 )) |] 
  &&  [| ((0 + 1 ) <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = (i + 1 )) |] 
  &&  [| ((val_r + ((0 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (UIntArray.full rp_pre (i + 1 ) l_r )
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_return_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_ceil rp_pre i n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  EX (val_r_out: Z) ,
  [| ((val_r_out + (cy * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_a + val_b )) |]
  &&  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out n_pre )
.

Definition mpn_add_n_partial_solve_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) ,
  [| (n_pre > 0) |]
  &&  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  [| (n_pre > 0) |]
  &&  (mpd_store_Z UINT_MOD ap_pre val_a n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_add_n_partial_solve_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_ceil rp_pre i n_pre )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (((ap_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l_a 0))
  **  (UIntArray.missing_i ap_pre i 0 n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_ceil rp_pre i n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_partial_solve_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_ceil rp_pre i n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (((bp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l_b 0))
  **  (UIntArray.missing_i bp_pre i 0 n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_ceil rp_pre i n_pre )
.

Definition mpn_add_n_partial_solve_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_ceil rp_pre i n_pre )
|--
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
.

Definition mpn_add_n_partial_solve_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_ceil rp_pre i n_pre )
|--
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
.

Definition mpn_add_n_partial_solve_wit_6 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_ceil rp_pre i n_pre )
|--
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
.

Definition mpn_add_n_partial_solve_wit_7 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
  **  (UIntArray.undef_ceil rp_pre i n_pre )
|--
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((Zlength (l_r)) = i) |] 
  &&  [| ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |] 
  &&  [| (n_pre > 0) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (UIntArray.undef_ceil rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full rp_pre i l_r )
.

Definition mpn_add_n_which_implies_wit_1 := 
forall (val_b: Z) (val_a: Z) (n: Z) (ap: Z) (bp: Z) ,
  (mpd_store_Z UINT_MOD ap val_a n )
  **  (mpd_store_Z UINT_MOD bp val_b n )
|--
  EX (l_b: (@list Z))  (l_a: (@list Z)) ,
  [| ((Zlength (l_a)) = n) |] 
  &&  [| ((Zlength (l_b)) = n) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_a)) = val_a) |] 
  &&  [| (list_within_bound UINT_MOD l_a ) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_b)) = val_b) |] 
  &&  [| (list_within_bound UINT_MOD l_b ) |]
  &&  (UIntArray.full ap n l_a )
  **  (UIntArray.full bp n l_b )
.

(*----- Function mpn_add -----*)

Definition mpn_add_safety_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (l_r: (@list Z)) ,
  [| (an_pre > bn_pre) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= UINT_MAX) |] 
  &&  [| (an_pre <= INT_MAX) |] 
  &&  [| (bn_pre <= INT_MAX) |] 
  &&  [| (an_pre >= INT_MIN) |] 
  &&  [| (bn_pre >= INT_MIN) |] 
  &&  [| ((Zlength (l_r)) = bn_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) |] 
  &&  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  [| ((an_pre - bn_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (an_pre - bn_pre )) |]
.

Definition mpn_add_entail_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (l_r: (@list Z)) ,
  [| ((Zlength (l_r)) = bn_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) |] 
  &&  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  [| (0 <= retval) |] 
  &&  [| (retval <= UINT_MAX) |] 
  &&  [| (an_pre <= INT_MAX) |] 
  &&  [| (bn_pre <= INT_MAX) |] 
  &&  [| (an_pre >= INT_MIN) |] 
  &&  [| (bn_pre >= INT_MIN) |] 
  &&  [| ((Zlength (l_r)) = bn_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) |] 
  &&  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
.

Definition mpn_add_return_wit_1_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out_2: Z) (retval: Z) (l_r: (@list Z)) ,
  [| (an_pre <= bn_pre) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= UINT_MAX) |] 
  &&  [| (an_pre <= INT_MAX) |] 
  &&  [| (bn_pre <= INT_MAX) |] 
  &&  [| (an_pre >= INT_MIN) |] 
  &&  [| (bn_pre >= INT_MIN) |] 
  &&  [| ((Zlength (l_r)) = bn_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r_out_2) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((val_r_out_2 + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) |] 
  &&  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
|--
  EX (val_r_out: Z) ,
  [| ((val_r_out + (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a + val_b )) |]
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
.

Definition mpn_add_return_wit_1_2 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out_2: Z) (retval_2: Z) (l_r: (@list Z)) (val': Z) (retval: Z) ,
  [| ((val' + (retval * (Z.pow (UINT_MOD) ((an_pre - bn_pre ))) ) ) = (val_a_high + retval_2 )) |] 
  &&  [| (an_pre > bn_pre) |] 
  &&  [| (0 <= retval_2) |] 
  &&  [| (retval_2 <= UINT_MAX) |] 
  &&  [| (an_pre <= INT_MAX) |] 
  &&  [| (bn_pre <= INT_MAX) |] 
  &&  [| (an_pre >= INT_MIN) |] 
  &&  [| (bn_pre >= INT_MIN) |] 
  &&  [| ((Zlength (l_r)) = bn_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r_out_2) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((val_r_out_2 + (retval_2 * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) |] 
  &&  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (rp_pre + (bn_pre * sizeof(UINT) ) ) val' (an_pre - bn_pre ) )
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  EX (val_r_out: Z) ,
  [| ((val_r_out + (retval * (Z.pow (UINT_MOD) (an_pre)) ) ) = (val_a + val_b )) |]
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out an_pre )
.

Definition mpn_add_partial_solve_wit_1_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) ,
  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  [| (an_pre >= bn_pre) |] 
  &&  [| (bn_pre > 0) |]
.

Definition mpn_add_partial_solve_wit_1_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) ,
  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  [| (an_pre >= bn_pre) |] 
  &&  [| (bn_pre > 0) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  (mpd_store_Z UINT_MOD ap_pre val_a an_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
.

Definition mpn_add_partial_solve_wit_1 := mpn_add_partial_solve_wit_1_pure -> mpn_add_partial_solve_wit_1_aux.

Definition mpn_add_partial_solve_wit_2_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) ,
  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  [| (an_pre >= bn_pre) |] 
  &&  [| (bn_pre > 0) |]
.

Definition mpn_add_partial_solve_wit_2_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) ,
  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre an_pre )
|--
  [| (an_pre >= bn_pre) |] 
  &&  [| (bn_pre > 0) |] 
  &&  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  (UIntArray.undef_full rp_pre an_pre )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
.

Definition mpn_add_partial_solve_wit_2 := mpn_add_partial_solve_wit_2_pure -> mpn_add_partial_solve_wit_2_aux.

Definition mpn_add_partial_solve_wit_3_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) ,
  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_full rp_pre bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  [| (bn_pre > 0) |]
.

Definition mpn_add_partial_solve_wit_3_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) ,
  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  (UIntArray.undef_full rp_pre bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
|--
  [| (bn_pre > 0) |] 
  &&  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full rp_pre bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
.

Definition mpn_add_partial_solve_wit_3 := mpn_add_partial_solve_wit_3_pure -> mpn_add_partial_solve_wit_3_aux.

Definition mpn_add_partial_solve_wit_4 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) ,
  [| ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) |] 
  &&  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
|--
  [| ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) |] 
  &&  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  (mpd_store_Z UINT_MOD rp_pre val_r_out bn_pre )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
.

Definition mpn_add_partial_solve_wit_5_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (l_r: (@list Z)) ,
  [| (an_pre > bn_pre) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= UINT_MAX) |] 
  &&  [| (an_pre <= INT_MAX) |] 
  &&  [| (bn_pre <= INT_MAX) |] 
  &&  [| (an_pre >= INT_MIN) |] 
  &&  [| (bn_pre >= INT_MIN) |] 
  &&  [| ((Zlength (l_r)) = bn_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) |] 
  &&  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  ((( &( "cy" ) )) # UInt  |-> retval)
  **  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
|--
  [| ((an_pre - bn_pre ) > 0) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= UINT_MAX) |]
.

Definition mpn_add_partial_solve_wit_5_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b: Z) (val_a: Z) (val_a_low: Z) (val_a_high: Z) (val_r_out: Z) (retval: Z) (l_r: (@list Z)) ,
  [| (an_pre > bn_pre) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= UINT_MAX) |] 
  &&  [| (an_pre <= INT_MAX) |] 
  &&  [| (bn_pre <= INT_MAX) |] 
  &&  [| (an_pre >= INT_MIN) |] 
  &&  [| (bn_pre >= INT_MIN) |] 
  &&  [| ((Zlength (l_r)) = bn_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) |] 
  &&  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
|--
  [| ((an_pre - bn_pre ) > 0) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= UINT_MAX) |] 
  &&  [| (an_pre > bn_pre) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval <= UINT_MAX) |] 
  &&  [| (an_pre <= INT_MAX) |] 
  &&  [| (bn_pre <= INT_MAX) |] 
  &&  [| (an_pre >= INT_MIN) |] 
  &&  [| (bn_pre >= INT_MIN) |] 
  &&  [| ((Zlength (l_r)) = bn_pre) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |] 
  &&  [| ((val_r_out + (retval * (Z.pow (UINT_MOD) (bn_pre)) ) ) = (val_a_low + val_b )) |] 
  &&  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn_pre)) ) )) |] 
  &&  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre > 0) |] 
  &&  [| (bn_pre > 0) |]
  &&  (mpd_store_Z UINT_MOD (ap_pre + (bn_pre * sizeof(UINT) ) ) val_a_high (an_pre - bn_pre ) )
  **  (UIntArray.undef_full (rp_pre + (bn_pre * sizeof(UINT) ) ) (an_pre - bn_pre ) )
  **  (UIntArray.full rp_pre bn_pre l_r )
  **  (mpd_store_Z UINT_MOD ap_pre val_a_low bn_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b bn_pre )
.

Definition mpn_add_partial_solve_wit_5 := mpn_add_partial_solve_wit_5_pure -> mpn_add_partial_solve_wit_5_aux.

Definition mpn_add_which_implies_wit_1 := 
forall (val_a: Z) (an: Z) (ap: Z) (bn: Z) ,
  [| (an >= bn) |] 
  &&  [| (bn > 0) |]
  &&  (mpd_store_Z UINT_MOD ap val_a an )
|--
  EX (val_a_high: Z)  (val_a_low: Z) ,
  [| (val_a = (val_a_low + (val_a_high * (Z.pow (UINT_MOD) (bn)) ) )) |]
  &&  (mpd_store_Z UINT_MOD ap val_a_low bn )
  **  (mpd_store_Z UINT_MOD (ap + (bn * sizeof(UINT) ) ) val_a_high (an - bn ) )
.

Definition mpn_add_which_implies_wit_2 := 
forall (an: Z) (bn: Z) (rp: Z) ,
  [| (an >= bn) |] 
  &&  [| (bn > 0) |]
  &&  (UIntArray.undef_full rp an )
|--
  (UIntArray.undef_full rp bn )
  **  (UIntArray.undef_full (rp + (bn * sizeof(UINT) ) ) (an - bn ) )
.

Definition mpn_add_which_implies_wit_3 := 
forall (val_r_out: Z) (bn: Z) (rp: Z) ,
  (mpd_store_Z UINT_MOD rp val_r_out bn )
|--
  EX (l_r: (@list Z)) ,
  [| ((Zlength (l_r)) = bn) |] 
  &&  [| ((list_to_Z (UINT_MOD) (l_r)) = val_r_out) |] 
  &&  [| (list_within_bound UINT_MOD l_r ) |]
  &&  (UIntArray.full rp bn l_r )
.

(*----- Function mpz_clear -----*)

Definition mpz_clear_return_wit_1_1 := 
forall (r_pre: Z) (n: Z) (ptr_2: Z) (cap_2: Z) (size_2: Z) ,
  [| (cap_2 = 0) |] 
  &&  [| ((Zabs (size_2)) <= cap_2) |] 
  &&  [| (size_2 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr_2 n size_2 )
  **  (UIntArray.undef_ceil ptr_2 size_2 cap_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_return_wit_1_2 := 
forall (r_pre: Z) (n: Z) (ptr_2: Z) (cap_2: Z) (size_2: Z) ,
  [| (cap_2 = 0) |] 
  &&  [| ((Zabs (size_2)) <= cap_2) |] 
  &&  [| (size_2 < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr_2 (-n) (-size_2) )
  **  (UIntArray.undef_ceil ptr_2 (-size_2) cap_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_return_wit_1_3 := 
forall (r_pre: Z) (n: Z) (ptr_2: Z) (cap_2: Z) (size_2: Z) ,
  [| (cap_2 <> 0) |] 
  &&  [| ((Zabs (size_2)) <= cap_2) |] 
  &&  [| (size_2 < 0) |] 
  &&  [| (n < 0) |]
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_return_wit_1_4 := 
forall (r_pre: Z) (n: Z) (ptr_2: Z) (cap_2: Z) (size_2: Z) ,
  [| (cap_2 <> 0) |] 
  &&  [| ((Zabs (size_2)) <= cap_2) |] 
  &&  [| (size_2 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_partial_solve_wit_1 := 
forall (r_pre: Z) (n: Z) ,
  (store_Z r_pre n )
|--
  (store_Z r_pre n )
.

Definition mpz_clear_partial_solve_wit_2 := 
forall (r_pre: Z) (n: Z) (ptr: Z) (cap: Z) (size: Z) ,
  [| (cap <> 0) |] 
  &&  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-size) )
  **  (UIntArray.undef_ceil ptr (-size) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (cap <> 0) |] 
  &&  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-size) )
  **  (UIntArray.undef_ceil ptr (-size) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_partial_solve_wit_3 := 
forall (r_pre: Z) (n: Z) (ptr: Z) (cap: Z) (size: Z) ,
  [| (cap <> 0) |] 
  &&  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n size )
  **  (UIntArray.undef_ceil ptr size cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (cap <> 0) |] 
  &&  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n size )
  **  (UIntArray.undef_ceil ptr size cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_which_implies_wit_1 := 
forall (n: Z) (r: Z) ,
  (store_Z r n )
|--
  (EX (ptr: Z)  (cap: Z)  (size: Z) ,
  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-size) )
  **  (UIntArray.undef_ceil ptr (-size) cap )
  **  ((&((r)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr))
  ||
  (EX (ptr: Z)  (cap: Z)  (size: Z) ,
  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n size )
  **  (UIntArray.undef_ceil ptr size cap )
  **  ((&((r)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr))
.

(*----- Function mpz_realloc -----*)

Definition mpz_realloc_safety_wit_1 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) ,
  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr n old )
  **  (UIntArray.undef_ceil ptr old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition mpz_realloc_safety_wit_2 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) ,
  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (-n) (-old) )
  **  (UIntArray.undef_ceil ptr (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition mpz_realloc_safety_wit_3 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 > retval) |] 
  &&  [| (retval_3 = (Zabs (old))) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (-n) (-old) )
  **  (UIntArray.undef_ceil ptr (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpz_realloc_safety_wit_4 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 > retval) |] 
  &&  [| (retval_3 = (Zabs (old))) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr n old )
  **  (UIntArray.undef_ceil ptr old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpz_realloc_safety_wit_5 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 > retval) |] 
  &&  [| (retval_3 = (Zabs (old))) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD retval_2 (-n) (-old) )
  **  (UIntArray.undef_ceil retval_2 (-old) retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpz_realloc_safety_wit_6 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 > retval) |] 
  &&  [| (retval_3 = (Zabs (old))) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD retval_2 n old )
  **  (UIntArray.undef_ceil retval_2 old retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpz_realloc_return_wit_1_1 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval: Z) (retval_3: Z) ,
  [| (retval_3 <= retval_2) |] 
  &&  [| (retval_3 = (Zabs (old))) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD retval n old )
  **  (UIntArray.undef_ceil retval old retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  (EX (r_pre__mp_alloc: Z) ,
  [| (n >= 0) |] 
  &&  [| (r_pre__mp_alloc = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval n old )
  **  (UIntArray.undef_ceil retval old (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
  ||
  (EX (r_pre__mp_alloc_2: Z) ,
  [| (n < 0) |] 
  &&  [| (r_pre__mp_alloc_2 = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval (-n) (-old) )
  **  (UIntArray.undef_ceil retval (-old) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
.

Definition mpz_realloc_return_wit_1_2 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval: Z) (retval_3: Z) ,
  [| (retval_3 <= retval_2) |] 
  &&  [| (retval_3 = (Zabs (old))) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD retval (-n) (-old) )
  **  (UIntArray.undef_ceil retval (-old) retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  (EX (r_pre__mp_alloc: Z) ,
  [| (n >= 0) |] 
  &&  [| (r_pre__mp_alloc = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval n old )
  **  (UIntArray.undef_ceil retval old (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
  ||
  (EX (r_pre__mp_alloc_2: Z) ,
  [| (n < 0) |] 
  &&  [| (r_pre__mp_alloc_2 = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval (-n) (-old) )
  **  (UIntArray.undef_ceil retval (-old) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
.

Definition mpz_realloc_return_wit_1_3 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval: Z) (retval_3: Z) ,
  [| (retval_3 <= retval_2) |] 
  &&  [| (retval_3 = (Zabs (old))) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr n old )
  **  (UIntArray.undef_ceil ptr old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  (EX (r_pre__mp_alloc: Z) ,
  [| (n >= 0) |] 
  &&  [| (r_pre__mp_alloc = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval n old )
  **  (UIntArray.undef_ceil retval old (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
  ||
  (EX (r_pre__mp_alloc_2: Z) ,
  [| (n < 0) |] 
  &&  [| (r_pre__mp_alloc_2 = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval (-n) (-old) )
  **  (UIntArray.undef_ceil retval (-old) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
.

Definition mpz_realloc_return_wit_1_4 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval: Z) (retval_3: Z) ,
  [| (retval_3 <= retval_2) |] 
  &&  [| (retval_3 = (Zabs (old))) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (-n) (-old) )
  **  (UIntArray.undef_ceil ptr (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  (EX (r_pre__mp_alloc: Z) ,
  [| (n >= 0) |] 
  &&  [| (r_pre__mp_alloc = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval n old )
  **  (UIntArray.undef_ceil retval old (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
  ||
  (EX (r_pre__mp_alloc_2: Z) ,
  [| (n < 0) |] 
  &&  [| (r_pre__mp_alloc_2 = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval (-n) (-old) )
  **  (UIntArray.undef_ceil retval (-old) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
.

Definition mpz_realloc_return_wit_1_5 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval: Z) (retval_3: Z) ,
  [| (retval_3 > retval_2) |] 
  &&  [| (retval_3 = (Zabs (old))) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (-n) (-old) )
  **  (UIntArray.undef_ceil ptr (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  (EX (r_pre__mp_alloc: Z) ,
  [| (n >= 0) |] 
  &&  [| (r_pre__mp_alloc = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval n old )
  **  (UIntArray.undef_ceil retval old (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
  ||
  (EX (r_pre__mp_alloc_2: Z) ,
  [| (n < 0) |] 
  &&  [| (r_pre__mp_alloc_2 = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval (-n) (-old) )
  **  (UIntArray.undef_ceil retval (-old) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
.

Definition mpz_realloc_return_wit_1_6 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval: Z) (retval_3: Z) ,
  [| (retval_3 > retval_2) |] 
  &&  [| (retval_3 = (Zabs (old))) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (UIntArray.undef_full retval retval_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr n old )
  **  (UIntArray.undef_ceil ptr old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  (EX (r_pre__mp_alloc: Z) ,
  [| (n >= 0) |] 
  &&  [| (r_pre__mp_alloc = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval n old )
  **  (UIntArray.undef_ceil retval old (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
  ||
  (EX (r_pre__mp_alloc_2: Z) ,
  [| (n < 0) |] 
  &&  [| (r_pre__mp_alloc_2 = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval (-n) (-old) )
  **  (UIntArray.undef_ceil retval (-old) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
.

Definition mpz_realloc_return_wit_1_7 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval: Z) (retval_3: Z) ,
  [| (retval_3 > retval_2) |] 
  &&  [| (retval_3 = (Zabs (old))) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD retval (-n) (-old) )
  **  (UIntArray.undef_ceil retval (-old) retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  (EX (r_pre__mp_alloc: Z) ,
  [| (n >= 0) |] 
  &&  [| (r_pre__mp_alloc = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval n old )
  **  (UIntArray.undef_ceil retval old (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
  ||
  (EX (r_pre__mp_alloc_2: Z) ,
  [| (n < 0) |] 
  &&  [| (r_pre__mp_alloc_2 = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval (-n) (-old) )
  **  (UIntArray.undef_ceil retval (-old) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
.

Definition mpz_realloc_return_wit_1_8 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval: Z) (retval_3: Z) ,
  [| (retval_3 > retval_2) |] 
  &&  [| (retval_3 = (Zabs (old))) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD retval n old )
  **  (UIntArray.undef_ceil retval old retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  (EX (r_pre__mp_alloc: Z) ,
  [| (n >= 0) |] 
  &&  [| (r_pre__mp_alloc = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval n old )
  **  (UIntArray.undef_ceil retval old (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
  ||
  (EX (r_pre__mp_alloc_2: Z) ,
  [| (n < 0) |] 
  &&  [| (r_pre__mp_alloc_2 = (Z.max (size_pre) (1))) |]
  &&  (mpd_store_Z_compact UINT_MOD retval (-n) (-old) )
  **  (UIntArray.undef_ceil retval (-old) (Z.max (size_pre) (1)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> r_pre__mp_alloc_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval))
.

Definition mpz_realloc_partial_solve_wit_1 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) ,
  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n old )
  **  (UIntArray.undef_ceil ptr old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n old )
  **  (UIntArray.undef_ceil ptr old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_2 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) ,
  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-old) )
  **  (UIntArray.undef_ceil ptr (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-old) )
  **  (UIntArray.undef_ceil ptr (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_3_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (-n) (-old) )
  **  (UIntArray.undef_ceil ptr (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (cap >= 0) |] 
  &&  [| (retval >= cap) |] 
  &&  [| ((Z.max (size_pre) (1)) >= cap) |]
.

Definition mpz_realloc_partial_solve_wit_3_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-old) )
  **  (UIntArray.undef_ceil ptr (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (cap >= 0) |] 
  &&  [| (retval >= cap) |] 
  &&  [| ((Z.max (size_pre) (1)) >= cap) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-old) )
  **  (UIntArray.undef_ceil ptr (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_3 := mpz_realloc_partial_solve_wit_3_pure -> mpz_realloc_partial_solve_wit_3_aux.

Definition mpz_realloc_partial_solve_wit_4_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr n old )
  **  (UIntArray.undef_ceil ptr old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (cap >= 0) |] 
  &&  [| (retval >= cap) |] 
  &&  [| ((Z.max (size_pre) (1)) >= cap) |]
.

Definition mpz_realloc_partial_solve_wit_4_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n old )
  **  (UIntArray.undef_ceil ptr old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (cap >= 0) |] 
  &&  [| (retval >= cap) |] 
  &&  [| ((Z.max (size_pre) (1)) >= cap) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n old )
  **  (UIntArray.undef_ceil ptr old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_4 := mpz_realloc_partial_solve_wit_4_pure -> mpz_realloc_partial_solve_wit_4_aux.

Definition mpz_realloc_partial_solve_wit_5_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (-n) (-old) )
  **  (UIntArray.undef_ceil ptr (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (retval >= 0) |]
.

Definition mpz_realloc_partial_solve_wit_5_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-old) )
  **  (UIntArray.undef_ceil ptr (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (retval >= 0) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-old) )
  **  (UIntArray.undef_ceil ptr (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_5 := mpz_realloc_partial_solve_wit_5_pure -> mpz_realloc_partial_solve_wit_5_aux.

Definition mpz_realloc_partial_solve_wit_6_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr n old )
  **  (UIntArray.undef_ceil ptr old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (retval >= 0) |]
.

Definition mpz_realloc_partial_solve_wit_6_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n old )
  **  (UIntArray.undef_ceil ptr old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (retval >= 0) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n old )
  **  (UIntArray.undef_ceil ptr old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_6 := mpz_realloc_partial_solve_wit_6_pure -> mpz_realloc_partial_solve_wit_6_aux.

Definition mpz_realloc_partial_solve_wit_7_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr (-n) (-old) )
  **  (UIntArray.undef_ceil ptr (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (old <= INT_MAX) |] 
  &&  [| (INT_MIN < old) |]
.

Definition mpz_realloc_partial_solve_wit_7_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (UIntArray.undef_full retval_2 retval )
  **  (mpd_store_Z_compact UINT_MOD ptr (-n) (-old) )
  **  (UIntArray.undef_ceil ptr (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (old <= INT_MAX) |] 
  &&  [| (INT_MIN < old) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (UIntArray.undef_full retval_2 retval )
  **  (mpd_store_Z_compact UINT_MOD ptr (-n) (-old) )
  **  (UIntArray.undef_ceil ptr (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
.

Definition mpz_realloc_partial_solve_wit_7 := mpz_realloc_partial_solve_wit_7_pure -> mpz_realloc_partial_solve_wit_7_aux.

Definition mpz_realloc_partial_solve_wit_8_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (UIntArray.undef_full retval_2 retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact UINT_MOD ptr n old )
  **  (UIntArray.undef_ceil ptr old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (INT_MIN < old) |] 
  &&  [| (old <= INT_MAX) |]
.

Definition mpz_realloc_partial_solve_wit_8_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (UIntArray.undef_full retval_2 retval )
  **  (mpd_store_Z_compact UINT_MOD ptr n old )
  **  (UIntArray.undef_ceil ptr old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (INT_MIN < old) |] 
  &&  [| (old <= INT_MAX) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (UIntArray.undef_full retval_2 retval )
  **  (mpd_store_Z_compact UINT_MOD ptr n old )
  **  (UIntArray.undef_ceil ptr old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
.

Definition mpz_realloc_partial_solve_wit_8 := mpz_realloc_partial_solve_wit_8_pure -> mpz_realloc_partial_solve_wit_8_aux.

Definition mpz_realloc_partial_solve_wit_9_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD retval_2 (-n) (-old) )
  **  (UIntArray.undef_ceil retval_2 (-old) retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (old <= INT_MAX) |] 
  &&  [| (INT_MIN < old) |]
.

Definition mpz_realloc_partial_solve_wit_9_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD retval_2 (-n) (-old) )
  **  (UIntArray.undef_ceil retval_2 (-old) retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (old <= INT_MAX) |] 
  &&  [| (INT_MIN < old) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD retval_2 (-n) (-old) )
  **  (UIntArray.undef_ceil retval_2 (-old) retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
.

Definition mpz_realloc_partial_solve_wit_9 := mpz_realloc_partial_solve_wit_9_pure -> mpz_realloc_partial_solve_wit_9_aux.

Definition mpz_realloc_partial_solve_wit_10_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD retval_2 n old )
  **  (UIntArray.undef_ceil retval_2 old retval )
  **  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (INT_MIN < old) |] 
  &&  [| (old <= INT_MAX) |]
.

Definition mpz_realloc_partial_solve_wit_10_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD retval_2 n old )
  **  (UIntArray.undef_ceil retval_2 old retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (INT_MIN < old) |] 
  &&  [| (old <= INT_MAX) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= INT_MAX) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| ((Zabs (old)) <= cap) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD retval_2 n old )
  **  (UIntArray.undef_ceil retval_2 old retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
.

Definition mpz_realloc_partial_solve_wit_10 := mpz_realloc_partial_solve_wit_10_pure -> mpz_realloc_partial_solve_wit_10_aux.

(*----- Function mpz_sgn -----*)

Definition mpz_sgn_safety_wit_1 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (cap: Z) (size: Z) ,
  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-size) )
  **  (UIntArray.undef_ceil ptr (-size) cap )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpz_sgn_safety_wit_2 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (cap: Z) (size: Z) (retval: Z) ,
  [| (size = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-size) )
  **  (UIntArray.undef_ceil ptr (-size) cap )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| False |]
.

Definition mpz_sgn_safety_wit_3 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (cap: Z) (size: Z) (retval: Z) ,
  [| (size > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-size) )
  **  (UIntArray.undef_ceil ptr (-size) cap )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| False |]
.

Definition mpz_sgn_safety_wit_4 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (cap: Z) (size: Z) ,
  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n size )
  **  (UIntArray.undef_ceil ptr size cap )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpz_sgn_safety_wit_5 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (cap: Z) (size: Z) (retval: Z) ,
  [| (size < 0) |] 
  &&  [| (retval = (-1)) |] 
  &&  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n size )
  **  (UIntArray.undef_ceil ptr size cap )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| False |]
.

Definition mpz_sgn_return_wit_1_1 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (cap: Z) (size: Z) (retval: Z) ,
  [| (size > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n size )
  **  (UIntArray.undef_ceil ptr size cap )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  ([| (n < 0) |] 
  &&  [| (retval = (-1)) |]
  &&  (store_Z u_pre n ))
  ||
  ([| (n = 0) |] 
  &&  [| (retval = 0) |]
  &&  (store_Z u_pre n ))
  ||
  ([| (n > 0) |] 
  &&  [| (retval = 1) |]
  &&  (store_Z u_pre n ))
.

Definition mpz_sgn_return_wit_1_2 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (cap: Z) (size: Z) (retval: Z) ,
  [| (size = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n size )
  **  (UIntArray.undef_ceil ptr size cap )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  ([| (n < 0) |] 
  &&  [| (retval = (-1)) |]
  &&  (store_Z u_pre n ))
  ||
  ([| (n = 0) |] 
  &&  [| (retval = 0) |]
  &&  (store_Z u_pre n ))
  ||
  ([| (n > 0) |] 
  &&  [| (retval = 1) |]
  &&  (store_Z u_pre n ))
.

Definition mpz_sgn_return_wit_1_3 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (cap: Z) (size: Z) (retval: Z) ,
  [| (size < 0) |] 
  &&  [| (retval = (-1)) |] 
  &&  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-size) )
  **  (UIntArray.undef_ceil ptr (-size) cap )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  ([| (n < 0) |] 
  &&  [| (retval = (-1)) |]
  &&  (store_Z u_pre n ))
  ||
  ([| (n = 0) |] 
  &&  [| (retval = 0) |]
  &&  (store_Z u_pre n ))
  ||
  ([| (n > 0) |] 
  &&  [| (retval = 1) |]
  &&  (store_Z u_pre n ))
.

Definition mpz_sgn_partial_solve_wit_1 := 
forall (u_pre: Z) (n: Z) ,
  (store_Z u_pre n )
|--
  (store_Z u_pre n )
.

Definition mpz_sgn_partial_solve_wit_2 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (cap: Z) (size: Z) ,
  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-size) )
  **  (UIntArray.undef_ceil ptr (-size) cap )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-size) )
  **  (UIntArray.undef_ceil ptr (-size) cap )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_sgn_partial_solve_wit_3 := 
forall (u_pre: Z) (n: Z) (ptr: Z) (cap: Z) (size: Z) ,
  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n size )
  **  (UIntArray.undef_ceil ptr size cap )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n size )
  **  (UIntArray.undef_ceil ptr size cap )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_sgn_which_implies_wit_1 := 
forall (n: Z) (u: Z) ,
  (store_Z u n )
|--
  (EX (ptr: Z)  (cap: Z)  (size: Z) ,
  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr (-n) (-size) )
  **  (UIntArray.undef_ceil ptr (-size) cap )
  **  ((&((u)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr))
  ||
  (EX (ptr: Z)  (cap: Z)  (size: Z) ,
  [| ((Zabs (size)) <= cap) |] 
  &&  [| (size >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr n size )
  **  (UIntArray.undef_ceil ptr size cap )
  **  ((&((u)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr))
.

(*----- Function mpz_swap -----*)

Definition mpz_swap_return_wit_1_1 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 < 0) |] 
  &&  [| (m < 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 (-m) (-size2) )
  **  (UIntArray.undef_ceil ptr2 (-size2) cap2 )
  **  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
|--
  (store_Z u_pre m )
  **  (store_Z v_pre n )
.

Definition mpz_swap_return_wit_1_2 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 >= 0) |] 
  &&  [| (m >= 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 m size2 )
  **  (UIntArray.undef_ceil ptr2 size2 cap2 )
  **  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
|--
  (store_Z u_pre m )
  **  (store_Z v_pre n )
.

Definition mpz_swap_return_wit_1_3 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 < 0) |] 
  &&  [| (m < 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 (-m) (-size2) )
  **  (UIntArray.undef_ceil ptr2 (-size2) cap2 )
  **  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
|--
  (store_Z u_pre m )
  **  (store_Z v_pre n )
.

Definition mpz_swap_return_wit_1_4 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 >= 0) |] 
  &&  [| (m >= 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 m size2 )
  **  (UIntArray.undef_ceil ptr2 size2 cap2 )
  **  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
|--
  (store_Z u_pre m )
  **  (store_Z v_pre n )
.

Definition mpz_swap_partial_solve_wit_1 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) ,
  (store_Z u_pre n )
  **  (store_Z v_pre m )
|--
  (store_Z u_pre n )
  **  (store_Z v_pre m )
.

Definition mpz_swap_partial_solve_wit_2 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) ,
  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  (store_Z v_pre m )
|--
  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (store_Z v_pre m )
  **  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
.

Definition mpz_swap_partial_solve_wit_3 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) ,
  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  (store_Z v_pre m )
|--
  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  (store_Z v_pre m )
  **  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
.

Definition mpz_swap_partial_solve_wit_4 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 < 0) |] 
  &&  [| (m < 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr2 (-m) (-size2) )
  **  (UIntArray.undef_ceil ptr2 (-size2) cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
|--
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 < 0) |] 
  &&  [| (m < 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  (mpd_store_Z_compact UINT_MOD ptr2 (-m) (-size2) )
  **  (UIntArray.undef_ceil ptr2 (-size2) cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
.

Definition mpz_swap_partial_solve_wit_5 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 >= 0) |] 
  &&  [| (m >= 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr2 m size2 )
  **  (UIntArray.undef_ceil ptr2 size2 cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
|--
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 >= 0) |] 
  &&  [| (m >= 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  (mpd_store_Z_compact UINT_MOD ptr2 m size2 )
  **  (UIntArray.undef_ceil ptr2 size2 cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
.

Definition mpz_swap_partial_solve_wit_6 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 < 0) |] 
  &&  [| (m < 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr2 (-m) (-size2) )
  **  (UIntArray.undef_ceil ptr2 (-size2) cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
|--
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 < 0) |] 
  &&  [| (m < 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  (mpd_store_Z_compact UINT_MOD ptr2 (-m) (-size2) )
  **  (UIntArray.undef_ceil ptr2 (-size2) cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
.

Definition mpz_swap_partial_solve_wit_7 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 >= 0) |] 
  &&  [| (m >= 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr2 m size2 )
  **  (UIntArray.undef_ceil ptr2 size2 cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
|--
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 >= 0) |] 
  &&  [| (m >= 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  (mpd_store_Z_compact UINT_MOD ptr2 m size2 )
  **  (UIntArray.undef_ceil ptr2 size2 cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
.

Definition mpz_swap_partial_solve_wit_8 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 >= 0) |] 
  &&  [| (m >= 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 m size2 )
  **  (UIntArray.undef_ceil ptr2 size2 cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
|--
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 >= 0) |] 
  &&  [| (m >= 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 m size2 )
  **  (UIntArray.undef_ceil ptr2 size2 cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
.

Definition mpz_swap_partial_solve_wit_9 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 < 0) |] 
  &&  [| (m < 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 (-m) (-size2) )
  **  (UIntArray.undef_ceil ptr2 (-size2) cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
|--
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 < 0) |] 
  &&  [| (m < 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 (-m) (-size2) )
  **  (UIntArray.undef_ceil ptr2 (-size2) cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
.

Definition mpz_swap_partial_solve_wit_10 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 >= 0) |] 
  &&  [| (m >= 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 m size2 )
  **  (UIntArray.undef_ceil ptr2 size2 cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
|--
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 >= 0) |] 
  &&  [| (m >= 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 m size2 )
  **  (UIntArray.undef_ceil ptr2 size2 cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
.

Definition mpz_swap_partial_solve_wit_11 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 < 0) |] 
  &&  [| (m < 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 (-m) (-size2) )
  **  (UIntArray.undef_ceil ptr2 (-size2) cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
|--
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 < 0) |] 
  &&  [| (m < 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 (-m) (-size2) )
  **  (UIntArray.undef_ceil ptr2 (-size2) cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
.

Definition mpz_swap_partial_solve_wit_12 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 < 0) |] 
  &&  [| (m < 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 (-m) (-size2) )
  **  (UIntArray.undef_ceil ptr2 (-size2) cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
|--
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 < 0) |] 
  &&  [| (m < 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 (-m) (-size2) )
  **  (UIntArray.undef_ceil ptr2 (-size2) cap2 )
  **  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
.

Definition mpz_swap_partial_solve_wit_13 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 >= 0) |] 
  &&  [| (m >= 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 m size2 )
  **  (UIntArray.undef_ceil ptr2 size2 cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
|--
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 >= 0) |] 
  &&  [| (m >= 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 m size2 )
  **  (UIntArray.undef_ceil ptr2 size2 cap2 )
  **  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
.

Definition mpz_swap_partial_solve_wit_14 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 < 0) |] 
  &&  [| (m < 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 (-m) (-size2) )
  **  (UIntArray.undef_ceil ptr2 (-size2) cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
|--
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 < 0) |] 
  &&  [| (m < 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 (-m) (-size2) )
  **  (UIntArray.undef_ceil ptr2 (-size2) cap2 )
  **  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
.

Definition mpz_swap_partial_solve_wit_15 := 
forall (v_pre: Z) (u_pre: Z) (m: Z) (n: Z) (ptr1: Z) (cap1: Z) (size1: Z) (ptr2: Z) (cap2: Z) (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 >= 0) |] 
  &&  [| (m >= 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 m size2 )
  **  (UIntArray.undef_ceil ptr2 size2 cap2 )
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
|--
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 >= 0) |] 
  &&  [| (m >= 0) |] 
  &&  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  (mpd_store_Z_compact UINT_MOD ptr2 m size2 )
  **  (UIntArray.undef_ceil ptr2 size2 cap2 )
  **  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
.

Definition mpz_swap_which_implies_wit_1 := 
forall (n: Z) (u: Z) ,
  (store_Z u n )
|--
  (EX (ptr1: Z)  (cap1: Z)  (size1: Z) ,
  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr1 (-n) (-size1) )
  **  (UIntArray.undef_ceil ptr1 (-size1) cap1 )
  **  ((&((u)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  ((&((u)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1))
  ||
  (EX (ptr1: Z)  (cap1: Z)  (size1: Z) ,
  [| ((Zabs (size1)) <= cap1) |] 
  &&  [| (size1 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr1 n size1 )
  **  (UIntArray.undef_ceil ptr1 size1 cap1 )
  **  ((&((u)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size1)
  **  ((&((u)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap1)
  **  ((&((u)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr1))
.

Definition mpz_swap_which_implies_wit_2 := 
forall (m: Z) (v: Z) ,
  (store_Z v m )
|--
  (EX (ptr2: Z)  (cap2: Z)  (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 < 0) |] 
  &&  [| (m < 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr2 (-m) (-size2) )
  **  (UIntArray.undef_ceil ptr2 (-size2) cap2 )
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2))
  ||
  (EX (ptr2: Z)  (cap2: Z)  (size2: Z) ,
  [| ((Zabs (size2)) <= cap2) |] 
  &&  [| (size2 >= 0) |] 
  &&  [| (m >= 0) |]
  &&  (mpd_store_Z_compact UINT_MOD ptr2 m size2 )
  **  (UIntArray.undef_ceil ptr2 size2 cap2 )
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size2)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap2)
  **  ((&((v)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr2))
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_gmp_abs_safety_wit_1 : gmp_abs_safety_wit_1.
Axiom proof_of_gmp_abs_return_wit_1_1 : gmp_abs_return_wit_1_1.
Axiom proof_of_gmp_abs_return_wit_1_2 : gmp_abs_return_wit_1_2.
Axiom proof_of_gmp_max_return_wit_1_1 : gmp_max_return_wit_1_1.
Axiom proof_of_gmp_max_return_wit_1_2 : gmp_max_return_wit_1_2.
Axiom proof_of_gmp_cmp_safety_wit_1 : gmp_cmp_safety_wit_1.
Axiom proof_of_gmp_cmp_safety_wit_2 : gmp_cmp_safety_wit_2.
Axiom proof_of_gmp_cmp_safety_wit_3 : gmp_cmp_safety_wit_3.
Axiom proof_of_gmp_cmp_safety_wit_4 : gmp_cmp_safety_wit_4.
Axiom proof_of_gmp_cmp_return_wit_1_1 : gmp_cmp_return_wit_1_1.
Axiom proof_of_gmp_cmp_return_wit_1_2 : gmp_cmp_return_wit_1_2.
Axiom proof_of_gmp_cmp_return_wit_1_3 : gmp_cmp_return_wit_1_3.
Axiom proof_of_mpn_copyi_safety_wit_1 : mpn_copyi_safety_wit_1.
Axiom proof_of_mpn_copyi_safety_wit_2 : mpn_copyi_safety_wit_2.
Axiom proof_of_mpn_copyi_entail_wit_1 : mpn_copyi_entail_wit_1.
Axiom proof_of_mpn_copyi_entail_wit_2 : mpn_copyi_entail_wit_2.
Axiom proof_of_mpn_copyi_return_wit_1 : mpn_copyi_return_wit_1.
Axiom proof_of_mpn_copyi_partial_solve_wit_1 : mpn_copyi_partial_solve_wit_1.
Axiom proof_of_mpn_copyi_partial_solve_wit_2 : mpn_copyi_partial_solve_wit_2.
Axiom proof_of_mpn_copyi_partial_solve_wit_3 : mpn_copyi_partial_solve_wit_3.
Axiom proof_of_mpn_copyi_which_implies_wit_1 : mpn_copyi_which_implies_wit_1.
Axiom proof_of_mpn_cmp_safety_wit_1 : mpn_cmp_safety_wit_1.
Axiom proof_of_mpn_cmp_safety_wit_2 : mpn_cmp_safety_wit_2.
Axiom proof_of_mpn_cmp_safety_wit_3 : mpn_cmp_safety_wit_3.
Axiom proof_of_mpn_cmp_safety_wit_4 : mpn_cmp_safety_wit_4.
Axiom proof_of_mpn_cmp_safety_wit_5 : mpn_cmp_safety_wit_5.
Axiom proof_of_mpn_cmp_safety_wit_6 : mpn_cmp_safety_wit_6.
Axiom proof_of_mpn_cmp_safety_wit_7 : mpn_cmp_safety_wit_7.
Axiom proof_of_mpn_cmp_entail_wit_1 : mpn_cmp_entail_wit_1.
Axiom proof_of_mpn_cmp_entail_wit_2 : mpn_cmp_entail_wit_2.
Axiom proof_of_mpn_cmp_return_wit_1_1 : mpn_cmp_return_wit_1_1.
Axiom proof_of_mpn_cmp_return_wit_1_2 : mpn_cmp_return_wit_1_2.
Axiom proof_of_mpn_cmp_return_wit_2 : mpn_cmp_return_wit_2.
Axiom proof_of_mpn_cmp_partial_solve_wit_1 : mpn_cmp_partial_solve_wit_1.
Axiom proof_of_mpn_cmp_partial_solve_wit_2 : mpn_cmp_partial_solve_wit_2.
Axiom proof_of_mpn_cmp_partial_solve_wit_3 : mpn_cmp_partial_solve_wit_3.
Axiom proof_of_mpn_cmp_which_implies_wit_1 : mpn_cmp_which_implies_wit_1.
Axiom proof_of_mpn_cmp4_safety_wit_1 : mpn_cmp4_safety_wit_1.
Axiom proof_of_mpn_cmp4_safety_wit_2 : mpn_cmp4_safety_wit_2.
Axiom proof_of_mpn_cmp4_safety_wit_3 : mpn_cmp4_safety_wit_3.
Axiom proof_of_mpn_cmp4_return_wit_1_1 : mpn_cmp4_return_wit_1_1.
Axiom proof_of_mpn_cmp4_return_wit_1_2 : mpn_cmp4_return_wit_1_2.
Axiom proof_of_mpn_cmp4_return_wit_2_1 : mpn_cmp4_return_wit_2_1.
Axiom proof_of_mpn_cmp4_return_wit_2_2 : mpn_cmp4_return_wit_2_2.
Axiom proof_of_mpn_cmp4_return_wit_2_3 : mpn_cmp4_return_wit_2_3.
Axiom proof_of_mpn_cmp4_partial_solve_wit_1_pure : mpn_cmp4_partial_solve_wit_1_pure.
Axiom proof_of_mpn_cmp4_partial_solve_wit_1 : mpn_cmp4_partial_solve_wit_1.
Axiom proof_of_mpn_normalized_size_safety_wit_1 : mpn_normalized_size_safety_wit_1.
Axiom proof_of_mpn_normalized_size_safety_wit_2 : mpn_normalized_size_safety_wit_2.
Axiom proof_of_mpn_normalized_size_safety_wit_3 : mpn_normalized_size_safety_wit_3.
Axiom proof_of_mpn_normalized_size_safety_wit_4 : mpn_normalized_size_safety_wit_4.
Axiom proof_of_mpn_normalized_size_safety_wit_5 : mpn_normalized_size_safety_wit_5.
Axiom proof_of_mpn_normalized_size_entail_wit_1 : mpn_normalized_size_entail_wit_1.
Axiom proof_of_mpn_normalized_size_entail_wit_2 : mpn_normalized_size_entail_wit_2.
Axiom proof_of_mpn_normalized_size_entail_wit_3 : mpn_normalized_size_entail_wit_3.
Axiom proof_of_mpn_normalized_size_return_wit_1_1 : mpn_normalized_size_return_wit_1_1.
Axiom proof_of_mpn_normalized_size_return_wit_1_2 : mpn_normalized_size_return_wit_1_2.
Axiom proof_of_mpn_normalized_size_partial_solve_wit_1 : mpn_normalized_size_partial_solve_wit_1.
Axiom proof_of_mpn_normalized_size_partial_solve_wit_2 : mpn_normalized_size_partial_solve_wit_2.
Axiom proof_of_mpn_normalized_size_which_implies_wit_1 : mpn_normalized_size_which_implies_wit_1.
Axiom proof_of_mpn_add_1_safety_wit_1 : mpn_add_1_safety_wit_1.
Axiom proof_of_mpn_add_1_safety_wit_2 : mpn_add_1_safety_wit_2.
Axiom proof_of_mpn_add_1_safety_wit_3 : mpn_add_1_safety_wit_3.
Axiom proof_of_mpn_add_1_safety_wit_4 : mpn_add_1_safety_wit_4.
Axiom proof_of_mpn_add_1_safety_wit_5 : mpn_add_1_safety_wit_5.
Axiom proof_of_mpn_add_1_entail_wit_1_1 : mpn_add_1_entail_wit_1_1.
Axiom proof_of_mpn_add_1_entail_wit_1_2 : mpn_add_1_entail_wit_1_2.
Axiom proof_of_mpn_add_1_entail_wit_2_1 : mpn_add_1_entail_wit_2_1.
Axiom proof_of_mpn_add_1_entail_wit_2_2 : mpn_add_1_entail_wit_2_2.
Axiom proof_of_mpn_add_1_return_wit_1 : mpn_add_1_return_wit_1.
Axiom proof_of_mpn_add_1_partial_solve_wit_1 : mpn_add_1_partial_solve_wit_1.
Axiom proof_of_mpn_add_1_partial_solve_wit_2 : mpn_add_1_partial_solve_wit_2.
Axiom proof_of_mpn_add_1_partial_solve_wit_3 : mpn_add_1_partial_solve_wit_3.
Axiom proof_of_mpn_add_1_partial_solve_wit_4 : mpn_add_1_partial_solve_wit_4.
Axiom proof_of_mpn_add_1_partial_solve_wit_5 : mpn_add_1_partial_solve_wit_5.
Axiom proof_of_mpn_add_1_partial_solve_wit_6 : mpn_add_1_partial_solve_wit_6.
Axiom proof_of_mpn_add_1_partial_solve_wit_7 : mpn_add_1_partial_solve_wit_7.
Axiom proof_of_mpn_add_1_which_implies_wit_1 : mpn_add_1_which_implies_wit_1.
Axiom proof_of_mpn_add_n_safety_wit_1 : mpn_add_n_safety_wit_1.
Axiom proof_of_mpn_add_n_safety_wit_2 : mpn_add_n_safety_wit_2.
Axiom proof_of_mpn_add_n_safety_wit_3 : mpn_add_n_safety_wit_3.
Axiom proof_of_mpn_add_n_safety_wit_4 : mpn_add_n_safety_wit_4.
Axiom proof_of_mpn_add_n_safety_wit_5 : mpn_add_n_safety_wit_5.
Axiom proof_of_mpn_add_n_safety_wit_6 : mpn_add_n_safety_wit_6.
Axiom proof_of_mpn_add_n_entail_wit_1 : mpn_add_n_entail_wit_1.
Axiom proof_of_mpn_add_n_entail_wit_2_1 : mpn_add_n_entail_wit_2_1.
Axiom proof_of_mpn_add_n_entail_wit_2_2 : mpn_add_n_entail_wit_2_2.
Axiom proof_of_mpn_add_n_entail_wit_2_3 : mpn_add_n_entail_wit_2_3.
Axiom proof_of_mpn_add_n_entail_wit_2_4 : mpn_add_n_entail_wit_2_4.
Axiom proof_of_mpn_add_n_return_wit_1 : mpn_add_n_return_wit_1.
Axiom proof_of_mpn_add_n_partial_solve_wit_1 : mpn_add_n_partial_solve_wit_1.
Axiom proof_of_mpn_add_n_partial_solve_wit_2 : mpn_add_n_partial_solve_wit_2.
Axiom proof_of_mpn_add_n_partial_solve_wit_3 : mpn_add_n_partial_solve_wit_3.
Axiom proof_of_mpn_add_n_partial_solve_wit_4 : mpn_add_n_partial_solve_wit_4.
Axiom proof_of_mpn_add_n_partial_solve_wit_5 : mpn_add_n_partial_solve_wit_5.
Axiom proof_of_mpn_add_n_partial_solve_wit_6 : mpn_add_n_partial_solve_wit_6.
Axiom proof_of_mpn_add_n_partial_solve_wit_7 : mpn_add_n_partial_solve_wit_7.
Axiom proof_of_mpn_add_n_which_implies_wit_1 : mpn_add_n_which_implies_wit_1.
Axiom proof_of_mpn_add_safety_wit_1 : mpn_add_safety_wit_1.
Axiom proof_of_mpn_add_entail_wit_1 : mpn_add_entail_wit_1.
Axiom proof_of_mpn_add_return_wit_1_1 : mpn_add_return_wit_1_1.
Axiom proof_of_mpn_add_return_wit_1_2 : mpn_add_return_wit_1_2.
Axiom proof_of_mpn_add_partial_solve_wit_1_pure : mpn_add_partial_solve_wit_1_pure.
Axiom proof_of_mpn_add_partial_solve_wit_1 : mpn_add_partial_solve_wit_1.
Axiom proof_of_mpn_add_partial_solve_wit_2_pure : mpn_add_partial_solve_wit_2_pure.
Axiom proof_of_mpn_add_partial_solve_wit_2 : mpn_add_partial_solve_wit_2.
Axiom proof_of_mpn_add_partial_solve_wit_3_pure : mpn_add_partial_solve_wit_3_pure.
Axiom proof_of_mpn_add_partial_solve_wit_3 : mpn_add_partial_solve_wit_3.
Axiom proof_of_mpn_add_partial_solve_wit_4 : mpn_add_partial_solve_wit_4.
Axiom proof_of_mpn_add_partial_solve_wit_5_pure : mpn_add_partial_solve_wit_5_pure.
Axiom proof_of_mpn_add_partial_solve_wit_5 : mpn_add_partial_solve_wit_5.
Axiom proof_of_mpn_add_which_implies_wit_1 : mpn_add_which_implies_wit_1.
Axiom proof_of_mpn_add_which_implies_wit_2 : mpn_add_which_implies_wit_2.
Axiom proof_of_mpn_add_which_implies_wit_3 : mpn_add_which_implies_wit_3.
Axiom proof_of_mpz_clear_return_wit_1_1 : mpz_clear_return_wit_1_1.
Axiom proof_of_mpz_clear_return_wit_1_2 : mpz_clear_return_wit_1_2.
Axiom proof_of_mpz_clear_return_wit_1_3 : mpz_clear_return_wit_1_3.
Axiom proof_of_mpz_clear_return_wit_1_4 : mpz_clear_return_wit_1_4.
Axiom proof_of_mpz_clear_partial_solve_wit_1 : mpz_clear_partial_solve_wit_1.
Axiom proof_of_mpz_clear_partial_solve_wit_2 : mpz_clear_partial_solve_wit_2.
Axiom proof_of_mpz_clear_partial_solve_wit_3 : mpz_clear_partial_solve_wit_3.
Axiom proof_of_mpz_clear_which_implies_wit_1 : mpz_clear_which_implies_wit_1.
Axiom proof_of_mpz_realloc_safety_wit_1 : mpz_realloc_safety_wit_1.
Axiom proof_of_mpz_realloc_safety_wit_2 : mpz_realloc_safety_wit_2.
Axiom proof_of_mpz_realloc_safety_wit_3 : mpz_realloc_safety_wit_3.
Axiom proof_of_mpz_realloc_safety_wit_4 : mpz_realloc_safety_wit_4.
Axiom proof_of_mpz_realloc_safety_wit_5 : mpz_realloc_safety_wit_5.
Axiom proof_of_mpz_realloc_safety_wit_6 : mpz_realloc_safety_wit_6.
Axiom proof_of_mpz_realloc_return_wit_1_1 : mpz_realloc_return_wit_1_1.
Axiom proof_of_mpz_realloc_return_wit_1_2 : mpz_realloc_return_wit_1_2.
Axiom proof_of_mpz_realloc_return_wit_1_3 : mpz_realloc_return_wit_1_3.
Axiom proof_of_mpz_realloc_return_wit_1_4 : mpz_realloc_return_wit_1_4.
Axiom proof_of_mpz_realloc_return_wit_1_5 : mpz_realloc_return_wit_1_5.
Axiom proof_of_mpz_realloc_return_wit_1_6 : mpz_realloc_return_wit_1_6.
Axiom proof_of_mpz_realloc_return_wit_1_7 : mpz_realloc_return_wit_1_7.
Axiom proof_of_mpz_realloc_return_wit_1_8 : mpz_realloc_return_wit_1_8.
Axiom proof_of_mpz_realloc_partial_solve_wit_1 : mpz_realloc_partial_solve_wit_1.
Axiom proof_of_mpz_realloc_partial_solve_wit_2 : mpz_realloc_partial_solve_wit_2.
Axiom proof_of_mpz_realloc_partial_solve_wit_3_pure : mpz_realloc_partial_solve_wit_3_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_3 : mpz_realloc_partial_solve_wit_3.
Axiom proof_of_mpz_realloc_partial_solve_wit_4_pure : mpz_realloc_partial_solve_wit_4_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_4 : mpz_realloc_partial_solve_wit_4.
Axiom proof_of_mpz_realloc_partial_solve_wit_5_pure : mpz_realloc_partial_solve_wit_5_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_5 : mpz_realloc_partial_solve_wit_5.
Axiom proof_of_mpz_realloc_partial_solve_wit_6_pure : mpz_realloc_partial_solve_wit_6_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_6 : mpz_realloc_partial_solve_wit_6.
Axiom proof_of_mpz_realloc_partial_solve_wit_7_pure : mpz_realloc_partial_solve_wit_7_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_7 : mpz_realloc_partial_solve_wit_7.
Axiom proof_of_mpz_realloc_partial_solve_wit_8_pure : mpz_realloc_partial_solve_wit_8_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_8 : mpz_realloc_partial_solve_wit_8.
Axiom proof_of_mpz_realloc_partial_solve_wit_9_pure : mpz_realloc_partial_solve_wit_9_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_9 : mpz_realloc_partial_solve_wit_9.
Axiom proof_of_mpz_realloc_partial_solve_wit_10_pure : mpz_realloc_partial_solve_wit_10_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_10 : mpz_realloc_partial_solve_wit_10.
Axiom proof_of_mpz_sgn_safety_wit_1 : mpz_sgn_safety_wit_1.
Axiom proof_of_mpz_sgn_safety_wit_2 : mpz_sgn_safety_wit_2.
Axiom proof_of_mpz_sgn_safety_wit_3 : mpz_sgn_safety_wit_3.
Axiom proof_of_mpz_sgn_safety_wit_4 : mpz_sgn_safety_wit_4.
Axiom proof_of_mpz_sgn_safety_wit_5 : mpz_sgn_safety_wit_5.
Axiom proof_of_mpz_sgn_return_wit_1_1 : mpz_sgn_return_wit_1_1.
Axiom proof_of_mpz_sgn_return_wit_1_2 : mpz_sgn_return_wit_1_2.
Axiom proof_of_mpz_sgn_return_wit_1_3 : mpz_sgn_return_wit_1_3.
Axiom proof_of_mpz_sgn_partial_solve_wit_1 : mpz_sgn_partial_solve_wit_1.
Axiom proof_of_mpz_sgn_partial_solve_wit_2 : mpz_sgn_partial_solve_wit_2.
Axiom proof_of_mpz_sgn_partial_solve_wit_3 : mpz_sgn_partial_solve_wit_3.
Axiom proof_of_mpz_sgn_which_implies_wit_1 : mpz_sgn_which_implies_wit_1.
Axiom proof_of_mpz_swap_return_wit_1_1 : mpz_swap_return_wit_1_1.
Axiom proof_of_mpz_swap_return_wit_1_2 : mpz_swap_return_wit_1_2.
Axiom proof_of_mpz_swap_return_wit_1_3 : mpz_swap_return_wit_1_3.
Axiom proof_of_mpz_swap_return_wit_1_4 : mpz_swap_return_wit_1_4.
Axiom proof_of_mpz_swap_partial_solve_wit_1 : mpz_swap_partial_solve_wit_1.
Axiom proof_of_mpz_swap_partial_solve_wit_2 : mpz_swap_partial_solve_wit_2.
Axiom proof_of_mpz_swap_partial_solve_wit_3 : mpz_swap_partial_solve_wit_3.
Axiom proof_of_mpz_swap_partial_solve_wit_4 : mpz_swap_partial_solve_wit_4.
Axiom proof_of_mpz_swap_partial_solve_wit_5 : mpz_swap_partial_solve_wit_5.
Axiom proof_of_mpz_swap_partial_solve_wit_6 : mpz_swap_partial_solve_wit_6.
Axiom proof_of_mpz_swap_partial_solve_wit_7 : mpz_swap_partial_solve_wit_7.
Axiom proof_of_mpz_swap_partial_solve_wit_8 : mpz_swap_partial_solve_wit_8.
Axiom proof_of_mpz_swap_partial_solve_wit_9 : mpz_swap_partial_solve_wit_9.
Axiom proof_of_mpz_swap_partial_solve_wit_10 : mpz_swap_partial_solve_wit_10.
Axiom proof_of_mpz_swap_partial_solve_wit_11 : mpz_swap_partial_solve_wit_11.
Axiom proof_of_mpz_swap_partial_solve_wit_12 : mpz_swap_partial_solve_wit_12.
Axiom proof_of_mpz_swap_partial_solve_wit_13 : mpz_swap_partial_solve_wit_13.
Axiom proof_of_mpz_swap_partial_solve_wit_14 : mpz_swap_partial_solve_wit_14.
Axiom proof_of_mpz_swap_partial_solve_wit_15 : mpz_swap_partial_solve_wit_15.
Axiom proof_of_mpz_swap_which_implies_wit_1 : mpz_swap_which_implies_wit_1.
Axiom proof_of_mpz_swap_which_implies_wit_2 : mpz_swap_which_implies_wit_2.

End VC_Correct.
