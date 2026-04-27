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
Require Import coins_126.
Local Open Scope sac.
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.

(*----- Function is_sorted -----*)

Definition is_sorted_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) ,
  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_sorted_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i - 1 )) |]
.

Definition is_sorted_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_sorted_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| ((Znth i lv 0) < (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_sorted_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_sorted_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i - 1 )) |]
.

Definition is_sorted_safety_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_sorted_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| ((Znth i lv 0) = (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i - 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i - 2 )) |]
.

Definition is_sorted_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| ((Znth i lv 0) = (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_sorted_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| ((Znth i lv 0) = (Znth (i - 2 ) lv 0)) |] 
  &&  [| ((Znth i lv 0) = (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_sorted_safety_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| ((Znth i lv 0) <> (Znth (i - 2 ) lv 0)) |] 
  &&  [| ((Znth i lv 0) = (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_sorted_safety_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| (i < 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_sorted_safety_wit_13 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| ((Znth i lv 0) <> (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_sorted_safety_wit_14 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_sorted_entail_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) ,
  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix 1 lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition is_sorted_entail_wit_2_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| ((Znth i lv 0) <> (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix (i + 1 ) lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition is_sorted_entail_wit_2_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| (i < 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix (i + 1 ) lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition is_sorted_entail_wit_2_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| ((Znth i lv 0) <> (Znth (i - 2 ) lv 0)) |] 
  &&  [| ((Znth i lv 0) = (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix (i + 1 ) lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition is_sorted_return_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  ([| (1 = 0) |] 
  &&  [| (problem_126_spec_z lv false ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv ))
  ||
  ([| (1 <> 0) |] 
  &&  [| (problem_126_spec_z lv true ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv ))
.

Definition is_sorted_return_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| ((Znth i lv 0) = (Znth (i - 2 ) lv 0)) |] 
  &&  [| ((Znth i lv 0) = (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  ([| (0 = 0) |] 
  &&  [| (problem_126_spec_z lv false ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv ))
  ||
  ([| (0 <> 0) |] 
  &&  [| (problem_126_spec_z lv true ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv ))
.

Definition is_sorted_return_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| ((Znth i lv 0) < (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  ([| (0 = 0) |] 
  &&  [| (problem_126_spec_z lv false ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv ))
  ||
  ([| (0 <> 0) |] 
  &&  [| (problem_126_spec_z lv true ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv ))
.

Definition is_sorted_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre lv )
.

Definition is_sorted_partial_solve_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (((lst_pre + ((i - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (i - 1 ) lv 0))
  **  (IntArray.missing_i lst_pre (i - 1 ) 0 lst_size_pre lv )
.

Definition is_sorted_partial_solve_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre lv )
.

Definition is_sorted_partial_solve_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (((lst_pre + ((i - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (i - 1 ) lv 0))
  **  (IntArray.missing_i lst_pre (i - 1 ) 0 lst_size_pre lv )
.

Definition is_sorted_partial_solve_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| ((Znth i lv 0) = (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((Znth i lv 0) = (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre lv )
.

Definition is_sorted_partial_solve_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (i: Z) ,
  [| ((Znth i lv 0) = (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  [| ((Znth i lv 0) = (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i >= 2) |] 
  &&  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (1 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_126_pre_z lv ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (sorted_no_triple_prefix i lv ) |]
  &&  (((lst_pre + ((i - 2 ) * sizeof(INT) ) )) # Int  |-> (Znth (i - 2 ) lv 0))
  **  (IntArray.missing_i lst_pre (i - 2 ) 0 lst_size_pre lv )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_is_sorted_safety_wit_1 : is_sorted_safety_wit_1.
Axiom proof_of_is_sorted_safety_wit_2 : is_sorted_safety_wit_2.
Axiom proof_of_is_sorted_safety_wit_3 : is_sorted_safety_wit_3.
Axiom proof_of_is_sorted_safety_wit_4 : is_sorted_safety_wit_4.
Axiom proof_of_is_sorted_safety_wit_5 : is_sorted_safety_wit_5.
Axiom proof_of_is_sorted_safety_wit_6 : is_sorted_safety_wit_6.
Axiom proof_of_is_sorted_safety_wit_7 : is_sorted_safety_wit_7.
Axiom proof_of_is_sorted_safety_wit_8 : is_sorted_safety_wit_8.
Axiom proof_of_is_sorted_safety_wit_9 : is_sorted_safety_wit_9.
Axiom proof_of_is_sorted_safety_wit_10 : is_sorted_safety_wit_10.
Axiom proof_of_is_sorted_safety_wit_11 : is_sorted_safety_wit_11.
Axiom proof_of_is_sorted_safety_wit_12 : is_sorted_safety_wit_12.
Axiom proof_of_is_sorted_safety_wit_13 : is_sorted_safety_wit_13.
Axiom proof_of_is_sorted_safety_wit_14 : is_sorted_safety_wit_14.
Axiom proof_of_is_sorted_entail_wit_1 : is_sorted_entail_wit_1.
Axiom proof_of_is_sorted_entail_wit_2_1 : is_sorted_entail_wit_2_1.
Axiom proof_of_is_sorted_entail_wit_2_2 : is_sorted_entail_wit_2_2.
Axiom proof_of_is_sorted_entail_wit_2_3 : is_sorted_entail_wit_2_3.
Axiom proof_of_is_sorted_return_wit_1 : is_sorted_return_wit_1.
Axiom proof_of_is_sorted_return_wit_2 : is_sorted_return_wit_2.
Axiom proof_of_is_sorted_return_wit_3 : is_sorted_return_wit_3.
Axiom proof_of_is_sorted_partial_solve_wit_1 : is_sorted_partial_solve_wit_1.
Axiom proof_of_is_sorted_partial_solve_wit_2 : is_sorted_partial_solve_wit_2.
Axiom proof_of_is_sorted_partial_solve_wit_3 : is_sorted_partial_solve_wit_3.
Axiom proof_of_is_sorted_partial_solve_wit_4 : is_sorted_partial_solve_wit_4.
Axiom proof_of_is_sorted_partial_solve_wit_5 : is_sorted_partial_solve_wit_5.
Axiom proof_of_is_sorted_partial_solve_wit_6 : is_sorted_partial_solve_wit_6.

End VC_Correct.
