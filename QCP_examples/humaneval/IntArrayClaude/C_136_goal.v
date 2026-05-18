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
Require Import coins_136.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function largest_smallest_integers -----*)

Definition largest_smallest_integers_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |]
  &&  ((( &( "minpos" ) )) # Int  |->_)
  **  ((( &( "maxneg" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition largest_smallest_integers_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |]
  &&  ((( &( "maxneg" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition largest_smallest_integers_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "minpos" ) )) # Int  |-> 0)
  **  ((( &( "maxneg" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition largest_smallest_integers_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition largest_smallest_integers_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition largest_smallest_integers_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= maxneg) |] 
  &&  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition largest_smallest_integers_safety_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition largest_smallest_integers_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) > maxneg) |] 
  &&  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> (Znth i input_l 0))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition largest_smallest_integers_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| (maxneg = 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> (Znth i input_l 0))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition largest_smallest_integers_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) > 0) |] 
  &&  [| ((Znth i input_l 0) <= maxneg) |] 
  &&  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
|--
  [| False |]
.

Definition largest_smallest_integers_safety_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) > 0) |] 
  &&  [| ((Znth i input_l 0) > maxneg) |] 
  &&  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> (Znth i input_l 0))
|--
  [| False |]
.

Definition largest_smallest_integers_safety_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) > 0) |] 
  &&  [| (maxneg = 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> (Znth i input_l 0))
|--
  [| False |]
.

Definition largest_smallest_integers_safety_wit_13 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) > 0) |] 
  &&  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition largest_smallest_integers_safety_wit_14 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) >= minpos) |] 
  &&  [| (minpos <> 0) |] 
  &&  [| ((Znth i input_l 0) > 0) |] 
  &&  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition largest_smallest_integers_safety_wit_15 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= 0) |] 
  &&  [| ((Znth i input_l 0) <= maxneg) |] 
  &&  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition largest_smallest_integers_safety_wit_16 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= 0) |] 
  &&  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition largest_smallest_integers_safety_wit_17 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= 0) |] 
  &&  [| ((Znth i input_l 0) > maxneg) |] 
  &&  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> (Znth i input_l 0))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition largest_smallest_integers_safety_wit_18 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= 0) |] 
  &&  [| (maxneg = 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> (Znth i input_l 0))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition largest_smallest_integers_safety_wit_19 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) < minpos) |] 
  &&  [| (minpos <> 0) |] 
  &&  [| ((Znth i input_l 0) > 0) |] 
  &&  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition largest_smallest_integers_safety_wit_20 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| (minpos = 0) |] 
  &&  [| ((Znth i input_l 0) > 0) |] 
  &&  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition largest_smallest_integers_safety_wit_21 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition largest_smallest_integers_safety_wit_22 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition largest_smallest_integers_safety_wit_23 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition largest_smallest_integers_safety_wit_24 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> maxneg)
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition largest_smallest_integers_entail_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix 0 input_l 0 0 ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition largest_smallest_integers_entail_wit_2_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| (minpos = 0) |] 
  &&  [| ((Znth i input_l 0) > 0) |] 
  &&  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix (i + 1 ) input_l maxneg (Znth i input_l 0) ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition largest_smallest_integers_entail_wit_2_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) < minpos) |] 
  &&  [| (minpos <> 0) |] 
  &&  [| ((Znth i input_l 0) > 0) |] 
  &&  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix (i + 1 ) input_l maxneg (Znth i input_l 0) ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition largest_smallest_integers_entail_wit_2_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= 0) |] 
  &&  [| (maxneg = 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix (i + 1 ) input_l (Znth i input_l 0) minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition largest_smallest_integers_entail_wit_2_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= 0) |] 
  &&  [| ((Znth i input_l 0) > maxneg) |] 
  &&  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix (i + 1 ) input_l (Znth i input_l 0) minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition largest_smallest_integers_entail_wit_2_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= 0) |] 
  &&  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix (i + 1 ) input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition largest_smallest_integers_entail_wit_2_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= 0) |] 
  &&  [| ((Znth i input_l 0) <= maxneg) |] 
  &&  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix (i + 1 ) input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition largest_smallest_integers_entail_wit_2_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) >= minpos) |] 
  &&  [| (minpos <> 0) |] 
  &&  [| ((Znth i input_l 0) > 0) |] 
  &&  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix (i + 1 ) input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition largest_smallest_integers_return_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |-> minpos)
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> maxneg)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  [| (retval <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (problem_136_spec_z input_l output_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full lst_pre lst_size_pre input_l )
  **  (IntArray.full data output_size output_l )
.

Definition largest_smallest_integers_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition largest_smallest_integers_partial_solve_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition largest_smallest_integers_partial_solve_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| (maxneg = 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (maxneg = 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition largest_smallest_integers_partial_solve_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) > maxneg) |] 
  &&  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| ((Znth i input_l 0) > maxneg) |] 
  &&  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition largest_smallest_integers_partial_solve_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= maxneg) |] 
  &&  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| ((Znth i input_l 0) <= maxneg) |] 
  &&  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition largest_smallest_integers_partial_solve_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition largest_smallest_integers_partial_solve_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) > maxneg) |] 
  &&  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| ((Znth i input_l 0) > maxneg) |] 
  &&  [| (maxneg <> 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition largest_smallest_integers_partial_solve_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| (maxneg = 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (maxneg = 0) |] 
  &&  [| ((Znth i input_l 0) < 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition largest_smallest_integers_partial_solve_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| (minpos <> 0) |] 
  &&  [| ((Znth i input_l 0) > 0) |] 
  &&  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (minpos <> 0) |] 
  &&  [| ((Znth i input_l 0) > 0) |] 
  &&  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition largest_smallest_integers_partial_solve_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| (minpos = 0) |] 
  &&  [| ((Znth i input_l 0) > 0) |] 
  &&  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (minpos = 0) |] 
  &&  [| ((Znth i input_l 0) > 0) |] 
  &&  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition largest_smallest_integers_partial_solve_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| ((Znth i input_l 0) < minpos) |] 
  &&  [| (minpos <> 0) |] 
  &&  [| ((Znth i input_l 0) > 0) |] 
  &&  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| ((Znth i input_l 0) < minpos) |] 
  &&  [| (minpos <> 0) |] 
  &&  [| ((Znth i input_l 0) > 0) |] 
  &&  [| ((Znth i input_l 0) >= 0) |] 
  &&  [| (i < lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition largest_smallest_integers_partial_solve_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) ,
  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition largest_smallest_integers_partial_solve_wit_13_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "minpos" ) )) # Int  |-> minpos)
  **  ((( &( "maxneg" ) )) # Int  |-> maxneg)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (2 >= 0) |] 
  &&  [| (2 < INT_MAX) |]
.

Definition largest_smallest_integers_partial_solve_wit_13_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (2 >= 0) |] 
  &&  [| (2 < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition largest_smallest_integers_partial_solve_wit_13 := largest_smallest_integers_partial_solve_wit_13_pure -> largest_smallest_integers_partial_solve_wit_13_aux.

Definition largest_smallest_integers_partial_solve_wit_14 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition largest_smallest_integers_partial_solve_wit_15 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (maxneg: Z) (minpos: Z) (i: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> maxneg)
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (i >= lst_size_pre) |] 
  &&  [| (0 <= lst_size_pre) |] 
  &&  [| (lst_size_pre < INT_MAX) |] 
  &&  [| (lst_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_136_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst_size_pre) |] 
  &&  [| (largest_smallest_prefix i input_l maxneg minpos ) |]
  &&  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> maxneg)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full lst_pre lst_size_pre input_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_largest_smallest_integers_safety_wit_1 : largest_smallest_integers_safety_wit_1.
Axiom proof_of_largest_smallest_integers_safety_wit_2 : largest_smallest_integers_safety_wit_2.
Axiom proof_of_largest_smallest_integers_safety_wit_3 : largest_smallest_integers_safety_wit_3.
Axiom proof_of_largest_smallest_integers_safety_wit_4 : largest_smallest_integers_safety_wit_4.
Axiom proof_of_largest_smallest_integers_safety_wit_5 : largest_smallest_integers_safety_wit_5.
Axiom proof_of_largest_smallest_integers_safety_wit_6 : largest_smallest_integers_safety_wit_6.
Axiom proof_of_largest_smallest_integers_safety_wit_7 : largest_smallest_integers_safety_wit_7.
Axiom proof_of_largest_smallest_integers_safety_wit_8 : largest_smallest_integers_safety_wit_8.
Axiom proof_of_largest_smallest_integers_safety_wit_9 : largest_smallest_integers_safety_wit_9.
Axiom proof_of_largest_smallest_integers_safety_wit_10 : largest_smallest_integers_safety_wit_10.
Axiom proof_of_largest_smallest_integers_safety_wit_11 : largest_smallest_integers_safety_wit_11.
Axiom proof_of_largest_smallest_integers_safety_wit_12 : largest_smallest_integers_safety_wit_12.
Axiom proof_of_largest_smallest_integers_safety_wit_13 : largest_smallest_integers_safety_wit_13.
Axiom proof_of_largest_smallest_integers_safety_wit_14 : largest_smallest_integers_safety_wit_14.
Axiom proof_of_largest_smallest_integers_safety_wit_15 : largest_smallest_integers_safety_wit_15.
Axiom proof_of_largest_smallest_integers_safety_wit_16 : largest_smallest_integers_safety_wit_16.
Axiom proof_of_largest_smallest_integers_safety_wit_17 : largest_smallest_integers_safety_wit_17.
Axiom proof_of_largest_smallest_integers_safety_wit_18 : largest_smallest_integers_safety_wit_18.
Axiom proof_of_largest_smallest_integers_safety_wit_19 : largest_smallest_integers_safety_wit_19.
Axiom proof_of_largest_smallest_integers_safety_wit_20 : largest_smallest_integers_safety_wit_20.
Axiom proof_of_largest_smallest_integers_safety_wit_21 : largest_smallest_integers_safety_wit_21.
Axiom proof_of_largest_smallest_integers_safety_wit_22 : largest_smallest_integers_safety_wit_22.
Axiom proof_of_largest_smallest_integers_safety_wit_23 : largest_smallest_integers_safety_wit_23.
Axiom proof_of_largest_smallest_integers_safety_wit_24 : largest_smallest_integers_safety_wit_24.
Axiom proof_of_largest_smallest_integers_entail_wit_1 : largest_smallest_integers_entail_wit_1.
Axiom proof_of_largest_smallest_integers_entail_wit_2_1 : largest_smallest_integers_entail_wit_2_1.
Axiom proof_of_largest_smallest_integers_entail_wit_2_2 : largest_smallest_integers_entail_wit_2_2.
Axiom proof_of_largest_smallest_integers_entail_wit_2_3 : largest_smallest_integers_entail_wit_2_3.
Axiom proof_of_largest_smallest_integers_entail_wit_2_4 : largest_smallest_integers_entail_wit_2_4.
Axiom proof_of_largest_smallest_integers_entail_wit_2_5 : largest_smallest_integers_entail_wit_2_5.
Axiom proof_of_largest_smallest_integers_entail_wit_2_6 : largest_smallest_integers_entail_wit_2_6.
Axiom proof_of_largest_smallest_integers_entail_wit_2_7 : largest_smallest_integers_entail_wit_2_7.
Axiom proof_of_largest_smallest_integers_return_wit_1 : largest_smallest_integers_return_wit_1.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_1 : largest_smallest_integers_partial_solve_wit_1.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_2 : largest_smallest_integers_partial_solve_wit_2.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_3 : largest_smallest_integers_partial_solve_wit_3.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_4 : largest_smallest_integers_partial_solve_wit_4.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_5 : largest_smallest_integers_partial_solve_wit_5.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_6 : largest_smallest_integers_partial_solve_wit_6.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_7 : largest_smallest_integers_partial_solve_wit_7.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_8 : largest_smallest_integers_partial_solve_wit_8.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_9 : largest_smallest_integers_partial_solve_wit_9.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_10 : largest_smallest_integers_partial_solve_wit_10.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_11 : largest_smallest_integers_partial_solve_wit_11.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_12 : largest_smallest_integers_partial_solve_wit_12.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_13_pure : largest_smallest_integers_partial_solve_wit_13_pure.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_13 : largest_smallest_integers_partial_solve_wit_13.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_14 : largest_smallest_integers_partial_solve_wit_14.
Axiom proof_of_largest_smallest_integers_partial_solve_wit_15 : largest_smallest_integers_partial_solve_wit_15.

End VC_Correct.
