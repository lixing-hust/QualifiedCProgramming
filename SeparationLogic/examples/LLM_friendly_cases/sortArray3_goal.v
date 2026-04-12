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
Require Import SimpleC.EE.LLM_friendly_cases.sortArray_lib.
Local Open Scope sac.
From SimpleC.EE.LLM_friendly_cases Require Import common_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import common_strategy_proof.
From SimpleC.EE.LLM_friendly_cases Require Import int_array_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import int_array_strategy_proof.
From SimpleC.EE.LLM_friendly_cases Require Import uint_array_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import uint_array_strategy_proof.
From SimpleC.EE.LLM_friendly_cases Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.LLM_friendly_cases Require Import array_shape_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import array_shape_strategy_proof.

(*----- Function sortArray -----*)

Definition sortArray_safety_wit_1 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) ,
  [| ((Zlength (l)) = numsSize_pre) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |]
  &&  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sortArray_safety_wit_2 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) ,
  [| (numsSize_pre > 1) |] 
  &&  [| ((Zlength (l)) = numsSize_pre) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sortArray_safety_wit_3 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app (l1) (l2))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l2))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (1 <= (Zlength (l1))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l2 ) |] 
  &&  [| (prefix_suffix_sorted l1 l2 ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  [| ((numsSize_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (numsSize_pre - 1 )) |]
.

Definition sortArray_safety_wit_4 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app (l1) (l2))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l2))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (1 <= (Zlength (l1))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l2 ) |] 
  &&  [| (prefix_suffix_sorted l1 l2 ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sortArray_safety_wit_5 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app (l1) (l2))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l2))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (1 <= (Zlength (l1))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l2 ) |] 
  &&  [| (prefix_suffix_sorted l1 l2 ) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sortArray_safety_wit_6 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  [| ((numsSize_pre - i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (numsSize_pre - i )) |]
.

Definition sortArray_safety_wit_7 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition sortArray_safety_wit_8 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sortArray_safety_wit_9 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition sortArray_safety_wit_10 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sortArray_safety_wit_11 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j l3 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition sortArray_safety_wit_12 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j l3 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sortArray_safety_wit_13 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (IntArray.full nums_pre numsSize_pre (replace_Znth (j) ((Znth (j + 1 ) l3 0)) (l3)) )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j l3 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition sortArray_safety_wit_14 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (IntArray.full nums_pre numsSize_pre (replace_Znth (j) ((Znth (j + 1 ) l3 0)) (l3)) )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j l3 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sortArray_safety_wit_15 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| ((Znth j l3 0) <= (Znth (j + 1 ) l3 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition sortArray_safety_wit_16 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (IntArray.full nums_pre numsSize_pre (replace_Znth ((j + 1 )) ((Znth j l3 0)) ((replace_Znth (j) ((Znth (j + 1 ) l3 0)) (l3)))) )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition sortArray_safety_wit_17 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| ((j + 1 ) >= (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition sortArray_entail_wit_1 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) ,
  [| (numsSize_pre > 1) |] 
  &&  [| ((Zlength (l)) = numsSize_pre) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |]
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app (l1) (l2))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (0 = (Zlength (l2))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 < numsSize_pre) |] 
  &&  [| (1 <= (Zlength (l1))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l2 ) |] 
  &&  [| (prefix_suffix_sorted l1 l2 ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
.

Definition sortArray_entail_wit_2 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) ,
  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3_2 = (app (l1_2) (l2_2))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l2_2))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (1 <= (Zlength (l1_2))) |] 
  &&  [| (Permutation l l3_2 ) |] 
  &&  [| (increasing l2_2 ) |] 
  &&  [| (prefix_suffix_sorted l1_2 l2_2 ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3_2 )
|--
  EX (l1: (@list Z))  (key: Z)  (l2: (@list Z))  (l4: (@list Z))  (l3: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (0 = (Zlength (l1))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| ((0 + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
.

Definition sortArray_entail_wit_3_1 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1_2: (@list Z)) (key_2: Z) (l2_2: (@list Z)) (l4_2: (@list Z)) (l3_2: (@list Z)) ,
  [| ((Znth j l3_2 0) > (Znth (j + 1 ) l3_2 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3_2 = (app ((app (l1_2) ((cons (key_2) (l2_2))))) (l4_2))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4_2))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1_2))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1_2) ((cons (key_2) (l2_2))))))) |] 
  &&  [| (Permutation l l3_2 ) |] 
  &&  [| (increasing l4_2 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1_2) ((cons (key_2) (l2_2)))) l4_2 ) |] 
  &&  [| (prefix_suffix_sorted l1_2 (cons (key_2) (nil)) ) |]
  &&  (IntArray.full nums_pre numsSize_pre (replace_Znth ((j + 1 )) ((Znth j l3_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) l3_2 0)) (l3_2)))) )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  EX (l1: (@list Z))  (key: Z)  (l2: (@list Z))  (l4: (@list Z))  (l3: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| ((j + 1 ) = (Zlength (l1))) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| (((j + 1 ) + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
.

Definition sortArray_entail_wit_3_2 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1_2: (@list Z)) (key_2: Z) (l2_2: (@list Z)) (l4_2: (@list Z)) (l3_2: (@list Z)) ,
  [| ((Znth j l3_2 0) <= (Znth (j + 1 ) l3_2 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3_2 = (app ((app (l1_2) ((cons (key_2) (l2_2))))) (l4_2))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4_2))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1_2))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1_2) ((cons (key_2) (l2_2))))))) |] 
  &&  [| (Permutation l l3_2 ) |] 
  &&  [| (increasing l4_2 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1_2) ((cons (key_2) (l2_2)))) l4_2 ) |] 
  &&  [| (prefix_suffix_sorted l1_2 (cons (key_2) (nil)) ) |]
  &&  (IntArray.full nums_pre numsSize_pre l3_2 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  EX (l1: (@list Z))  (key: Z)  (l2: (@list Z))  (l4: (@list Z))  (l3: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| ((j + 1 ) = (Zlength (l1))) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| (((j + 1 ) + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
.

Definition sortArray_entail_wit_4 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1_2: (@list Z)) (key: Z) (l2_2: (@list Z)) (l4: (@list Z)) (l3_2: (@list Z)) ,
  [| ((j + 1 ) >= (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3_2 = (app ((app (l1_2) ((cons (key) (l2_2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1_2))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1_2) ((cons (key) (l2_2))))))) |] 
  &&  [| (Permutation l l3_2 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1_2) ((cons (key) (l2_2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1_2 (cons (key) (nil)) ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app (l1) (l2))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| ((i + 1 ) = (Zlength (l2))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) < numsSize_pre) |] 
  &&  [| (1 <= (Zlength (l1))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l2 ) |] 
  &&  [| (prefix_suffix_sorted l1 l2 ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
.

Definition sortArray_return_wit_1 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) ,
  [| (numsSize_pre <= 1) |] 
  &&  [| ((Zlength (l)) = numsSize_pre) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |]
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  EX (l1: (@list Z)) ,
  [| (Permutation l l1 ) |] 
  &&  [| (increasing l1 ) |] 
  &&  [| ((Zlength (l1)) = numsSize_pre) |]
  &&  (IntArray.full nums_pre numsSize_pre l1 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_return_wit_2 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) ,
  [| (i >= (numsSize_pre - 1 )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app (l1_2) (l2))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l2))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (1 <= (Zlength (l1_2))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l2 ) |] 
  &&  [| (prefix_suffix_sorted l1_2 l2 ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  EX (l1: (@list Z)) ,
  [| (Permutation l l1 ) |] 
  &&  [| (increasing l1 ) |] 
  &&  [| ((Zlength (l1)) = numsSize_pre) |]
  &&  (IntArray.full nums_pre numsSize_pre l1 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_1 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (((nums_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j l3 0))
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_2 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j + 1 ) l3 0))
  **  (IntArray.missing_i nums_pre (j + 1 ) 0 numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_3 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (((nums_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j l3 0))
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_4 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (j + 1 ) l3 0))
  **  (IntArray.missing_i nums_pre (j + 1 ) 0 numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_5 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (((nums_pre + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_6 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) ,
  [| ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (IntArray.full nums_pre numsSize_pre (replace_Znth (j) ((Znth (j + 1 ) l3 0)) (l3)) )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) |] 
  &&  [| ((j + 1 ) < (numsSize_pre - i )) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) |] 
  &&  [| (numsSize_pre = (Zlength (l))) |] 
  &&  [| (i = (Zlength (l4))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < numsSize_pre) |] 
  &&  [| (i < (numsSize_pre - 1 )) |] 
  &&  [| (j = (Zlength (l1))) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((j + 1 ) <= (numsSize_pre - i )) |] 
  &&  [| ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) |] 
  &&  [| (Permutation l l3 ) |] 
  &&  [| (increasing l4 ) |] 
  &&  [| (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) |] 
  &&  [| (prefix_suffix_sorted l1 (cons (key) (nil)) ) |]
  &&  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) 0 numsSize_pre (replace_Znth (j) ((Znth (j + 1 ) l3 0)) (l3)) )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_sortArray_safety_wit_1 : sortArray_safety_wit_1.
Axiom proof_of_sortArray_safety_wit_2 : sortArray_safety_wit_2.
Axiom proof_of_sortArray_safety_wit_3 : sortArray_safety_wit_3.
Axiom proof_of_sortArray_safety_wit_4 : sortArray_safety_wit_4.
Axiom proof_of_sortArray_safety_wit_5 : sortArray_safety_wit_5.
Axiom proof_of_sortArray_safety_wit_6 : sortArray_safety_wit_6.
Axiom proof_of_sortArray_safety_wit_7 : sortArray_safety_wit_7.
Axiom proof_of_sortArray_safety_wit_8 : sortArray_safety_wit_8.
Axiom proof_of_sortArray_safety_wit_9 : sortArray_safety_wit_9.
Axiom proof_of_sortArray_safety_wit_10 : sortArray_safety_wit_10.
Axiom proof_of_sortArray_safety_wit_11 : sortArray_safety_wit_11.
Axiom proof_of_sortArray_safety_wit_12 : sortArray_safety_wit_12.
Axiom proof_of_sortArray_safety_wit_13 : sortArray_safety_wit_13.
Axiom proof_of_sortArray_safety_wit_14 : sortArray_safety_wit_14.
Axiom proof_of_sortArray_safety_wit_15 : sortArray_safety_wit_15.
Axiom proof_of_sortArray_safety_wit_16 : sortArray_safety_wit_16.
Axiom proof_of_sortArray_safety_wit_17 : sortArray_safety_wit_17.
Axiom proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1.
Axiom proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2.
Axiom proof_of_sortArray_entail_wit_3_1 : sortArray_entail_wit_3_1.
Axiom proof_of_sortArray_entail_wit_3_2 : sortArray_entail_wit_3_2.
Axiom proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4.
Axiom proof_of_sortArray_return_wit_1 : sortArray_return_wit_1.
Axiom proof_of_sortArray_return_wit_2 : sortArray_return_wit_2.
Axiom proof_of_sortArray_partial_solve_wit_1 : sortArray_partial_solve_wit_1.
Axiom proof_of_sortArray_partial_solve_wit_2 : sortArray_partial_solve_wit_2.
Axiom proof_of_sortArray_partial_solve_wit_3 : sortArray_partial_solve_wit_3.
Axiom proof_of_sortArray_partial_solve_wit_4 : sortArray_partial_solve_wit_4.
Axiom proof_of_sortArray_partial_solve_wit_5 : sortArray_partial_solve_wit_5.
Axiom proof_of_sortArray_partial_solve_wit_6 : sortArray_partial_solve_wit_6.

End VC_Correct.
