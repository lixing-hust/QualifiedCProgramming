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
Require Import SimpleC.EE.QCP_democases.sortArray_lib.
Local Open Scope sac.

(*----- Function sortArray -----*)

Definition sortArray_safety_wit_1 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) ,
  [| ((Zlength (l)) = numsSize_pre) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sortArray_safety_wit_2 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (i < numsSize_pre) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.seg nums_pre i numsSize_pre l2 )
  **  ((( &( "key" ) )) # Int  |-> (Znth (i - i ) l2 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 i l0 )
|--
  [| ((i - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i - 1 )) |]
.

Definition sortArray_safety_wit_3 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (i < numsSize_pre) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.seg nums_pre i numsSize_pre l2 )
  **  ((( &( "key" ) )) # Int  |-> (Znth (i - i ) l2 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 i l0 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sortArray_safety_wit_4 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2) (l3))) |] 
  &&  [| ((j + 1 ) = (Zlength (l2))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (strict_upperbound key l3 ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sortArray_safety_wit_5 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (l0: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (l5: (@list Z)) (j: Z) (i: Z) (key: Z) ,
  [| (l2 = (app (l5) ((cons ((Znth j l2 0)) (nil))))) |] 
  &&  [| (j = (Zlength (l5))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2) (l3))) |] 
  &&  [| (strict_upperbound key l3 ) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((Znth j l2 0) > key) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 j l5 )
  **  (((nums_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j l2 0))
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition sortArray_safety_wit_6 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (l0: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (l5: (@list Z)) (j: Z) (i: Z) (key: Z) ,
  [| (l2 = (app (l5) ((cons ((Znth j l2 0)) (nil))))) |] 
  &&  [| (j = (Zlength (l5))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2) (l3))) |] 
  &&  [| (strict_upperbound key l3 ) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((Znth j l2 0) > key) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 j l5 )
  **  (((nums_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j l2 0))
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sortArray_safety_wit_7 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (l0: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (l5: (@list Z)) (j: Z) (i: Z) (key: Z) ,
  [| (l2 = (app (l5) ((cons ((Znth j l2 0)) (nil))))) |] 
  &&  [| (j = (Zlength (l5))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2) (l3))) |] 
  &&  [| (strict_upperbound key l3 ) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((Znth j l2 0) > key) |]
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 j l5 )
  **  (((nums_pre + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre j j (i + 1 ) (cons (key) ((cons ((Znth j l2 0)) (l3)))) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  [| ((j - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j - 1 )) |]
.

Definition sortArray_safety_wit_8 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) ,
  [| (j < 0) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2) (l3))) |] 
  &&  [| ((j + 1 ) = (Zlength (l2))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (strict_upperbound key l3 ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition sortArray_safety_wit_9 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) ,
  [| ((Znth (j - 0 ) l2 0) <= key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2) (l3))) |] 
  &&  [| ((j + 1 ) = (Zlength (l2))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (strict_upperbound key l3 ) |]
  &&  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition sortArray_safety_wit_10 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) ,
  [| ((Znth (j - 0 ) l2 0) <= key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2) (l3))) |] 
  &&  [| ((j + 1 ) = (Zlength (l2))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (strict_upperbound key l3 ) |]
  &&  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sortArray_safety_wit_11 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) ,
  [| (j < 0) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2) (l3))) |] 
  &&  [| ((j + 1 ) = (Zlength (l2))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (strict_upperbound key l3 ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sortArray_safety_wit_12 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) ,
  [| (j < 0) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2) (l3))) |] 
  &&  [| ((j + 1 ) = (Zlength (l2))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (strict_upperbound key l3 ) |]
  &&  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |-> key)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition sortArray_safety_wit_13 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) ,
  [| ((Znth (j - 0 ) l2 0) <= key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2) (l3))) |] 
  &&  [| ((j + 1 ) = (Zlength (l2))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (strict_upperbound key l3 ) |]
  &&  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |-> key)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition sortArray_entail_wit_1 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) ,
  [| ((Zlength (l)) = numsSize_pre) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |]
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  EX (l0: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (1 = (Zlength (l1))) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 1 l0 )
  **  (IntArray.seg nums_pre 1 numsSize_pre l2 )
.

Definition sortArray_entail_wit_2 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l0_2: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2: (@list Z)) ,
  [| (i < numsSize_pre) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1_2) (l2))) |] 
  &&  [| (i = (Zlength (l1_2))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1_2 l0_2 ) |] 
  &&  [| (increasing l0_2 ) |]
  &&  (IntArray.seg nums_pre i numsSize_pre l2 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 i l0_2 )
|--
  EX (l2_2: (@list Z))  (l3: (@list Z))  (l0: (@list Z))  (l1: (@list Z))  (l4: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons ((Znth (i - i ) l2 0)) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2_2) (l3))) |] 
  &&  [| (((i - 1 ) + 1 ) = (Zlength (l2_2))) |] 
  &&  [| (((i - 1 ) + 1 ) <= i) |] 
  &&  [| (strict_upperbound (Znth (i - i ) l2 0) l3 ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 ((i - 1 ) + 1 ) l2_2 )
  **  (((nums_pre + (((i - 1 ) + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre ((i - 1 ) + 1 ) ((i - 1 ) + 1 ) (i + 1 ) (cons ((Znth (i - i ) l2 0)) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
.

Definition sortArray_entail_wit_3 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2_2: (@list Z)) (l3_2: (@list Z)) (l0_2: (@list Z)) (i: Z) (l1_2: (@list Z)) (key: Z) (l4_2: (@list Z)) ,
  [| ((Znth (j - 0 ) l2_2 0) > key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1_2) ((cons (key) (l4_2))))) |] 
  &&  [| (i = (Zlength (l1_2))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1_2 l0_2 ) |] 
  &&  [| (increasing l0_2 ) |] 
  &&  [| (l0_2 = (app (l2_2) (l3_2))) |] 
  &&  [| ((j + 1 ) = (Zlength (l2_2))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (strict_upperbound key l3_2 ) |]
  &&  (IntArray.seg nums_pre 0 (j + 1 ) l2_2 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3_2)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4_2 )
|--
  EX (l3: (@list Z))  (l0: (@list Z))  (l1: (@list Z))  (l4: (@list Z))  (l5: (@list Z))  (l2: (@list Z)) ,
  [| (l2 = (app (l5) ((cons ((Znth j l2 0)) (nil))))) |] 
  &&  [| (j = (Zlength (l5))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2) (l3))) |] 
  &&  [| (strict_upperbound key l3 ) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((Znth j l2 0) > key) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 j l5 )
  **  (((nums_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j l2 0))
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
.

Definition sortArray_entail_wit_4 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l0_2: (@list Z)) (l3_2: (@list Z)) (l4_2: (@list Z)) (l5_2: (@list Z)) (j: Z) (i: Z) (key: Z) ,
  [| (l2_2 = (app (l5_2) ((cons ((Znth j l2_2 0)) (nil))))) |] 
  &&  [| (j = (Zlength (l5_2))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1_2) ((cons (key) (l4_2))))) |] 
  &&  [| (i = (Zlength (l1_2))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1_2 l0_2 ) |] 
  &&  [| (increasing l0_2 ) |] 
  &&  [| (l0_2 = (app (l2_2) (l3_2))) |] 
  &&  [| (strict_upperbound key l3_2 ) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((Znth j l2_2 0) > key) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 j l5_2 )
  **  (((nums_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth j l2_2 0))
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth j l2_2 0))
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3_2)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4_2 )
|--
  EX (l3: (@list Z))  (l0: (@list Z))  (l1: (@list Z))  (l4: (@list Z))  (l5: (@list Z))  (l2: (@list Z)) ,
  [| (l2 = (app (l5) ((cons ((Znth j l2 0)) (nil))))) |] 
  &&  [| (j = (Zlength (l5))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2) (l3))) |] 
  &&  [| (strict_upperbound key l3 ) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((Znth j l2 0) > key) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 j l5 )
  **  (((nums_pre + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre j j (i + 1 ) (cons (key) ((cons ((Znth j l2 0)) (l3)))) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
.

Definition sortArray_entail_wit_5 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l0_2: (@list Z)) (l3_2: (@list Z)) (l4_2: (@list Z)) (l5: (@list Z)) (j: Z) (i: Z) (key: Z) ,
  [| (l2_2 = (app (l5) ((cons ((Znth j l2_2 0)) (nil))))) |] 
  &&  [| (j = (Zlength (l5))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1_2) ((cons (key) (l4_2))))) |] 
  &&  [| (i = (Zlength (l1_2))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1_2 l0_2 ) |] 
  &&  [| (increasing l0_2 ) |] 
  &&  [| (l0_2 = (app (l2_2) (l3_2))) |] 
  &&  [| (strict_upperbound key l3_2 ) |] 
  &&  [| (0 <= j) |] 
  &&  [| ((Znth j l2_2 0) > key) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 j l5 )
  **  (((nums_pre + (j * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre j j (i + 1 ) (cons (key) ((cons ((Znth j l2_2 0)) (l3_2)))) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4_2 )
|--
  EX (l2: (@list Z))  (l3: (@list Z))  (l0: (@list Z))  (l1: (@list Z))  (l4: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2) (l3))) |] 
  &&  [| (((j - 1 ) + 1 ) = (Zlength (l2))) |] 
  &&  [| (((j - 1 ) + 1 ) <= i) |] 
  &&  [| (strict_upperbound key l3 ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 ((j - 1 ) + 1 ) l2 )
  **  (((nums_pre + (((j - 1 ) + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre ((j - 1 ) + 1 ) ((j - 1 ) + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
.

Definition sortArray_entail_wit_6_1 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2_2: (@list Z)) (l3: (@list Z)) (l0_2: (@list Z)) (i: Z) (l1_2: (@list Z)) (key: Z) (l4: (@list Z)) ,
  [| ((Znth (j - 0 ) l2_2 0) <= key) |] 
  &&  [| (j >= 0) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1_2) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1_2))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1_2 l0_2 ) |] 
  &&  [| (increasing l0_2 ) |] 
  &&  [| (l0_2 = (app (l2_2) (l3))) |] 
  &&  [| ((j + 1 ) = (Zlength (l2_2))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (strict_upperbound key l3 ) |]
  &&  (IntArray.seg nums_pre 0 (j + 1 ) l2_2 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |-> key)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  EX (l0: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((i + 1 ) = (Zlength (l1))) |] 
  &&  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (i + 1 ) l0 )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l2 )
.

Definition sortArray_entail_wit_6_2 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2_2: (@list Z)) (l3: (@list Z)) (l0_2: (@list Z)) (i: Z) (l1_2: (@list Z)) (key: Z) (l4: (@list Z)) ,
  [| (j < 0) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1_2) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1_2))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1_2 l0_2 ) |] 
  &&  [| (increasing l0_2 ) |] 
  &&  [| (l0_2 = (app (l2_2) (l3))) |] 
  &&  [| ((j + 1 ) = (Zlength (l2_2))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (strict_upperbound key l3 ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (j + 1 ) l2_2 )
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |-> key)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  EX (l0: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| ((i + 1 ) = (Zlength (l1))) |] 
  &&  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (i + 1 ) l0 )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l2 )
.

Definition sortArray_return_wit_1 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l0: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2: (@list Z)) ,
  [| (i >= numsSize_pre) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1_2) (l2))) |] 
  &&  [| (i = (Zlength (l1_2))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1_2 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 i l0 )
  **  (IntArray.seg nums_pre i numsSize_pre l2 )
|--
  EX (l1: (@list Z)) ,
  [| (Permutation l l1 ) |] 
  &&  [| (increasing l1 ) |] 
  &&  [| ((Zlength (l1)) = numsSize_pre) |]
  &&  (IntArray.full nums_pre numsSize_pre l1 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_1 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  [| (i < numsSize_pre) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 i l0 )
  **  (IntArray.seg nums_pre i numsSize_pre l2 )
|--
  [| (i < numsSize_pre) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) (l2))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  (((nums_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth (i - i ) l2 0))
  **  (IntArray.missing_i nums_pre i i numsSize_pre l2 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 i l0 )
.

Definition sortArray_partial_solve_wit_2 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) ,
  [| (j >= 0) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2) (l3))) |] 
  &&  [| ((j + 1 ) = (Zlength (l2))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (strict_upperbound key l3 ) |]
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  [| (j >= 0) |] 
  &&  [| (1 <= numsSize_pre) |] 
  &&  [| (numsSize_pre <= 50000) |] 
  &&  [| (l = (app (l1) ((cons (key) (l4))))) |] 
  &&  [| (i = (Zlength (l1))) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numsSize_pre) |] 
  &&  [| (Permutation l1 l0 ) |] 
  &&  [| (increasing l0 ) |] 
  &&  [| (l0 = (app (l2) (l3))) |] 
  &&  [| ((j + 1 ) = (Zlength (l2))) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (strict_upperbound key l3 ) |]
  &&  (((nums_pre + (j * sizeof(INT) ) )) # Int  |-> (Znth (j - 0 ) l2 0))
  **  (IntArray.missing_i nums_pre j 0 (j + 1 ) l2 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (((nums_pre + ((j + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
.

Module Type VC_Correct.


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
Axiom proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1.
Axiom proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2.
Axiom proof_of_sortArray_entail_wit_3 : sortArray_entail_wit_3.
Axiom proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4.
Axiom proof_of_sortArray_entail_wit_5 : sortArray_entail_wit_5.
Axiom proof_of_sortArray_entail_wit_6_1 : sortArray_entail_wit_6_1.
Axiom proof_of_sortArray_entail_wit_6_2 : sortArray_entail_wit_6_2.
Axiom proof_of_sortArray_return_wit_1 : sortArray_return_wit_1.
Axiom proof_of_sortArray_partial_solve_wit_1 : sortArray_partial_solve_wit_1.
Axiom proof_of_sortArray_partial_solve_wit_2 : sortArray_partial_solve_wit_2.

End VC_Correct.
