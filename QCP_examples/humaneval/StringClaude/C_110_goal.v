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
Require Import coins_110.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function exchange -----*)

Definition exchange_safety_wit_1 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |]
  &&  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exchange_safety_wit_2 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exchange_safety_wit_3 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (i < lst1_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst1_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= i) |] 
  &&  [| (num = (count_even_upto (i) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (((Znth i l1 0) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition exchange_safety_wit_4 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (i < lst1_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst1_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= i) |] 
  &&  [| (num = (count_even_upto (i) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition exchange_safety_wit_5 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (i < lst1_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst1_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= i) |] 
  &&  [| (num = (count_even_upto (i) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exchange_safety_wit_6 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (((Znth i l1 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < lst1_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst1_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= i) |] 
  &&  [| (num = (count_even_upto (i) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| ((num + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (num + 1 )) |]
.

Definition exchange_safety_wit_7 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (((Znth i l1 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < lst1_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst1_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= i) |] 
  &&  [| (num = (count_even_upto (i) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition exchange_safety_wit_8 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (((Znth i l1 0) % ( 2 ) ) <> 0) |] 
  &&  [| (i < lst1_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst1_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= i) |] 
  &&  [| (num = (count_even_upto (i) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition exchange_safety_wit_9 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (((Znth i l1 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < lst1_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst1_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= i) |] 
  &&  [| (num = (count_even_upto (i) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> (num + 1 ))
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition exchange_safety_wit_10 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) ,
  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= lst1_size_pre) |] 
  &&  [| (num = (count_even_upto (lst1_size_pre) (l1))) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exchange_safety_wit_11 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (i < lst2_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + i )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (i) (l2)) )) |]
  &&  (IntArray.full lst2_pre lst2_size_pre l2 )
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full lst1_pre lst1_size_pre l1 )
|--
  [| (((Znth i l2 0) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition exchange_safety_wit_12 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (i < lst2_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + i )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (i) (l2)) )) |]
  &&  (IntArray.full lst2_pre lst2_size_pre l2 )
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full lst1_pre lst1_size_pre l1 )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition exchange_safety_wit_13 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (i < lst2_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + i )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (i) (l2)) )) |]
  &&  (IntArray.full lst2_pre lst2_size_pre l2 )
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full lst1_pre lst1_size_pre l1 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exchange_safety_wit_14 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (((Znth i l2 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < lst2_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + i )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (i) (l2)) )) |]
  &&  (IntArray.full lst2_pre lst2_size_pre l2 )
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full lst1_pre lst1_size_pre l1 )
|--
  [| ((num + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (num + 1 )) |]
.

Definition exchange_safety_wit_15 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (((Znth i l2 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < lst2_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + i )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (i) (l2)) )) |]
  &&  (IntArray.full lst2_pre lst2_size_pre l2 )
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full lst1_pre lst1_size_pre l1 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition exchange_safety_wit_16 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (((Znth i l2 0) % ( 2 ) ) <> 0) |] 
  &&  [| (i < lst2_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + i )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (i) (l2)) )) |]
  &&  (IntArray.full lst2_pre lst2_size_pre l2 )
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full lst1_pre lst1_size_pre l1 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition exchange_safety_wit_17 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (((Znth i l2 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < lst2_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + i )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (i) (l2)) )) |]
  &&  (IntArray.full lst2_pre lst2_size_pre l2 )
  **  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> (num + 1 ))
  **  (IntArray.full lst1_pre lst1_size_pre l1 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition exchange_safety_wit_18 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (num >= lst1_size_pre) |] 
  &&  [| (i >= lst2_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + i )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (i) (l2)) )) |]
  &&  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition exchange_safety_wit_19 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (num < lst1_size_pre) |] 
  &&  [| (i >= lst2_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + i )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (i) (l2)) )) |]
  &&  ((( &( "lst1" ) )) # Ptr  |-> lst1_pre)
  **  ((( &( "lst2" ) )) # Ptr  |-> lst2_pre)
  **  ((( &( "lst1_size" ) )) # Int  |-> lst1_size_pre)
  **  ((( &( "lst2_size" ) )) # Int  |-> lst2_size_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition exchange_entail_wit_1 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= lst1_size_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 = (count_even_upto (0) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
.

Definition exchange_entail_wit_2_1 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (((Znth i l1 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < lst1_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst1_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= i) |] 
  &&  [| (num = (count_even_upto (i) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst1_size_pre) |] 
  &&  [| (0 <= (num + 1 )) |] 
  &&  [| ((num + 1 ) <= (i + 1 )) |] 
  &&  [| ((num + 1 ) = (count_even_upto ((i + 1 )) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
.

Definition exchange_entail_wit_2_2 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (((Znth i l1 0) % ( 2 ) ) <> 0) |] 
  &&  [| (i < lst1_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst1_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= i) |] 
  &&  [| (num = (count_even_upto (i) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst1_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (i + 1 )) |] 
  &&  [| (num = (count_even_upto ((i + 1 )) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
.

Definition exchange_entail_wit_3 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (i >= lst1_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst1_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= i) |] 
  &&  [| (num = (count_even_upto (i) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= lst1_size_pre) |] 
  &&  [| (num = (count_even_upto (lst1_size_pre) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
.

Definition exchange_entail_wit_4 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) ,
  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= lst1_size_pre) |] 
  &&  [| (num = (count_even_upto (lst1_size_pre) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + 0 )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (0) (l2)) )) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
.

Definition exchange_entail_wit_5_1 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (((Znth i l2 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < lst2_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + i )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (i) (l2)) )) |]
  &&  (IntArray.full lst2_pre lst2_size_pre l2 )
  **  (IntArray.full lst1_pre lst1_size_pre l1 )
|--
  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst2_size_pre) |] 
  &&  [| (0 <= (num + 1 )) |] 
  &&  [| ((num + 1 ) <= (lst1_size_pre + (i + 1 ) )) |] 
  &&  [| ((num + 1 ) = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto ((i + 1 )) (l2)) )) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
.

Definition exchange_entail_wit_5_2 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (((Znth i l2 0) % ( 2 ) ) <> 0) |] 
  &&  [| (i < lst2_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + i )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (i) (l2)) )) |]
  &&  (IntArray.full lst2_pre lst2_size_pre l2 )
  **  (IntArray.full lst1_pre lst1_size_pre l1 )
|--
  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + (i + 1 ) )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto ((i + 1 )) (l2)) )) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
.

Definition exchange_return_wit_1 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (num < lst1_size_pre) |] 
  &&  [| (i >= lst2_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + i )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (i) (l2)) )) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (problem_110_spec_z l1 l2 0 ) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
.

Definition exchange_return_wit_2 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (num >= lst1_size_pre) |] 
  &&  [| (i >= lst2_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + i )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (i) (l2)) )) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (problem_110_spec_z l1 l2 1 ) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
.

Definition exchange_partial_solve_wit_1 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (i < lst1_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst1_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= i) |] 
  &&  [| (num = (count_even_upto (i) (l1))) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (i < lst1_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst1_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= i) |] 
  &&  [| (num = (count_even_upto (i) (l1))) |]
  &&  (((lst1_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l1 0))
  **  (IntArray.missing_i lst1_pre i 0 lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
.

Definition exchange_partial_solve_wit_2 := 
forall (lst2_size_pre: Z) (lst2_pre: Z) (lst1_size_pre: Z) (lst1_pre: Z) (l2: (@list Z)) (l1: (@list Z)) (num: Z) (i: Z) ,
  [| (i < lst2_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + i )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (i) (l2)) )) |]
  &&  (IntArray.full lst1_pre lst1_size_pre l1 )
  **  (IntArray.full lst2_pre lst2_size_pre l2 )
|--
  [| (i < lst2_size_pre) |] 
  &&  [| (0 < lst1_size_pre) |] 
  &&  [| (lst1_size_pre < INT_MAX) |] 
  &&  [| (0 < lst2_size_pre) |] 
  &&  [| (lst2_size_pre < INT_MAX) |] 
  &&  [| ((lst1_size_pre + lst2_size_pre ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = lst1_size_pre) |] 
  &&  [| ((Zlength (l2)) = lst2_size_pre) |] 
  &&  [| (problem_110_pre_z l1 l2 ) |] 
  &&  [| (nonnegative_list_z l1 ) |] 
  &&  [| (nonnegative_list_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= lst2_size_pre) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= (lst1_size_pre + i )) |] 
  &&  [| (num = ((count_even_upto (lst1_size_pre) (l1)) + (count_even_upto (i) (l2)) )) |]
  &&  (((lst2_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l2 0))
  **  (IntArray.missing_i lst2_pre i 0 lst2_size_pre l2 )
  **  (IntArray.full lst1_pre lst1_size_pre l1 )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_exchange_safety_wit_1 : exchange_safety_wit_1.
Axiom proof_of_exchange_safety_wit_2 : exchange_safety_wit_2.
Axiom proof_of_exchange_safety_wit_3 : exchange_safety_wit_3.
Axiom proof_of_exchange_safety_wit_4 : exchange_safety_wit_4.
Axiom proof_of_exchange_safety_wit_5 : exchange_safety_wit_5.
Axiom proof_of_exchange_safety_wit_6 : exchange_safety_wit_6.
Axiom proof_of_exchange_safety_wit_7 : exchange_safety_wit_7.
Axiom proof_of_exchange_safety_wit_8 : exchange_safety_wit_8.
Axiom proof_of_exchange_safety_wit_9 : exchange_safety_wit_9.
Axiom proof_of_exchange_safety_wit_10 : exchange_safety_wit_10.
Axiom proof_of_exchange_safety_wit_11 : exchange_safety_wit_11.
Axiom proof_of_exchange_safety_wit_12 : exchange_safety_wit_12.
Axiom proof_of_exchange_safety_wit_13 : exchange_safety_wit_13.
Axiom proof_of_exchange_safety_wit_14 : exchange_safety_wit_14.
Axiom proof_of_exchange_safety_wit_15 : exchange_safety_wit_15.
Axiom proof_of_exchange_safety_wit_16 : exchange_safety_wit_16.
Axiom proof_of_exchange_safety_wit_17 : exchange_safety_wit_17.
Axiom proof_of_exchange_safety_wit_18 : exchange_safety_wit_18.
Axiom proof_of_exchange_safety_wit_19 : exchange_safety_wit_19.
Axiom proof_of_exchange_entail_wit_1 : exchange_entail_wit_1.
Axiom proof_of_exchange_entail_wit_2_1 : exchange_entail_wit_2_1.
Axiom proof_of_exchange_entail_wit_2_2 : exchange_entail_wit_2_2.
Axiom proof_of_exchange_entail_wit_3 : exchange_entail_wit_3.
Axiom proof_of_exchange_entail_wit_4 : exchange_entail_wit_4.
Axiom proof_of_exchange_entail_wit_5_1 : exchange_entail_wit_5_1.
Axiom proof_of_exchange_entail_wit_5_2 : exchange_entail_wit_5_2.
Axiom proof_of_exchange_return_wit_1 : exchange_return_wit_1.
Axiom proof_of_exchange_return_wit_2 : exchange_return_wit_2.
Axiom proof_of_exchange_partial_solve_wit_1 : exchange_partial_solve_wit_1.
Axiom proof_of_exchange_partial_solve_wit_2 : exchange_partial_solve_wit_2.

End VC_Correct.
