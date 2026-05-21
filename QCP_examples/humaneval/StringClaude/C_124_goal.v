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
Require Import coins_124.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function valid_date -----*)

Definition valid_date_safety_wit_1 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition valid_date_safety_wit_2 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 10) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_3 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = 10) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_4 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition valid_date_safety_wit_5 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition valid_date_safety_wit_6 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition valid_date_safety_wit_7 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i = 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (45 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 45) |]
.

Definition valid_date_safety_wit_8 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i = 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (45 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 45) |]
.

Definition valid_date_safety_wit_9 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 45) |] 
  &&  [| (i = 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_10 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 45) |] 
  &&  [| (i = 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_11 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i <> 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition valid_date_safety_wit_12 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) |] 
  &&  [| (i <> 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (57 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 57) |]
.

Definition valid_date_safety_wit_13 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) |] 
  &&  [| (i <> 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_14 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) |] 
  &&  [| (i <> 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_15 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) |] 
  &&  [| (i <> 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition valid_date_safety_wit_16 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 45) |] 
  &&  [| (i = 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition valid_date_safety_wit_17 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 45) |] 
  &&  [| (i = 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition valid_date_safety_wit_18 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "mm" ) )) # Int  |->_)
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) )) |]
.

Definition valid_date_safety_wit_19 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "mm" ) )) # Int  |->_)
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 )) |]
.

Definition valid_date_safety_wit_20 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "mm" ) )) # Int  |->_)
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 )) |]
.

Definition valid_date_safety_wit_21 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "mm" ) )) # Int  |->_)
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 )) |]
.

Definition valid_date_safety_wit_22 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  ((( &( "mm" ) )) # Int  |->_)
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_23 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "mm" ) )) # Int  |->_)
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition valid_date_safety_wit_24 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "mm" ) )) # Int  |->_)
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition valid_date_safety_wit_25 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "mm" ) )) # Int  |->_)
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition valid_date_safety_wit_26 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "mm" ) )) # Int  |->_)
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition valid_date_safety_wit_27 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |->_)
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) )) |]
.

Definition valid_date_safety_wit_28 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |->_)
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 )) |]
.

Definition valid_date_safety_wit_29 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |->_)
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 )) |]
.

Definition valid_date_safety_wit_30 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |->_)
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 )) |]
.

Definition valid_date_safety_wit_31 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  ((( &( "dd" ) )) # Int  |->_)
  **  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition valid_date_safety_wit_32 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |->_)
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition valid_date_safety_wit_33 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |->_)
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition valid_date_safety_wit_34 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |->_)
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition valid_date_safety_wit_35 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |->_)
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition valid_date_safety_wit_36 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition valid_date_safety_wit_37 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (12 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 12) |]
.

Definition valid_date_safety_wit_38 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) > 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_39 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) < 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_40 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition valid_date_safety_wit_41 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (31 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 31) |]
.

Definition valid_date_safety_wit_42 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) > 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_43 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) < 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_44 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (31 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 31) |]
.

Definition valid_date_safety_wit_45 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition valid_date_safety_wit_46 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition valid_date_safety_wit_47 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 6) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (9 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 9) |]
.

Definition valid_date_safety_wit_48 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 9) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 6) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (11 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 11) |]
.

Definition valid_date_safety_wit_49 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 11) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 9) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 6) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition valid_date_safety_wit_50 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 11) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 9) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 6) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_51 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 6) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_52 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_53 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 9) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 6) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_54 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 2) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 11) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 9) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 6) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_55 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 2) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 11) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 9) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 6) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (30 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 30) |]
.

Definition valid_date_safety_wit_56 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (30 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 30) |]
.

Definition valid_date_safety_wit_57 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 30) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 2) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 11) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 9) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 6) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| False |]
.

Definition valid_date_safety_wit_58 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 30) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition valid_date_safety_wit_59 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 2) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 30) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition valid_date_safety_wit_60 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 2) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 30) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition valid_date_safety_wit_61 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 30) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 2) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 11) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 9) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 6) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition valid_date_safety_wit_62 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 30) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "dd" ) )) # Int  |-> ((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "mm" ) )) # Int  |-> ((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "date" ) )) # Ptr  |-> date_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition valid_date_entail_wit_1 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = 10) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (retval = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 10) |] 
  &&  [| (date_prefix_valid 0 l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_entail_wit_2_1 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 45) |] 
  &&  [| (i = 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= 10) |] 
  &&  [| (date_prefix_valid (i + 1 ) l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_entail_wit_2_2 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 45) |] 
  &&  [| (i = 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= 10) |] 
  &&  [| (date_prefix_valid (i + 1 ) l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_entail_wit_2_3 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) |] 
  &&  [| (i <> 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= 10) |] 
  &&  [| (date_prefix_valid (i + 1 ) l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_1 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 30) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 1 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_2 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 30) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 2) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 11) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 9) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 6) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 1 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_3 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 2) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 30) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 1 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_4 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 2) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 30) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 0 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_5 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 2) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 11) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 9) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 6) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 0 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_6 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 9) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 6) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 0 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_7 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 0 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_8 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 6) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 0 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_9 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 11) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 9) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 6) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <> 4) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 0 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_10 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) < 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 0 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_11 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) > 31) |] 
  &&  [| (((((Znth 3 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 4 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 0 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_12 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) < 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 0 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_13 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) > 12) |] 
  &&  [| (((((Znth 0 (app (l) ((cons (0) (nil)))) 0) - 48 ) * 10 ) + ((Znth 1 (app (l) ((cons (0) (nil)))) 0) - 48 ) ) >= 1) |] 
  &&  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 0 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_14 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) |] 
  &&  [| (i <> 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 0 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_15 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) |] 
  &&  [| (i <> 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 0 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_16 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 45) |] 
  &&  [| (i = 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 0 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_17 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 45) |] 
  &&  [| (i = 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 0 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_return_wit_18 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 10) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_124_spec_z l 0 ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_partial_solve_wit_1 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_partial_solve_wit_2 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i = 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i = 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (((date_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i date_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_partial_solve_wit_3 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i = 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i = 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (((date_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i date_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_partial_solve_wit_4 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i <> 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i <> 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (((date_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i date_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_partial_solve_wit_5 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) |] 
  &&  [| (i <> 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) |] 
  &&  [| (i <> 5) |] 
  &&  [| (i <> 2) |] 
  &&  [| (i < 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (((date_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i date_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_partial_solve_wit_6 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (((date_pre + (0 * sizeof(CHAR) ) )) # Char  |-> (Znth 0 (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i date_pre 0 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_partial_solve_wit_7 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (((date_pre + (1 * sizeof(CHAR) ) )) # Char  |-> (Znth 1 (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i date_pre 1 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_partial_solve_wit_8 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (((date_pre + (3 * sizeof(CHAR) ) )) # Char  |-> (Znth 3 (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i date_pre 3 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition valid_date_partial_solve_wit_9 := 
forall (date_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (n: Z) ,
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (CharArray.full date_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i >= 10) |] 
  &&  [| (n = 10) |] 
  &&  [| (len = 10) |] 
  &&  [| ((Zlength (l)) = 10) |] 
  &&  [| (problem_124_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 10) |] 
  &&  [| (date_prefix_valid i l ) |]
  &&  (((date_pre + (4 * sizeof(CHAR) ) )) # Char  |-> (Znth 4 (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i date_pre 4 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_valid_date_safety_wit_1 : valid_date_safety_wit_1.
Axiom proof_of_valid_date_safety_wit_2 : valid_date_safety_wit_2.
Axiom proof_of_valid_date_safety_wit_3 : valid_date_safety_wit_3.
Axiom proof_of_valid_date_safety_wit_4 : valid_date_safety_wit_4.
Axiom proof_of_valid_date_safety_wit_5 : valid_date_safety_wit_5.
Axiom proof_of_valid_date_safety_wit_6 : valid_date_safety_wit_6.
Axiom proof_of_valid_date_safety_wit_7 : valid_date_safety_wit_7.
Axiom proof_of_valid_date_safety_wit_8 : valid_date_safety_wit_8.
Axiom proof_of_valid_date_safety_wit_9 : valid_date_safety_wit_9.
Axiom proof_of_valid_date_safety_wit_10 : valid_date_safety_wit_10.
Axiom proof_of_valid_date_safety_wit_11 : valid_date_safety_wit_11.
Axiom proof_of_valid_date_safety_wit_12 : valid_date_safety_wit_12.
Axiom proof_of_valid_date_safety_wit_13 : valid_date_safety_wit_13.
Axiom proof_of_valid_date_safety_wit_14 : valid_date_safety_wit_14.
Axiom proof_of_valid_date_safety_wit_15 : valid_date_safety_wit_15.
Axiom proof_of_valid_date_safety_wit_16 : valid_date_safety_wit_16.
Axiom proof_of_valid_date_safety_wit_17 : valid_date_safety_wit_17.
Axiom proof_of_valid_date_safety_wit_18 : valid_date_safety_wit_18.
Axiom proof_of_valid_date_safety_wit_19 : valid_date_safety_wit_19.
Axiom proof_of_valid_date_safety_wit_20 : valid_date_safety_wit_20.
Axiom proof_of_valid_date_safety_wit_21 : valid_date_safety_wit_21.
Axiom proof_of_valid_date_safety_wit_22 : valid_date_safety_wit_22.
Axiom proof_of_valid_date_safety_wit_23 : valid_date_safety_wit_23.
Axiom proof_of_valid_date_safety_wit_24 : valid_date_safety_wit_24.
Axiom proof_of_valid_date_safety_wit_25 : valid_date_safety_wit_25.
Axiom proof_of_valid_date_safety_wit_26 : valid_date_safety_wit_26.
Axiom proof_of_valid_date_safety_wit_27 : valid_date_safety_wit_27.
Axiom proof_of_valid_date_safety_wit_28 : valid_date_safety_wit_28.
Axiom proof_of_valid_date_safety_wit_29 : valid_date_safety_wit_29.
Axiom proof_of_valid_date_safety_wit_30 : valid_date_safety_wit_30.
Axiom proof_of_valid_date_safety_wit_31 : valid_date_safety_wit_31.
Axiom proof_of_valid_date_safety_wit_32 : valid_date_safety_wit_32.
Axiom proof_of_valid_date_safety_wit_33 : valid_date_safety_wit_33.
Axiom proof_of_valid_date_safety_wit_34 : valid_date_safety_wit_34.
Axiom proof_of_valid_date_safety_wit_35 : valid_date_safety_wit_35.
Axiom proof_of_valid_date_safety_wit_36 : valid_date_safety_wit_36.
Axiom proof_of_valid_date_safety_wit_37 : valid_date_safety_wit_37.
Axiom proof_of_valid_date_safety_wit_38 : valid_date_safety_wit_38.
Axiom proof_of_valid_date_safety_wit_39 : valid_date_safety_wit_39.
Axiom proof_of_valid_date_safety_wit_40 : valid_date_safety_wit_40.
Axiom proof_of_valid_date_safety_wit_41 : valid_date_safety_wit_41.
Axiom proof_of_valid_date_safety_wit_42 : valid_date_safety_wit_42.
Axiom proof_of_valid_date_safety_wit_43 : valid_date_safety_wit_43.
Axiom proof_of_valid_date_safety_wit_44 : valid_date_safety_wit_44.
Axiom proof_of_valid_date_safety_wit_45 : valid_date_safety_wit_45.
Axiom proof_of_valid_date_safety_wit_46 : valid_date_safety_wit_46.
Axiom proof_of_valid_date_safety_wit_47 : valid_date_safety_wit_47.
Axiom proof_of_valid_date_safety_wit_48 : valid_date_safety_wit_48.
Axiom proof_of_valid_date_safety_wit_49 : valid_date_safety_wit_49.
Axiom proof_of_valid_date_safety_wit_50 : valid_date_safety_wit_50.
Axiom proof_of_valid_date_safety_wit_51 : valid_date_safety_wit_51.
Axiom proof_of_valid_date_safety_wit_52 : valid_date_safety_wit_52.
Axiom proof_of_valid_date_safety_wit_53 : valid_date_safety_wit_53.
Axiom proof_of_valid_date_safety_wit_54 : valid_date_safety_wit_54.
Axiom proof_of_valid_date_safety_wit_55 : valid_date_safety_wit_55.
Axiom proof_of_valid_date_safety_wit_56 : valid_date_safety_wit_56.
Axiom proof_of_valid_date_safety_wit_57 : valid_date_safety_wit_57.
Axiom proof_of_valid_date_safety_wit_58 : valid_date_safety_wit_58.
Axiom proof_of_valid_date_safety_wit_59 : valid_date_safety_wit_59.
Axiom proof_of_valid_date_safety_wit_60 : valid_date_safety_wit_60.
Axiom proof_of_valid_date_safety_wit_61 : valid_date_safety_wit_61.
Axiom proof_of_valid_date_safety_wit_62 : valid_date_safety_wit_62.
Axiom proof_of_valid_date_entail_wit_1 : valid_date_entail_wit_1.
Axiom proof_of_valid_date_entail_wit_2_1 : valid_date_entail_wit_2_1.
Axiom proof_of_valid_date_entail_wit_2_2 : valid_date_entail_wit_2_2.
Axiom proof_of_valid_date_entail_wit_2_3 : valid_date_entail_wit_2_3.
Axiom proof_of_valid_date_return_wit_1 : valid_date_return_wit_1.
Axiom proof_of_valid_date_return_wit_2 : valid_date_return_wit_2.
Axiom proof_of_valid_date_return_wit_3 : valid_date_return_wit_3.
Axiom proof_of_valid_date_return_wit_4 : valid_date_return_wit_4.
Axiom proof_of_valid_date_return_wit_5 : valid_date_return_wit_5.
Axiom proof_of_valid_date_return_wit_6 : valid_date_return_wit_6.
Axiom proof_of_valid_date_return_wit_7 : valid_date_return_wit_7.
Axiom proof_of_valid_date_return_wit_8 : valid_date_return_wit_8.
Axiom proof_of_valid_date_return_wit_9 : valid_date_return_wit_9.
Axiom proof_of_valid_date_return_wit_10 : valid_date_return_wit_10.
Axiom proof_of_valid_date_return_wit_11 : valid_date_return_wit_11.
Axiom proof_of_valid_date_return_wit_12 : valid_date_return_wit_12.
Axiom proof_of_valid_date_return_wit_13 : valid_date_return_wit_13.
Axiom proof_of_valid_date_return_wit_14 : valid_date_return_wit_14.
Axiom proof_of_valid_date_return_wit_15 : valid_date_return_wit_15.
Axiom proof_of_valid_date_return_wit_16 : valid_date_return_wit_16.
Axiom proof_of_valid_date_return_wit_17 : valid_date_return_wit_17.
Axiom proof_of_valid_date_return_wit_18 : valid_date_return_wit_18.
Axiom proof_of_valid_date_partial_solve_wit_1 : valid_date_partial_solve_wit_1.
Axiom proof_of_valid_date_partial_solve_wit_2 : valid_date_partial_solve_wit_2.
Axiom proof_of_valid_date_partial_solve_wit_3 : valid_date_partial_solve_wit_3.
Axiom proof_of_valid_date_partial_solve_wit_4 : valid_date_partial_solve_wit_4.
Axiom proof_of_valid_date_partial_solve_wit_5 : valid_date_partial_solve_wit_5.
Axiom proof_of_valid_date_partial_solve_wit_6 : valid_date_partial_solve_wit_6.
Axiom proof_of_valid_date_partial_solve_wit_7 : valid_date_partial_solve_wit_7.
Axiom proof_of_valid_date_partial_solve_wit_8 : valid_date_partial_solve_wit_8.
Axiom proof_of_valid_date_partial_solve_wit_9 : valid_date_partial_solve_wit_9.

End VC_Correct.
