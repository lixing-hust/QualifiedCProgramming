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
Require Import coins_98.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function count_upper -----*)

Definition count_upper_safety_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "count" ) )) # Int  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_upper_safety_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_upper_safety_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((i <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition count_upper_safety_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition count_upper_safety_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_upper_safety_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition count_upper_safety_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (69 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 69) |]
.

Definition count_upper_safety_wit_8 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (73 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 73) |]
.

Definition count_upper_safety_wit_9 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (79 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 79) |]
.

Definition count_upper_safety_wit_10 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (85 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 85) |]
.

Definition count_upper_safety_wit_11 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition count_upper_safety_wit_12 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_upper_safety_wit_13 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition count_upper_safety_wit_14 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_upper_safety_wit_15 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition count_upper_safety_wit_16 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_upper_safety_wit_17 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition count_upper_safety_wit_18 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_upper_safety_wit_19 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition count_upper_safety_wit_20 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_upper_safety_wit_21 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((i % ( 2 ) ) <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_upper_safety_wit_22 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_upper_safety_wit_23 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_upper_safety_wit_24 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_upper_safety_wit_25 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_upper_safety_wit_26 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_upper_safety_wit_27 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_upper_entail_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 = (count_upper_even_upto (0) (l))) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_upper_entail_wit_2_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (i + 1 )) |] 
  &&  [| ((count + 1 ) = (count_upper_even_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_upper_entail_wit_2_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (i + 1 )) |] 
  &&  [| ((count + 1 ) = (count_upper_even_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_upper_entail_wit_2_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (i + 1 )) |] 
  &&  [| ((count + 1 ) = (count_upper_even_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_upper_entail_wit_2_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (i + 1 )) |] 
  &&  [| ((count + 1 ) = (count_upper_even_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_upper_entail_wit_2_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (i + 1 )) |] 
  &&  [| ((count + 1 ) = (count_upper_even_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_upper_entail_wit_2_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i + 1 )) |] 
  &&  [| (count = (count_upper_even_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_upper_entail_wit_2_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((i % ( 2 ) ) <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i + 1 )) |] 
  &&  [| (count = (count_upper_even_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_upper_return_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_98_spec_z l count ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_upper_partial_solve_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_upper_partial_solve_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_upper_partial_solve_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_upper_partial_solve_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_upper_partial_solve_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_upper_partial_solve_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_98_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_upper_even_upto (i) (l))) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_count_upper_safety_wit_1 : count_upper_safety_wit_1.
Axiom proof_of_count_upper_safety_wit_2 : count_upper_safety_wit_2.
Axiom proof_of_count_upper_safety_wit_3 : count_upper_safety_wit_3.
Axiom proof_of_count_upper_safety_wit_4 : count_upper_safety_wit_4.
Axiom proof_of_count_upper_safety_wit_5 : count_upper_safety_wit_5.
Axiom proof_of_count_upper_safety_wit_6 : count_upper_safety_wit_6.
Axiom proof_of_count_upper_safety_wit_7 : count_upper_safety_wit_7.
Axiom proof_of_count_upper_safety_wit_8 : count_upper_safety_wit_8.
Axiom proof_of_count_upper_safety_wit_9 : count_upper_safety_wit_9.
Axiom proof_of_count_upper_safety_wit_10 : count_upper_safety_wit_10.
Axiom proof_of_count_upper_safety_wit_11 : count_upper_safety_wit_11.
Axiom proof_of_count_upper_safety_wit_12 : count_upper_safety_wit_12.
Axiom proof_of_count_upper_safety_wit_13 : count_upper_safety_wit_13.
Axiom proof_of_count_upper_safety_wit_14 : count_upper_safety_wit_14.
Axiom proof_of_count_upper_safety_wit_15 : count_upper_safety_wit_15.
Axiom proof_of_count_upper_safety_wit_16 : count_upper_safety_wit_16.
Axiom proof_of_count_upper_safety_wit_17 : count_upper_safety_wit_17.
Axiom proof_of_count_upper_safety_wit_18 : count_upper_safety_wit_18.
Axiom proof_of_count_upper_safety_wit_19 : count_upper_safety_wit_19.
Axiom proof_of_count_upper_safety_wit_20 : count_upper_safety_wit_20.
Axiom proof_of_count_upper_safety_wit_21 : count_upper_safety_wit_21.
Axiom proof_of_count_upper_safety_wit_22 : count_upper_safety_wit_22.
Axiom proof_of_count_upper_safety_wit_23 : count_upper_safety_wit_23.
Axiom proof_of_count_upper_safety_wit_24 : count_upper_safety_wit_24.
Axiom proof_of_count_upper_safety_wit_25 : count_upper_safety_wit_25.
Axiom proof_of_count_upper_safety_wit_26 : count_upper_safety_wit_26.
Axiom proof_of_count_upper_safety_wit_27 : count_upper_safety_wit_27.
Axiom proof_of_count_upper_entail_wit_1 : count_upper_entail_wit_1.
Axiom proof_of_count_upper_entail_wit_2_1 : count_upper_entail_wit_2_1.
Axiom proof_of_count_upper_entail_wit_2_2 : count_upper_entail_wit_2_2.
Axiom proof_of_count_upper_entail_wit_2_3 : count_upper_entail_wit_2_3.
Axiom proof_of_count_upper_entail_wit_2_4 : count_upper_entail_wit_2_4.
Axiom proof_of_count_upper_entail_wit_2_5 : count_upper_entail_wit_2_5.
Axiom proof_of_count_upper_entail_wit_2_6 : count_upper_entail_wit_2_6.
Axiom proof_of_count_upper_entail_wit_2_7 : count_upper_entail_wit_2_7.
Axiom proof_of_count_upper_return_wit_1 : count_upper_return_wit_1.
Axiom proof_of_count_upper_partial_solve_wit_1 : count_upper_partial_solve_wit_1.
Axiom proof_of_count_upper_partial_solve_wit_2 : count_upper_partial_solve_wit_2.
Axiom proof_of_count_upper_partial_solve_wit_3 : count_upper_partial_solve_wit_3.
Axiom proof_of_count_upper_partial_solve_wit_4 : count_upper_partial_solve_wit_4.
Axiom proof_of_count_upper_partial_solve_wit_5 : count_upper_partial_solve_wit_5.
Axiom proof_of_count_upper_partial_solve_wit_6 : count_upper_partial_solve_wit_6.

End VC_Correct.
