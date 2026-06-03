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
Require Import coins_161.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function solve -----*)

Definition solve_safety_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "has_letter" ) )) # Int  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "has_letter" ) )) # Int  |-> 0)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((retval + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval + 1 )) |]
.

Definition solve_safety_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "has_letter" ) )) # Int  |-> 0)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition solve_safety_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "has_letter" ) )) # Int  |-> 0)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition solve_safety_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| (90 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 90) |]
.

Definition solve_safety_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition solve_safety_wit_8 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition solve_safety_wit_9 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| False |]
.

Definition solve_safety_wit_10 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| (122 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 122) |]
.

Definition solve_safety_wit_11 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition solve_safety_wit_12 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition solve_safety_wit_13 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition solve_safety_wit_14 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition solve_safety_wit_15 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition solve_safety_wit_16 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> 1)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition solve_safety_wit_17 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> 1)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition solve_safety_wit_18 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition solve_safety_wit_19 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| (has_letter = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_20 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition solve_safety_wit_21 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (90 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 90) |]
.

Definition solve_safety_wit_22 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 )) |]
.

Definition solve_safety_wit_23 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition solve_safety_wit_24 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition solve_safety_wit_25 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition solve_safety_wit_26 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition solve_safety_wit_27 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (122 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 122) |]
.

Definition solve_safety_wit_28 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 )) |]
.

Definition solve_safety_wit_29 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition solve_safety_wit_30 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition solve_safety_wit_31 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition solve_safety_wit_32 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition solve_safety_wit_33 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition solve_safety_wit_34 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition solve_safety_wit_35 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| (has_letter <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_36 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (Znth (((len - 1 ) - k )) (l) (0)))) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (((len - 1 ) - i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((len - 1 ) - i )) |]
.

Definition solve_safety_wit_37 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (Znth (((len - 1 ) - k )) (l) (0)))) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| ((len - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (len - 1 )) |]
.

Definition solve_safety_wit_38 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (Znth (((len - 1 ) - k )) (l) (0)))) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition solve_safety_wit_39 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (Znth (((len - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((Znth ((len - 1 ) - i ) (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition solve_safety_wit_40 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (Znth (((len - 1 ) - k )) (l) (0)))) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_safety_wit_41 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "has_letter" ) )) # Int  |-> has_letter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition solve_entail_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval_2 = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.undef_full retval (retval_2 + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 = (contains_letter_prefix_z (0) (l))) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_full retval (len + 1 ) )
.

Definition solve_entail_wit_2_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (1 = (contains_letter_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_full out (len + 1 ) )
.

Definition solve_entail_wit_2_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (1 = (contains_letter_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_full out (len + 1 ) )
.

Definition solve_entail_wit_2_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_full out (len + 1 ) )
.

Definition solve_entail_wit_2_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_full out (len + 1 ) )
.

Definition solve_entail_wit_2_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_full out (len + 1 ) )
.

Definition solve_entail_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| (has_letter = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_full out (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((Zlength (out_l)) = 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out 0 out_l )
  **  (CharArray.undef_seg out 0 (len + 1 ) )
.

Definition solve_entail_wit_4_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition solve_entail_wit_4_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition solve_entail_wit_4_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition solve_entail_wit_4_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition solve_entail_wit_4_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition solve_entail_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| (has_letter <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_full out (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((Zlength (out_l)) = 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (out_l) (0)) = (Znth (((len - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out 0 out_l )
  **  (CharArray.undef_seg out 0 (len + 1 ) )
.

Definition solve_entail_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (Znth (((len - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((Znth ((len - 1 ) - i ) (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (Znth (((len - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition solve_return_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (Znth (((len - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (len + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (out_l)) = len) |] 
  &&  [| (problem_161_spec_z l out_l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition solve_return_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (len + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (out_l)) = len) |] 
  &&  [| (problem_161_spec_z l out_l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition solve_partial_solve_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition solve_partial_solve_wit_2_pure := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "has_letter" ) )) # Int  |-> 0)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((retval + 1 ) > 0) |]
.

Definition solve_partial_solve_wit_2_aux := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((retval + 1 ) > 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition solve_partial_solve_wit_2 := solve_partial_solve_wit_2_pure -> solve_partial_solve_wit_2_aux.

Definition solve_partial_solve_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (has_letter: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_full out (len + 1 ) )
|--
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (has_letter = (contains_letter_prefix_z (i) (l))) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_full out (len + 1 ) )
.

Definition solve_partial_solve_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
.

Definition solve_partial_solve_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition solve_partial_solve_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition solve_partial_solve_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition solve_partial_solve_wit_8 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition solve_partial_solve_wit_9 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition solve_partial_solve_wit_10 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (Znth (((len - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (Znth (((len - 1 ) - k )) (l) (0)))) |]
  &&  (((s_pre + (((len - 1 ) - i ) * sizeof(CHAR) ) )) # Char  |-> (Znth ((len - 1 ) - i ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre ((len - 1 ) - i ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
.

Definition solve_partial_solve_wit_11 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (Znth (((len - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (Znth (((len - 1 ) - k )) (l) (0)))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition solve_partial_solve_wit_12 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (Znth (((len - 1 ) - k )) (l) (0)))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (Znth (((len - 1 ) - k )) (l) (0)))) |]
  &&  (((out + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out len i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition solve_partial_solve_wit_13 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (has_letter: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_161_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (has_letter = (contains_letter_z (l))) |] 
  &&  [| (has_letter = 1) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out len i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_solve_safety_wit_1 : solve_safety_wit_1.
Axiom proof_of_solve_safety_wit_2 : solve_safety_wit_2.
Axiom proof_of_solve_safety_wit_3 : solve_safety_wit_3.
Axiom proof_of_solve_safety_wit_4 : solve_safety_wit_4.
Axiom proof_of_solve_safety_wit_5 : solve_safety_wit_5.
Axiom proof_of_solve_safety_wit_6 : solve_safety_wit_6.
Axiom proof_of_solve_safety_wit_7 : solve_safety_wit_7.
Axiom proof_of_solve_safety_wit_8 : solve_safety_wit_8.
Axiom proof_of_solve_safety_wit_9 : solve_safety_wit_9.
Axiom proof_of_solve_safety_wit_10 : solve_safety_wit_10.
Axiom proof_of_solve_safety_wit_11 : solve_safety_wit_11.
Axiom proof_of_solve_safety_wit_12 : solve_safety_wit_12.
Axiom proof_of_solve_safety_wit_13 : solve_safety_wit_13.
Axiom proof_of_solve_safety_wit_14 : solve_safety_wit_14.
Axiom proof_of_solve_safety_wit_15 : solve_safety_wit_15.
Axiom proof_of_solve_safety_wit_16 : solve_safety_wit_16.
Axiom proof_of_solve_safety_wit_17 : solve_safety_wit_17.
Axiom proof_of_solve_safety_wit_18 : solve_safety_wit_18.
Axiom proof_of_solve_safety_wit_19 : solve_safety_wit_19.
Axiom proof_of_solve_safety_wit_20 : solve_safety_wit_20.
Axiom proof_of_solve_safety_wit_21 : solve_safety_wit_21.
Axiom proof_of_solve_safety_wit_22 : solve_safety_wit_22.
Axiom proof_of_solve_safety_wit_23 : solve_safety_wit_23.
Axiom proof_of_solve_safety_wit_24 : solve_safety_wit_24.
Axiom proof_of_solve_safety_wit_25 : solve_safety_wit_25.
Axiom proof_of_solve_safety_wit_26 : solve_safety_wit_26.
Axiom proof_of_solve_safety_wit_27 : solve_safety_wit_27.
Axiom proof_of_solve_safety_wit_28 : solve_safety_wit_28.
Axiom proof_of_solve_safety_wit_29 : solve_safety_wit_29.
Axiom proof_of_solve_safety_wit_30 : solve_safety_wit_30.
Axiom proof_of_solve_safety_wit_31 : solve_safety_wit_31.
Axiom proof_of_solve_safety_wit_32 : solve_safety_wit_32.
Axiom proof_of_solve_safety_wit_33 : solve_safety_wit_33.
Axiom proof_of_solve_safety_wit_34 : solve_safety_wit_34.
Axiom proof_of_solve_safety_wit_35 : solve_safety_wit_35.
Axiom proof_of_solve_safety_wit_36 : solve_safety_wit_36.
Axiom proof_of_solve_safety_wit_37 : solve_safety_wit_37.
Axiom proof_of_solve_safety_wit_38 : solve_safety_wit_38.
Axiom proof_of_solve_safety_wit_39 : solve_safety_wit_39.
Axiom proof_of_solve_safety_wit_40 : solve_safety_wit_40.
Axiom proof_of_solve_safety_wit_41 : solve_safety_wit_41.
Axiom proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Axiom proof_of_solve_entail_wit_2_1 : solve_entail_wit_2_1.
Axiom proof_of_solve_entail_wit_2_2 : solve_entail_wit_2_2.
Axiom proof_of_solve_entail_wit_2_3 : solve_entail_wit_2_3.
Axiom proof_of_solve_entail_wit_2_4 : solve_entail_wit_2_4.
Axiom proof_of_solve_entail_wit_2_5 : solve_entail_wit_2_5.
Axiom proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Axiom proof_of_solve_entail_wit_4_1 : solve_entail_wit_4_1.
Axiom proof_of_solve_entail_wit_4_2 : solve_entail_wit_4_2.
Axiom proof_of_solve_entail_wit_4_3 : solve_entail_wit_4_3.
Axiom proof_of_solve_entail_wit_4_4 : solve_entail_wit_4_4.
Axiom proof_of_solve_entail_wit_4_5 : solve_entail_wit_4_5.
Axiom proof_of_solve_entail_wit_5 : solve_entail_wit_5.
Axiom proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Axiom proof_of_solve_return_wit_1 : solve_return_wit_1.
Axiom proof_of_solve_return_wit_2 : solve_return_wit_2.
Axiom proof_of_solve_partial_solve_wit_1 : solve_partial_solve_wit_1.
Axiom proof_of_solve_partial_solve_wit_2_pure : solve_partial_solve_wit_2_pure.
Axiom proof_of_solve_partial_solve_wit_2 : solve_partial_solve_wit_2.
Axiom proof_of_solve_partial_solve_wit_3 : solve_partial_solve_wit_3.
Axiom proof_of_solve_partial_solve_wit_4 : solve_partial_solve_wit_4.
Axiom proof_of_solve_partial_solve_wit_5 : solve_partial_solve_wit_5.
Axiom proof_of_solve_partial_solve_wit_6 : solve_partial_solve_wit_6.
Axiom proof_of_solve_partial_solve_wit_7 : solve_partial_solve_wit_7.
Axiom proof_of_solve_partial_solve_wit_8 : solve_partial_solve_wit_8.
Axiom proof_of_solve_partial_solve_wit_9 : solve_partial_solve_wit_9.
Axiom proof_of_solve_partial_solve_wit_10 : solve_partial_solve_wit_10.
Axiom proof_of_solve_partial_solve_wit_11 : solve_partial_solve_wit_11.
Axiom proof_of_solve_partial_solve_wit_12 : solve_partial_solve_wit_12.
Axiom proof_of_solve_partial_solve_wit_13 : solve_partial_solve_wit_13.

End VC_Correct.
