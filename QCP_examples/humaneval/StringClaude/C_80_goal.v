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
Require Import coins_80.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function is_happy -----*)

Definition is_happy_safety_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition is_happy_safety_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval < 3) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_happy_safety_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval >= 3) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_happy_safety_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval >= 3) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_happy_safety_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth 0 (app (l) ((cons (0) (nil)))) 0) = (Znth 1 (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (retval >= 3) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_happy_safety_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth 0 (app (l) ((cons (0) (nil)))) 0) <> (Znth 1 (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (retval >= 3) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_happy_safety_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i - 1 )) |]
.

Definition is_happy_safety_wit_8 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_happy_safety_wit_9 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_happy_safety_wit_10 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i - 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i - 2 )) |]
.

Definition is_happy_safety_wit_11 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_happy_safety_wit_12 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth (i - 2 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_happy_safety_wit_13 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 2 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_happy_safety_wit_14 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| (i >= len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_happy_entail_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth 0 (app (l) ((cons (0) (nil)))) 0) <> (Znth 1 (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (retval >= 3) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= 2) |] 
  &&  [| (2 <= len) |] 
  &&  [| (happy_prefix_z 2 l ) |] 
  &&  [| (happy_adjacent_z 2 l ) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_happy_entail_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 2 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (happy_prefix_z (i + 1 ) l ) |] 
  &&  [| (happy_adjacent_z (i + 1 ) l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_happy_return_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| (i >= len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_80_spec_z l 1 ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_happy_return_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth (i - 2 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_80_spec_z l 0 ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_happy_return_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_80_spec_z l 0 ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_happy_return_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth 0 (app (l) ((cons (0) (nil)))) 0) = (Znth 1 (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (retval >= 3) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_80_spec_z l 0 ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_happy_return_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval < 3) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_80_spec_z l 0 ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_happy_partial_solve_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_happy_partial_solve_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval >= 3) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (retval >= 3) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (((s_pre + (0 * sizeof(CHAR) ) )) # Char  |-> (Znth 0 (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre 0 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_happy_partial_solve_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval >= 3) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (retval >= 3) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (((s_pre + (1 * sizeof(CHAR) ) )) # Char  |-> (Znth 1 (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre 1 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_happy_partial_solve_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_happy_partial_solve_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (((s_pre + ((i - 1 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre (i - 1 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_happy_partial_solve_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_happy_partial_solve_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) |] 
  &&  [| (i < len) |] 
  &&  [| (3 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_80_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (happy_prefix_z i l ) |] 
  &&  [| (happy_adjacent_z i l ) |]
  &&  (((s_pre + ((i - 2 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (i - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre (i - 2 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_is_happy_safety_wit_1 : is_happy_safety_wit_1.
Axiom proof_of_is_happy_safety_wit_2 : is_happy_safety_wit_2.
Axiom proof_of_is_happy_safety_wit_3 : is_happy_safety_wit_3.
Axiom proof_of_is_happy_safety_wit_4 : is_happy_safety_wit_4.
Axiom proof_of_is_happy_safety_wit_5 : is_happy_safety_wit_5.
Axiom proof_of_is_happy_safety_wit_6 : is_happy_safety_wit_6.
Axiom proof_of_is_happy_safety_wit_7 : is_happy_safety_wit_7.
Axiom proof_of_is_happy_safety_wit_8 : is_happy_safety_wit_8.
Axiom proof_of_is_happy_safety_wit_9 : is_happy_safety_wit_9.
Axiom proof_of_is_happy_safety_wit_10 : is_happy_safety_wit_10.
Axiom proof_of_is_happy_safety_wit_11 : is_happy_safety_wit_11.
Axiom proof_of_is_happy_safety_wit_12 : is_happy_safety_wit_12.
Axiom proof_of_is_happy_safety_wit_13 : is_happy_safety_wit_13.
Axiom proof_of_is_happy_safety_wit_14 : is_happy_safety_wit_14.
Axiom proof_of_is_happy_entail_wit_1 : is_happy_entail_wit_1.
Axiom proof_of_is_happy_entail_wit_2 : is_happy_entail_wit_2.
Axiom proof_of_is_happy_return_wit_1 : is_happy_return_wit_1.
Axiom proof_of_is_happy_return_wit_2 : is_happy_return_wit_2.
Axiom proof_of_is_happy_return_wit_3 : is_happy_return_wit_3.
Axiom proof_of_is_happy_return_wit_4 : is_happy_return_wit_4.
Axiom proof_of_is_happy_return_wit_5 : is_happy_return_wit_5.
Axiom proof_of_is_happy_partial_solve_wit_1 : is_happy_partial_solve_wit_1.
Axiom proof_of_is_happy_partial_solve_wit_2 : is_happy_partial_solve_wit_2.
Axiom proof_of_is_happy_partial_solve_wit_3 : is_happy_partial_solve_wit_3.
Axiom proof_of_is_happy_partial_solve_wit_4 : is_happy_partial_solve_wit_4.
Axiom proof_of_is_happy_partial_solve_wit_5 : is_happy_partial_solve_wit_5.
Axiom proof_of_is_happy_partial_solve_wit_6 : is_happy_partial_solve_wit_6.
Axiom proof_of_is_happy_partial_solve_wit_7 : is_happy_partial_solve_wit_7.

End VC_Correct.
