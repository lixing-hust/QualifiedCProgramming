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
Require Import coins_54.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function same_chars -----*)

Definition same_chars_safety_wit_1 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = n1) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (retval = n0) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (0 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "len1" ) )) # Int  |-> retval_2)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "len0" ) )) # Int  |-> retval)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition same_chars_safety_wit_2 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| ~((char_in_z (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 )) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (i < n0) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (same_chars_prefix_z i l0 l1 ) |]
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l0) ((cons (0) (nil)))) 0))
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition same_chars_safety_wit_3 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (char_in_z (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 ) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (i < n0) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (same_chars_prefix_z i l0 l1 ) |]
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l0) ((cons (0) (nil)))) 0))
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition same_chars_safety_wit_4 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ~((char_in_z (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 )) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (i < n0) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (same_chars_prefix_z i l0 l1 ) |]
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l0) ((cons (0) (nil)))) 0))
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| False |]
.

Definition same_chars_safety_wit_5 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (char_in_z (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 ) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (i < n0) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (same_chars_prefix_z i l0 l1 ) |]
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l0) ((cons (0) (nil)))) 0))
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| False |]
.

Definition same_chars_safety_wit_6 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ~((char_in_z (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 )) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (i < n0) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (same_chars_prefix_z i l0 l1 ) |]
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l0) ((cons (0) (nil)))) 0))
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition same_chars_safety_wit_7 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (char_in_z (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 ) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (i < n0) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (same_chars_prefix_z i l0 l1 ) |]
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition same_chars_safety_wit_8 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  [| (i >= n0) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (same_chars_prefix_z i l0 l1 ) |]
  &&  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition same_chars_safety_wit_9 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| ~((char_in_z (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 )) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (i < n1) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n1) |] 
  &&  [| (same_chars_prefix_z i l1 l0 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition same_chars_safety_wit_10 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (char_in_z (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 ) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (i < n1) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n1) |] 
  &&  [| (same_chars_prefix_z i l1 l0 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition same_chars_safety_wit_11 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ~((char_in_z (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 )) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (i < n1) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n1) |] 
  &&  [| (same_chars_prefix_z i l1 l0 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| False |]
.

Definition same_chars_safety_wit_12 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (char_in_z (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 ) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (i < n1) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n1) |] 
  &&  [| (same_chars_prefix_z i l1 l0 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| False |]
.

Definition same_chars_safety_wit_13 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ~((char_in_z (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 )) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (i < n1) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n1) |] 
  &&  [| (same_chars_prefix_z i l1 l0 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition same_chars_safety_wit_14 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (char_in_z (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 ) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (i < n1) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n1) |] 
  &&  [| (same_chars_prefix_z i l1 l0 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition same_chars_safety_wit_15 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  [| (i >= n1) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n1) |] 
  &&  [| (same_chars_prefix_z i l1 l0 ) |]
  &&  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition same_chars_entail_wit_1 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = n1) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (retval = n0) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (0 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |]
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "len1" ) )) # Int  |-> retval_2)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "len0" ) )) # Int  |-> retval)
|--
  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= n0) |] 
  &&  [| (same_chars_prefix_z 0 l0 l1 ) |]
  &&  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition same_chars_entail_wit_2 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (char_in_z (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 ) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (i < n0) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (same_chars_prefix_z i l0 l1 ) |]
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n0) |] 
  &&  [| (same_chars_prefix_z (i + 1 ) l0 l1 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition same_chars_entail_wit_3 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  [| (i >= n0) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (same_chars_prefix_z i l0 l1 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (same_chars_prefix_z 0 l1 l0 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition same_chars_entail_wit_4 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (char_in_z (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 ) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (i < n1) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n1) |] 
  &&  [| (same_chars_prefix_z i l1 l0 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n1) |] 
  &&  [| (same_chars_prefix_z (i + 1 ) l1 l0 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition same_chars_return_wit_1 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  [| (i >= n1) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n1) |] 
  &&  [| (same_chars_prefix_z i l1 l0 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (problem_54_spec_z l0 l1 1 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition same_chars_return_wit_2 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ~((char_in_z (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 )) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (i < n1) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n1) |] 
  &&  [| (same_chars_prefix_z i l1 l0 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (problem_54_spec_z l0 l1 0 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition same_chars_return_wit_3 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| ~((char_in_z (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 )) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (i < n0) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (same_chars_prefix_z i l0 l1 ) |]
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
|--
  [| (problem_54_spec_z l0 l1 0 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition same_chars_partial_solve_wit_1 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) ,
  [| (0 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= (n1 + 1 )) |] 
  &&  [| (0 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition same_chars_partial_solve_wit_2 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (retval: Z) ,
  [| (retval = n0) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (0 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= (n0 + 1 )) |] 
  &&  [| (retval = n0) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (0 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (0 <= n1) |] 
  &&  [| (n1 < INT_MAX) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |]
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
.

Definition same_chars_partial_solve_wit_3 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  [| (i < n0) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (same_chars_prefix_z i l0 l1 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= (n1 + 1 )) |] 
  &&  [| (i < n0) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (same_chars_prefix_z i l0 l1 ) |]
  &&  (((s0_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l0) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s0_pre i 0 (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition same_chars_partial_solve_wit_4 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  [| (0 <= (n1 + 1 )) |] 
  &&  [| (i < n0) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (same_chars_prefix_z i l0 l1 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= (n0 + 1 )) |] 
  &&  [| (0 <= (n1 + 1 )) |] 
  &&  [| (i < n0) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (same_chars_prefix_z i l0 l1 ) |]
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
.

Definition same_chars_partial_solve_wit_5 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  [| (i < n1) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n1) |] 
  &&  [| (same_chars_prefix_z i l1 l0 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= (n0 + 1 )) |] 
  &&  [| (i < n1) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n1) |] 
  &&  [| (same_chars_prefix_z i l1 l0 ) |]
  &&  (((s1_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s1_pre i 0 (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
.

Definition same_chars_partial_solve_wit_6 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  [| (0 <= (n0 + 1 )) |] 
  &&  [| (i < n1) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n1) |] 
  &&  [| (same_chars_prefix_z i l1 l0 ) |]
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
|--
  [| (0 <= (n1 + 1 )) |] 
  &&  [| (0 <= (n0 + 1 )) |] 
  &&  [| (i < n1) |] 
  &&  [| ((Zlength (l0)) = n0) |] 
  &&  [| ((Zlength (l1)) = n1) |] 
  &&  [| (problem_54_pre_z l0 l1 ) |] 
  &&  [| (ascii_range_z l0 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (no_zero_z l0 ) |] 
  &&  [| (no_zero_z l1 ) |] 
  &&  [| (same_chars_all_z l0 l1 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n1) |] 
  &&  [| (same_chars_prefix_z i l1 l0 ) |]
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_same_chars_safety_wit_1 : same_chars_safety_wit_1.
Axiom proof_of_same_chars_safety_wit_2 : same_chars_safety_wit_2.
Axiom proof_of_same_chars_safety_wit_3 : same_chars_safety_wit_3.
Axiom proof_of_same_chars_safety_wit_4 : same_chars_safety_wit_4.
Axiom proof_of_same_chars_safety_wit_5 : same_chars_safety_wit_5.
Axiom proof_of_same_chars_safety_wit_6 : same_chars_safety_wit_6.
Axiom proof_of_same_chars_safety_wit_7 : same_chars_safety_wit_7.
Axiom proof_of_same_chars_safety_wit_8 : same_chars_safety_wit_8.
Axiom proof_of_same_chars_safety_wit_9 : same_chars_safety_wit_9.
Axiom proof_of_same_chars_safety_wit_10 : same_chars_safety_wit_10.
Axiom proof_of_same_chars_safety_wit_11 : same_chars_safety_wit_11.
Axiom proof_of_same_chars_safety_wit_12 : same_chars_safety_wit_12.
Axiom proof_of_same_chars_safety_wit_13 : same_chars_safety_wit_13.
Axiom proof_of_same_chars_safety_wit_14 : same_chars_safety_wit_14.
Axiom proof_of_same_chars_safety_wit_15 : same_chars_safety_wit_15.
Axiom proof_of_same_chars_entail_wit_1 : same_chars_entail_wit_1.
Axiom proof_of_same_chars_entail_wit_2 : same_chars_entail_wit_2.
Axiom proof_of_same_chars_entail_wit_3 : same_chars_entail_wit_3.
Axiom proof_of_same_chars_entail_wit_4 : same_chars_entail_wit_4.
Axiom proof_of_same_chars_return_wit_1 : same_chars_return_wit_1.
Axiom proof_of_same_chars_return_wit_2 : same_chars_return_wit_2.
Axiom proof_of_same_chars_return_wit_3 : same_chars_return_wit_3.
Axiom proof_of_same_chars_partial_solve_wit_1 : same_chars_partial_solve_wit_1.
Axiom proof_of_same_chars_partial_solve_wit_2 : same_chars_partial_solve_wit_2.
Axiom proof_of_same_chars_partial_solve_wit_3 : same_chars_partial_solve_wit_3.
Axiom proof_of_same_chars_partial_solve_wit_4 : same_chars_partial_solve_wit_4.
Axiom proof_of_same_chars_partial_solve_wit_5 : same_chars_partial_solve_wit_5.
Axiom proof_of_same_chars_partial_solve_wit_6 : same_chars_partial_solve_wit_6.

End VC_Correct.
