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
Require Import coins_119.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function match_parens -----*)

Definition match_parens_safety_wit_1 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |]
  &&  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_2 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |]
  &&  ((( &( "can" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_parens_safety_wit_3 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = len2) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (retval = len1) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "n2" ) )) # Int  |-> retval_2)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "can" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_4 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (40 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 40) |]
.

Definition match_parens_safety_wit_5 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition match_parens_safety_wit_6 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_parens_safety_wit_7 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (41 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 41) |]
.

Definition match_parens_safety_wit_8 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((count - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count - 1 )) |]
.

Definition match_parens_safety_wit_9 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_parens_safety_wit_10 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_11 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_12 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_13 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_14 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_15 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_16 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_17 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_18 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count >= 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_19 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> 0)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_20 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> 0)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_21 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> 0)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_22 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (i >= len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_23 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (40 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 40) |]
.

Definition match_parens_safety_wit_24 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition match_parens_safety_wit_25 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_parens_safety_wit_26 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (41 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 41) |]
.

Definition match_parens_safety_wit_27 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((count - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count - 1 )) |]
.

Definition match_parens_safety_wit_28 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_parens_safety_wit_29 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_30 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_31 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_32 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_33 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_34 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_35 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_36 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_37 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count >= 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_38 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> 0)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_39 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> 0)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_40 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> 0)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_41 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (i >= len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_42 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count <> 0) |] 
  &&  [| (i >= len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_43 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count = 0) |] 
  &&  [| (i >= len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_parens_safety_wit_44 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (can = 1) |] 
  &&  [| (count = 0) |] 
  &&  [| (i >= len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_parens_safety_wit_45 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (count: Z) (can: Z) (i: Z) ,
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (count = 0) |] 
  &&  [| (can = 0) |] 
  &&  [| (i = len2) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |]
  &&  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_46 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (count: Z) (can: Z) (i: Z) ,
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (count = 0) |] 
  &&  [| (can = 0) |] 
  &&  [| (i = len2) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |]
  &&  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_parens_safety_wit_47 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (count: Z) (can: Z) (i: Z) ,
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (count = 0) |] 
  &&  [| (can = 0) |] 
  &&  [| (i = len2) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |]
  &&  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "can" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_48 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (40 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 40) |]
.

Definition match_parens_safety_wit_49 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition match_parens_safety_wit_50 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_parens_safety_wit_51 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (41 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 41) |]
.

Definition match_parens_safety_wit_52 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((count - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count - 1 )) |]
.

Definition match_parens_safety_wit_53 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_parens_safety_wit_54 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_55 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_56 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_57 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_58 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_59 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_60 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_61 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_62 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count >= 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_63 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> 0)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_64 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> 0)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_65 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> 0)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_66 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (i >= len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_67 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (40 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 40) |]
.

Definition match_parens_safety_wit_68 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition match_parens_safety_wit_69 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_parens_safety_wit_70 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (41 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 41) |]
.

Definition match_parens_safety_wit_71 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((count - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count - 1 )) |]
.

Definition match_parens_safety_wit_72 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_parens_safety_wit_73 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_74 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_75 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_76 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_77 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_78 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_safety_wit_79 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_80 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_81 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count >= 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_82 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> 0)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_83 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count - 1 ))
  **  ((( &( "can" ) )) # Int  |-> 0)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_84 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "can" ) )) # Int  |-> 0)
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition match_parens_safety_wit_85 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (i >= len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_parens_safety_wit_86 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (can = 1) |] 
  &&  [| (i >= len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition match_parens_safety_wit_87 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (can <> 1) |] 
  &&  [| (i >= len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "can" ) )) # Int  |-> can)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition match_parens_entail_wit_1 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = len2) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (retval = len1) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "n2" ) )) # Int  |-> retval_2)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "n1" ) )) # Int  |-> retval)
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len1) |] 
  &&  [| ((-0) <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 = (paren_level_upto (0) ((app (l1) (l2))))) |] 
  &&  [| (1 = (paren_good_prefix_flag (0) ((app (l1) (l2))))) |]
  &&  ((( &( "n1" ) )) # Int  |-> len1)
  **  ((( &( "n2" ) )) # Int  |-> len2)
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_2_1 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len1) |] 
  &&  [| ((-(i + 1 )) <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (i + 1 )) |] 
  &&  [| ((count + 1 ) = (paren_level_upto ((i + 1 )) ((app (l1) (l2))))) |] 
  &&  [| (0 = (paren_good_prefix_flag ((i + 1 )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_2_2 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len1) |] 
  &&  [| ((-(i + 1 )) <= (count - 1 )) |] 
  &&  [| ((count - 1 ) <= (i + 1 )) |] 
  &&  [| ((count - 1 ) = (paren_level_upto ((i + 1 )) ((app (l1) (l2))))) |] 
  &&  [| (0 = (paren_good_prefix_flag ((i + 1 )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_2_3 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len1) |] 
  &&  [| ((-(i + 1 )) <= count) |] 
  &&  [| (count <= (i + 1 )) |] 
  &&  [| (count = (paren_level_upto ((i + 1 )) ((app (l1) (l2))))) |] 
  &&  [| (0 = (paren_good_prefix_flag ((i + 1 )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_2_4 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count >= 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len1) |] 
  &&  [| ((-(i + 1 )) <= count) |] 
  &&  [| (count <= (i + 1 )) |] 
  &&  [| (count = (paren_level_upto ((i + 1 )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((i + 1 )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_2_5 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len1) |] 
  &&  [| ((-(i + 1 )) <= (count - 1 )) |] 
  &&  [| ((count - 1 ) <= (i + 1 )) |] 
  &&  [| ((count - 1 ) = (paren_level_upto ((i + 1 )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((i + 1 )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_2_6 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len1) |] 
  &&  [| ((-(i + 1 )) <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (i + 1 )) |] 
  &&  [| ((count + 1 ) = (paren_level_upto ((i + 1 )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((i + 1 )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_3 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (i >= len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len2) |] 
  &&  [| ((-(len1 + 0 )) <= count) |] 
  &&  [| (count <= (len1 + 0 )) |] 
  &&  [| (count = (paren_level_upto ((len1 + 0 )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + 0 )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_4_1 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len2) |] 
  &&  [| ((-(len1 + (i + 1 ) )) <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (len1 + (i + 1 ) )) |] 
  &&  [| ((count + 1 ) = (paren_level_upto ((len1 + (i + 1 ) )) ((app (l1) (l2))))) |] 
  &&  [| (0 = (paren_good_prefix_flag ((len1 + (i + 1 ) )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_4_2 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len2) |] 
  &&  [| ((-(len1 + (i + 1 ) )) <= (count - 1 )) |] 
  &&  [| ((count - 1 ) <= (len1 + (i + 1 ) )) |] 
  &&  [| ((count - 1 ) = (paren_level_upto ((len1 + (i + 1 ) )) ((app (l1) (l2))))) |] 
  &&  [| (0 = (paren_good_prefix_flag ((len1 + (i + 1 ) )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_4_3 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len2) |] 
  &&  [| ((-(len1 + (i + 1 ) )) <= count) |] 
  &&  [| (count <= (len1 + (i + 1 ) )) |] 
  &&  [| (count = (paren_level_upto ((len1 + (i + 1 ) )) ((app (l1) (l2))))) |] 
  &&  [| (0 = (paren_good_prefix_flag ((len1 + (i + 1 ) )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_4_4 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count >= 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len2) |] 
  &&  [| ((-(len1 + (i + 1 ) )) <= count) |] 
  &&  [| (count <= (len1 + (i + 1 ) )) |] 
  &&  [| (count = (paren_level_upto ((len1 + (i + 1 ) )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + (i + 1 ) )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_4_5 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len2) |] 
  &&  [| ((-(len1 + (i + 1 ) )) <= (count - 1 )) |] 
  &&  [| ((count - 1 ) <= (len1 + (i + 1 ) )) |] 
  &&  [| ((count - 1 ) = (paren_level_upto ((len1 + (i + 1 ) )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + (i + 1 ) )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_4_6 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len2) |] 
  &&  [| ((-(len1 + (i + 1 ) )) <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (len1 + (i + 1 ) )) |] 
  &&  [| ((count + 1 ) = (paren_level_upto ((len1 + (i + 1 ) )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + (i + 1 ) )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_5 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (can <> 1) |] 
  &&  [| (count = 0) |] 
  &&  [| (i >= len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (count = 0) |] 
  &&  [| (can = 0) |] 
  &&  [| (i = len2) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_6 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (count: Z) (can: Z) (i: Z) ,
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (count = 0) |] 
  &&  [| (can = 0) |] 
  &&  [| (i = len2) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len2) |] 
  &&  [| ((-0) <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 = (paren_level_upto (0) ((app (l2) (l1))))) |] 
  &&  [| (1 = (paren_good_prefix_flag (0) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_7_1 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len2) |] 
  &&  [| ((-(i + 1 )) <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (i + 1 )) |] 
  &&  [| ((count + 1 ) = (paren_level_upto ((i + 1 )) ((app (l2) (l1))))) |] 
  &&  [| (0 = (paren_good_prefix_flag ((i + 1 )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_7_2 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len2) |] 
  &&  [| ((-(i + 1 )) <= (count - 1 )) |] 
  &&  [| ((count - 1 ) <= (i + 1 )) |] 
  &&  [| ((count - 1 ) = (paren_level_upto ((i + 1 )) ((app (l2) (l1))))) |] 
  &&  [| (0 = (paren_good_prefix_flag ((i + 1 )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_7_3 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count < 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len2) |] 
  &&  [| ((-(i + 1 )) <= count) |] 
  &&  [| (count <= (i + 1 )) |] 
  &&  [| (count = (paren_level_upto ((i + 1 )) ((app (l2) (l1))))) |] 
  &&  [| (0 = (paren_good_prefix_flag ((i + 1 )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_7_4 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count >= 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len2) |] 
  &&  [| ((-(i + 1 )) <= count) |] 
  &&  [| (count <= (i + 1 )) |] 
  &&  [| (count = (paren_level_upto ((i + 1 )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((i + 1 )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_7_5 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len2) |] 
  &&  [| ((-(i + 1 )) <= (count - 1 )) |] 
  &&  [| ((count - 1 ) <= (i + 1 )) |] 
  &&  [| ((count - 1 ) = (paren_level_upto ((i + 1 )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((i + 1 )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_7_6 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len2) |] 
  &&  [| ((-(i + 1 )) <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (i + 1 )) |] 
  &&  [| ((count + 1 ) = (paren_level_upto ((i + 1 )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((i + 1 )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_8 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (i >= len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len1) |] 
  &&  [| ((-(len2 + 0 )) <= count) |] 
  &&  [| (count <= (len2 + 0 )) |] 
  &&  [| (count = (paren_level_upto ((len2 + 0 )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + 0 )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_9_1 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len1) |] 
  &&  [| ((-(len2 + (i + 1 ) )) <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (len2 + (i + 1 ) )) |] 
  &&  [| ((count + 1 ) = (paren_level_upto ((len2 + (i + 1 ) )) ((app (l2) (l1))))) |] 
  &&  [| (0 = (paren_good_prefix_flag ((len2 + (i + 1 ) )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_9_2 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len1) |] 
  &&  [| ((-(len2 + (i + 1 ) )) <= (count - 1 )) |] 
  &&  [| ((count - 1 ) <= (len2 + (i + 1 ) )) |] 
  &&  [| ((count - 1 ) = (paren_level_upto ((len2 + (i + 1 ) )) ((app (l2) (l1))))) |] 
  &&  [| (0 = (paren_good_prefix_flag ((len2 + (i + 1 ) )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_9_3 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count < 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len1) |] 
  &&  [| ((-(len2 + (i + 1 ) )) <= count) |] 
  &&  [| (count <= (len2 + (i + 1 ) )) |] 
  &&  [| (count = (paren_level_upto ((len2 + (i + 1 ) )) ((app (l2) (l1))))) |] 
  &&  [| (0 = (paren_good_prefix_flag ((len2 + (i + 1 ) )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_9_4 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count >= 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len1) |] 
  &&  [| ((-(len2 + (i + 1 ) )) <= count) |] 
  &&  [| (count <= (len2 + (i + 1 ) )) |] 
  &&  [| (count = (paren_level_upto ((len2 + (i + 1 ) )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + (i + 1 ) )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_9_5 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count - 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len1) |] 
  &&  [| ((-(len2 + (i + 1 ) )) <= (count - 1 )) |] 
  &&  [| ((count - 1 ) <= (len2 + (i + 1 ) )) |] 
  &&  [| ((count - 1 ) = (paren_level_upto ((len2 + (i + 1 ) )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + (i + 1 ) )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_entail_wit_9_6 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((count + 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len1) |] 
  &&  [| ((-(len2 + (i + 1 ) )) <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (len2 + (i + 1 ) )) |] 
  &&  [| ((count + 1 ) = (paren_level_upto ((len2 + (i + 1 ) )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + (i + 1 ) )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_return_wit_1 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (can <> 1) |] 
  &&  [| (i >= len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (problem_119_spec_z l1 l2 0 ) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_return_wit_2 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (can = 1) |] 
  &&  [| (i >= len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (problem_119_spec_z l1 l2 1 ) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_return_wit_3 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (can = 1) |] 
  &&  [| (count = 0) |] 
  &&  [| (i >= len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (problem_119_spec_z l1 l2 1 ) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_return_wit_4 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (count <> 0) |] 
  &&  [| (i >= len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (problem_119_spec_z l1 l2 0 ) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_partial_solve_wit_1 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= (len2 + 1 )) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_partial_solve_wit_2 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) ,
  [| (retval = len1) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= (len1 + 1 )) |] 
  &&  [| (retval = len1) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition match_parens_partial_solve_wit_3 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (((s1_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s1_pre i 0 (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_partial_solve_wit_4 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l1) (l2))))) |]
  &&  (((s1_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s1_pre i 0 (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_partial_solve_wit_5 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (((s2_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l2) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s2_pre i 0 (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition match_parens_partial_solve_wit_6 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-(len1 + i )) <= count) |] 
  &&  [| (count <= (len1 + i )) |] 
  &&  [| (count = (paren_level_upto ((len1 + i )) ((app (l1) (l2))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len1 + i )) ((app (l1) (l2))))) |]
  &&  (((s2_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l2) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s2_pre i 0 (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition match_parens_partial_solve_wit_7 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (((s2_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l2) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s2_pre i 0 (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition match_parens_partial_solve_wit_8 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l2) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len1 + 1 )) |] 
  &&  [| (i < len2) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len2) |] 
  &&  [| ((-i) <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (paren_level_upto (i) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag (i) ((app (l2) (l1))))) |]
  &&  (((s2_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l2) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s2_pre i 0 (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition match_parens_partial_solve_wit_9 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (((s1_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s1_pre i 0 (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition match_parens_partial_solve_wit_10 := 
forall (s2_pre: Z) (s1_pre: Z) (len2: Z) (len1: Z) (l2: (@list Z)) (l1: (@list Z)) (can: Z) (count: Z) (i: Z) ,
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (CharArray.full s1_pre (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (0 <= (len2 + 1 )) |] 
  &&  [| (i < len1) |] 
  &&  [| (0 <= len1) |] 
  &&  [| (len1 < INT_MAX) |] 
  &&  [| (0 <= len2) |] 
  &&  [| (len2 < INT_MAX) |] 
  &&  [| ((len1 + len2 ) < INT_MAX) |] 
  &&  [| ((Zlength (l1)) = len1) |] 
  &&  [| ((Zlength (l2)) = len2) |] 
  &&  [| (problem_119_pre_z l1 l2 ) |] 
  &&  [| (ascii_range_z l1 ) |] 
  &&  [| (ascii_range_z l2 ) |] 
  &&  [| ((paren_level_upto ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| ((paren_good_prefix_flag ((len1 + len2 )) ((app (l1) (l2)))) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len1) |] 
  &&  [| ((-(len2 + i )) <= count) |] 
  &&  [| (count <= (len2 + i )) |] 
  &&  [| (count = (paren_level_upto ((len2 + i )) ((app (l2) (l1))))) |] 
  &&  [| (can = (paren_good_prefix_flag ((len2 + i )) ((app (l2) (l1))))) |]
  &&  (((s1_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s1_pre i 0 (len1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s2_pre (len2 + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_match_parens_safety_wit_1 : match_parens_safety_wit_1.
Axiom proof_of_match_parens_safety_wit_2 : match_parens_safety_wit_2.
Axiom proof_of_match_parens_safety_wit_3 : match_parens_safety_wit_3.
Axiom proof_of_match_parens_safety_wit_4 : match_parens_safety_wit_4.
Axiom proof_of_match_parens_safety_wit_5 : match_parens_safety_wit_5.
Axiom proof_of_match_parens_safety_wit_6 : match_parens_safety_wit_6.
Axiom proof_of_match_parens_safety_wit_7 : match_parens_safety_wit_7.
Axiom proof_of_match_parens_safety_wit_8 : match_parens_safety_wit_8.
Axiom proof_of_match_parens_safety_wit_9 : match_parens_safety_wit_9.
Axiom proof_of_match_parens_safety_wit_10 : match_parens_safety_wit_10.
Axiom proof_of_match_parens_safety_wit_11 : match_parens_safety_wit_11.
Axiom proof_of_match_parens_safety_wit_12 : match_parens_safety_wit_12.
Axiom proof_of_match_parens_safety_wit_13 : match_parens_safety_wit_13.
Axiom proof_of_match_parens_safety_wit_14 : match_parens_safety_wit_14.
Axiom proof_of_match_parens_safety_wit_15 : match_parens_safety_wit_15.
Axiom proof_of_match_parens_safety_wit_16 : match_parens_safety_wit_16.
Axiom proof_of_match_parens_safety_wit_17 : match_parens_safety_wit_17.
Axiom proof_of_match_parens_safety_wit_18 : match_parens_safety_wit_18.
Axiom proof_of_match_parens_safety_wit_19 : match_parens_safety_wit_19.
Axiom proof_of_match_parens_safety_wit_20 : match_parens_safety_wit_20.
Axiom proof_of_match_parens_safety_wit_21 : match_parens_safety_wit_21.
Axiom proof_of_match_parens_safety_wit_22 : match_parens_safety_wit_22.
Axiom proof_of_match_parens_safety_wit_23 : match_parens_safety_wit_23.
Axiom proof_of_match_parens_safety_wit_24 : match_parens_safety_wit_24.
Axiom proof_of_match_parens_safety_wit_25 : match_parens_safety_wit_25.
Axiom proof_of_match_parens_safety_wit_26 : match_parens_safety_wit_26.
Axiom proof_of_match_parens_safety_wit_27 : match_parens_safety_wit_27.
Axiom proof_of_match_parens_safety_wit_28 : match_parens_safety_wit_28.
Axiom proof_of_match_parens_safety_wit_29 : match_parens_safety_wit_29.
Axiom proof_of_match_parens_safety_wit_30 : match_parens_safety_wit_30.
Axiom proof_of_match_parens_safety_wit_31 : match_parens_safety_wit_31.
Axiom proof_of_match_parens_safety_wit_32 : match_parens_safety_wit_32.
Axiom proof_of_match_parens_safety_wit_33 : match_parens_safety_wit_33.
Axiom proof_of_match_parens_safety_wit_34 : match_parens_safety_wit_34.
Axiom proof_of_match_parens_safety_wit_35 : match_parens_safety_wit_35.
Axiom proof_of_match_parens_safety_wit_36 : match_parens_safety_wit_36.
Axiom proof_of_match_parens_safety_wit_37 : match_parens_safety_wit_37.
Axiom proof_of_match_parens_safety_wit_38 : match_parens_safety_wit_38.
Axiom proof_of_match_parens_safety_wit_39 : match_parens_safety_wit_39.
Axiom proof_of_match_parens_safety_wit_40 : match_parens_safety_wit_40.
Axiom proof_of_match_parens_safety_wit_41 : match_parens_safety_wit_41.
Axiom proof_of_match_parens_safety_wit_42 : match_parens_safety_wit_42.
Axiom proof_of_match_parens_safety_wit_43 : match_parens_safety_wit_43.
Axiom proof_of_match_parens_safety_wit_44 : match_parens_safety_wit_44.
Axiom proof_of_match_parens_safety_wit_45 : match_parens_safety_wit_45.
Axiom proof_of_match_parens_safety_wit_46 : match_parens_safety_wit_46.
Axiom proof_of_match_parens_safety_wit_47 : match_parens_safety_wit_47.
Axiom proof_of_match_parens_safety_wit_48 : match_parens_safety_wit_48.
Axiom proof_of_match_parens_safety_wit_49 : match_parens_safety_wit_49.
Axiom proof_of_match_parens_safety_wit_50 : match_parens_safety_wit_50.
Axiom proof_of_match_parens_safety_wit_51 : match_parens_safety_wit_51.
Axiom proof_of_match_parens_safety_wit_52 : match_parens_safety_wit_52.
Axiom proof_of_match_parens_safety_wit_53 : match_parens_safety_wit_53.
Axiom proof_of_match_parens_safety_wit_54 : match_parens_safety_wit_54.
Axiom proof_of_match_parens_safety_wit_55 : match_parens_safety_wit_55.
Axiom proof_of_match_parens_safety_wit_56 : match_parens_safety_wit_56.
Axiom proof_of_match_parens_safety_wit_57 : match_parens_safety_wit_57.
Axiom proof_of_match_parens_safety_wit_58 : match_parens_safety_wit_58.
Axiom proof_of_match_parens_safety_wit_59 : match_parens_safety_wit_59.
Axiom proof_of_match_parens_safety_wit_60 : match_parens_safety_wit_60.
Axiom proof_of_match_parens_safety_wit_61 : match_parens_safety_wit_61.
Axiom proof_of_match_parens_safety_wit_62 : match_parens_safety_wit_62.
Axiom proof_of_match_parens_safety_wit_63 : match_parens_safety_wit_63.
Axiom proof_of_match_parens_safety_wit_64 : match_parens_safety_wit_64.
Axiom proof_of_match_parens_safety_wit_65 : match_parens_safety_wit_65.
Axiom proof_of_match_parens_safety_wit_66 : match_parens_safety_wit_66.
Axiom proof_of_match_parens_safety_wit_67 : match_parens_safety_wit_67.
Axiom proof_of_match_parens_safety_wit_68 : match_parens_safety_wit_68.
Axiom proof_of_match_parens_safety_wit_69 : match_parens_safety_wit_69.
Axiom proof_of_match_parens_safety_wit_70 : match_parens_safety_wit_70.
Axiom proof_of_match_parens_safety_wit_71 : match_parens_safety_wit_71.
Axiom proof_of_match_parens_safety_wit_72 : match_parens_safety_wit_72.
Axiom proof_of_match_parens_safety_wit_73 : match_parens_safety_wit_73.
Axiom proof_of_match_parens_safety_wit_74 : match_parens_safety_wit_74.
Axiom proof_of_match_parens_safety_wit_75 : match_parens_safety_wit_75.
Axiom proof_of_match_parens_safety_wit_76 : match_parens_safety_wit_76.
Axiom proof_of_match_parens_safety_wit_77 : match_parens_safety_wit_77.
Axiom proof_of_match_parens_safety_wit_78 : match_parens_safety_wit_78.
Axiom proof_of_match_parens_safety_wit_79 : match_parens_safety_wit_79.
Axiom proof_of_match_parens_safety_wit_80 : match_parens_safety_wit_80.
Axiom proof_of_match_parens_safety_wit_81 : match_parens_safety_wit_81.
Axiom proof_of_match_parens_safety_wit_82 : match_parens_safety_wit_82.
Axiom proof_of_match_parens_safety_wit_83 : match_parens_safety_wit_83.
Axiom proof_of_match_parens_safety_wit_84 : match_parens_safety_wit_84.
Axiom proof_of_match_parens_safety_wit_85 : match_parens_safety_wit_85.
Axiom proof_of_match_parens_safety_wit_86 : match_parens_safety_wit_86.
Axiom proof_of_match_parens_safety_wit_87 : match_parens_safety_wit_87.
Axiom proof_of_match_parens_entail_wit_1 : match_parens_entail_wit_1.
Axiom proof_of_match_parens_entail_wit_2_1 : match_parens_entail_wit_2_1.
Axiom proof_of_match_parens_entail_wit_2_2 : match_parens_entail_wit_2_2.
Axiom proof_of_match_parens_entail_wit_2_3 : match_parens_entail_wit_2_3.
Axiom proof_of_match_parens_entail_wit_2_4 : match_parens_entail_wit_2_4.
Axiom proof_of_match_parens_entail_wit_2_5 : match_parens_entail_wit_2_5.
Axiom proof_of_match_parens_entail_wit_2_6 : match_parens_entail_wit_2_6.
Axiom proof_of_match_parens_entail_wit_3 : match_parens_entail_wit_3.
Axiom proof_of_match_parens_entail_wit_4_1 : match_parens_entail_wit_4_1.
Axiom proof_of_match_parens_entail_wit_4_2 : match_parens_entail_wit_4_2.
Axiom proof_of_match_parens_entail_wit_4_3 : match_parens_entail_wit_4_3.
Axiom proof_of_match_parens_entail_wit_4_4 : match_parens_entail_wit_4_4.
Axiom proof_of_match_parens_entail_wit_4_5 : match_parens_entail_wit_4_5.
Axiom proof_of_match_parens_entail_wit_4_6 : match_parens_entail_wit_4_6.
Axiom proof_of_match_parens_entail_wit_5 : match_parens_entail_wit_5.
Axiom proof_of_match_parens_entail_wit_6 : match_parens_entail_wit_6.
Axiom proof_of_match_parens_entail_wit_7_1 : match_parens_entail_wit_7_1.
Axiom proof_of_match_parens_entail_wit_7_2 : match_parens_entail_wit_7_2.
Axiom proof_of_match_parens_entail_wit_7_3 : match_parens_entail_wit_7_3.
Axiom proof_of_match_parens_entail_wit_7_4 : match_parens_entail_wit_7_4.
Axiom proof_of_match_parens_entail_wit_7_5 : match_parens_entail_wit_7_5.
Axiom proof_of_match_parens_entail_wit_7_6 : match_parens_entail_wit_7_6.
Axiom proof_of_match_parens_entail_wit_8 : match_parens_entail_wit_8.
Axiom proof_of_match_parens_entail_wit_9_1 : match_parens_entail_wit_9_1.
Axiom proof_of_match_parens_entail_wit_9_2 : match_parens_entail_wit_9_2.
Axiom proof_of_match_parens_entail_wit_9_3 : match_parens_entail_wit_9_3.
Axiom proof_of_match_parens_entail_wit_9_4 : match_parens_entail_wit_9_4.
Axiom proof_of_match_parens_entail_wit_9_5 : match_parens_entail_wit_9_5.
Axiom proof_of_match_parens_entail_wit_9_6 : match_parens_entail_wit_9_6.
Axiom proof_of_match_parens_return_wit_1 : match_parens_return_wit_1.
Axiom proof_of_match_parens_return_wit_2 : match_parens_return_wit_2.
Axiom proof_of_match_parens_return_wit_3 : match_parens_return_wit_3.
Axiom proof_of_match_parens_return_wit_4 : match_parens_return_wit_4.
Axiom proof_of_match_parens_partial_solve_wit_1 : match_parens_partial_solve_wit_1.
Axiom proof_of_match_parens_partial_solve_wit_2 : match_parens_partial_solve_wit_2.
Axiom proof_of_match_parens_partial_solve_wit_3 : match_parens_partial_solve_wit_3.
Axiom proof_of_match_parens_partial_solve_wit_4 : match_parens_partial_solve_wit_4.
Axiom proof_of_match_parens_partial_solve_wit_5 : match_parens_partial_solve_wit_5.
Axiom proof_of_match_parens_partial_solve_wit_6 : match_parens_partial_solve_wit_6.
Axiom proof_of_match_parens_partial_solve_wit_7 : match_parens_partial_solve_wit_7.
Axiom proof_of_match_parens_partial_solve_wit_8 : match_parens_partial_solve_wit_8.
Axiom proof_of_match_parens_partial_solve_wit_9 : match_parens_partial_solve_wit_9.
Axiom proof_of_match_parens_partial_solve_wit_10 : match_parens_partial_solve_wit_10.

End VC_Correct.
