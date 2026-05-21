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
Require Import coins_61.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function correct_bracketing -----*)

Definition correct_bracketing_safety_wit_1 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |]
  &&  ((( &( "level" ) )) # Int  |->_)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition correct_bracketing_safety_wit_2 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition correct_bracketing_safety_wit_3 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  [| (40 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 40) |]
.

Definition correct_bracketing_safety_wit_4 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  [| ((level + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (level + 1 )) |]
.

Definition correct_bracketing_safety_wit_5 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition correct_bracketing_safety_wit_6 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  [| (41 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 41) |]
.

Definition correct_bracketing_safety_wit_7 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  [| ((level - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (level - 1 )) |]
.

Definition correct_bracketing_safety_wit_8 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition correct_bracketing_safety_wit_9 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition correct_bracketing_safety_wit_10 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition correct_bracketing_safety_wit_11 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level + 1 ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition correct_bracketing_safety_wit_12 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| (level < 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  [| False |]
.

Definition correct_bracketing_safety_wit_13 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((level + 1 ) < 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level + 1 ))
|--
  [| False |]
.

Definition correct_bracketing_safety_wit_14 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((level - 1 ) < 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition correct_bracketing_safety_wit_15 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((level + 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition correct_bracketing_safety_wit_16 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((level - 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition correct_bracketing_safety_wit_17 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| (level >= 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition correct_bracketing_safety_wit_18 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition correct_bracketing_safety_wit_19 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| (level <> 0) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition correct_bracketing_safety_wit_20 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| (level = 0) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition correct_bracketing_entail_wit_1 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 = (paren_level_upto (0) (l))) |] 
  &&  [| (paren_nonnegative_prefix 0 l ) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition correct_bracketing_entail_wit_2_1 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| (level >= 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 41) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= (i + 1 )) |] 
  &&  [| (level = (paren_level_upto ((i + 1 )) (l))) |] 
  &&  [| (paren_nonnegative_prefix (i + 1 ) l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition correct_bracketing_entail_wit_2_2 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((level - 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (level - 1 )) |] 
  &&  [| ((level - 1 ) <= (i + 1 )) |] 
  &&  [| ((level - 1 ) = (paren_level_upto ((i + 1 )) (l))) |] 
  &&  [| (paren_nonnegative_prefix (i + 1 ) l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition correct_bracketing_entail_wit_2_3 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((level + 1 ) >= 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (level + 1 )) |] 
  &&  [| ((level + 1 ) <= (i + 1 )) |] 
  &&  [| ((level + 1 ) = (paren_level_upto ((i + 1 )) (l))) |] 
  &&  [| (paren_nonnegative_prefix (i + 1 ) l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition correct_bracketing_return_wit_1 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| (level = 0) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_61_spec_z l 1 ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition correct_bracketing_return_wit_2 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| (level <> 0) |] 
  &&  [| (i >= len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_61_spec_z l 0 ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition correct_bracketing_return_wit_3 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((level - 1 ) < 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 41) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_61_spec_z l 0 ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition correct_bracketing_partial_solve_wit_1 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition correct_bracketing_partial_solve_wit_2 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (((brackets_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i brackets_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition correct_bracketing_partial_solve_wit_3 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_61_pre_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (level = (paren_level_upto (i) (l))) |] 
  &&  [| (paren_nonnegative_prefix i l ) |]
  &&  (((brackets_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i brackets_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_correct_bracketing_safety_wit_1 : correct_bracketing_safety_wit_1.
Axiom proof_of_correct_bracketing_safety_wit_2 : correct_bracketing_safety_wit_2.
Axiom proof_of_correct_bracketing_safety_wit_3 : correct_bracketing_safety_wit_3.
Axiom proof_of_correct_bracketing_safety_wit_4 : correct_bracketing_safety_wit_4.
Axiom proof_of_correct_bracketing_safety_wit_5 : correct_bracketing_safety_wit_5.
Axiom proof_of_correct_bracketing_safety_wit_6 : correct_bracketing_safety_wit_6.
Axiom proof_of_correct_bracketing_safety_wit_7 : correct_bracketing_safety_wit_7.
Axiom proof_of_correct_bracketing_safety_wit_8 : correct_bracketing_safety_wit_8.
Axiom proof_of_correct_bracketing_safety_wit_9 : correct_bracketing_safety_wit_9.
Axiom proof_of_correct_bracketing_safety_wit_10 : correct_bracketing_safety_wit_10.
Axiom proof_of_correct_bracketing_safety_wit_11 : correct_bracketing_safety_wit_11.
Axiom proof_of_correct_bracketing_safety_wit_12 : correct_bracketing_safety_wit_12.
Axiom proof_of_correct_bracketing_safety_wit_13 : correct_bracketing_safety_wit_13.
Axiom proof_of_correct_bracketing_safety_wit_14 : correct_bracketing_safety_wit_14.
Axiom proof_of_correct_bracketing_safety_wit_15 : correct_bracketing_safety_wit_15.
Axiom proof_of_correct_bracketing_safety_wit_16 : correct_bracketing_safety_wit_16.
Axiom proof_of_correct_bracketing_safety_wit_17 : correct_bracketing_safety_wit_17.
Axiom proof_of_correct_bracketing_safety_wit_18 : correct_bracketing_safety_wit_18.
Axiom proof_of_correct_bracketing_safety_wit_19 : correct_bracketing_safety_wit_19.
Axiom proof_of_correct_bracketing_safety_wit_20 : correct_bracketing_safety_wit_20.
Axiom proof_of_correct_bracketing_entail_wit_1 : correct_bracketing_entail_wit_1.
Axiom proof_of_correct_bracketing_entail_wit_2_1 : correct_bracketing_entail_wit_2_1.
Axiom proof_of_correct_bracketing_entail_wit_2_2 : correct_bracketing_entail_wit_2_2.
Axiom proof_of_correct_bracketing_entail_wit_2_3 : correct_bracketing_entail_wit_2_3.
Axiom proof_of_correct_bracketing_return_wit_1 : correct_bracketing_return_wit_1.
Axiom proof_of_correct_bracketing_return_wit_2 : correct_bracketing_return_wit_2.
Axiom proof_of_correct_bracketing_return_wit_3 : correct_bracketing_return_wit_3.
Axiom proof_of_correct_bracketing_partial_solve_wit_1 : correct_bracketing_partial_solve_wit_1.
Axiom proof_of_correct_bracketing_partial_solve_wit_2 : correct_bracketing_partial_solve_wit_2.
Axiom proof_of_correct_bracketing_partial_solve_wit_3 : correct_bracketing_partial_solve_wit_3.

End VC_Correct.
