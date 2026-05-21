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
Require Import coins_51.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function remove_vowels -----*)

Definition remove_vowels_safety_wit_1 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition remove_vowels_safety_wit_2 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  [| ((retval + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval + 1 )) |]
.

Definition remove_vowels_safety_wit_3 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition remove_vowels_safety_wit_4 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition remove_vowels_safety_wit_5 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition remove_vowels_safety_wit_6 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| (69 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 69) |]
.

Definition remove_vowels_safety_wit_7 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| (73 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 73) |]
.

Definition remove_vowels_safety_wit_8 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| (79 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 79) |]
.

Definition remove_vowels_safety_wit_9 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| (85 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 85) |]
.

Definition remove_vowels_safety_wit_10 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition remove_vowels_safety_wit_11 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| (101 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 101) |]
.

Definition remove_vowels_safety_wit_12 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| (105 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 105) |]
.

Definition remove_vowels_safety_wit_13 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| (111 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 111) |]
.

Definition remove_vowels_safety_wit_14 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| (117 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 117) |]
.

Definition remove_vowels_safety_wit_15 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full out (j + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (j + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition remove_vowels_safety_wit_16 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full out (j + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (j + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition remove_vowels_safety_wit_17 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full out (j + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (j + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_vowels_safety_wit_18 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 117) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_vowels_safety_wit_19 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_vowels_safety_wit_20 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_vowels_safety_wit_21 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_vowels_safety_wit_22 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_vowels_safety_wit_23 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_vowels_safety_wit_24 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_vowels_safety_wit_25 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_vowels_safety_wit_26 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_vowels_safety_wit_27 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_vowels_safety_wit_28 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition remove_vowels_entail_wit_1 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval_2 = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  (CharArray.undef_full retval (retval_2 + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| ((Zlength (out_l)) = 0) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (0) (l))) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (len + 1 ) )
.

Definition remove_vowels_entail_wit_2_1 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l_2)) = j) |] 
  &&  [| (out_l_2 = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition remove_vowels_entail_wit_2_2 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l_2)) = j) |] 
  &&  [| (out_l_2 = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition remove_vowels_entail_wit_2_3 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l_2)) = j) |] 
  &&  [| (out_l_2 = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition remove_vowels_entail_wit_2_4 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l_2)) = j) |] 
  &&  [| (out_l_2 = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition remove_vowels_entail_wit_2_5 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l_2)) = j) |] 
  &&  [| (out_l_2 = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition remove_vowels_entail_wit_2_6 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l_2)) = j) |] 
  &&  [| (out_l_2 = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition remove_vowels_entail_wit_2_7 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l_2)) = j) |] 
  &&  [| (out_l_2 = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition remove_vowels_entail_wit_2_8 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l_2)) = j) |] 
  &&  [| (out_l_2 = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition remove_vowels_entail_wit_2_9 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l_2)) = j) |] 
  &&  [| (out_l_2 = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition remove_vowels_entail_wit_2_10 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 117) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l_2)) = j) |] 
  &&  [| (out_l_2 = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition remove_vowels_entail_wit_2_11 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l_2)) = j) |] 
  &&  [| (out_l_2 = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full out (j + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (j + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = (j + 1 )) |] 
  &&  [| (out_l = (remove_vowels_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (j + 1 ) out_l )
  **  (CharArray.undef_seg out (j + 1 ) (len + 1 ) )
.

Definition remove_vowels_return_wit_1 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l_2)) = j) |] 
  &&  [| (out_l_2 = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full out (j + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (j + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z))  (out_len: Z) ,
  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (problem_51_spec_z l out_l ) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 1 ) )
.

Definition remove_vowels_partial_solve_wit_1 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition remove_vowels_partial_solve_wit_2_pure := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  [| ((retval + 1 ) > 0) |]
.

Definition remove_vowels_partial_solve_wit_2_aux := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((retval + 1 ) > 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition remove_vowels_partial_solve_wit_2 := remove_vowels_partial_solve_wit_2_pure -> remove_vowels_partial_solve_wit_2_aux.

Definition remove_vowels_partial_solve_wit_3 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (((text_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i text_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition remove_vowels_partial_solve_wit_4 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (((out + (j * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out j j (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
.

Definition remove_vowels_partial_solve_wit_5 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_51_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| ((Zlength (out_l)) = j) |] 
  &&  [| (out_l = (remove_vowels_prefix_z (i) (l))) |]
  &&  (((out + (j * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out j j (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_remove_vowels_safety_wit_1 : remove_vowels_safety_wit_1.
Axiom proof_of_remove_vowels_safety_wit_2 : remove_vowels_safety_wit_2.
Axiom proof_of_remove_vowels_safety_wit_3 : remove_vowels_safety_wit_3.
Axiom proof_of_remove_vowels_safety_wit_4 : remove_vowels_safety_wit_4.
Axiom proof_of_remove_vowels_safety_wit_5 : remove_vowels_safety_wit_5.
Axiom proof_of_remove_vowels_safety_wit_6 : remove_vowels_safety_wit_6.
Axiom proof_of_remove_vowels_safety_wit_7 : remove_vowels_safety_wit_7.
Axiom proof_of_remove_vowels_safety_wit_8 : remove_vowels_safety_wit_8.
Axiom proof_of_remove_vowels_safety_wit_9 : remove_vowels_safety_wit_9.
Axiom proof_of_remove_vowels_safety_wit_10 : remove_vowels_safety_wit_10.
Axiom proof_of_remove_vowels_safety_wit_11 : remove_vowels_safety_wit_11.
Axiom proof_of_remove_vowels_safety_wit_12 : remove_vowels_safety_wit_12.
Axiom proof_of_remove_vowels_safety_wit_13 : remove_vowels_safety_wit_13.
Axiom proof_of_remove_vowels_safety_wit_14 : remove_vowels_safety_wit_14.
Axiom proof_of_remove_vowels_safety_wit_15 : remove_vowels_safety_wit_15.
Axiom proof_of_remove_vowels_safety_wit_16 : remove_vowels_safety_wit_16.
Axiom proof_of_remove_vowels_safety_wit_17 : remove_vowels_safety_wit_17.
Axiom proof_of_remove_vowels_safety_wit_18 : remove_vowels_safety_wit_18.
Axiom proof_of_remove_vowels_safety_wit_19 : remove_vowels_safety_wit_19.
Axiom proof_of_remove_vowels_safety_wit_20 : remove_vowels_safety_wit_20.
Axiom proof_of_remove_vowels_safety_wit_21 : remove_vowels_safety_wit_21.
Axiom proof_of_remove_vowels_safety_wit_22 : remove_vowels_safety_wit_22.
Axiom proof_of_remove_vowels_safety_wit_23 : remove_vowels_safety_wit_23.
Axiom proof_of_remove_vowels_safety_wit_24 : remove_vowels_safety_wit_24.
Axiom proof_of_remove_vowels_safety_wit_25 : remove_vowels_safety_wit_25.
Axiom proof_of_remove_vowels_safety_wit_26 : remove_vowels_safety_wit_26.
Axiom proof_of_remove_vowels_safety_wit_27 : remove_vowels_safety_wit_27.
Axiom proof_of_remove_vowels_safety_wit_28 : remove_vowels_safety_wit_28.
Axiom proof_of_remove_vowels_entail_wit_1 : remove_vowels_entail_wit_1.
Axiom proof_of_remove_vowels_entail_wit_2_1 : remove_vowels_entail_wit_2_1.
Axiom proof_of_remove_vowels_entail_wit_2_2 : remove_vowels_entail_wit_2_2.
Axiom proof_of_remove_vowels_entail_wit_2_3 : remove_vowels_entail_wit_2_3.
Axiom proof_of_remove_vowels_entail_wit_2_4 : remove_vowels_entail_wit_2_4.
Axiom proof_of_remove_vowels_entail_wit_2_5 : remove_vowels_entail_wit_2_5.
Axiom proof_of_remove_vowels_entail_wit_2_6 : remove_vowels_entail_wit_2_6.
Axiom proof_of_remove_vowels_entail_wit_2_7 : remove_vowels_entail_wit_2_7.
Axiom proof_of_remove_vowels_entail_wit_2_8 : remove_vowels_entail_wit_2_8.
Axiom proof_of_remove_vowels_entail_wit_2_9 : remove_vowels_entail_wit_2_9.
Axiom proof_of_remove_vowels_entail_wit_2_10 : remove_vowels_entail_wit_2_10.
Axiom proof_of_remove_vowels_entail_wit_2_11 : remove_vowels_entail_wit_2_11.
Axiom proof_of_remove_vowels_return_wit_1 : remove_vowels_return_wit_1.
Axiom proof_of_remove_vowels_partial_solve_wit_1 : remove_vowels_partial_solve_wit_1.
Axiom proof_of_remove_vowels_partial_solve_wit_2_pure : remove_vowels_partial_solve_wit_2_pure.
Axiom proof_of_remove_vowels_partial_solve_wit_2 : remove_vowels_partial_solve_wit_2.
Axiom proof_of_remove_vowels_partial_solve_wit_3 : remove_vowels_partial_solve_wit_3.
Axiom proof_of_remove_vowels_partial_solve_wit_4 : remove_vowels_partial_solve_wit_4.
Axiom proof_of_remove_vowels_partial_solve_wit_5 : remove_vowels_partial_solve_wit_5.

End VC_Correct.
