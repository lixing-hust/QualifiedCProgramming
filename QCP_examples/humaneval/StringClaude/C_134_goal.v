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
Require Import coins_134.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function check_if_last_char_is_a_letter -----*)

Definition check_if_last_char_is_a_letter_safety_wit_1 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_2 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_3 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  ((( &( "chr" ) )) # Int  |->_)
  **  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| ((retval - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval - 1 )) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_4 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  ((( &( "chr" ) )) # Int  |->_)
  **  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_5 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_6 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_7 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| (90 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 90) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_8 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_9 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_10 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| (122 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 122) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_11 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| (122 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 122) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_12 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| False |]
.

Definition check_if_last_char_is_a_letter_safety_wit_13 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_14 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_15 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_16 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_17 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_18 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (chr: Z) ,
  [| (1 < len) |] 
  &&  [| (chr = (Znth ((len - 1 )) (l) (0))) |] 
  &&  [| (is_alpha_z chr ) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((len - 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (len - 2 )) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_19 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (chr: Z) ,
  [| (1 < len) |] 
  &&  [| (chr = (Znth ((len - 1 )) (l) (0))) |] 
  &&  [| (is_alpha_z chr ) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_20 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (chr: Z) ,
  [| (1 < len) |] 
  &&  [| (chr = (Znth ((len - 1 )) (l) (0))) |] 
  &&  [| (is_alpha_z chr ) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "chr" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_21 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (chr: Z) ,
  [| ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (1 < len) |] 
  &&  [| (chr = (Znth ((len - 1 )) (l) (0))) |] 
  &&  [| (is_alpha_z chr ) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "chr" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition check_if_last_char_is_a_letter_safety_wit_22 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (chr: Z) ,
  [| ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (1 < len) |] 
  &&  [| (chr = (Znth ((len - 1 )) (l) (0))) |] 
  &&  [| (is_alpha_z chr ) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "chr" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition check_if_last_char_is_a_letter_entail_wit_1_1 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 1) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  [| (1 < len) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) = (Znth ((len - 1 )) (l) (0))) |] 
  &&  [| (is_alpha_z (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) ) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition check_if_last_char_is_a_letter_entail_wit_1_2 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 1) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  [| (1 < len) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) = (Znth ((len - 1 )) (l) (0))) |] 
  &&  [| (is_alpha_z (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) ) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition check_if_last_char_is_a_letter_return_wit_1 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (chr: Z) ,
  [| ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (1 < len) |] 
  &&  [| (chr = (Znth ((len - 1 )) (l) (0))) |] 
  &&  [| (is_alpha_z chr ) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_134_spec_z l 0 ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition check_if_last_char_is_a_letter_return_wit_2 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (chr: Z) ,
  [| ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (1 < len) |] 
  &&  [| (chr = (Znth ((len - 1 )) (l) (0))) |] 
  &&  [| (is_alpha_z chr ) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_134_spec_z l 1 ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition check_if_last_char_is_a_letter_return_wit_3 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_134_spec_z l 1 ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition check_if_last_char_is_a_letter_return_wit_4 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_134_spec_z l 1 ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition check_if_last_char_is_a_letter_return_wit_5 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_134_spec_z l 0 ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition check_if_last_char_is_a_letter_return_wit_6 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_134_spec_z l 0 ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition check_if_last_char_is_a_letter_return_wit_7 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_134_spec_z l 0 ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition check_if_last_char_is_a_letter_return_wit_8 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_134_spec_z l 0 ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition check_if_last_char_is_a_letter_partial_solve_wit_1 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition check_if_last_char_is_a_letter_partial_solve_wit_2 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (retval <> 0) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (((txt_pre + ((retval - 1 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i txt_pre (retval - 1 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition check_if_last_char_is_a_letter_partial_solve_wit_3 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (chr: Z) ,
  [| (1 < len) |] 
  &&  [| (chr = (Znth ((len - 1 )) (l) (0))) |] 
  &&  [| (is_alpha_z chr ) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 < len) |] 
  &&  [| (chr = (Znth ((len - 1 )) (l) (0))) |] 
  &&  [| (is_alpha_z chr ) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (problem_134_pre_z l ) |]
  &&  (((txt_pre + ((len - 2 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i txt_pre (len - 2 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_1 : check_if_last_char_is_a_letter_safety_wit_1.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_2 : check_if_last_char_is_a_letter_safety_wit_2.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_3 : check_if_last_char_is_a_letter_safety_wit_3.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_4 : check_if_last_char_is_a_letter_safety_wit_4.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_5 : check_if_last_char_is_a_letter_safety_wit_5.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_6 : check_if_last_char_is_a_letter_safety_wit_6.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_7 : check_if_last_char_is_a_letter_safety_wit_7.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_8 : check_if_last_char_is_a_letter_safety_wit_8.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_9 : check_if_last_char_is_a_letter_safety_wit_9.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_10 : check_if_last_char_is_a_letter_safety_wit_10.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_11 : check_if_last_char_is_a_letter_safety_wit_11.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_12 : check_if_last_char_is_a_letter_safety_wit_12.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_13 : check_if_last_char_is_a_letter_safety_wit_13.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_14 : check_if_last_char_is_a_letter_safety_wit_14.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_15 : check_if_last_char_is_a_letter_safety_wit_15.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_16 : check_if_last_char_is_a_letter_safety_wit_16.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_17 : check_if_last_char_is_a_letter_safety_wit_17.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_18 : check_if_last_char_is_a_letter_safety_wit_18.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_19 : check_if_last_char_is_a_letter_safety_wit_19.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_20 : check_if_last_char_is_a_letter_safety_wit_20.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_21 : check_if_last_char_is_a_letter_safety_wit_21.
Axiom proof_of_check_if_last_char_is_a_letter_safety_wit_22 : check_if_last_char_is_a_letter_safety_wit_22.
Axiom proof_of_check_if_last_char_is_a_letter_entail_wit_1_1 : check_if_last_char_is_a_letter_entail_wit_1_1.
Axiom proof_of_check_if_last_char_is_a_letter_entail_wit_1_2 : check_if_last_char_is_a_letter_entail_wit_1_2.
Axiom proof_of_check_if_last_char_is_a_letter_return_wit_1 : check_if_last_char_is_a_letter_return_wit_1.
Axiom proof_of_check_if_last_char_is_a_letter_return_wit_2 : check_if_last_char_is_a_letter_return_wit_2.
Axiom proof_of_check_if_last_char_is_a_letter_return_wit_3 : check_if_last_char_is_a_letter_return_wit_3.
Axiom proof_of_check_if_last_char_is_a_letter_return_wit_4 : check_if_last_char_is_a_letter_return_wit_4.
Axiom proof_of_check_if_last_char_is_a_letter_return_wit_5 : check_if_last_char_is_a_letter_return_wit_5.
Axiom proof_of_check_if_last_char_is_a_letter_return_wit_6 : check_if_last_char_is_a_letter_return_wit_6.
Axiom proof_of_check_if_last_char_is_a_letter_return_wit_7 : check_if_last_char_is_a_letter_return_wit_7.
Axiom proof_of_check_if_last_char_is_a_letter_return_wit_8 : check_if_last_char_is_a_letter_return_wit_8.
Axiom proof_of_check_if_last_char_is_a_letter_partial_solve_wit_1 : check_if_last_char_is_a_letter_partial_solve_wit_1.
Axiom proof_of_check_if_last_char_is_a_letter_partial_solve_wit_2 : check_if_last_char_is_a_letter_partial_solve_wit_2.
Axiom proof_of_check_if_last_char_is_a_letter_partial_solve_wit_3 : check_if_last_char_is_a_letter_partial_solve_wit_3.

End VC_Correct.
