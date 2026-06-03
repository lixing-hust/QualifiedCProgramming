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
Require Import coins_143.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function is_prime_len -----*)

Definition is_prime_len_safety_wit_1 := 
forall (len_pre: Z) ,
  [| (0 <= len_pre) |] 
  &&  [| (len_pre <= 100) |]
  &&  ((( &( "composite" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |-> len_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_prime_len_safety_wit_2 := 
forall (len_pre: Z) ,
  [| (0 <= len_pre) |] 
  &&  [| (len_pre <= 100) |]
  &&  ((( &( "composite" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |-> len_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_prime_len_safety_wit_3 := 
forall (len_pre: Z) ,
  [| (len_pre < 2) |] 
  &&  [| (0 <= len_pre) |] 
  &&  [| (len_pre <= 100) |]
  &&  ((( &( "composite" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |-> len_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_prime_len_safety_wit_4 := 
forall (len_pre: Z) ,
  [| (len_pre >= 2) |] 
  &&  [| (0 <= len_pre) |] 
  &&  [| (len_pre <= 100) |]
  &&  ((( &( "composite" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |-> len_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_prime_len_safety_wit_5 := 
forall (len_pre: Z) (composite: Z) (j: Z) ,
  [| (j < len_pre) |] 
  &&  [| (2 <= len_pre) |] 
  &&  [| (len_pre <= 100) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= len_pre) |] 
  &&  [| (0 <= composite) |] 
  &&  [| (composite <= 1) |] 
  &&  [| (prime_loop_state_z len_pre j composite ) |]
  &&  ((( &( "len" ) )) # Int  |-> len_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "composite" ) )) # Int  |-> composite)
|--
  [| ((len_pre <> (INT_MIN)) \/ (j <> (-1))) |] 
  &&  [| (j <> 0) |]
.

Definition is_prime_len_safety_wit_6 := 
forall (len_pre: Z) (composite: Z) (j: Z) ,
  [| (j < len_pre) |] 
  &&  [| (2 <= len_pre) |] 
  &&  [| (len_pre <= 100) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= len_pre) |] 
  &&  [| (0 <= composite) |] 
  &&  [| (composite <= 1) |] 
  &&  [| (prime_loop_state_z len_pre j composite ) |]
  &&  ((( &( "len" ) )) # Int  |-> len_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "composite" ) )) # Int  |-> composite)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_prime_len_safety_wit_7 := 
forall (len_pre: Z) (composite: Z) (j: Z) ,
  [| ((len_pre % ( j ) ) = 0) |] 
  &&  [| (j < len_pre) |] 
  &&  [| (2 <= len_pre) |] 
  &&  [| (len_pre <= 100) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= len_pre) |] 
  &&  [| (0 <= composite) |] 
  &&  [| (composite <= 1) |] 
  &&  [| (prime_loop_state_z len_pre j composite ) |]
  &&  ((( &( "len" ) )) # Int  |-> len_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "composite" ) )) # Int  |-> composite)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_prime_len_safety_wit_8 := 
forall (len_pre: Z) (composite: Z) (j: Z) ,
  [| ((len_pre % ( j ) ) <> 0) |] 
  &&  [| (j < len_pre) |] 
  &&  [| (2 <= len_pre) |] 
  &&  [| (len_pre <= 100) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= len_pre) |] 
  &&  [| (0 <= composite) |] 
  &&  [| (composite <= 1) |] 
  &&  [| (prime_loop_state_z len_pre j composite ) |]
  &&  ((( &( "len" ) )) # Int  |-> len_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "composite" ) )) # Int  |-> composite)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition is_prime_len_safety_wit_9 := 
forall (len_pre: Z) (composite: Z) (j: Z) ,
  [| ((len_pre % ( j ) ) = 0) |] 
  &&  [| (j < len_pre) |] 
  &&  [| (2 <= len_pre) |] 
  &&  [| (len_pre <= 100) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= len_pre) |] 
  &&  [| (0 <= composite) |] 
  &&  [| (composite <= 1) |] 
  &&  [| (prime_loop_state_z len_pre j composite ) |]
  &&  ((( &( "len" ) )) # Int  |-> len_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "composite" ) )) # Int  |-> 1)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition is_prime_len_safety_wit_10 := 
forall (len_pre: Z) (composite: Z) (j: Z) ,
  [| (j >= len_pre) |] 
  &&  [| (2 <= len_pre) |] 
  &&  [| (len_pre <= 100) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= len_pre) |] 
  &&  [| (0 <= composite) |] 
  &&  [| (composite <= 1) |] 
  &&  [| (prime_loop_state_z len_pre j composite ) |]
  &&  ((( &( "len" ) )) # Int  |-> len_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "composite" ) )) # Int  |-> composite)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_prime_len_safety_wit_11 := 
forall (len_pre: Z) (composite: Z) (j: Z) ,
  [| (composite = 1) |] 
  &&  [| (j >= len_pre) |] 
  &&  [| (2 <= len_pre) |] 
  &&  [| (len_pre <= 100) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= len_pre) |] 
  &&  [| (0 <= composite) |] 
  &&  [| (composite <= 1) |] 
  &&  [| (prime_loop_state_z len_pre j composite ) |]
  &&  ((( &( "len" ) )) # Int  |-> len_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "composite" ) )) # Int  |-> composite)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_prime_len_safety_wit_12 := 
forall (len_pre: Z) (composite: Z) (j: Z) ,
  [| (composite <> 1) |] 
  &&  [| (j >= len_pre) |] 
  &&  [| (2 <= len_pre) |] 
  &&  [| (len_pre <= 100) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= len_pre) |] 
  &&  [| (0 <= composite) |] 
  &&  [| (composite <= 1) |] 
  &&  [| (prime_loop_state_z len_pre j composite ) |]
  &&  ((( &( "len" ) )) # Int  |-> len_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "composite" ) )) # Int  |-> composite)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_prime_len_entail_wit_1 := 
forall (len_pre: Z) ,
  [| (len_pre >= 2) |] 
  &&  [| (0 <= len_pre) |] 
  &&  [| (len_pre <= 100) |]
  &&  emp
|--
  [| (2 <= len_pre) |] 
  &&  [| (len_pre <= 100) |] 
  &&  [| (2 <= 2) |] 
  &&  [| (2 <= len_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (prime_loop_state_z len_pre 2 0 ) |]
  &&  emp
.

Definition is_prime_len_entail_wit_2_1 := 
forall (len_pre: Z) (composite: Z) (j: Z) ,
  [| ((len_pre % ( j ) ) = 0) |] 
  &&  [| (j < len_pre) |] 
  &&  [| (2 <= len_pre) |] 
  &&  [| (len_pre <= 100) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= len_pre) |] 
  &&  [| (0 <= composite) |] 
  &&  [| (composite <= 1) |] 
  &&  [| (prime_loop_state_z len_pre j composite ) |]
  &&  emp
|--
  [| (2 <= len_pre) |] 
  &&  [| (len_pre <= 100) |] 
  &&  [| (2 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= len_pre) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (prime_loop_state_z len_pre (j + 1 ) 1 ) |]
  &&  emp
.

Definition is_prime_len_entail_wit_2_2 := 
forall (len_pre: Z) (composite: Z) (j: Z) ,
  [| ((len_pre % ( j ) ) <> 0) |] 
  &&  [| (j < len_pre) |] 
  &&  [| (2 <= len_pre) |] 
  &&  [| (len_pre <= 100) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= len_pre) |] 
  &&  [| (0 <= composite) |] 
  &&  [| (composite <= 1) |] 
  &&  [| (prime_loop_state_z len_pre j composite ) |]
  &&  emp
|--
  [| (2 <= len_pre) |] 
  &&  [| (len_pre <= 100) |] 
  &&  [| (2 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= len_pre) |] 
  &&  [| (0 <= composite) |] 
  &&  [| (composite <= 1) |] 
  &&  [| (prime_loop_state_z len_pre (j + 1 ) composite ) |]
  &&  emp
.

Definition is_prime_len_return_wit_1 := 
forall (len_pre: Z) (composite: Z) (j: Z) ,
  [| (composite <> 1) |] 
  &&  [| (j >= len_pre) |] 
  &&  [| (2 <= len_pre) |] 
  &&  [| (len_pre <= 100) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= len_pre) |] 
  &&  [| (0 <= composite) |] 
  &&  [| (composite <= 1) |] 
  &&  [| (prime_loop_state_z len_pre j composite ) |]
  &&  emp
|--
  [| (1 = (prime_len_flag_z (len_pre))) |]
  &&  emp
.

Definition is_prime_len_return_wit_2 := 
forall (len_pre: Z) (composite: Z) (j: Z) ,
  [| (composite = 1) |] 
  &&  [| (j >= len_pre) |] 
  &&  [| (2 <= len_pre) |] 
  &&  [| (len_pre <= 100) |] 
  &&  [| (2 <= j) |] 
  &&  [| (j <= len_pre) |] 
  &&  [| (0 <= composite) |] 
  &&  [| (composite <= 1) |] 
  &&  [| (prime_loop_state_z len_pre j composite ) |]
  &&  emp
|--
  [| (0 = (prime_len_flag_z (len_pre))) |]
  &&  emp
.

Definition is_prime_len_return_wit_3 := 
forall (len_pre: Z) ,
  [| (len_pre < 2) |] 
  &&  [| (0 <= len_pre) |] 
  &&  [| (len_pre <= 100) |]
  &&  emp
|--
  [| (0 = (prime_len_flag_z (len_pre))) |]
  &&  emp
.

(*----- Function words_in_sentence -----*)

Definition words_in_sentence_safety_wit_1 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  [| ((retval + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval + 2 )) |]
.

Definition words_in_sentence_safety_wit_2 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition words_in_sentence_safety_wit_3 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out_len" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_2 (retval + 2 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition words_in_sentence_safety_wit_4 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_2 (retval + 2 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition words_in_sentence_safety_wit_5 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition words_in_sentence_safety_wit_6 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition words_in_sentence_safety_wit_7 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition words_in_sentence_safety_wit_8 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| False |]
.

Definition words_in_sentence_safety_wit_9 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| False |]
.

Definition words_in_sentence_safety_wit_10 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) ,
  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition words_in_sentence_safety_wit_11 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition words_in_sentence_safety_wit_12 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition words_in_sentence_safety_wit_13 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  ((( &( "word_len" ) )) # Int  |->_)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| ((i - start ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i - start )) |]
.

Definition words_in_sentence_safety_wit_14 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) ,
  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  ((( &( "word_len" ) )) # Int  |->_)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| ((i - start ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i - start )) |]
.

Definition words_in_sentence_safety_wit_15 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  ((( &( "prime" ) )) # Int  |-> retval)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition words_in_sentence_safety_wit_16 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  ((( &( "prime" ) )) # Int  |-> retval)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition words_in_sentence_safety_wit_17 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "prime" ) )) # Int  |-> retval)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition words_in_sentence_safety_wit_18 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "prime" ) )) # Int  |-> retval)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition words_in_sentence_safety_wit_19 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "prime" ) )) # Int  |-> retval)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition words_in_sentence_safety_wit_20 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "prime" ) )) # Int  |-> retval)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition words_in_sentence_safety_wit_21 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "prime" ) )) # Int  |-> retval)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((out_len + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (out_len + 1 )) |]
.

Definition words_in_sentence_safety_wit_22 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "prime" ) )) # Int  |-> retval)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition words_in_sentence_safety_wit_23 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "prime" ) )) # Int  |-> retval)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((out_len + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (out_len + 1 )) |]
.

Definition words_in_sentence_safety_wit_24 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "prime" ) )) # Int  |-> retval)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition words_in_sentence_safety_wit_25 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len <= 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "prime" ) )) # Int  |-> retval)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition words_in_sentence_safety_wit_26 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len <= 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "prime" ) )) # Int  |-> retval)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition words_in_sentence_safety_wit_27 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "prime" ) )) # Int  |-> retval)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition words_in_sentence_safety_wit_28 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
  **  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "prime" ) )) # Int  |-> retval)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + 1 ))
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition words_in_sentence_safety_wit_29 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (k: Z) (prime: Z) (word_len: Z) (i: Z) (start: Z) ,
  [| (k < word_len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (word_len = (i - start )) |] 
  &&  [| (prime = 1) |] 
  &&  [| (prime = (prime_len_flag_z (word_len))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= word_len) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (((out_len + word_len ) - k ) <= (len + 2 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (word_copy_prefix_z (start) (k) (l))) |]
  &&  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "word_len" ) )) # Int  |-> word_len)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| ((start + k ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (start + k )) |]
.

Definition words_in_sentence_safety_wit_30 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (k: Z) (prime: Z) (word_len: Z) (i: Z) (start: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (k < word_len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (word_len = (i - start )) |] 
  &&  [| (prime = 1) |] 
  &&  [| (prime = (prime_len_flag_z (word_len))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= word_len) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (((out_len + word_len ) - k ) <= (len + 2 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (word_copy_prefix_z (start) (k) (l))) |]
  &&  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons ((Znth (start + k ) (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "word_len" ) )) # Int  |-> word_len)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((out_len + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (out_len + 1 )) |]
.

Definition words_in_sentence_safety_wit_31 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (k: Z) (prime: Z) (word_len: Z) (i: Z) (start: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (k < word_len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (word_len = (i - start )) |] 
  &&  [| (prime = 1) |] 
  &&  [| (prime = (prime_len_flag_z (word_len))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= word_len) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (((out_len + word_len ) - k ) <= (len + 2 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (word_copy_prefix_z (start) (k) (l))) |]
  &&  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons ((Znth (start + k ) (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "word_len" ) )) # Int  |-> word_len)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition words_in_sentence_safety_wit_32 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (k: Z) (prime: Z) (word_len: Z) (i: Z) (start: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (k < word_len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (word_len = (i - start )) |] 
  &&  [| (prime = 1) |] 
  &&  [| (prime = (prime_len_flag_z (word_len))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= word_len) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (((out_len + word_len ) - k ) <= (len + 2 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (word_copy_prefix_z (start) (k) (l))) |]
  &&  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons ((Znth (start + k ) (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "word_len" ) )) # Int  |-> word_len)
  **  ((( &( "prime" ) )) # Int  |-> prime)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition words_in_sentence_safety_wit_33 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) ,
  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition words_in_sentence_entail_wit_1 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval_2 = len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.undef_full retval (retval_2 + 2 ) )
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (scan_ready_z l len 0 ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (0 + 1 )) |] 
  &&  [| ((Zlength (out_l)) = 0) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (0) (l))) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (len + 2 ) )
.

Definition words_in_sentence_entail_wit_2 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (out_len: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l_2)) = out_len) |] 
  &&  [| (out_l_2 = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
.

Definition words_in_sentence_entail_wit_3 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (out_len: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l_2)) = out_len) |] 
  &&  [| (out_l_2 = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (scan_ready_z l len (i + 1 ) ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= ((i + 1 ) + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z ((i + 1 )) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
.

Definition words_in_sentence_entail_wit_4 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (out_len: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l_2)) = out_len) |] 
  &&  [| (out_l_2 = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l i ) |] 
  &&  [| (word_chars_z l i i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
.

Definition words_in_sentence_entail_wit_5 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (out_len: Z) (i: Z) (start: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l_2)) = out_len) |] 
  &&  [| (out_l_2 = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start (i + 1 ) ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
.

Definition words_in_sentence_entail_wit_6_1 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l_2)) = out_len) |] 
  &&  [| (out_l_2 = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full out (out_len + 1 ) (app (out_l_2) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| ((i - start ) = (i - start )) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (i - start )) |] 
  &&  [| (0 <= (out_len + 1 )) |] 
  &&  [| ((((out_len + 1 ) + (i - start ) ) - 0 ) <= (len + 2 )) |] 
  &&  [| ((Zlength (out_l)) = (out_len + 1 )) |] 
  &&  [| (out_l = (word_copy_prefix_z (start) (0) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (out_len + 1 ) out_l )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
.

Definition words_in_sentence_entail_wit_6_2 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l_2)) = out_len) |] 
  &&  [| (out_l_2 = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full out (out_len + 1 ) (app (out_l_2) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| ((i - start ) = (i - start )) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (i - start )) |] 
  &&  [| (0 <= (out_len + 1 )) |] 
  &&  [| ((((out_len + 1 ) + (i - start ) ) - 0 ) <= (len + 2 )) |] 
  &&  [| ((Zlength (out_l)) = (out_len + 1 )) |] 
  &&  [| (out_l = (word_copy_prefix_z (start) (0) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (out_len + 1 ) out_l )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
.

Definition words_in_sentence_entail_wit_6_3 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len <= 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l_2)) = out_len) |] 
  &&  [| (out_l_2 = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| ((i - start ) = (i - start )) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (i - start )) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (((out_len + (i - start ) ) - 0 ) <= (len + 2 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (word_copy_prefix_z (start) (0) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
.

Definition words_in_sentence_entail_wit_6_4 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len <= 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l_2)) = out_len) |] 
  &&  [| (out_l_2 = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| ((i - start ) = (i - start )) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (i - start )) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (((out_len + (i - start ) ) - 0 ) <= (len + 2 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (word_copy_prefix_z (start) (0) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
.

Definition words_in_sentence_entail_wit_7 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (out_len: Z) (k: Z) (prime: Z) (word_len: Z) (i: Z) (start: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (k < word_len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (word_len = (i - start )) |] 
  &&  [| (prime = 1) |] 
  &&  [| (prime = (prime_len_flag_z (word_len))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= word_len) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (((out_len + word_len ) - k ) <= (len + 2 )) |] 
  &&  [| ((Zlength (out_l_2)) = out_len) |] 
  &&  [| (out_l_2 = (word_copy_prefix_z (start) (k) (l))) |]
  &&  (CharArray.full out (out_len + 1 ) (app (out_l_2) ((cons ((Znth (start + k ) (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (word_len = (i - start )) |] 
  &&  [| (prime = 1) |] 
  &&  [| (prime = (prime_len_flag_z (word_len))) |] 
  &&  [| (0 <= (k + 1 )) |] 
  &&  [| ((k + 1 ) <= word_len) |] 
  &&  [| (0 <= (out_len + 1 )) |] 
  &&  [| ((((out_len + 1 ) + word_len ) - (k + 1 ) ) <= (len + 2 )) |] 
  &&  [| ((Zlength (out_l)) = (out_len + 1 )) |] 
  &&  [| (out_l = (word_copy_prefix_z (start) ((k + 1 )) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (out_len + 1 ) out_l )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
.

Definition words_in_sentence_entail_wit_8_1 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (out_len: Z) (i: Z) ,
  [| (i >= len) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l_2)) = out_len) |] 
  &&  [| (out_l_2 = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
.

Definition words_in_sentence_entail_wit_8_2 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (retval <> 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l_2)) = out_len) |] 
  &&  [| (out_l_2 = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
.

Definition words_in_sentence_entail_wit_8_3 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (retval <> 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l_2)) = out_len) |] 
  &&  [| (out_l_2 = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
.

Definition words_in_sentence_entail_wit_8_4 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (out_len: Z) (k: Z) (prime: Z) (word_len: Z) (i: Z) (start: Z) ,
  [| (k >= word_len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (word_len = (i - start )) |] 
  &&  [| (prime = 1) |] 
  &&  [| (prime = (prime_len_flag_z (word_len))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= word_len) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (((out_len + word_len ) - k ) <= (len + 2 )) |] 
  &&  [| ((Zlength (out_l_2)) = out_len) |] 
  &&  [| (out_l_2 = (word_copy_prefix_z (start) (k) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l_2 )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
.

Definition words_in_sentence_return_wit_1 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (out_len_2: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len_2) |] 
  &&  [| (out_len_2 <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l_2)) = out_len_2) |] 
  &&  [| (out_l_2 = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full out (out_len_2 + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (out_len_2 + 1 ) (len + 2 ) )
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z))  (out_len: Z) ,
  [| (0 <= out_len) |] 
  &&  [| (out_len <= (len + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_output_z (l))) |] 
  &&  [| (problem_143_spec_z l out_l ) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 2 ) )
.

Definition words_in_sentence_partial_solve_wit_1 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition words_in_sentence_partial_solve_wit_2_pure := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
|--
  [| ((retval + 2 ) > 0) |]
.

Definition words_in_sentence_partial_solve_wit_2_aux := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((retval + 2 ) > 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition words_in_sentence_partial_solve_wit_2 := words_in_sentence_partial_solve_wit_2_pure -> words_in_sentence_partial_solve_wit_2_aux.

Definition words_in_sentence_partial_solve_wit_3 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (((sentence_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i sentence_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
.

Definition words_in_sentence_partial_solve_wit_4 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) ,
  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (((sentence_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i sentence_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
.

Definition words_in_sentence_partial_solve_wit_5_pure := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) ,
  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  ((( &( "prime" ) )) # Int  |->_)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (0 <= (i - start )) |] 
  &&  [| ((i - start ) <= 100) |]
.

Definition words_in_sentence_partial_solve_wit_5_aux := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) ,
  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (0 <= (i - start )) |] 
  &&  [| ((i - start ) <= 100) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
.

Definition words_in_sentence_partial_solve_wit_5 := words_in_sentence_partial_solve_wit_5_pure -> words_in_sentence_partial_solve_wit_5_aux.

Definition words_in_sentence_partial_solve_wit_6_pure := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  ((( &( "prime" ) )) # Int  |->_)
  **  ((( &( "word_len" ) )) # Int  |-> (i - start ))
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "sentence" ) )) # Ptr  |-> sentence_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (0 <= (i - start )) |] 
  &&  [| ((i - start ) <= 100) |]
.

Definition words_in_sentence_partial_solve_wit_6_aux := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (0 <= (i - start )) |] 
  &&  [| ((i - start ) <= 100) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
.

Definition words_in_sentence_partial_solve_wit_6 := words_in_sentence_partial_solve_wit_6_pure -> words_in_sentence_partial_solve_wit_6_aux.

Definition words_in_sentence_partial_solve_wit_7 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (out_len > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (((out + (out_len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out out_len out_len (len + 2 ) )
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
.

Definition words_in_sentence_partial_solve_wit_8 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) (start: Z) (retval: Z) ,
  [| (out_len > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (out_len > 0) |] 
  &&  [| (retval = 1) |] 
  &&  [| (retval = (prime_len_flag_z ((i - start )))) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (start + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (start) (l))) |]
  &&  (((out + (out_len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out out_len out_len (len + 2 ) )
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
.

Definition words_in_sentence_partial_solve_wit_9 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (k: Z) (prime: Z) (word_len: Z) (i: Z) (start: Z) ,
  [| (k < word_len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (word_len = (i - start )) |] 
  &&  [| (prime = 1) |] 
  &&  [| (prime = (prime_len_flag_z (word_len))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= word_len) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (((out_len + word_len ) - k ) <= (len + 2 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (word_copy_prefix_z (start) (k) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (k < word_len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (word_len = (i - start )) |] 
  &&  [| (prime = 1) |] 
  &&  [| (prime = (prime_len_flag_z (word_len))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= word_len) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (((out_len + word_len ) - k ) <= (len + 2 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (word_copy_prefix_z (start) (k) (l))) |]
  &&  (((sentence_pre + ((start + k ) * sizeof(CHAR) ) )) # Char  |-> (Znth (start + k ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i sentence_pre (start + k ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
.

Definition words_in_sentence_partial_solve_wit_10 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (k: Z) (prime: Z) (word_len: Z) (i: Z) (start: Z) ,
  [| (k < word_len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (word_len = (i - start )) |] 
  &&  [| (prime = 1) |] 
  &&  [| (prime = (prime_len_flag_z (word_len))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= word_len) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (((out_len + word_len ) - k ) <= (len + 2 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (word_copy_prefix_z (start) (k) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (k < word_len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= start) |] 
  &&  [| (start <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (word_start_z l start ) |] 
  &&  [| (word_chars_z l start i ) |] 
  &&  [| (word_len = (i - start )) |] 
  &&  [| (prime = 1) |] 
  &&  [| (prime = (prime_len_flag_z (word_len))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= word_len) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (((out_len + word_len ) - k ) <= (len + 2 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (word_copy_prefix_z (start) (k) (l))) |]
  &&  (((out + (out_len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out out_len out_len (len + 2 ) )
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
.

Definition words_in_sentence_partial_solve_wit_11 := 
forall (sentence_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (out_len: Z) (i: Z) ,
  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
  **  (CharArray.undef_seg out out_len (len + 2 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (1 <= len) |] 
  &&  [| (len <= 100) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_143_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (scan_ready_z l len i ) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= (i + 1 )) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (out_l = (words_in_sentence_prefix_z (i) (l))) |]
  &&  (((out + (out_len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out out_len out_len (len + 2 ) )
  **  (CharArray.full sentence_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len out_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_is_prime_len_safety_wit_1 : is_prime_len_safety_wit_1.
Axiom proof_of_is_prime_len_safety_wit_2 : is_prime_len_safety_wit_2.
Axiom proof_of_is_prime_len_safety_wit_3 : is_prime_len_safety_wit_3.
Axiom proof_of_is_prime_len_safety_wit_4 : is_prime_len_safety_wit_4.
Axiom proof_of_is_prime_len_safety_wit_5 : is_prime_len_safety_wit_5.
Axiom proof_of_is_prime_len_safety_wit_6 : is_prime_len_safety_wit_6.
Axiom proof_of_is_prime_len_safety_wit_7 : is_prime_len_safety_wit_7.
Axiom proof_of_is_prime_len_safety_wit_8 : is_prime_len_safety_wit_8.
Axiom proof_of_is_prime_len_safety_wit_9 : is_prime_len_safety_wit_9.
Axiom proof_of_is_prime_len_safety_wit_10 : is_prime_len_safety_wit_10.
Axiom proof_of_is_prime_len_safety_wit_11 : is_prime_len_safety_wit_11.
Axiom proof_of_is_prime_len_safety_wit_12 : is_prime_len_safety_wit_12.
Axiom proof_of_is_prime_len_entail_wit_1 : is_prime_len_entail_wit_1.
Axiom proof_of_is_prime_len_entail_wit_2_1 : is_prime_len_entail_wit_2_1.
Axiom proof_of_is_prime_len_entail_wit_2_2 : is_prime_len_entail_wit_2_2.
Axiom proof_of_is_prime_len_return_wit_1 : is_prime_len_return_wit_1.
Axiom proof_of_is_prime_len_return_wit_2 : is_prime_len_return_wit_2.
Axiom proof_of_is_prime_len_return_wit_3 : is_prime_len_return_wit_3.
Axiom proof_of_words_in_sentence_safety_wit_1 : words_in_sentence_safety_wit_1.
Axiom proof_of_words_in_sentence_safety_wit_2 : words_in_sentence_safety_wit_2.
Axiom proof_of_words_in_sentence_safety_wit_3 : words_in_sentence_safety_wit_3.
Axiom proof_of_words_in_sentence_safety_wit_4 : words_in_sentence_safety_wit_4.
Axiom proof_of_words_in_sentence_safety_wit_5 : words_in_sentence_safety_wit_5.
Axiom proof_of_words_in_sentence_safety_wit_6 : words_in_sentence_safety_wit_6.
Axiom proof_of_words_in_sentence_safety_wit_7 : words_in_sentence_safety_wit_7.
Axiom proof_of_words_in_sentence_safety_wit_8 : words_in_sentence_safety_wit_8.
Axiom proof_of_words_in_sentence_safety_wit_9 : words_in_sentence_safety_wit_9.
Axiom proof_of_words_in_sentence_safety_wit_10 : words_in_sentence_safety_wit_10.
Axiom proof_of_words_in_sentence_safety_wit_11 : words_in_sentence_safety_wit_11.
Axiom proof_of_words_in_sentence_safety_wit_12 : words_in_sentence_safety_wit_12.
Axiom proof_of_words_in_sentence_safety_wit_13 : words_in_sentence_safety_wit_13.
Axiom proof_of_words_in_sentence_safety_wit_14 : words_in_sentence_safety_wit_14.
Axiom proof_of_words_in_sentence_safety_wit_15 : words_in_sentence_safety_wit_15.
Axiom proof_of_words_in_sentence_safety_wit_16 : words_in_sentence_safety_wit_16.
Axiom proof_of_words_in_sentence_safety_wit_17 : words_in_sentence_safety_wit_17.
Axiom proof_of_words_in_sentence_safety_wit_18 : words_in_sentence_safety_wit_18.
Axiom proof_of_words_in_sentence_safety_wit_19 : words_in_sentence_safety_wit_19.
Axiom proof_of_words_in_sentence_safety_wit_20 : words_in_sentence_safety_wit_20.
Axiom proof_of_words_in_sentence_safety_wit_21 : words_in_sentence_safety_wit_21.
Axiom proof_of_words_in_sentence_safety_wit_22 : words_in_sentence_safety_wit_22.
Axiom proof_of_words_in_sentence_safety_wit_23 : words_in_sentence_safety_wit_23.
Axiom proof_of_words_in_sentence_safety_wit_24 : words_in_sentence_safety_wit_24.
Axiom proof_of_words_in_sentence_safety_wit_25 : words_in_sentence_safety_wit_25.
Axiom proof_of_words_in_sentence_safety_wit_26 : words_in_sentence_safety_wit_26.
Axiom proof_of_words_in_sentence_safety_wit_27 : words_in_sentence_safety_wit_27.
Axiom proof_of_words_in_sentence_safety_wit_28 : words_in_sentence_safety_wit_28.
Axiom proof_of_words_in_sentence_safety_wit_29 : words_in_sentence_safety_wit_29.
Axiom proof_of_words_in_sentence_safety_wit_30 : words_in_sentence_safety_wit_30.
Axiom proof_of_words_in_sentence_safety_wit_31 : words_in_sentence_safety_wit_31.
Axiom proof_of_words_in_sentence_safety_wit_32 : words_in_sentence_safety_wit_32.
Axiom proof_of_words_in_sentence_safety_wit_33 : words_in_sentence_safety_wit_33.
Axiom proof_of_words_in_sentence_entail_wit_1 : words_in_sentence_entail_wit_1.
Axiom proof_of_words_in_sentence_entail_wit_2 : words_in_sentence_entail_wit_2.
Axiom proof_of_words_in_sentence_entail_wit_3 : words_in_sentence_entail_wit_3.
Axiom proof_of_words_in_sentence_entail_wit_4 : words_in_sentence_entail_wit_4.
Axiom proof_of_words_in_sentence_entail_wit_5 : words_in_sentence_entail_wit_5.
Axiom proof_of_words_in_sentence_entail_wit_6_1 : words_in_sentence_entail_wit_6_1.
Axiom proof_of_words_in_sentence_entail_wit_6_2 : words_in_sentence_entail_wit_6_2.
Axiom proof_of_words_in_sentence_entail_wit_6_3 : words_in_sentence_entail_wit_6_3.
Axiom proof_of_words_in_sentence_entail_wit_6_4 : words_in_sentence_entail_wit_6_4.
Axiom proof_of_words_in_sentence_entail_wit_7 : words_in_sentence_entail_wit_7.
Axiom proof_of_words_in_sentence_entail_wit_8_1 : words_in_sentence_entail_wit_8_1.
Axiom proof_of_words_in_sentence_entail_wit_8_2 : words_in_sentence_entail_wit_8_2.
Axiom proof_of_words_in_sentence_entail_wit_8_3 : words_in_sentence_entail_wit_8_3.
Axiom proof_of_words_in_sentence_entail_wit_8_4 : words_in_sentence_entail_wit_8_4.
Axiom proof_of_words_in_sentence_return_wit_1 : words_in_sentence_return_wit_1.
Axiom proof_of_words_in_sentence_partial_solve_wit_1 : words_in_sentence_partial_solve_wit_1.
Axiom proof_of_words_in_sentence_partial_solve_wit_2_pure : words_in_sentence_partial_solve_wit_2_pure.
Axiom proof_of_words_in_sentence_partial_solve_wit_2 : words_in_sentence_partial_solve_wit_2.
Axiom proof_of_words_in_sentence_partial_solve_wit_3 : words_in_sentence_partial_solve_wit_3.
Axiom proof_of_words_in_sentence_partial_solve_wit_4 : words_in_sentence_partial_solve_wit_4.
Axiom proof_of_words_in_sentence_partial_solve_wit_5_pure : words_in_sentence_partial_solve_wit_5_pure.
Axiom proof_of_words_in_sentence_partial_solve_wit_5 : words_in_sentence_partial_solve_wit_5.
Axiom proof_of_words_in_sentence_partial_solve_wit_6_pure : words_in_sentence_partial_solve_wit_6_pure.
Axiom proof_of_words_in_sentence_partial_solve_wit_6 : words_in_sentence_partial_solve_wit_6.
Axiom proof_of_words_in_sentence_partial_solve_wit_7 : words_in_sentence_partial_solve_wit_7.
Axiom proof_of_words_in_sentence_partial_solve_wit_8 : words_in_sentence_partial_solve_wit_8.
Axiom proof_of_words_in_sentence_partial_solve_wit_9 : words_in_sentence_partial_solve_wit_9.
Axiom proof_of_words_in_sentence_partial_solve_wit_10 : words_in_sentence_partial_solve_wit_10.
Axiom proof_of_words_in_sentence_partial_solve_wit_11 : words_in_sentence_partial_solve_wit_11.

End VC_Correct.
