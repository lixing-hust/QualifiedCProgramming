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
Require Import coins_50.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function encode_shift -----*)

Definition encode_shift_safety_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((retval + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval + 1 )) |]
.

Definition encode_shift_safety_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition encode_shift_safety_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition encode_shift_safety_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| ((((((Znth i (app (l) ((cons (0) (nil)))) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((((Znth i (app (l) ((cons (0) (nil)))) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 )) |]
.

Definition encode_shift_safety_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (((((Znth i (app (l) ((cons (0) (nil)))) 0) + 5 ) - 97 ) <> (INT_MIN)) \/ (26 <> (-1))) |] 
  &&  [| (26 <> 0) |]
.

Definition encode_shift_safety_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 5 ) - 97 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth i (app (l) ((cons (0) (nil)))) 0) + 5 ) - 97 )) |]
.

Definition encode_shift_safety_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i (app (l) ((cons (0) (nil)))) 0) + 5 )) |]
.

Definition encode_shift_safety_wit_8 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition encode_shift_safety_wit_9 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition encode_shift_safety_wit_10 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (26 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 26) |]
.

Definition encode_shift_safety_wit_11 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition encode_shift_safety_wit_12 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((signed_last_nbits ((((((Znth i (app (l) ((cons (0) (nil)))) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 )) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_shift_safety_wit_13 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition encode_shift_entail_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval_2 = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.undef_full retval (retval_2 + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((Zlength (out_l)) = 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (len + 1 ) )
.

Definition encode_shift_entail_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((((((Znth i (app (l) ((cons (0) (nil)))) 0) + 5 ) - 97 ) % ( 26 ) ) + 97 )) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_shift_return_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (len + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (out_l)) = len) |] 
  &&  [| (problem_50_encode_spec_z l out_l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition encode_shift_partial_solve_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition encode_shift_partial_solve_wit_2_pure := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((retval + 1 ) > 0) |]
.

Definition encode_shift_partial_solve_wit_2_aux := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((retval + 1 ) > 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition encode_shift_partial_solve_wit_2 := encode_shift_partial_solve_wit_2_pure -> encode_shift_partial_solve_wit_2_aux.

Definition encode_shift_partial_solve_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
.

Definition encode_shift_partial_solve_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_shift_partial_solve_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out len i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

(*----- Function decode_shift -----*)

Definition decode_shift_safety_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((retval + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval + 1 )) |]
.

Definition decode_shift_safety_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition decode_shift_safety_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition decode_shift_safety_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| ((((((Znth i (app (l) ((cons (0) (nil)))) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((((Znth i (app (l) ((cons (0) (nil)))) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 )) |]
.

Definition decode_shift_safety_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (((((Znth i (app (l) ((cons (0) (nil)))) 0) + 21 ) - 97 ) <> (INT_MIN)) \/ (26 <> (-1))) |] 
  &&  [| (26 <> 0) |]
.

Definition decode_shift_safety_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 21 ) - 97 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth i (app (l) ((cons (0) (nil)))) 0) + 21 ) - 97 )) |]
.

Definition decode_shift_safety_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 21 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i (app (l) ((cons (0) (nil)))) 0) + 21 )) |]
.

Definition decode_shift_safety_wit_8 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (21 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 21) |]
.

Definition decode_shift_safety_wit_9 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition decode_shift_safety_wit_10 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (26 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 26) |]
.

Definition decode_shift_safety_wit_11 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition decode_shift_safety_wit_12 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((signed_last_nbits ((((((Znth i (app (l) ((cons (0) (nil)))) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 )) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition decode_shift_safety_wit_13 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition decode_shift_entail_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval_2 = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.undef_full retval (retval_2 + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((Zlength (out_l)) = 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (len + 1 ) )
.

Definition decode_shift_entail_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((((((Znth i (app (l) ((cons (0) (nil)))) 0) + 21 ) - 97 ) % ( 26 ) ) + 97 )) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition decode_shift_return_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (len + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (out_l)) = len) |] 
  &&  [| (problem_50_decode_spec_z l out_l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition decode_shift_partial_solve_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition decode_shift_partial_solve_wit_2_pure := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((retval + 1 ) > 0) |]
.

Definition decode_shift_partial_solve_wit_2_aux := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((retval + 1 ) > 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition decode_shift_partial_solve_wit_2 := decode_shift_partial_solve_wit_2_pure -> decode_shift_partial_solve_wit_2_aux.

Definition decode_shift_partial_solve_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
.

Definition decode_shift_partial_solve_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition decode_shift_partial_solve_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_50_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (decode_shift_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out len i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_encode_shift_safety_wit_1 : encode_shift_safety_wit_1.
Axiom proof_of_encode_shift_safety_wit_2 : encode_shift_safety_wit_2.
Axiom proof_of_encode_shift_safety_wit_3 : encode_shift_safety_wit_3.
Axiom proof_of_encode_shift_safety_wit_4 : encode_shift_safety_wit_4.
Axiom proof_of_encode_shift_safety_wit_5 : encode_shift_safety_wit_5.
Axiom proof_of_encode_shift_safety_wit_6 : encode_shift_safety_wit_6.
Axiom proof_of_encode_shift_safety_wit_7 : encode_shift_safety_wit_7.
Axiom proof_of_encode_shift_safety_wit_8 : encode_shift_safety_wit_8.
Axiom proof_of_encode_shift_safety_wit_9 : encode_shift_safety_wit_9.
Axiom proof_of_encode_shift_safety_wit_10 : encode_shift_safety_wit_10.
Axiom proof_of_encode_shift_safety_wit_11 : encode_shift_safety_wit_11.
Axiom proof_of_encode_shift_safety_wit_12 : encode_shift_safety_wit_12.
Axiom proof_of_encode_shift_safety_wit_13 : encode_shift_safety_wit_13.
Axiom proof_of_encode_shift_entail_wit_1 : encode_shift_entail_wit_1.
Axiom proof_of_encode_shift_entail_wit_2 : encode_shift_entail_wit_2.
Axiom proof_of_encode_shift_return_wit_1 : encode_shift_return_wit_1.
Axiom proof_of_encode_shift_partial_solve_wit_1 : encode_shift_partial_solve_wit_1.
Axiom proof_of_encode_shift_partial_solve_wit_2_pure : encode_shift_partial_solve_wit_2_pure.
Axiom proof_of_encode_shift_partial_solve_wit_2 : encode_shift_partial_solve_wit_2.
Axiom proof_of_encode_shift_partial_solve_wit_3 : encode_shift_partial_solve_wit_3.
Axiom proof_of_encode_shift_partial_solve_wit_4 : encode_shift_partial_solve_wit_4.
Axiom proof_of_encode_shift_partial_solve_wit_5 : encode_shift_partial_solve_wit_5.
Axiom proof_of_decode_shift_safety_wit_1 : decode_shift_safety_wit_1.
Axiom proof_of_decode_shift_safety_wit_2 : decode_shift_safety_wit_2.
Axiom proof_of_decode_shift_safety_wit_3 : decode_shift_safety_wit_3.
Axiom proof_of_decode_shift_safety_wit_4 : decode_shift_safety_wit_4.
Axiom proof_of_decode_shift_safety_wit_5 : decode_shift_safety_wit_5.
Axiom proof_of_decode_shift_safety_wit_6 : decode_shift_safety_wit_6.
Axiom proof_of_decode_shift_safety_wit_7 : decode_shift_safety_wit_7.
Axiom proof_of_decode_shift_safety_wit_8 : decode_shift_safety_wit_8.
Axiom proof_of_decode_shift_safety_wit_9 : decode_shift_safety_wit_9.
Axiom proof_of_decode_shift_safety_wit_10 : decode_shift_safety_wit_10.
Axiom proof_of_decode_shift_safety_wit_11 : decode_shift_safety_wit_11.
Axiom proof_of_decode_shift_safety_wit_12 : decode_shift_safety_wit_12.
Axiom proof_of_decode_shift_safety_wit_13 : decode_shift_safety_wit_13.
Axiom proof_of_decode_shift_entail_wit_1 : decode_shift_entail_wit_1.
Axiom proof_of_decode_shift_entail_wit_2 : decode_shift_entail_wit_2.
Axiom proof_of_decode_shift_return_wit_1 : decode_shift_return_wit_1.
Axiom proof_of_decode_shift_partial_solve_wit_1 : decode_shift_partial_solve_wit_1.
Axiom proof_of_decode_shift_partial_solve_wit_2_pure : decode_shift_partial_solve_wit_2_pure.
Axiom proof_of_decode_shift_partial_solve_wit_2 : decode_shift_partial_solve_wit_2.
Axiom proof_of_decode_shift_partial_solve_wit_3 : decode_shift_partial_solve_wit_3.
Axiom proof_of_decode_shift_partial_solve_wit_4 : decode_shift_partial_solve_wit_4.
Axiom proof_of_decode_shift_partial_solve_wit_5 : decode_shift_partial_solve_wit_5.

End VC_Correct.
