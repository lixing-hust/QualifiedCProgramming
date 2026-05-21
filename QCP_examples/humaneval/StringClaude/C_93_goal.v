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
Require Import coins_93.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function encode -----*)

Definition encode_safety_wit_1 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
|--
  [| ((retval + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval + 1 )) |]
.

Definition encode_safety_wit_2 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition encode_safety_wit_3 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition encode_safety_wit_4 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition encode_safety_wit_5 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (122 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 122) |]
.

Definition encode_safety_wit_6 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 )) |]
.

Definition encode_safety_wit_7 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition encode_safety_wit_8 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition encode_safety_wit_9 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition encode_safety_wit_10 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_11 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (90 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 90) |]
.

Definition encode_safety_wit_12 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (90 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 90) |]
.

Definition encode_safety_wit_13 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_14 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 )) |]
.

Definition encode_safety_wit_15 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition encode_safety_wit_16 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition encode_safety_wit_17 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition encode_safety_wit_18 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition encode_safety_wit_19 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition encode_safety_wit_20 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition encode_safety_wit_21 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_22 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_23 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_24 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_25 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (69 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 69) |]
.

Definition encode_safety_wit_26 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (69 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 69) |]
.

Definition encode_safety_wit_27 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (69 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 69) |]
.

Definition encode_safety_wit_28 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (69 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 69) |]
.

Definition encode_safety_wit_29 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (69 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 69) |]
.

Definition encode_safety_wit_30 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_31 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_32 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_33 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_34 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (73 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 73) |]
.

Definition encode_safety_wit_35 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (73 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 73) |]
.

Definition encode_safety_wit_36 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (73 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 73) |]
.

Definition encode_safety_wit_37 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (73 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 73) |]
.

Definition encode_safety_wit_38 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (73 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 73) |]
.

Definition encode_safety_wit_39 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_40 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_41 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_42 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_43 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (79 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 79) |]
.

Definition encode_safety_wit_44 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (79 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 79) |]
.

Definition encode_safety_wit_45 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (79 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 79) |]
.

Definition encode_safety_wit_46 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (79 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 79) |]
.

Definition encode_safety_wit_47 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (79 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 79) |]
.

Definition encode_safety_wit_48 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_49 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_50 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_51 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_52 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (85 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 85) |]
.

Definition encode_safety_wit_53 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (85 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 85) |]
.

Definition encode_safety_wit_54 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (85 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 85) |]
.

Definition encode_safety_wit_55 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (85 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 85) |]
.

Definition encode_safety_wit_56 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (85 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 85) |]
.

Definition encode_safety_wit_57 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_58 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_59 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_60 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_61 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition encode_safety_wit_62 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition encode_safety_wit_63 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition encode_safety_wit_64 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition encode_safety_wit_65 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition encode_safety_wit_66 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_67 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_68 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_69 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_70 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (101 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 101) |]
.

Definition encode_safety_wit_71 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (101 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 101) |]
.

Definition encode_safety_wit_72 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (101 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 101) |]
.

Definition encode_safety_wit_73 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (101 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 101) |]
.

Definition encode_safety_wit_74 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (101 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 101) |]
.

Definition encode_safety_wit_75 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_76 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_77 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_78 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_79 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (105 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 105) |]
.

Definition encode_safety_wit_80 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (105 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 105) |]
.

Definition encode_safety_wit_81 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (105 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 105) |]
.

Definition encode_safety_wit_82 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (105 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 105) |]
.

Definition encode_safety_wit_83 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (105 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 105) |]
.

Definition encode_safety_wit_84 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_85 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_86 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_87 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_88 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (111 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 111) |]
.

Definition encode_safety_wit_89 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (111 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 111) |]
.

Definition encode_safety_wit_90 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (111 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 111) |]
.

Definition encode_safety_wit_91 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (111 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 111) |]
.

Definition encode_safety_wit_92 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (111 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 111) |]
.

Definition encode_safety_wit_93 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_94 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_95 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_96 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_97 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (117 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 117) |]
.

Definition encode_safety_wit_98 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (117 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 117) |]
.

Definition encode_safety_wit_99 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (117 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 117) |]
.

Definition encode_safety_wit_100 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (117 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 117) |]
.

Definition encode_safety_wit_101 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (117 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 117) |]
.

Definition encode_safety_wit_102 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 117) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_103 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
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
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_104 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
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
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_105 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
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
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition encode_safety_wit_106 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 117) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 )) |]
.

Definition encode_safety_wit_107 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 117) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition encode_safety_wit_108 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 )) |]
.

Definition encode_safety_wit_109 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition encode_safety_wit_110 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 )) |]
.

Definition encode_safety_wit_111 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition encode_safety_wit_112 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| ((((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 )) |]
.

Definition encode_safety_wit_113 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition encode_safety_wit_114 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| ((((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 )) |]
.

Definition encode_safety_wit_115 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition encode_safety_wit_116 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| ((((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 )) |]
.

Definition encode_safety_wit_117 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition encode_safety_wit_118 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| ((((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 )) |]
.

Definition encode_safety_wit_119 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition encode_safety_wit_120 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| ((((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 )) |]
.

Definition encode_safety_wit_121 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition encode_safety_wit_122 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 )) |]
.

Definition encode_safety_wit_123 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition encode_safety_wit_124 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 )) |]
.

Definition encode_safety_wit_125 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition encode_safety_wit_126 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 117) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_safety_wit_127 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_safety_wit_128 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_safety_wit_129 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_safety_wit_130 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_safety_wit_131 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_safety_wit_132 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_safety_wit_133 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_safety_wit_134 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_safety_wit_135 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_safety_wit_136 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
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
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_safety_wit_137 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
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
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_safety_wit_138 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
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
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_safety_wit_139 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 117) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_safety_wit_140 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 117) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition encode_safety_wit_141 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  ((( &( "message" ) )) # Ptr  |-> message_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition encode_entail_wit_1 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval_2 = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.undef_full retval (retval_2 + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((Zlength (out_l)) = 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (len + 1 ) )
.

Definition encode_entail_wit_2_1 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 117) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_entail_wit_2_2 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 117) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_entail_wit_2_3 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
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
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_entail_wit_2_4 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
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
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_entail_wit_2_5 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
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
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_entail_wit_2_6 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_entail_wit_2_7 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_entail_wit_2_8 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_entail_wit_2_9 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_entail_wit_2_10 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_entail_wit_2_11 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_entail_wit_2_12 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_entail_wit_2_13 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_entail_wit_2_14 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_entail_wit_2_15 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 117) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) + 2 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition encode_return_wit_1 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (len + 1 ) (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (out_l)) = len) |] 
  &&  [| (problem_93_spec_z l out_l ) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition encode_partial_solve_wit_1 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition encode_partial_solve_wit_2_pure := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "message" ) )) # Ptr  |-> message_pre)
|--
  [| ((retval + 1 ) > 0) |]
.

Definition encode_partial_solve_wit_2_aux := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((retval + 1 ) > 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition encode_partial_solve_wit_2 := encode_partial_solve_wit_2_pure -> encode_partial_solve_wit_2_aux.

Definition encode_partial_solve_wit_3 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((message_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i message_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
.

Definition encode_partial_solve_wit_4 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 117) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 117) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_partial_solve_wit_5 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 117) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 117) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_partial_solve_wit_6 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
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
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
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
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_partial_solve_wit_7 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
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
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
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
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_partial_solve_wit_8 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
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
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
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
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_partial_solve_wit_9 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_partial_solve_wit_10 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_partial_solve_wit_11 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_partial_solve_wit_12 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_partial_solve_wit_13 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_partial_solve_wit_14 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_partial_solve_wit_15 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) = 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_partial_solve_wit_16 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_partial_solve_wit_17 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_partial_solve_wit_18 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 117) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = 117) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 111) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 105) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 101) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 97) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 85) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 79) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 73) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 69) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <> 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition encode_partial_solve_wit_19 := 
forall (message_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_93_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (encode_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out len i (len + 1 ) )
  **  (CharArray.full message_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_encode_safety_wit_1 : encode_safety_wit_1.
Axiom proof_of_encode_safety_wit_2 : encode_safety_wit_2.
Axiom proof_of_encode_safety_wit_3 : encode_safety_wit_3.
Axiom proof_of_encode_safety_wit_4 : encode_safety_wit_4.
Axiom proof_of_encode_safety_wit_5 : encode_safety_wit_5.
Axiom proof_of_encode_safety_wit_6 : encode_safety_wit_6.
Axiom proof_of_encode_safety_wit_7 : encode_safety_wit_7.
Axiom proof_of_encode_safety_wit_8 : encode_safety_wit_8.
Axiom proof_of_encode_safety_wit_9 : encode_safety_wit_9.
Axiom proof_of_encode_safety_wit_10 : encode_safety_wit_10.
Axiom proof_of_encode_safety_wit_11 : encode_safety_wit_11.
Axiom proof_of_encode_safety_wit_12 : encode_safety_wit_12.
Axiom proof_of_encode_safety_wit_13 : encode_safety_wit_13.
Axiom proof_of_encode_safety_wit_14 : encode_safety_wit_14.
Axiom proof_of_encode_safety_wit_15 : encode_safety_wit_15.
Axiom proof_of_encode_safety_wit_16 : encode_safety_wit_16.
Axiom proof_of_encode_safety_wit_17 : encode_safety_wit_17.
Axiom proof_of_encode_safety_wit_18 : encode_safety_wit_18.
Axiom proof_of_encode_safety_wit_19 : encode_safety_wit_19.
Axiom proof_of_encode_safety_wit_20 : encode_safety_wit_20.
Axiom proof_of_encode_safety_wit_21 : encode_safety_wit_21.
Axiom proof_of_encode_safety_wit_22 : encode_safety_wit_22.
Axiom proof_of_encode_safety_wit_23 : encode_safety_wit_23.
Axiom proof_of_encode_safety_wit_24 : encode_safety_wit_24.
Axiom proof_of_encode_safety_wit_25 : encode_safety_wit_25.
Axiom proof_of_encode_safety_wit_26 : encode_safety_wit_26.
Axiom proof_of_encode_safety_wit_27 : encode_safety_wit_27.
Axiom proof_of_encode_safety_wit_28 : encode_safety_wit_28.
Axiom proof_of_encode_safety_wit_29 : encode_safety_wit_29.
Axiom proof_of_encode_safety_wit_30 : encode_safety_wit_30.
Axiom proof_of_encode_safety_wit_31 : encode_safety_wit_31.
Axiom proof_of_encode_safety_wit_32 : encode_safety_wit_32.
Axiom proof_of_encode_safety_wit_33 : encode_safety_wit_33.
Axiom proof_of_encode_safety_wit_34 : encode_safety_wit_34.
Axiom proof_of_encode_safety_wit_35 : encode_safety_wit_35.
Axiom proof_of_encode_safety_wit_36 : encode_safety_wit_36.
Axiom proof_of_encode_safety_wit_37 : encode_safety_wit_37.
Axiom proof_of_encode_safety_wit_38 : encode_safety_wit_38.
Axiom proof_of_encode_safety_wit_39 : encode_safety_wit_39.
Axiom proof_of_encode_safety_wit_40 : encode_safety_wit_40.
Axiom proof_of_encode_safety_wit_41 : encode_safety_wit_41.
Axiom proof_of_encode_safety_wit_42 : encode_safety_wit_42.
Axiom proof_of_encode_safety_wit_43 : encode_safety_wit_43.
Axiom proof_of_encode_safety_wit_44 : encode_safety_wit_44.
Axiom proof_of_encode_safety_wit_45 : encode_safety_wit_45.
Axiom proof_of_encode_safety_wit_46 : encode_safety_wit_46.
Axiom proof_of_encode_safety_wit_47 : encode_safety_wit_47.
Axiom proof_of_encode_safety_wit_48 : encode_safety_wit_48.
Axiom proof_of_encode_safety_wit_49 : encode_safety_wit_49.
Axiom proof_of_encode_safety_wit_50 : encode_safety_wit_50.
Axiom proof_of_encode_safety_wit_51 : encode_safety_wit_51.
Axiom proof_of_encode_safety_wit_52 : encode_safety_wit_52.
Axiom proof_of_encode_safety_wit_53 : encode_safety_wit_53.
Axiom proof_of_encode_safety_wit_54 : encode_safety_wit_54.
Axiom proof_of_encode_safety_wit_55 : encode_safety_wit_55.
Axiom proof_of_encode_safety_wit_56 : encode_safety_wit_56.
Axiom proof_of_encode_safety_wit_57 : encode_safety_wit_57.
Axiom proof_of_encode_safety_wit_58 : encode_safety_wit_58.
Axiom proof_of_encode_safety_wit_59 : encode_safety_wit_59.
Axiom proof_of_encode_safety_wit_60 : encode_safety_wit_60.
Axiom proof_of_encode_safety_wit_61 : encode_safety_wit_61.
Axiom proof_of_encode_safety_wit_62 : encode_safety_wit_62.
Axiom proof_of_encode_safety_wit_63 : encode_safety_wit_63.
Axiom proof_of_encode_safety_wit_64 : encode_safety_wit_64.
Axiom proof_of_encode_safety_wit_65 : encode_safety_wit_65.
Axiom proof_of_encode_safety_wit_66 : encode_safety_wit_66.
Axiom proof_of_encode_safety_wit_67 : encode_safety_wit_67.
Axiom proof_of_encode_safety_wit_68 : encode_safety_wit_68.
Axiom proof_of_encode_safety_wit_69 : encode_safety_wit_69.
Axiom proof_of_encode_safety_wit_70 : encode_safety_wit_70.
Axiom proof_of_encode_safety_wit_71 : encode_safety_wit_71.
Axiom proof_of_encode_safety_wit_72 : encode_safety_wit_72.
Axiom proof_of_encode_safety_wit_73 : encode_safety_wit_73.
Axiom proof_of_encode_safety_wit_74 : encode_safety_wit_74.
Axiom proof_of_encode_safety_wit_75 : encode_safety_wit_75.
Axiom proof_of_encode_safety_wit_76 : encode_safety_wit_76.
Axiom proof_of_encode_safety_wit_77 : encode_safety_wit_77.
Axiom proof_of_encode_safety_wit_78 : encode_safety_wit_78.
Axiom proof_of_encode_safety_wit_79 : encode_safety_wit_79.
Axiom proof_of_encode_safety_wit_80 : encode_safety_wit_80.
Axiom proof_of_encode_safety_wit_81 : encode_safety_wit_81.
Axiom proof_of_encode_safety_wit_82 : encode_safety_wit_82.
Axiom proof_of_encode_safety_wit_83 : encode_safety_wit_83.
Axiom proof_of_encode_safety_wit_84 : encode_safety_wit_84.
Axiom proof_of_encode_safety_wit_85 : encode_safety_wit_85.
Axiom proof_of_encode_safety_wit_86 : encode_safety_wit_86.
Axiom proof_of_encode_safety_wit_87 : encode_safety_wit_87.
Axiom proof_of_encode_safety_wit_88 : encode_safety_wit_88.
Axiom proof_of_encode_safety_wit_89 : encode_safety_wit_89.
Axiom proof_of_encode_safety_wit_90 : encode_safety_wit_90.
Axiom proof_of_encode_safety_wit_91 : encode_safety_wit_91.
Axiom proof_of_encode_safety_wit_92 : encode_safety_wit_92.
Axiom proof_of_encode_safety_wit_93 : encode_safety_wit_93.
Axiom proof_of_encode_safety_wit_94 : encode_safety_wit_94.
Axiom proof_of_encode_safety_wit_95 : encode_safety_wit_95.
Axiom proof_of_encode_safety_wit_96 : encode_safety_wit_96.
Axiom proof_of_encode_safety_wit_97 : encode_safety_wit_97.
Axiom proof_of_encode_safety_wit_98 : encode_safety_wit_98.
Axiom proof_of_encode_safety_wit_99 : encode_safety_wit_99.
Axiom proof_of_encode_safety_wit_100 : encode_safety_wit_100.
Axiom proof_of_encode_safety_wit_101 : encode_safety_wit_101.
Axiom proof_of_encode_safety_wit_102 : encode_safety_wit_102.
Axiom proof_of_encode_safety_wit_103 : encode_safety_wit_103.
Axiom proof_of_encode_safety_wit_104 : encode_safety_wit_104.
Axiom proof_of_encode_safety_wit_105 : encode_safety_wit_105.
Axiom proof_of_encode_safety_wit_106 : encode_safety_wit_106.
Axiom proof_of_encode_safety_wit_107 : encode_safety_wit_107.
Axiom proof_of_encode_safety_wit_108 : encode_safety_wit_108.
Axiom proof_of_encode_safety_wit_109 : encode_safety_wit_109.
Axiom proof_of_encode_safety_wit_110 : encode_safety_wit_110.
Axiom proof_of_encode_safety_wit_111 : encode_safety_wit_111.
Axiom proof_of_encode_safety_wit_112 : encode_safety_wit_112.
Axiom proof_of_encode_safety_wit_113 : encode_safety_wit_113.
Axiom proof_of_encode_safety_wit_114 : encode_safety_wit_114.
Axiom proof_of_encode_safety_wit_115 : encode_safety_wit_115.
Axiom proof_of_encode_safety_wit_116 : encode_safety_wit_116.
Axiom proof_of_encode_safety_wit_117 : encode_safety_wit_117.
Axiom proof_of_encode_safety_wit_118 : encode_safety_wit_118.
Axiom proof_of_encode_safety_wit_119 : encode_safety_wit_119.
Axiom proof_of_encode_safety_wit_120 : encode_safety_wit_120.
Axiom proof_of_encode_safety_wit_121 : encode_safety_wit_121.
Axiom proof_of_encode_safety_wit_122 : encode_safety_wit_122.
Axiom proof_of_encode_safety_wit_123 : encode_safety_wit_123.
Axiom proof_of_encode_safety_wit_124 : encode_safety_wit_124.
Axiom proof_of_encode_safety_wit_125 : encode_safety_wit_125.
Axiom proof_of_encode_safety_wit_126 : encode_safety_wit_126.
Axiom proof_of_encode_safety_wit_127 : encode_safety_wit_127.
Axiom proof_of_encode_safety_wit_128 : encode_safety_wit_128.
Axiom proof_of_encode_safety_wit_129 : encode_safety_wit_129.
Axiom proof_of_encode_safety_wit_130 : encode_safety_wit_130.
Axiom proof_of_encode_safety_wit_131 : encode_safety_wit_131.
Axiom proof_of_encode_safety_wit_132 : encode_safety_wit_132.
Axiom proof_of_encode_safety_wit_133 : encode_safety_wit_133.
Axiom proof_of_encode_safety_wit_134 : encode_safety_wit_134.
Axiom proof_of_encode_safety_wit_135 : encode_safety_wit_135.
Axiom proof_of_encode_safety_wit_136 : encode_safety_wit_136.
Axiom proof_of_encode_safety_wit_137 : encode_safety_wit_137.
Axiom proof_of_encode_safety_wit_138 : encode_safety_wit_138.
Axiom proof_of_encode_safety_wit_139 : encode_safety_wit_139.
Axiom proof_of_encode_safety_wit_140 : encode_safety_wit_140.
Axiom proof_of_encode_safety_wit_141 : encode_safety_wit_141.
Axiom proof_of_encode_entail_wit_1 : encode_entail_wit_1.
Axiom proof_of_encode_entail_wit_2_1 : encode_entail_wit_2_1.
Axiom proof_of_encode_entail_wit_2_2 : encode_entail_wit_2_2.
Axiom proof_of_encode_entail_wit_2_3 : encode_entail_wit_2_3.
Axiom proof_of_encode_entail_wit_2_4 : encode_entail_wit_2_4.
Axiom proof_of_encode_entail_wit_2_5 : encode_entail_wit_2_5.
Axiom proof_of_encode_entail_wit_2_6 : encode_entail_wit_2_6.
Axiom proof_of_encode_entail_wit_2_7 : encode_entail_wit_2_7.
Axiom proof_of_encode_entail_wit_2_8 : encode_entail_wit_2_8.
Axiom proof_of_encode_entail_wit_2_9 : encode_entail_wit_2_9.
Axiom proof_of_encode_entail_wit_2_10 : encode_entail_wit_2_10.
Axiom proof_of_encode_entail_wit_2_11 : encode_entail_wit_2_11.
Axiom proof_of_encode_entail_wit_2_12 : encode_entail_wit_2_12.
Axiom proof_of_encode_entail_wit_2_13 : encode_entail_wit_2_13.
Axiom proof_of_encode_entail_wit_2_14 : encode_entail_wit_2_14.
Axiom proof_of_encode_entail_wit_2_15 : encode_entail_wit_2_15.
Axiom proof_of_encode_return_wit_1 : encode_return_wit_1.
Axiom proof_of_encode_partial_solve_wit_1 : encode_partial_solve_wit_1.
Axiom proof_of_encode_partial_solve_wit_2_pure : encode_partial_solve_wit_2_pure.
Axiom proof_of_encode_partial_solve_wit_2 : encode_partial_solve_wit_2.
Axiom proof_of_encode_partial_solve_wit_3 : encode_partial_solve_wit_3.
Axiom proof_of_encode_partial_solve_wit_4 : encode_partial_solve_wit_4.
Axiom proof_of_encode_partial_solve_wit_5 : encode_partial_solve_wit_5.
Axiom proof_of_encode_partial_solve_wit_6 : encode_partial_solve_wit_6.
Axiom proof_of_encode_partial_solve_wit_7 : encode_partial_solve_wit_7.
Axiom proof_of_encode_partial_solve_wit_8 : encode_partial_solve_wit_8.
Axiom proof_of_encode_partial_solve_wit_9 : encode_partial_solve_wit_9.
Axiom proof_of_encode_partial_solve_wit_10 : encode_partial_solve_wit_10.
Axiom proof_of_encode_partial_solve_wit_11 : encode_partial_solve_wit_11.
Axiom proof_of_encode_partial_solve_wit_12 : encode_partial_solve_wit_12.
Axiom proof_of_encode_partial_solve_wit_13 : encode_partial_solve_wit_13.
Axiom proof_of_encode_partial_solve_wit_14 : encode_partial_solve_wit_14.
Axiom proof_of_encode_partial_solve_wit_15 : encode_partial_solve_wit_15.
Axiom proof_of_encode_partial_solve_wit_16 : encode_partial_solve_wit_16.
Axiom proof_of_encode_partial_solve_wit_17 : encode_partial_solve_wit_17.
Axiom proof_of_encode_partial_solve_wit_18 : encode_partial_solve_wit_18.
Axiom proof_of_encode_partial_solve_wit_19 : encode_partial_solve_wit_19.

End VC_Correct.
