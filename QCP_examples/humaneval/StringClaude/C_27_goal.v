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
Require Import coins_27.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function filp_case -----*)

Definition filp_case_safety_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| ((retval + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval + 1 )) |]
.

Definition filp_case_safety_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition filp_case_safety_wit_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition filp_case_safety_wit_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (97 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 97) |]
.

Definition filp_case_safety_wit_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (122 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 122) |]
.

Definition filp_case_safety_wit_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 )) |]
.

Definition filp_case_safety_wit_7 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition filp_case_safety_wit_8 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition filp_case_safety_wit_9 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition filp_case_safety_wit_10 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition filp_case_safety_wit_11 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (90 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 90) |]
.

Definition filp_case_safety_wit_12 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (90 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 90) |]
.

Definition filp_case_safety_wit_13 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| False |]
.

Definition filp_case_safety_wit_14 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 )) |]
.

Definition filp_case_safety_wit_15 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition filp_case_safety_wit_16 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition filp_case_safety_wit_17 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition filp_case_safety_wit_18 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition filp_case_safety_wit_19 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition filp_case_safety_wit_20 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition filp_case_safety_wit_21 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition filp_case_entail_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval_2 = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  (CharArray.undef_full retval (retval_2 + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((Zlength (out_l)) = 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (len + 1 ) )
.

Definition filp_case_entail_wit_2_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition filp_case_entail_wit_2_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition filp_case_entail_wit_2_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition filp_case_entail_wit_2_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition filp_case_entail_wit_2_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| ((Zlength (out_l)) = (i + 1 )) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition filp_case_return_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l_2)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l_2) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (len + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (out_l)) = len) |] 
  &&  [| (problem_27_spec_z l out_l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition filp_case_partial_solve_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition filp_case_partial_solve_wit_2_pure := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| ((retval + 1 ) > 0) |]
.

Definition filp_case_partial_solve_wit_2_aux := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((retval + 1 ) > 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition filp_case_partial_solve_wit_2 := filp_case_partial_solve_wit_2_pure -> filp_case_partial_solve_wit_2_aux.

Definition filp_case_partial_solve_wit_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((str_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i str_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
.

Definition filp_case_partial_solve_wit_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition filp_case_partial_solve_wit_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition filp_case_partial_solve_wit_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition filp_case_partial_solve_wit_7 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition filp_case_partial_solve_wit_8 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition filp_case_partial_solve_wit_9 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_27_pre_z l ) |] 
  &&  [| (char_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| ((Zlength (out_l)) = i) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (out_l) (0)) = (flip_char_z ((Znth (k) (l) (0)))))) |]
  &&  (((out + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out len i (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_filp_case_safety_wit_1 : filp_case_safety_wit_1.
Axiom proof_of_filp_case_safety_wit_2 : filp_case_safety_wit_2.
Axiom proof_of_filp_case_safety_wit_3 : filp_case_safety_wit_3.
Axiom proof_of_filp_case_safety_wit_4 : filp_case_safety_wit_4.
Axiom proof_of_filp_case_safety_wit_5 : filp_case_safety_wit_5.
Axiom proof_of_filp_case_safety_wit_6 : filp_case_safety_wit_6.
Axiom proof_of_filp_case_safety_wit_7 : filp_case_safety_wit_7.
Axiom proof_of_filp_case_safety_wit_8 : filp_case_safety_wit_8.
Axiom proof_of_filp_case_safety_wit_9 : filp_case_safety_wit_9.
Axiom proof_of_filp_case_safety_wit_10 : filp_case_safety_wit_10.
Axiom proof_of_filp_case_safety_wit_11 : filp_case_safety_wit_11.
Axiom proof_of_filp_case_safety_wit_12 : filp_case_safety_wit_12.
Axiom proof_of_filp_case_safety_wit_13 : filp_case_safety_wit_13.
Axiom proof_of_filp_case_safety_wit_14 : filp_case_safety_wit_14.
Axiom proof_of_filp_case_safety_wit_15 : filp_case_safety_wit_15.
Axiom proof_of_filp_case_safety_wit_16 : filp_case_safety_wit_16.
Axiom proof_of_filp_case_safety_wit_17 : filp_case_safety_wit_17.
Axiom proof_of_filp_case_safety_wit_18 : filp_case_safety_wit_18.
Axiom proof_of_filp_case_safety_wit_19 : filp_case_safety_wit_19.
Axiom proof_of_filp_case_safety_wit_20 : filp_case_safety_wit_20.
Axiom proof_of_filp_case_safety_wit_21 : filp_case_safety_wit_21.
Axiom proof_of_filp_case_entail_wit_1 : filp_case_entail_wit_1.
Axiom proof_of_filp_case_entail_wit_2_1 : filp_case_entail_wit_2_1.
Axiom proof_of_filp_case_entail_wit_2_2 : filp_case_entail_wit_2_2.
Axiom proof_of_filp_case_entail_wit_2_3 : filp_case_entail_wit_2_3.
Axiom proof_of_filp_case_entail_wit_2_4 : filp_case_entail_wit_2_4.
Axiom proof_of_filp_case_entail_wit_2_5 : filp_case_entail_wit_2_5.
Axiom proof_of_filp_case_return_wit_1 : filp_case_return_wit_1.
Axiom proof_of_filp_case_partial_solve_wit_1 : filp_case_partial_solve_wit_1.
Axiom proof_of_filp_case_partial_solve_wit_2_pure : filp_case_partial_solve_wit_2_pure.
Axiom proof_of_filp_case_partial_solve_wit_2 : filp_case_partial_solve_wit_2.
Axiom proof_of_filp_case_partial_solve_wit_3 : filp_case_partial_solve_wit_3.
Axiom proof_of_filp_case_partial_solve_wit_4 : filp_case_partial_solve_wit_4.
Axiom proof_of_filp_case_partial_solve_wit_5 : filp_case_partial_solve_wit_5.
Axiom proof_of_filp_case_partial_solve_wit_6 : filp_case_partial_solve_wit_6.
Axiom proof_of_filp_case_partial_solve_wit_7 : filp_case_partial_solve_wit_7.
Axiom proof_of_filp_case_partial_solve_wit_8 : filp_case_partial_solve_wit_8.
Axiom proof_of_filp_case_partial_solve_wit_9 : filp_case_partial_solve_wit_9.

End VC_Correct.
