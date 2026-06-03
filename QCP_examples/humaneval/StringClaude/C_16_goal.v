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
Require Import coins_16.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function count_distinct_characters -----*)

Definition count_distinct_characters_safety_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "count" ) )) # Int  |->_)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_distinct_characters_safety_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_distinct_characters_safety_wit_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  ((( &( "seen" ) )) # Int  |->_)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_distinct_characters_safety_wit_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Int  |-> 0)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition count_distinct_characters_safety_wit_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Int  |-> 0)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (90 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 90) |]
.

Definition count_distinct_characters_safety_wit_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Int  |-> 0)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 )) |]
.

Definition count_distinct_characters_safety_wit_7 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Int  |-> 0)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition count_distinct_characters_safety_wit_8 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Int  |-> 0)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_distinct_characters_safety_wit_9 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Int  |-> 0)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_distinct_characters_safety_wit_10 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Int  |-> 0)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_distinct_characters_safety_wit_11 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (65 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 65) |]
.

Definition count_distinct_characters_safety_wit_12 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (90 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 90) |]
.

Definition count_distinct_characters_safety_wit_13 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 )) |]
.

Definition count_distinct_characters_safety_wit_14 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition count_distinct_characters_safety_wit_15 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| (((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 ) = c) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "d" ) )) # Int  |-> ((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_distinct_characters_safety_wit_16 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) = c) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_distinct_characters_safety_wit_17 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) = c) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_distinct_characters_safety_wit_18 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| (((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 ) <> c) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition count_distinct_characters_safety_wit_19 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) <> c) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition count_distinct_characters_safety_wit_20 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) <> c) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition count_distinct_characters_safety_wit_21 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) = c) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition count_distinct_characters_safety_wit_22 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) = c) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition count_distinct_characters_safety_wit_23 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| (((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 ) = c) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition count_distinct_characters_safety_wit_24 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| (j >= i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_distinct_characters_safety_wit_25 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| (seen = 0) |] 
  &&  [| (j >= i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition count_distinct_characters_safety_wit_26 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| (seen = 0) |] 
  &&  [| (j >= i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_distinct_characters_safety_wit_27 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| (seen <> 0) |] 
  &&  [| (j >= i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_distinct_characters_safety_wit_28 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| (seen = 0) |] 
  &&  [| (j >= i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_distinct_characters_entail_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 = (count_distinct_lower_upto (0) (l))) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_distinct_characters_entail_wit_2_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (lower_seen_state_z 0 i l ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) 0 ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_distinct_characters_entail_wit_2_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (lower_seen_state_z 0 i l (Znth i (app (l) ((cons (0) (nil)))) 0) 0 ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_distinct_characters_entail_wit_2_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| (lower_seen_state_z 0 i l (Znth i (app (l) ((cons (0) (nil)))) 0) 0 ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_distinct_characters_entail_wit_3_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| (((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 ) = c) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (lower_seen_state_z (j + 1 ) i l c 1 ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_distinct_characters_entail_wit_3_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) = c) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (lower_seen_state_z (j + 1 ) i l c 1 ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_distinct_characters_entail_wit_3_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) = c) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (lower_seen_state_z (j + 1 ) i l c 1 ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_distinct_characters_entail_wit_3_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) <> c) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) > 90) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (lower_seen_state_z (j + 1 ) i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_distinct_characters_entail_wit_3_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) <> c) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) < 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (lower_seen_state_z (j + 1 ) i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_distinct_characters_entail_wit_3_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| (((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 ) <> c) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) <= 90) |] 
  &&  [| ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) |] 
  &&  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= i) |] 
  &&  [| (lower_seen_state_z (j + 1 ) i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_distinct_characters_entail_wit_4_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| (seen = 0) |] 
  &&  [| (j >= i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= (i + 1 )) |] 
  &&  [| ((count + 1 ) = (count_distinct_lower_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_distinct_characters_entail_wit_4_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| (seen <> 0) |] 
  &&  [| (j >= i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i + 1 )) |] 
  &&  [| (count = (count_distinct_lower_upto ((i + 1 )) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_distinct_characters_return_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_16_spec_z l count ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_distinct_characters_partial_solve_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_distinct_characters_partial_solve_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (((str_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i str_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_distinct_characters_partial_solve_wit_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (seen: Z) (j: Z) (c: Z) (i: Z) ,
  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (j < i) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_16_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (c = (lower_z ((Znth (i) (l) (0))))) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= i) |] 
  &&  [| (lower_seen_state_z j i l c seen ) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= i) |] 
  &&  [| (count = (count_distinct_lower_upto (i) (l))) |]
  &&  (((str_pre + (j * sizeof(CHAR) ) )) # Char  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i str_pre j 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_count_distinct_characters_safety_wit_1 : count_distinct_characters_safety_wit_1.
Axiom proof_of_count_distinct_characters_safety_wit_2 : count_distinct_characters_safety_wit_2.
Axiom proof_of_count_distinct_characters_safety_wit_3 : count_distinct_characters_safety_wit_3.
Axiom proof_of_count_distinct_characters_safety_wit_4 : count_distinct_characters_safety_wit_4.
Axiom proof_of_count_distinct_characters_safety_wit_5 : count_distinct_characters_safety_wit_5.
Axiom proof_of_count_distinct_characters_safety_wit_6 : count_distinct_characters_safety_wit_6.
Axiom proof_of_count_distinct_characters_safety_wit_7 : count_distinct_characters_safety_wit_7.
Axiom proof_of_count_distinct_characters_safety_wit_8 : count_distinct_characters_safety_wit_8.
Axiom proof_of_count_distinct_characters_safety_wit_9 : count_distinct_characters_safety_wit_9.
Axiom proof_of_count_distinct_characters_safety_wit_10 : count_distinct_characters_safety_wit_10.
Axiom proof_of_count_distinct_characters_safety_wit_11 : count_distinct_characters_safety_wit_11.
Axiom proof_of_count_distinct_characters_safety_wit_12 : count_distinct_characters_safety_wit_12.
Axiom proof_of_count_distinct_characters_safety_wit_13 : count_distinct_characters_safety_wit_13.
Axiom proof_of_count_distinct_characters_safety_wit_14 : count_distinct_characters_safety_wit_14.
Axiom proof_of_count_distinct_characters_safety_wit_15 : count_distinct_characters_safety_wit_15.
Axiom proof_of_count_distinct_characters_safety_wit_16 : count_distinct_characters_safety_wit_16.
Axiom proof_of_count_distinct_characters_safety_wit_17 : count_distinct_characters_safety_wit_17.
Axiom proof_of_count_distinct_characters_safety_wit_18 : count_distinct_characters_safety_wit_18.
Axiom proof_of_count_distinct_characters_safety_wit_19 : count_distinct_characters_safety_wit_19.
Axiom proof_of_count_distinct_characters_safety_wit_20 : count_distinct_characters_safety_wit_20.
Axiom proof_of_count_distinct_characters_safety_wit_21 : count_distinct_characters_safety_wit_21.
Axiom proof_of_count_distinct_characters_safety_wit_22 : count_distinct_characters_safety_wit_22.
Axiom proof_of_count_distinct_characters_safety_wit_23 : count_distinct_characters_safety_wit_23.
Axiom proof_of_count_distinct_characters_safety_wit_24 : count_distinct_characters_safety_wit_24.
Axiom proof_of_count_distinct_characters_safety_wit_25 : count_distinct_characters_safety_wit_25.
Axiom proof_of_count_distinct_characters_safety_wit_26 : count_distinct_characters_safety_wit_26.
Axiom proof_of_count_distinct_characters_safety_wit_27 : count_distinct_characters_safety_wit_27.
Axiom proof_of_count_distinct_characters_safety_wit_28 : count_distinct_characters_safety_wit_28.
Axiom proof_of_count_distinct_characters_entail_wit_1 : count_distinct_characters_entail_wit_1.
Axiom proof_of_count_distinct_characters_entail_wit_2_1 : count_distinct_characters_entail_wit_2_1.
Axiom proof_of_count_distinct_characters_entail_wit_2_2 : count_distinct_characters_entail_wit_2_2.
Axiom proof_of_count_distinct_characters_entail_wit_2_3 : count_distinct_characters_entail_wit_2_3.
Axiom proof_of_count_distinct_characters_entail_wit_3_1 : count_distinct_characters_entail_wit_3_1.
Axiom proof_of_count_distinct_characters_entail_wit_3_2 : count_distinct_characters_entail_wit_3_2.
Axiom proof_of_count_distinct_characters_entail_wit_3_3 : count_distinct_characters_entail_wit_3_3.
Axiom proof_of_count_distinct_characters_entail_wit_3_4 : count_distinct_characters_entail_wit_3_4.
Axiom proof_of_count_distinct_characters_entail_wit_3_5 : count_distinct_characters_entail_wit_3_5.
Axiom proof_of_count_distinct_characters_entail_wit_3_6 : count_distinct_characters_entail_wit_3_6.
Axiom proof_of_count_distinct_characters_entail_wit_4_1 : count_distinct_characters_entail_wit_4_1.
Axiom proof_of_count_distinct_characters_entail_wit_4_2 : count_distinct_characters_entail_wit_4_2.
Axiom proof_of_count_distinct_characters_return_wit_1 : count_distinct_characters_return_wit_1.
Axiom proof_of_count_distinct_characters_partial_solve_wit_1 : count_distinct_characters_partial_solve_wit_1.
Axiom proof_of_count_distinct_characters_partial_solve_wit_2 : count_distinct_characters_partial_solve_wit_2.
Axiom proof_of_count_distinct_characters_partial_solve_wit_3 : count_distinct_characters_partial_solve_wit_3.

End VC_Correct.
