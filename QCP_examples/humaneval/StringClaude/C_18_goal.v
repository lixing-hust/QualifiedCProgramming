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
Require Import coins_18.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function how_many_times -----*)

Definition how_many_times_safety_wit_1 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  ((( &( "out" ) )) # Int  |->_)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition how_many_times_safety_wit_2 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Int  |-> 0)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition how_many_times_safety_wit_3 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Int  |-> 0)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition how_many_times_safety_wit_4 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Int  |-> 0)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition how_many_times_safety_wit_5 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  ((( &( "m0" ) )) # Int  |-> retval_2)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n0" ) )) # Int  |-> retval)
  **  ((( &( "ok" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Int  |-> 0)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition how_many_times_safety_wit_6 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  ((( &( "m0" ) )) # Int  |-> retval_2)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n0" ) )) # Int  |-> retval)
  **  ((( &( "ok" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Int  |-> 0)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition how_many_times_safety_wit_7 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  ((( &( "m0" ) )) # Int  |-> retval_2)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n0" ) )) # Int  |-> retval)
  **  ((( &( "ok" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Int  |-> 0)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition how_many_times_safety_wit_8 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  ((( &( "m0" ) )) # Int  |-> retval_2)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n0" ) )) # Int  |-> retval)
  **  ((( &( "ok" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Int  |-> 0)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition how_many_times_safety_wit_9 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 > retval) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  ((( &( "m0" ) )) # Int  |-> retval_2)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n0" ) )) # Int  |-> retval)
  **  ((( &( "ok" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Int  |-> 0)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition how_many_times_safety_wit_10 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <= retval) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  ((( &( "m0" ) )) # Int  |-> retval_2)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n0" ) )) # Int  |-> retval)
  **  ((( &( "ok" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Int  |-> 0)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition how_many_times_safety_wit_11 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (i: Z) (ok: Z) (j: Z) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= ((n - m ) + 1 )) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| ((n - m ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n - m )) |]
.

Definition how_many_times_safety_wit_12 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (i: Z) (ok: Z) (j: Z) ,
  [| (i <= (n - m )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= ((n - m ) + 1 )) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition how_many_times_safety_wit_13 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (i: Z) (j: Z) ,
  [| (i <= (n - m )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= ((n - m ) + 1 )) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition how_many_times_safety_wit_14 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| ((i + j ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + j )) |]
.

Definition how_many_times_safety_wit_15 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| ((i + j ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + j )) |]
.

Definition how_many_times_safety_wit_16 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| ((Znth (i + j ) (app (l) ((cons (0) (nil)))) 0) <> (Znth j (app (sub) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition how_many_times_safety_wit_17 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| ((Znth (i + j ) (app (l) ((cons (0) (nil)))) 0) <> (Znth j (app (sub) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition how_many_times_safety_wit_18 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| ((Znth (i + j ) (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (sub) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition how_many_times_safety_wit_19 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| ((Znth (i + j ) (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (sub) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition how_many_times_safety_wit_20 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| ((Znth (i + j ) (app (l) ((cons (0) (nil)))) 0) <> (Znth j (app (sub) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition how_many_times_safety_wit_21 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| ((Znth (i + j ) (app (l) ((cons (0) (nil)))) 0) <> (Znth j (app (sub) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Int  |-> out)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition how_many_times_safety_wit_22 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (j >= m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition how_many_times_safety_wit_23 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (j >= m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition how_many_times_safety_wit_24 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (ok = 1) |] 
  &&  [| (j >= m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| False |]
.

Definition how_many_times_safety_wit_25 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (ok <> 1) |] 
  &&  [| (j >= m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| False |]
.

Definition how_many_times_safety_wit_26 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (ok = 1) |] 
  &&  [| (j >= m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| ((out + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (out + 1 )) |]
.

Definition how_many_times_safety_wit_27 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (ok = 1) |] 
  &&  [| (j >= m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition how_many_times_safety_wit_28 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (ok <> 1) |] 
  &&  [| (j >= m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition how_many_times_safety_wit_29 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (ok = 1) |] 
  &&  [| (j >= m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "substring" ) )) # Ptr  |-> substring_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "out" ) )) # Int  |-> (out + 1 ))
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition how_many_times_entail_wit_1 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <= retval) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  ((( &( "m0" ) )) # Int  |-> retval_2)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n0" ) )) # Int  |-> retval)
|--
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= ((n - m ) + 1 )) |] 
  &&  [| (0 = (count_matches_upto (0) (l) (sub))) |]
  &&  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
.

Definition how_many_times_entail_wit_2 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| (i <= (n - m )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= ((n - m ) + 1 )) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  ([| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= m) |] 
  &&  [| (1 = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i 0 1 l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) ))
  ||
  ([| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= m) |] 
  &&  [| (1 = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i 0 1 l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) ))
.

Definition how_many_times_entail_wit_3_1 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| ((Znth (i + j ) (app (l) ((cons (0) (nil)))) 0) <> (Znth j (app (sub) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  ([| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= m) |] 
  &&  [| (0 = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i (j + 1 ) 0 l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) ))
  ||
  ([| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= m) |] 
  &&  [| (0 = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i (j + 1 ) 0 l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) ))
.

Definition how_many_times_entail_wit_3_2 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| ((Znth (i + j ) (app (l) ((cons (0) (nil)))) 0) <> (Znth j (app (sub) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  ([| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= m) |] 
  &&  [| (0 = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i (j + 1 ) 0 l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) ))
  ||
  ([| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= m) |] 
  &&  [| (0 = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i (j + 1 ) 0 l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) ))
.

Definition how_many_times_entail_wit_3_3 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| ((Znth (i + j ) (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (sub) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  ([| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i (j + 1 ) ok l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) ))
  ||
  ([| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i (j + 1 ) ok l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) ))
.

Definition how_many_times_entail_wit_3_4 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| ((Znth (i + j ) (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (sub) ((cons (0) (nil)))) 0)) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  ([| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i (j + 1 ) ok l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) ))
  ||
  ([| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i (j + 1 ) ok l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) ))
.

Definition how_many_times_entail_wit_4_1 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (ok = 1) |] 
  &&  [| (j >= m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= ((n - m ) + 1 )) |] 
  &&  [| ((out + 1 ) = (count_matches_upto ((i + 1 )) (l) (sub))) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
.

Definition how_many_times_entail_wit_4_2 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (ok <> 1) |] 
  &&  [| (j >= m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= ((n - m ) + 1 )) |] 
  &&  [| (out = (count_matches_upto ((i + 1 )) (l) (sub))) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
.

Definition how_many_times_return_wit_1 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (i: Z) ,
  [| (i > (n - m )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= ((n - m ) + 1 )) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (problem_18_spec_z l sub out ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
.

Definition how_many_times_return_wit_2 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 > retval) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_18_spec_z l sub 0 ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
.

Definition how_many_times_return_wit_3 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_18_spec_z l sub 0 ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
.

Definition how_many_times_return_wit_4 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval_2 = m) |] 
  &&  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_18_spec_z l sub 0 ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
.

Definition how_many_times_partial_solve_wit_1 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) ,
  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (0 <= (m + 1 )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
.

Definition how_many_times_partial_solve_wit_2 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (0 <= (n + 1 )) |] 
  &&  [| (retval = n) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |]
  &&  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition how_many_times_partial_solve_wit_3 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (((str_pre + ((i + j ) * sizeof(CHAR) ) )) # Char  |-> (Znth (i + j ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i str_pre (i + j ) 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
.

Definition how_many_times_partial_solve_wit_4 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (((str_pre + ((i + j ) * sizeof(CHAR) ) )) # Char  |-> (Znth (i + j ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i str_pre (i + j ) 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
.

Definition how_many_times_partial_solve_wit_5 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 0) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (((substring_pre + (j * sizeof(CHAR) ) )) # Char  |-> (Znth j (app (sub) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i substring_pre j 0 (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition how_many_times_partial_solve_wit_6 := 
forall (substring_pre: Z) (str_pre: Z) (m: Z) (sub: (@list Z)) (n: Z) (l: (@list Z)) (out: Z) (ok: Z) (j: Z) (i: Z) ,
  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full substring_pre (m + 1 ) (app (sub) ((cons (0) (nil)))) )
|--
  [| (0 <= (n + 1 )) |] 
  &&  [| (0 <= (m + 1 )) |] 
  &&  [| (j < m) |] 
  &&  [| (0 <= n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 <= m) |] 
  &&  [| (m < INT_MAX) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| ((Zlength (sub)) = m) |] 
  &&  [| (problem_18_pre_z l sub ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (ascii_range_z sub ) |] 
  &&  [| (0 < m) |] 
  &&  [| (m <= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (n - m )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= m) |] 
  &&  [| (ok = 1) |] 
  &&  [| (out = (count_matches_upto (i) (l) (sub))) |] 
  &&  [| (match_progress_z i j ok l sub ) |]
  &&  (((substring_pre + (j * sizeof(CHAR) ) )) # Char  |-> (Znth j (app (sub) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i substring_pre j 0 (m + 1 ) (app (sub) ((cons (0) (nil)))) )
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_how_many_times_safety_wit_1 : how_many_times_safety_wit_1.
Axiom proof_of_how_many_times_safety_wit_2 : how_many_times_safety_wit_2.
Axiom proof_of_how_many_times_safety_wit_3 : how_many_times_safety_wit_3.
Axiom proof_of_how_many_times_safety_wit_4 : how_many_times_safety_wit_4.
Axiom proof_of_how_many_times_safety_wit_5 : how_many_times_safety_wit_5.
Axiom proof_of_how_many_times_safety_wit_6 : how_many_times_safety_wit_6.
Axiom proof_of_how_many_times_safety_wit_7 : how_many_times_safety_wit_7.
Axiom proof_of_how_many_times_safety_wit_8 : how_many_times_safety_wit_8.
Axiom proof_of_how_many_times_safety_wit_9 : how_many_times_safety_wit_9.
Axiom proof_of_how_many_times_safety_wit_10 : how_many_times_safety_wit_10.
Axiom proof_of_how_many_times_safety_wit_11 : how_many_times_safety_wit_11.
Axiom proof_of_how_many_times_safety_wit_12 : how_many_times_safety_wit_12.
Axiom proof_of_how_many_times_safety_wit_13 : how_many_times_safety_wit_13.
Axiom proof_of_how_many_times_safety_wit_14 : how_many_times_safety_wit_14.
Axiom proof_of_how_many_times_safety_wit_15 : how_many_times_safety_wit_15.
Axiom proof_of_how_many_times_safety_wit_16 : how_many_times_safety_wit_16.
Axiom proof_of_how_many_times_safety_wit_17 : how_many_times_safety_wit_17.
Axiom proof_of_how_many_times_safety_wit_18 : how_many_times_safety_wit_18.
Axiom proof_of_how_many_times_safety_wit_19 : how_many_times_safety_wit_19.
Axiom proof_of_how_many_times_safety_wit_20 : how_many_times_safety_wit_20.
Axiom proof_of_how_many_times_safety_wit_21 : how_many_times_safety_wit_21.
Axiom proof_of_how_many_times_safety_wit_22 : how_many_times_safety_wit_22.
Axiom proof_of_how_many_times_safety_wit_23 : how_many_times_safety_wit_23.
Axiom proof_of_how_many_times_safety_wit_24 : how_many_times_safety_wit_24.
Axiom proof_of_how_many_times_safety_wit_25 : how_many_times_safety_wit_25.
Axiom proof_of_how_many_times_safety_wit_26 : how_many_times_safety_wit_26.
Axiom proof_of_how_many_times_safety_wit_27 : how_many_times_safety_wit_27.
Axiom proof_of_how_many_times_safety_wit_28 : how_many_times_safety_wit_28.
Axiom proof_of_how_many_times_safety_wit_29 : how_many_times_safety_wit_29.
Axiom proof_of_how_many_times_entail_wit_1 : how_many_times_entail_wit_1.
Axiom proof_of_how_many_times_entail_wit_2 : how_many_times_entail_wit_2.
Axiom proof_of_how_many_times_entail_wit_3_1 : how_many_times_entail_wit_3_1.
Axiom proof_of_how_many_times_entail_wit_3_2 : how_many_times_entail_wit_3_2.
Axiom proof_of_how_many_times_entail_wit_3_3 : how_many_times_entail_wit_3_3.
Axiom proof_of_how_many_times_entail_wit_3_4 : how_many_times_entail_wit_3_4.
Axiom proof_of_how_many_times_entail_wit_4_1 : how_many_times_entail_wit_4_1.
Axiom proof_of_how_many_times_entail_wit_4_2 : how_many_times_entail_wit_4_2.
Axiom proof_of_how_many_times_return_wit_1 : how_many_times_return_wit_1.
Axiom proof_of_how_many_times_return_wit_2 : how_many_times_return_wit_2.
Axiom proof_of_how_many_times_return_wit_3 : how_many_times_return_wit_3.
Axiom proof_of_how_many_times_return_wit_4 : how_many_times_return_wit_4.
Axiom proof_of_how_many_times_partial_solve_wit_1 : how_many_times_partial_solve_wit_1.
Axiom proof_of_how_many_times_partial_solve_wit_2 : how_many_times_partial_solve_wit_2.
Axiom proof_of_how_many_times_partial_solve_wit_3 : how_many_times_partial_solve_wit_3.
Axiom proof_of_how_many_times_partial_solve_wit_4 : how_many_times_partial_solve_wit_4.
Axiom proof_of_how_many_times_partial_solve_wit_5 : how_many_times_partial_solve_wit_5.
Axiom proof_of_how_many_times_partial_solve_wit_6 : how_many_times_partial_solve_wit_6.

End VC_Correct.
