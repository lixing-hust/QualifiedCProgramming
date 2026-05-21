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
Require Import coins_140.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function fix_spaces -----*)

Definition fix_spaces_safety_wit_1 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  [| ((retval + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval + 1 )) |]
.

Definition fix_spaces_safety_wit_2 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_3 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fix_spaces_safety_wit_4 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "spacelen" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fix_spaces_safety_wit_5 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fix_spaces_safety_wit_6 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition fix_spaces_safety_wit_7 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| ((spacelen + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (spacelen + 1 )) |]
.

Definition fix_spaces_safety_wit_8 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_9 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_10 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (95 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 95) |]
.

Definition fix_spaces_safety_wit_11 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition fix_spaces_safety_wit_12 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_13 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition fix_spaces_safety_wit_14 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (95 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 95) |]
.

Definition fix_spaces_safety_wit_15 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition fix_spaces_safety_wit_16 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_17 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (95 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 95) |]
.

Definition fix_spaces_safety_wit_18 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (95) (nil))))) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (((k + 1 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((k + 1 ) + 1 )) |]
.

Definition fix_spaces_safety_wit_19 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (95) (nil))))) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_20 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition fix_spaces_safety_wit_21 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (45 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 45) |]
.

Definition fix_spaces_safety_wit_22 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (45) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition fix_spaces_safety_wit_23 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (45) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_24 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen <= 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fix_spaces_safety_wit_25 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (45) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fix_spaces_safety_wit_26 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (95) (nil))))) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fix_spaces_safety_wit_27 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fix_spaces_safety_wit_28 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen <= 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition fix_spaces_safety_wit_29 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen <= 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_30 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (45) (nil))))) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (((k + 1 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((k + 1 ) + 1 )) |]
.

Definition fix_spaces_safety_wit_31 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (45) (nil))))) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_32 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= ((k + 1 ) + 1 )) |] 
  &&  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (((k + 1 ) + 1 ) + 1 ) (app ((app ((app (out_l) ((cons (95) (nil))))) ((cons (95) (nil))))) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (((k + 1 ) + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((((k + 1 ) + 1 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (((k + 1 ) + 1 ) + 1 )) |]
.

Definition fix_spaces_safety_wit_33 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= ((k + 1 ) + 1 )) |] 
  &&  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (((k + 1 ) + 1 ) + 1 ) (app ((app ((app (out_l) ((cons (95) (nil))))) ((cons (95) (nil))))) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (((k + 1 ) + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_34 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (95) (nil))))) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (((k + 1 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((k + 1 ) + 1 )) |]
.

Definition fix_spaces_safety_wit_35 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (95) (nil))))) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_36 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (95) (nil))))) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition fix_spaces_safety_wit_37 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= ((k + 1 ) + 1 )) |] 
  &&  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (((k + 1 ) + 1 ) + 1 ) (app ((app ((app (out_l) ((cons (95) (nil))))) ((cons (95) (nil))))) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (((k + 1 ) + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (((k + 1 ) + 1 ) + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition fix_spaces_safety_wit_38 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (45) (nil))))) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition fix_spaces_safety_wit_39 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen <= 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition fix_spaces_safety_wit_40 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> (spacelen + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition fix_spaces_safety_wit_41 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_42 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (95 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 95) |]
.

Definition fix_spaces_safety_wit_43 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition fix_spaces_safety_wit_44 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_45 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition fix_spaces_safety_wit_46 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (95 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 95) |]
.

Definition fix_spaces_safety_wit_47 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition fix_spaces_safety_wit_48 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_49 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (95 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 95) |]
.

Definition fix_spaces_safety_wit_50 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (95) (nil))))) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (((k + 1 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((k + 1 ) + 1 )) |]
.

Definition fix_spaces_safety_wit_51 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (95) (nil))))) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_52 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition fix_spaces_safety_wit_53 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (45 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 45) |]
.

Definition fix_spaces_safety_wit_54 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (45) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition fix_spaces_safety_wit_55 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (45) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fix_spaces_safety_wit_56 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen <= 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fix_spaces_safety_wit_57 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (45) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fix_spaces_safety_wit_58 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (95) (nil))))) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fix_spaces_safety_wit_59 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "spacelen" ) )) # Int  |-> spacelen)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fix_spaces_entail_wit_1 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval_2 = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.undef_full retval (retval_2 + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| ((0 + 0 ) <= 0) |] 
  &&  [| (0 = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (0) (l))) |] 
  &&  [| (0 = (fix_spaces_pending_z (0) (l))) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (len + 1 ) )
.

Definition fix_spaces_entail_wit_2_1 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l_2))) |] 
  &&  [| (out_l_2 = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l_2 )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= (i + 1 )) |] 
  &&  [| (0 <= (spacelen + 1 )) |] 
  &&  [| ((k + (spacelen + 1 ) ) <= (i + 1 )) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z ((i + 1 )) (l))) |] 
  &&  [| ((spacelen + 1 ) = (fix_spaces_pending_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
.

Definition fix_spaces_entail_wit_2_2 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen <= 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l_2))) |] 
  &&  [| (out_l_2 = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (k + 1 )) |] 
  &&  [| ((k + 1 ) <= (i + 1 )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (((k + 1 ) + 0 ) <= (i + 1 )) |] 
  &&  [| ((k + 1 ) = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (fix_spaces_pending_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (k + 1 ) out_l )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
.

Definition fix_spaces_entail_wit_2_3 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l_2))) |] 
  &&  [| (out_l_2 = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l_2) ((cons (45) (nil))))) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= ((k + 1 ) + 1 )) |] 
  &&  [| (((k + 1 ) + 1 ) <= (i + 1 )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| ((((k + 1 ) + 1 ) + 0 ) <= (i + 1 )) |] 
  &&  [| (((k + 1 ) + 1 ) = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (fix_spaces_pending_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out ((k + 1 ) + 1 ) out_l )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
.

Definition fix_spaces_entail_wit_2_4 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= ((k + 1 ) + 1 )) |] 
  &&  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l_2))) |] 
  &&  [| (out_l_2 = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (((k + 1 ) + 1 ) + 1 ) (app ((app ((app (out_l_2) ((cons (95) (nil))))) ((cons (95) (nil))))) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (((k + 1 ) + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= (((k + 1 ) + 1 ) + 1 )) |] 
  &&  [| ((((k + 1 ) + 1 ) + 1 ) <= (i + 1 )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (((((k + 1 ) + 1 ) + 1 ) + 0 ) <= (i + 1 )) |] 
  &&  [| ((((k + 1 ) + 1 ) + 1 ) = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (fix_spaces_pending_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (((k + 1 ) + 1 ) + 1 ) out_l )
  **  (CharArray.undef_seg out (((k + 1 ) + 1 ) + 1 ) (len + 1 ) )
.

Definition fix_spaces_entail_wit_2_5 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l_2))) |] 
  &&  [| (out_l_2 = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l_2) ((cons (95) (nil))))) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= ((k + 1 ) + 1 )) |] 
  &&  [| (((k + 1 ) + 1 ) <= (i + 1 )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| ((((k + 1 ) + 1 ) + 0 ) <= (i + 1 )) |] 
  &&  [| (((k + 1 ) + 1 ) = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (fix_spaces_pending_z ((i + 1 )) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out ((k + 1 ) + 1 ) out_l )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
.

Definition fix_spaces_return_wit_1 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen <= 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l_2))) |] 
  &&  [| (out_l_2 = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z))  (out_len: Z) ,
  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (problem_140_spec_z l out_l ) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 1 ) )
.

Definition fix_spaces_return_wit_2 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l_2))) |] 
  &&  [| (out_l_2 = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l_2) ((cons (45) (nil))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z))  (out_len: Z) ,
  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (problem_140_spec_z l out_l ) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 1 ) )
.

Definition fix_spaces_return_wit_3 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= ((k + 1 ) + 1 )) |] 
  &&  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l_2))) |] 
  &&  [| (out_l_2 = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (((k + 1 ) + 1 ) + 1 ) (app ((app ((app (out_l_2) ((cons (95) (nil))))) ((cons (95) (nil))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (((k + 1 ) + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z))  (out_len: Z) ,
  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (problem_140_spec_z l out_l ) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 1 ) )
.

Definition fix_spaces_return_wit_4 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l_2))) |] 
  &&  [| (out_l_2 = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l_2) ((cons (95) (nil))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z))  (out_len: Z) ,
  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| ((Zlength (out_l)) = out_len) |] 
  &&  [| (problem_140_spec_z l out_l ) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 1 ) )
.

Definition fix_spaces_partial_solve_wit_1 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition fix_spaces_partial_solve_wit_2_pure := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  [| ((retval + 1 ) > 0) |]
.

Definition fix_spaces_partial_solve_wit_2_aux := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((retval + 1 ) > 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition fix_spaces_partial_solve_wit_2 := fix_spaces_partial_solve_wit_2_pure -> fix_spaces_partial_solve_wit_2_aux.

Definition fix_spaces_partial_solve_wit_3 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((text_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i text_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
.

Definition fix_spaces_partial_solve_wit_4 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
.

Definition fix_spaces_partial_solve_wit_5 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
.

Definition fix_spaces_partial_solve_wit_6 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + ((k + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (k + 1 ) (k + 1 ) (len + 1 ) )
  **  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition fix_spaces_partial_solve_wit_7 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
.

Definition fix_spaces_partial_solve_wit_8 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + ((k + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (k + 1 ) (k + 1 ) (len + 1 ) )
  **  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition fix_spaces_partial_solve_wit_9 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (95) (nil))))) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= ((k + 1 ) + 1 )) |] 
  &&  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + (((k + 1 ) + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out ((k + 1 ) + 1 ) ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (95) (nil))))) ((cons (95) (nil)))) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition fix_spaces_partial_solve_wit_10 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (45) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + ((k + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (k + 1 ) (k + 1 ) (len + 1 ) )
  **  (CharArray.full out (k + 1 ) (app (out_l) ((cons (45) (nil)))) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition fix_spaces_partial_solve_wit_11 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen <= 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen <= 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
.

Definition fix_spaces_partial_solve_wit_12 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
.

Definition fix_spaces_partial_solve_wit_13 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
.

Definition fix_spaces_partial_solve_wit_14 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + ((k + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (k + 1 ) (k + 1 ) (len + 1 ) )
  **  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition fix_spaces_partial_solve_wit_15 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
.

Definition fix_spaces_partial_solve_wit_16 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (spacelen <= 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen <= 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out k out_l )
.

Definition fix_spaces_partial_solve_wit_17 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (45) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen > 2) |] 
  &&  [| (spacelen <> 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + ((k + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (k + 1 ) (k + 1 ) (len + 1 ) )
  **  (CharArray.full out (k + 1 ) (app (out_l) ((cons (45) (nil)))) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition fix_spaces_partial_solve_wit_18 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (95) (nil))))) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= ((k + 1 ) + 1 )) |] 
  &&  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 2) |] 
  &&  [| (spacelen <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + (((k + 1 ) + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out ((k + 1 ) + 1 ) ((k + 1 ) + 1 ) (len + 1 ) )
  **  (CharArray.full out ((k + 1 ) + 1 ) (app ((app (out_l) ((cons (95) (nil))))) ((cons (95) (nil)))) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition fix_spaces_partial_solve_wit_19 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (spacelen: Z) (k: Z) (i: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= (k + 1 )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (spacelen = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_140_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k <= i) |] 
  &&  [| (0 <= spacelen) |] 
  &&  [| ((k + spacelen ) <= i) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (fix_spaces_prefix_z (i) (l))) |] 
  &&  [| (spacelen = (fix_spaces_pending_z (i) (l))) |]
  &&  (((out + ((k + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (k + 1 ) (k + 1 ) (len + 1 ) )
  **  (CharArray.full out (k + 1 ) (app (out_l) ((cons (95) (nil)))) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_fix_spaces_safety_wit_1 : fix_spaces_safety_wit_1.
Axiom proof_of_fix_spaces_safety_wit_2 : fix_spaces_safety_wit_2.
Axiom proof_of_fix_spaces_safety_wit_3 : fix_spaces_safety_wit_3.
Axiom proof_of_fix_spaces_safety_wit_4 : fix_spaces_safety_wit_4.
Axiom proof_of_fix_spaces_safety_wit_5 : fix_spaces_safety_wit_5.
Axiom proof_of_fix_spaces_safety_wit_6 : fix_spaces_safety_wit_6.
Axiom proof_of_fix_spaces_safety_wit_7 : fix_spaces_safety_wit_7.
Axiom proof_of_fix_spaces_safety_wit_8 : fix_spaces_safety_wit_8.
Axiom proof_of_fix_spaces_safety_wit_9 : fix_spaces_safety_wit_9.
Axiom proof_of_fix_spaces_safety_wit_10 : fix_spaces_safety_wit_10.
Axiom proof_of_fix_spaces_safety_wit_11 : fix_spaces_safety_wit_11.
Axiom proof_of_fix_spaces_safety_wit_12 : fix_spaces_safety_wit_12.
Axiom proof_of_fix_spaces_safety_wit_13 : fix_spaces_safety_wit_13.
Axiom proof_of_fix_spaces_safety_wit_14 : fix_spaces_safety_wit_14.
Axiom proof_of_fix_spaces_safety_wit_15 : fix_spaces_safety_wit_15.
Axiom proof_of_fix_spaces_safety_wit_16 : fix_spaces_safety_wit_16.
Axiom proof_of_fix_spaces_safety_wit_17 : fix_spaces_safety_wit_17.
Axiom proof_of_fix_spaces_safety_wit_18 : fix_spaces_safety_wit_18.
Axiom proof_of_fix_spaces_safety_wit_19 : fix_spaces_safety_wit_19.
Axiom proof_of_fix_spaces_safety_wit_20 : fix_spaces_safety_wit_20.
Axiom proof_of_fix_spaces_safety_wit_21 : fix_spaces_safety_wit_21.
Axiom proof_of_fix_spaces_safety_wit_22 : fix_spaces_safety_wit_22.
Axiom proof_of_fix_spaces_safety_wit_23 : fix_spaces_safety_wit_23.
Axiom proof_of_fix_spaces_safety_wit_24 : fix_spaces_safety_wit_24.
Axiom proof_of_fix_spaces_safety_wit_25 : fix_spaces_safety_wit_25.
Axiom proof_of_fix_spaces_safety_wit_26 : fix_spaces_safety_wit_26.
Axiom proof_of_fix_spaces_safety_wit_27 : fix_spaces_safety_wit_27.
Axiom proof_of_fix_spaces_safety_wit_28 : fix_spaces_safety_wit_28.
Axiom proof_of_fix_spaces_safety_wit_29 : fix_spaces_safety_wit_29.
Axiom proof_of_fix_spaces_safety_wit_30 : fix_spaces_safety_wit_30.
Axiom proof_of_fix_spaces_safety_wit_31 : fix_spaces_safety_wit_31.
Axiom proof_of_fix_spaces_safety_wit_32 : fix_spaces_safety_wit_32.
Axiom proof_of_fix_spaces_safety_wit_33 : fix_spaces_safety_wit_33.
Axiom proof_of_fix_spaces_safety_wit_34 : fix_spaces_safety_wit_34.
Axiom proof_of_fix_spaces_safety_wit_35 : fix_spaces_safety_wit_35.
Axiom proof_of_fix_spaces_safety_wit_36 : fix_spaces_safety_wit_36.
Axiom proof_of_fix_spaces_safety_wit_37 : fix_spaces_safety_wit_37.
Axiom proof_of_fix_spaces_safety_wit_38 : fix_spaces_safety_wit_38.
Axiom proof_of_fix_spaces_safety_wit_39 : fix_spaces_safety_wit_39.
Axiom proof_of_fix_spaces_safety_wit_40 : fix_spaces_safety_wit_40.
Axiom proof_of_fix_spaces_safety_wit_41 : fix_spaces_safety_wit_41.
Axiom proof_of_fix_spaces_safety_wit_42 : fix_spaces_safety_wit_42.
Axiom proof_of_fix_spaces_safety_wit_43 : fix_spaces_safety_wit_43.
Axiom proof_of_fix_spaces_safety_wit_44 : fix_spaces_safety_wit_44.
Axiom proof_of_fix_spaces_safety_wit_45 : fix_spaces_safety_wit_45.
Axiom proof_of_fix_spaces_safety_wit_46 : fix_spaces_safety_wit_46.
Axiom proof_of_fix_spaces_safety_wit_47 : fix_spaces_safety_wit_47.
Axiom proof_of_fix_spaces_safety_wit_48 : fix_spaces_safety_wit_48.
Axiom proof_of_fix_spaces_safety_wit_49 : fix_spaces_safety_wit_49.
Axiom proof_of_fix_spaces_safety_wit_50 : fix_spaces_safety_wit_50.
Axiom proof_of_fix_spaces_safety_wit_51 : fix_spaces_safety_wit_51.
Axiom proof_of_fix_spaces_safety_wit_52 : fix_spaces_safety_wit_52.
Axiom proof_of_fix_spaces_safety_wit_53 : fix_spaces_safety_wit_53.
Axiom proof_of_fix_spaces_safety_wit_54 : fix_spaces_safety_wit_54.
Axiom proof_of_fix_spaces_safety_wit_55 : fix_spaces_safety_wit_55.
Axiom proof_of_fix_spaces_safety_wit_56 : fix_spaces_safety_wit_56.
Axiom proof_of_fix_spaces_safety_wit_57 : fix_spaces_safety_wit_57.
Axiom proof_of_fix_spaces_safety_wit_58 : fix_spaces_safety_wit_58.
Axiom proof_of_fix_spaces_safety_wit_59 : fix_spaces_safety_wit_59.
Axiom proof_of_fix_spaces_entail_wit_1 : fix_spaces_entail_wit_1.
Axiom proof_of_fix_spaces_entail_wit_2_1 : fix_spaces_entail_wit_2_1.
Axiom proof_of_fix_spaces_entail_wit_2_2 : fix_spaces_entail_wit_2_2.
Axiom proof_of_fix_spaces_entail_wit_2_3 : fix_spaces_entail_wit_2_3.
Axiom proof_of_fix_spaces_entail_wit_2_4 : fix_spaces_entail_wit_2_4.
Axiom proof_of_fix_spaces_entail_wit_2_5 : fix_spaces_entail_wit_2_5.
Axiom proof_of_fix_spaces_return_wit_1 : fix_spaces_return_wit_1.
Axiom proof_of_fix_spaces_return_wit_2 : fix_spaces_return_wit_2.
Axiom proof_of_fix_spaces_return_wit_3 : fix_spaces_return_wit_3.
Axiom proof_of_fix_spaces_return_wit_4 : fix_spaces_return_wit_4.
Axiom proof_of_fix_spaces_partial_solve_wit_1 : fix_spaces_partial_solve_wit_1.
Axiom proof_of_fix_spaces_partial_solve_wit_2_pure : fix_spaces_partial_solve_wit_2_pure.
Axiom proof_of_fix_spaces_partial_solve_wit_2 : fix_spaces_partial_solve_wit_2.
Axiom proof_of_fix_spaces_partial_solve_wit_3 : fix_spaces_partial_solve_wit_3.
Axiom proof_of_fix_spaces_partial_solve_wit_4 : fix_spaces_partial_solve_wit_4.
Axiom proof_of_fix_spaces_partial_solve_wit_5 : fix_spaces_partial_solve_wit_5.
Axiom proof_of_fix_spaces_partial_solve_wit_6 : fix_spaces_partial_solve_wit_6.
Axiom proof_of_fix_spaces_partial_solve_wit_7 : fix_spaces_partial_solve_wit_7.
Axiom proof_of_fix_spaces_partial_solve_wit_8 : fix_spaces_partial_solve_wit_8.
Axiom proof_of_fix_spaces_partial_solve_wit_9 : fix_spaces_partial_solve_wit_9.
Axiom proof_of_fix_spaces_partial_solve_wit_10 : fix_spaces_partial_solve_wit_10.
Axiom proof_of_fix_spaces_partial_solve_wit_11 : fix_spaces_partial_solve_wit_11.
Axiom proof_of_fix_spaces_partial_solve_wit_12 : fix_spaces_partial_solve_wit_12.
Axiom proof_of_fix_spaces_partial_solve_wit_13 : fix_spaces_partial_solve_wit_13.
Axiom proof_of_fix_spaces_partial_solve_wit_14 : fix_spaces_partial_solve_wit_14.
Axiom proof_of_fix_spaces_partial_solve_wit_15 : fix_spaces_partial_solve_wit_15.
Axiom proof_of_fix_spaces_partial_solve_wit_16 : fix_spaces_partial_solve_wit_16.
Axiom proof_of_fix_spaces_partial_solve_wit_17 : fix_spaces_partial_solve_wit_17.
Axiom proof_of_fix_spaces_partial_solve_wit_18 : fix_spaces_partial_solve_wit_18.
Axiom proof_of_fix_spaces_partial_solve_wit_19 : fix_spaces_partial_solve_wit_19.

End VC_Correct.
