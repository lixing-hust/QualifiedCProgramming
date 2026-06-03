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
Require Import coins_86.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function anti_shuffle -----*)

Definition anti_shuffle_safety_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "cap" ) )) # Int  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((retval + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval + 1 )) |]
.

Definition anti_shuffle_safety_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "cap" ) )) # Int  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition anti_shuffle_safety_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out_len" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "cur" ) )) # Ptr  |-> retval_3)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition anti_shuffle_safety_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "cur_len" ) )) # Int  |->_)
  **  ((( &( "out_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "cur" ) )) # Ptr  |-> retval_3)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition anti_shuffle_safety_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cur_len" ) )) # Int  |-> 0)
  **  ((( &( "out_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval_3 (retval + 1 ) )
  **  ((( &( "cur" ) )) # Ptr  |-> retval_3)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition anti_shuffle_safety_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.full cur cur_len (anti_cur_prefix_z (i) (l)) )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition anti_shuffle_safety_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full cur (cur_len + 1 ) (app ((anti_cur_prefix_z (i) (l))) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg cur (cur_len + 1 ) cap )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
|--
  [| ((cur_len + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (cur_len + 1 )) |]
.

Definition anti_shuffle_safety_wit_8 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full cur (cur_len + 1 ) (app ((anti_cur_prefix_z (i) (l))) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg cur (cur_len + 1 ) cap )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition anti_shuffle_safety_wit_9 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out (out_len + cur_len ) (app ((anti_out_prefix_z (i) (l))) ((sort_chars_z ((anti_cur_prefix_z (i) (l)))))) )
  **  (CharArray.undef_seg out (out_len + cur_len ) cap )
  **  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (i) (l)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| ((out_len + cur_len ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (out_len + cur_len )) |]
.

Definition anti_shuffle_safety_wit_10 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out (out_len + cur_len ) (app ((anti_out_prefix_z (i) (l))) ((sort_chars_z ((anti_cur_prefix_z (i) (l)))))) )
  **  (CharArray.undef_seg out (out_len + cur_len ) cap )
  **  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (i) (l)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + cur_len ))
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition anti_shuffle_safety_wit_11 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out (out_len + cur_len ) (app ((anti_out_prefix_z (i) (l))) ((sort_chars_z ((anti_cur_prefix_z (i) (l)))))) )
  **  (CharArray.undef_seg out (out_len + cur_len ) cap )
  **  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (i) (l)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + cur_len ))
  **  ((( &( "cur_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition anti_shuffle_safety_wit_12 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (out_len + cur_len )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out ((out_len + cur_len ) + 1 ) (app ((app ((anti_out_prefix_z (i) (l))) ((sort_chars_z ((anti_cur_prefix_z (i) (l))))))) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out ((out_len + cur_len ) + 1 ) cap )
  **  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (i) (l)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + cur_len ))
  **  ((( &( "cur_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (((out_len + cur_len ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((out_len + cur_len ) + 1 )) |]
.

Definition anti_shuffle_safety_wit_13 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (out_len + cur_len )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out ((out_len + cur_len ) + 1 ) (app ((app ((anti_out_prefix_z (i) (l))) ((sort_chars_z ((anti_cur_prefix_z (i) (l))))))) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out ((out_len + cur_len ) + 1 ) cap )
  **  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (i) (l)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + cur_len ))
  **  ((( &( "cur_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition anti_shuffle_safety_wit_14 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (out_len + cur_len )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out ((out_len + cur_len ) + 1 ) (app ((app ((anti_out_prefix_z (i) (l))) ((sort_chars_z ((anti_cur_prefix_z (i) (l))))))) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out ((out_len + cur_len ) + 1 ) cap )
  **  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (i) (l)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> ((out_len + cur_len ) + 1 ))
  **  ((( &( "cur_len" ) )) # Int  |-> 0)
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition anti_shuffle_safety_wit_15 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full cur (cur_len + 1 ) (app ((anti_cur_prefix_z (i) (l))) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg cur (cur_len + 1 ) cap )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> (cur_len + 1 ))
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition anti_shuffle_safety_wit_16 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out (out_len + cur_len ) (app ((anti_out_prefix_z (len) (l))) ((sort_chars_z ((anti_cur_prefix_z (len) (l)))))) )
  **  (CharArray.undef_seg out (out_len + cur_len ) cap )
  **  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (len) (l)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| ((out_len + cur_len ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (out_len + cur_len )) |]
.

Definition anti_shuffle_safety_wit_17 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (out_len + cur_len )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out (out_len + cur_len ) (app ((anti_out_prefix_z (len) (l))) ((sort_chars_z ((anti_cur_prefix_z (len) (l)))))) )
  **  (CharArray.undef_seg out (out_len + cur_len ) cap )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + cur_len ))
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition anti_shuffle_safety_wit_18 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (out_len + cur_len )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out (out_len + cur_len ) (app ((anti_out_prefix_z (len) (l))) ((sort_chars_z ((anti_cur_prefix_z (len) (l)))))) )
  **  (CharArray.undef_seg out (out_len + cur_len ) cap )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + cur_len ))
  **  ((( &( "cur_len" ) )) # Int  |-> 0)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition anti_shuffle_entail_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.undef_full retval_3 (retval + 1 ) )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  [| ((retval + 1 ) = (len + 1 )) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 = (Zlength ((anti_out_prefix_z (0) (l))))) |] 
  &&  [| (0 = (Zlength ((anti_cur_prefix_z (0) (l))))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((0 + 0 ) <= len) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval_2 0 (anti_out_prefix_z (0) (l)) )
  **  (CharArray.undef_seg retval_2 0 (retval + 1 ) )
  **  (CharArray.full retval_3 0 (anti_cur_prefix_z (0) (l)) )
  **  (CharArray.undef_seg retval_3 0 (retval + 1 ) )
.

Definition anti_shuffle_entail_wit_2_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full cur (cur_len + 1 ) (app ((anti_cur_prefix_z (i) (l))) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg cur (cur_len + 1 ) cap )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
|--
  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z ((i + 1 )) (l))))) |] 
  &&  [| ((cur_len + 1 ) = (Zlength ((anti_cur_prefix_z ((i + 1 )) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= (cur_len + 1 )) |] 
  &&  [| ((cur_len + 1 ) <= len) |] 
  &&  [| ((out_len + (cur_len + 1 ) ) <= len) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z ((i + 1 )) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.full cur (cur_len + 1 ) (anti_cur_prefix_z ((i + 1 )) (l)) )
  **  (CharArray.undef_seg cur (cur_len + 1 ) cap )
.

Definition anti_shuffle_entail_wit_2_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (out_len + cur_len )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out ((out_len + cur_len ) + 1 ) (app ((app ((anti_out_prefix_z (i) (l))) ((sort_chars_z ((anti_cur_prefix_z (i) (l))))))) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out ((out_len + cur_len ) + 1 ) cap )
  **  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (i) (l)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (((out_len + cur_len ) + 1 ) = (Zlength ((anti_out_prefix_z ((i + 1 )) (l))))) |] 
  &&  [| (0 = (Zlength ((anti_cur_prefix_z ((i + 1 )) (l))))) |] 
  &&  [| (0 <= ((out_len + cur_len ) + 1 )) |] 
  &&  [| (((out_len + cur_len ) + 1 ) <= len) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((((out_len + cur_len ) + 1 ) + 0 ) <= len) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out ((out_len + cur_len ) + 1 ) (anti_out_prefix_z ((i + 1 )) (l)) )
  **  (CharArray.undef_seg out ((out_len + cur_len ) + 1 ) cap )
  **  (CharArray.full cur 0 (anti_cur_prefix_z ((i + 1 )) (l)) )
  **  (CharArray.undef_seg cur 0 cap )
.

Definition anti_shuffle_entail_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (out_len + cur_len )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out ((out_len + cur_len ) + 1 ) (app ((app ((anti_out_prefix_z (len) (l))) ((sort_chars_z ((anti_cur_prefix_z (len) (l))))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out ((out_len + cur_len ) + 1 ) cap )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (i = len) |] 
  &&  [| ((out_len + cur_len ) = (Zlength ((anti_shuffle_output_z (l))))) |] 
  &&  [| (0 = 0) |] 
  &&  [| (problem_86_spec_z l (anti_shuffle_output_z (l)) ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out ((out_len + cur_len ) + 1 ) (app ((anti_shuffle_output_z (l))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out ((out_len + cur_len ) + 1 ) cap )
.

Definition anti_shuffle_return_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cap: Z) (out: Z) (cur: Z) (i: Z) (out_len: Z) (cur_len: Z) ,
  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (i = len) |] 
  &&  [| (out_len = (Zlength ((anti_shuffle_output_z (l))))) |] 
  &&  [| (cur_len = 0) |] 
  &&  [| (problem_86_spec_z l (anti_shuffle_output_z (l)) ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (out_len + 1 ) (app ((anti_shuffle_output_z (l))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) cap )
|--
  EX (out_l: (@list Z)) ,
  [| (problem_86_spec_z l out_l ) |]
  &&  (CharArray.full out ((Zlength (out_l)) + 1 ) (app (out_l) ((cons (0) (nil)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition anti_shuffle_partial_solve_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition anti_shuffle_partial_solve_wit_2_pure := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((retval + 1 ) > 0) |]
.

Definition anti_shuffle_partial_solve_wit_2_aux := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((retval + 1 ) > 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition anti_shuffle_partial_solve_wit_2 := anti_shuffle_partial_solve_wit_2_pure -> anti_shuffle_partial_solve_wit_2_aux.

Definition anti_shuffle_partial_solve_wit_3_pure := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "cur" ) )) # Ptr  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "cap" ) )) # Int  |-> (retval + 1 ))
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  [| ((retval + 1 ) > 0) |]
.

Definition anti_shuffle_partial_solve_wit_3_aux := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((retval + 1 ) > 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition anti_shuffle_partial_solve_wit_3 := anti_shuffle_partial_solve_wit_3_pure -> anti_shuffle_partial_solve_wit_3_aux.

Definition anti_shuffle_partial_solve_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.full cur cur_len (anti_cur_prefix_z (i) (l)) )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.full cur cur_len (anti_cur_prefix_z (i) (l)) )
  **  (CharArray.undef_seg cur cur_len cap )
.

Definition anti_shuffle_partial_solve_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.full cur cur_len (anti_cur_prefix_z (i) (l)) )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.full cur cur_len (anti_cur_prefix_z (i) (l)) )
  **  (CharArray.undef_seg cur cur_len cap )
.

Definition anti_shuffle_partial_solve_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.full cur cur_len (anti_cur_prefix_z (i) (l)) )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (((cur + (cur_len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i cur cur_len cur_len cap )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.full cur cur_len (anti_cur_prefix_z (i) (l)) )
.

Definition anti_shuffle_partial_solve_wit_7_pure := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.full cur cur_len (anti_cur_prefix_z (i) (l)) )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (0 <= cur_len) |] 
  &&  [| ((Zlength ((anti_cur_prefix_z (i) (l)))) = cur_len) |]
.

Definition anti_shuffle_partial_solve_wit_7_aux := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.full cur cur_len (anti_cur_prefix_z (i) (l)) )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (0 <= cur_len) |] 
  &&  [| ((Zlength ((anti_cur_prefix_z (i) (l)))) = cur_len) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full cur cur_len (anti_cur_prefix_z (i) (l)) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.undef_seg cur cur_len cap )
.

Definition anti_shuffle_partial_solve_wit_7 := anti_shuffle_partial_solve_wit_7_pure -> anti_shuffle_partial_solve_wit_7_aux.

Definition anti_shuffle_partial_solve_wit_8_pure := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (i) (l)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (0 <= out_len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| ((out_len + cur_len ) <= cap) |] 
  &&  [| ((Zlength ((anti_out_prefix_z (i) (l)))) = out_len) |] 
  &&  [| ((Zlength ((sort_chars_z ((anti_cur_prefix_z (i) (l)))))) = cur_len) |]
.

Definition anti_shuffle_partial_solve_wit_8_aux := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (i) (l)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (0 <= out_len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| ((out_len + cur_len ) <= cap) |] 
  &&  [| ((Zlength ((anti_out_prefix_z (i) (l)))) = out_len) |] 
  &&  [| ((Zlength ((sort_chars_z ((anti_cur_prefix_z (i) (l)))))) = cur_len) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (i) (l)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg cur cur_len cap )
.

Definition anti_shuffle_partial_solve_wit_8 := anti_shuffle_partial_solve_wit_8_pure -> anti_shuffle_partial_solve_wit_8_aux.

Definition anti_shuffle_partial_solve_wit_9 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out (out_len + cur_len ) (app ((anti_out_prefix_z (i) (l))) ((sort_chars_z ((anti_cur_prefix_z (i) (l)))))) )
  **  (CharArray.undef_seg out (out_len + cur_len ) cap )
  **  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (i) (l)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (0 <= (out_len + cur_len )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (((out + ((out_len + cur_len ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (out_len + cur_len ) (out_len + cur_len ) cap )
  **  (CharArray.full out (out_len + cur_len ) (app ((anti_out_prefix_z (i) (l))) ((sort_chars_z ((anti_cur_prefix_z (i) (l)))))) )
  **  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (i) (l)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg cur cur_len cap )
.

Definition anti_shuffle_partial_solve_wit_10_pure := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (i >= len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.full cur cur_len (anti_cur_prefix_z (i) (l)) )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (0 <= cur_len) |] 
  &&  [| ((Zlength ((anti_cur_prefix_z (len) (l)))) = cur_len) |]
.

Definition anti_shuffle_partial_solve_wit_10_aux := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (i >= len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.full cur cur_len (anti_cur_prefix_z (i) (l)) )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (0 <= cur_len) |] 
  &&  [| ((Zlength ((anti_cur_prefix_z (len) (l)))) = cur_len) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full cur cur_len (anti_cur_prefix_z (len) (l)) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.undef_seg cur cur_len cap )
.

Definition anti_shuffle_partial_solve_wit_10 := anti_shuffle_partial_solve_wit_10_pure -> anti_shuffle_partial_solve_wit_10_aux.

Definition anti_shuffle_partial_solve_wit_11_pure := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (len) (l)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (0 <= out_len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| ((out_len + cur_len ) <= cap) |] 
  &&  [| ((Zlength ((anti_out_prefix_z (len) (l)))) = out_len) |] 
  &&  [| ((Zlength ((sort_chars_z ((anti_cur_prefix_z (len) (l)))))) = cur_len) |]
.

Definition anti_shuffle_partial_solve_wit_11_aux := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (len) (l)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out out_len (anti_out_prefix_z (i) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (0 <= out_len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| ((out_len + cur_len ) <= cap) |] 
  &&  [| ((Zlength ((anti_out_prefix_z (len) (l)))) = out_len) |] 
  &&  [| ((Zlength ((sort_chars_z ((anti_cur_prefix_z (len) (l)))))) = cur_len) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out out_len (anti_out_prefix_z (len) (l)) )
  **  (CharArray.undef_seg out out_len cap )
  **  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (len) (l)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg cur cur_len cap )
.

Definition anti_shuffle_partial_solve_wit_11 := anti_shuffle_partial_solve_wit_11_pure -> anti_shuffle_partial_solve_wit_11_aux.

Definition anti_shuffle_partial_solve_wit_12_pure := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out (out_len + cur_len ) (app ((anti_out_prefix_z (len) (l))) ((sort_chars_z ((anti_cur_prefix_z (len) (l)))))) )
  **  (CharArray.undef_seg out (out_len + cur_len ) cap )
  **  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (len) (l)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_len" ) )) # Int  |-> (out_len + cur_len ))
  **  ((( &( "cur_len" ) )) # Int  |-> cur_len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (cur <> 0) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= cap) |] 
  &&  [| (0 <= cap) |] 
  &&  [| ((Zlength ((sort_chars_z ((anti_cur_prefix_z (len) (l)))))) = cur_len) |]
.

Definition anti_shuffle_partial_solve_wit_12_aux := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out (out_len + cur_len ) (app ((anti_out_prefix_z (len) (l))) ((sort_chars_z ((anti_cur_prefix_z (len) (l)))))) )
  **  (CharArray.undef_seg out (out_len + cur_len ) cap )
  **  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (len) (l)))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg cur cur_len cap )
|--
  [| (cur <> 0) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= cap) |] 
  &&  [| (0 <= cap) |] 
  &&  [| ((Zlength ((sort_chars_z ((anti_cur_prefix_z (len) (l)))))) = cur_len) |] 
  &&  [| (0 <= (out_len + cur_len )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full cur cur_len (sort_chars_z ((anti_cur_prefix_z (len) (l)))) )
  **  (CharArray.undef_seg cur cur_len cap )
  **  (CharArray.full out (out_len + cur_len ) (app ((anti_out_prefix_z (len) (l))) ((sort_chars_z ((anti_cur_prefix_z (len) (l)))))) )
  **  (CharArray.undef_seg out (out_len + cur_len ) cap )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition anti_shuffle_partial_solve_wit_12 := anti_shuffle_partial_solve_wit_12_pure -> anti_shuffle_partial_solve_wit_12_aux.

Definition anti_shuffle_partial_solve_wit_13 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (cur_len: Z) (out_len: Z) (i: Z) (cur: Z) (out: Z) (cap: Z) ,
  [| (0 <= (out_len + cur_len )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (CharArray.full out (out_len + cur_len ) (app ((anti_out_prefix_z (len) (l))) ((sort_chars_z ((anti_cur_prefix_z (len) (l)))))) )
  **  (CharArray.undef_seg out (out_len + cur_len ) cap )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= (out_len + cur_len )) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (cap = (len + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (cur <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_86_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (out_len = (Zlength ((anti_out_prefix_z (i) (l))))) |] 
  &&  [| (cur_len = (Zlength ((anti_cur_prefix_z (i) (l))))) |] 
  &&  [| (0 <= out_len) |] 
  &&  [| (out_len <= len) |] 
  &&  [| (0 <= cur_len) |] 
  &&  [| (cur_len <= len) |] 
  &&  [| ((out_len + cur_len ) <= len) |]
  &&  (((out + ((out_len + cur_len ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (out_len + cur_len ) (out_len + cur_len ) cap )
  **  (CharArray.full out (out_len + cur_len ) (app ((anti_out_prefix_z (len) (l))) ((sort_chars_z ((anti_cur_prefix_z (len) (l)))))) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_anti_shuffle_safety_wit_1 : anti_shuffle_safety_wit_1.
Axiom proof_of_anti_shuffle_safety_wit_2 : anti_shuffle_safety_wit_2.
Axiom proof_of_anti_shuffle_safety_wit_3 : anti_shuffle_safety_wit_3.
Axiom proof_of_anti_shuffle_safety_wit_4 : anti_shuffle_safety_wit_4.
Axiom proof_of_anti_shuffle_safety_wit_5 : anti_shuffle_safety_wit_5.
Axiom proof_of_anti_shuffle_safety_wit_6 : anti_shuffle_safety_wit_6.
Axiom proof_of_anti_shuffle_safety_wit_7 : anti_shuffle_safety_wit_7.
Axiom proof_of_anti_shuffle_safety_wit_8 : anti_shuffle_safety_wit_8.
Axiom proof_of_anti_shuffle_safety_wit_9 : anti_shuffle_safety_wit_9.
Axiom proof_of_anti_shuffle_safety_wit_10 : anti_shuffle_safety_wit_10.
Axiom proof_of_anti_shuffle_safety_wit_11 : anti_shuffle_safety_wit_11.
Axiom proof_of_anti_shuffle_safety_wit_12 : anti_shuffle_safety_wit_12.
Axiom proof_of_anti_shuffle_safety_wit_13 : anti_shuffle_safety_wit_13.
Axiom proof_of_anti_shuffle_safety_wit_14 : anti_shuffle_safety_wit_14.
Axiom proof_of_anti_shuffle_safety_wit_15 : anti_shuffle_safety_wit_15.
Axiom proof_of_anti_shuffle_safety_wit_16 : anti_shuffle_safety_wit_16.
Axiom proof_of_anti_shuffle_safety_wit_17 : anti_shuffle_safety_wit_17.
Axiom proof_of_anti_shuffle_safety_wit_18 : anti_shuffle_safety_wit_18.
Axiom proof_of_anti_shuffle_entail_wit_1 : anti_shuffle_entail_wit_1.
Axiom proof_of_anti_shuffle_entail_wit_2_1 : anti_shuffle_entail_wit_2_1.
Axiom proof_of_anti_shuffle_entail_wit_2_2 : anti_shuffle_entail_wit_2_2.
Axiom proof_of_anti_shuffle_entail_wit_3 : anti_shuffle_entail_wit_3.
Axiom proof_of_anti_shuffle_return_wit_1 : anti_shuffle_return_wit_1.
Axiom proof_of_anti_shuffle_partial_solve_wit_1 : anti_shuffle_partial_solve_wit_1.
Axiom proof_of_anti_shuffle_partial_solve_wit_2_pure : anti_shuffle_partial_solve_wit_2_pure.
Axiom proof_of_anti_shuffle_partial_solve_wit_2 : anti_shuffle_partial_solve_wit_2.
Axiom proof_of_anti_shuffle_partial_solve_wit_3_pure : anti_shuffle_partial_solve_wit_3_pure.
Axiom proof_of_anti_shuffle_partial_solve_wit_3 : anti_shuffle_partial_solve_wit_3.
Axiom proof_of_anti_shuffle_partial_solve_wit_4 : anti_shuffle_partial_solve_wit_4.
Axiom proof_of_anti_shuffle_partial_solve_wit_5 : anti_shuffle_partial_solve_wit_5.
Axiom proof_of_anti_shuffle_partial_solve_wit_6 : anti_shuffle_partial_solve_wit_6.
Axiom proof_of_anti_shuffle_partial_solve_wit_7_pure : anti_shuffle_partial_solve_wit_7_pure.
Axiom proof_of_anti_shuffle_partial_solve_wit_7 : anti_shuffle_partial_solve_wit_7.
Axiom proof_of_anti_shuffle_partial_solve_wit_8_pure : anti_shuffle_partial_solve_wit_8_pure.
Axiom proof_of_anti_shuffle_partial_solve_wit_8 : anti_shuffle_partial_solve_wit_8.
Axiom proof_of_anti_shuffle_partial_solve_wit_9 : anti_shuffle_partial_solve_wit_9.
Axiom proof_of_anti_shuffle_partial_solve_wit_10_pure : anti_shuffle_partial_solve_wit_10_pure.
Axiom proof_of_anti_shuffle_partial_solve_wit_10 : anti_shuffle_partial_solve_wit_10.
Axiom proof_of_anti_shuffle_partial_solve_wit_11_pure : anti_shuffle_partial_solve_wit_11_pure.
Axiom proof_of_anti_shuffle_partial_solve_wit_11 : anti_shuffle_partial_solve_wit_11.
Axiom proof_of_anti_shuffle_partial_solve_wit_12_pure : anti_shuffle_partial_solve_wit_12_pure.
Axiom proof_of_anti_shuffle_partial_solve_wit_12 : anti_shuffle_partial_solve_wit_12.
Axiom proof_of_anti_shuffle_partial_solve_wit_13 : anti_shuffle_partial_solve_wit_13.

End VC_Correct.
