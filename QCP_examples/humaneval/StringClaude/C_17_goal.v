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
Require Import coins_17.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function parse_music -----*)

Definition parse_music_safety_wit_1 := 
forall (music_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = len) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (music_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full music_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_music_safety_wit_2 := 
forall (music_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (music_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full music_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  [| ((retval + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (retval + 1 )) |]
.

Definition parse_music_safety_wit_3 := 
forall (music_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = len) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (music_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full music_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_music_safety_wit_4 := 
forall (music_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 = len) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (music_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "state" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (IntArray.undef_full retval_3 (retval_2 + 1 ) )
  **  (CharArray.full music_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_music_safety_wit_5 := 
forall (music_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 = len) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (music_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "state" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (IntArray.undef_full retval_3 (retval_2 + 1 ) )
  **  (CharArray.full music_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_music_safety_wit_6 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition parse_music_safety_wit_7 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_music_safety_wit_8 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition parse_music_safety_wit_9 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> 4)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition parse_music_safety_wit_10 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> 4)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_music_safety_wit_11 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition parse_music_safety_wit_12 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition parse_music_safety_wit_13 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> 2)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition parse_music_safety_wit_14 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> 2)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_music_safety_wit_15 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition parse_music_safety_wit_16 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_music_safety_wit_17 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition parse_music_safety_wit_18 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_music_safety_wit_19 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_music_safety_wit_20 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_music_safety_wit_21 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> 2)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_music_safety_wit_22 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> 4)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_music_safety_wit_23 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_music_safety_wit_24 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (111 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 111) |]
.

Definition parse_music_safety_wit_25 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 111) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_music_safety_wit_26 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_music_safety_wit_27 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_music_safety_wit_28 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| False |]
.

Definition parse_music_safety_wit_29 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| False |]
.

Definition parse_music_safety_wit_30 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (46 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 46) |]
.

Definition parse_music_safety_wit_31 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition parse_music_safety_wit_32 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_music_safety_wit_33 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_music_safety_wit_34 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| False |]
.

Definition parse_music_safety_wit_35 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (124 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 124) |]
.

Definition parse_music_safety_wit_36 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 124) |] 
  &&  [| (state = 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition parse_music_safety_wit_37 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) |] 
  &&  [| (state = 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition parse_music_safety_wit_38 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition parse_music_safety_wit_39 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition parse_music_safety_wit_40 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 3) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) |] 
  &&  [| (state = 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| False |]
.

Definition parse_music_safety_wit_41 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 3) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| False |]
.

Definition parse_music_safety_wit_42 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 3) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (124 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 124) |]
.

Definition parse_music_safety_wit_43 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 124) |] 
  &&  [| (state = 3) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition parse_music_safety_wit_44 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) |] 
  &&  [| (state = 3) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition parse_music_safety_wit_45 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 3) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) |] 
  &&  [| (state = 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition parse_music_safety_wit_46 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 3) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition parse_music_safety_wit_47 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 3) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition parse_music_safety_wit_48 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (out: Z) (data: Z) (i: Z) (state: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_l = (music_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (state = (music_prefix_state_z ((i + 1 )) (l))) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition parse_music_safety_wit_49 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_music_safety_wit_50 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition parse_music_safety_wit_51 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> 4)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition parse_music_safety_wit_52 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> 4)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_music_safety_wit_53 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition parse_music_safety_wit_54 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition parse_music_safety_wit_55 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> 2)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition parse_music_safety_wit_56 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> 2)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_music_safety_wit_57 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition parse_music_safety_wit_58 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_music_safety_wit_59 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition parse_music_safety_wit_60 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_music_entail_wit_1 := 
forall (music_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_3: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_3 = len) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (music_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (IntArray.undef_full retval_2 (retval_3 + 1 ) )
  **  (CharArray.full music_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 0) |] 
  &&  [| (output_l = (music_prefix_output_z (0) (l))) |] 
  &&  [| (0 = (music_prefix_state_z (0) (l))) |]
  &&  ((( &( "music_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg retval_2 0 output_size output_l )
  **  (IntArray.undef_seg retval_2 output_size (len + 1 ) )
.

Definition parse_music_entail_wit_2_1 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 (len + 1 ) )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_l = (music_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (music_prefix_state_z ((i + 1 )) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_2_2 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size_2 * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg data (output_size_2 + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size_2 + 1 ))
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_l = (music_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (music_prefix_state_z ((i + 1 )) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_2_3 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size_2 * sizeof(INT) ) )) # Int  |-> 2)
  **  (IntArray.undef_seg data (output_size_2 + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size_2 + 1 ))
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_l = (music_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (music_prefix_state_z ((i + 1 )) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_2_4 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size_2 * sizeof(INT) ) )) # Int  |-> 4)
  **  (IntArray.undef_seg data (output_size_2 + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size_2 + 1 ))
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_l = (music_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (music_prefix_state_z ((i + 1 )) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_2_5 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 111) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 (len + 1 ) )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_l = (music_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (1 = (music_prefix_state_z ((i + 1 )) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_2_6 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 (len + 1 ) )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= 3) |] 
  &&  [| (3 <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_l = (music_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (3 = (music_prefix_state_z ((i + 1 )) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_2_7 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 124) |] 
  &&  [| (state = 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 (len + 1 ) )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= 2) |] 
  &&  [| (2 <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_l = (music_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (2 = (music_prefix_state_z ((i + 1 )) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_2_8 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 124) |] 
  &&  [| (state = 3) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 (len + 1 ) )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= 4) |] 
  &&  [| (4 <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_l = (music_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (4 = (music_prefix_state_z ((i + 1 )) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_2_9 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) |] 
  &&  [| (state = 3) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 (len + 1 ) )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= 5) |] 
  &&  [| (5 <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_l = (music_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (5 = (music_prefix_state_z ((i + 1 )) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_2_10 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 3) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) |] 
  &&  [| (state = 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 (len + 1 ) )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= 5) |] 
  &&  [| (5 <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_l = (music_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (5 = (music_prefix_state_z ((i + 1 )) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_2_11 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 3) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 (len + 1 ) )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= 5) |] 
  &&  [| (5 <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_l = (music_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (5 = (music_prefix_state_z ((i + 1 )) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_2_12 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 3) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 (len + 1 ) )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= 5) |] 
  &&  [| (5 <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_l = (music_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (5 = (music_prefix_state_z ((i + 1 )) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_3 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (out: Z) (data: Z) (i: Z) (state: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= (i + 1 )) |] 
  &&  [| (output_l_2 = (music_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (state = (music_prefix_state_z ((i + 1 )) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 (len + 1 ) )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_l = (music_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (state = (music_prefix_state_z ((i + 1 )) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_4_1 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size_2 * sizeof(INT) ) )) # Int  |-> 4)
  **  (IntArray.undef_seg data (output_size_2 + 1 ) (len + 1 ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size_2 + 1 ))
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (len + 1 )) |] 
  &&  [| (output_l = (music_final_output_z ((music_prefix_output_z (len) (l))) ((music_prefix_state_z (len) (l))))) |]
  &&  ((( &( "i" ) )) # Int  |-> len)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_4_2 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size_2 * sizeof(INT) ) )) # Int  |-> 2)
  **  (IntArray.undef_seg data (output_size_2 + 1 ) (len + 1 ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size_2 + 1 ))
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (len + 1 )) |] 
  &&  [| (output_l = (music_final_output_z ((music_prefix_output_z (len) (l))) ((music_prefix_state_z (len) (l))))) |]
  &&  ((( &( "i" ) )) # Int  |-> len)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_4_3 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size_2 * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg data (output_size_2 + 1 ) (len + 1 ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size_2 + 1 ))
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (len + 1 )) |] 
  &&  [| (output_l = (music_final_output_z ((music_prefix_output_z (len) (l))) ((music_prefix_state_z (len) (l))))) |]
  &&  ((( &( "i" ) )) # Int  |-> len)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_entail_wit_4_4 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state <> 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_l_2 = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 (len + 1 ) )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (len + 1 )) |] 
  &&  [| (output_l = (music_final_output_z ((music_prefix_output_z (len) (l))) ((music_prefix_state_z (len) (l))))) |]
  &&  ((( &( "i" ) )) # Int  |-> len)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_return_wit_1 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (out: Z) (data_2: Z) (state: Z) ,
  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= (len + 1 )) |] 
  &&  [| (output_l_2 = (music_final_output_z ((music_prefix_output_z (len) (l))) ((music_prefix_state_z (len) (l))))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data_2 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data_2 output_size_2 (len + 1 ) )
|--
  EX (data: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (len + 1 )) |] 
  &&  [| (problem_17_spec_z l output_l ) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_partial_solve_wit_1 := 
forall (music_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) ,
  [| (music_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full music_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (music_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full music_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition parse_music_partial_solve_wit_2 := 
forall (music_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (music_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full music_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (music_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full music_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition parse_music_partial_solve_wit_3_pure := 
forall (music_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (music_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full music_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "music_string" ) )) # Ptr  |-> music_string_pre)
|--
  [| ((retval + 1 ) >= 0) |] 
  &&  [| ((retval + 1 ) < INT_MAX) |]
.

Definition parse_music_partial_solve_wit_3_aux := 
forall (music_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (music_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full music_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| ((retval + 1 ) >= 0) |] 
  &&  [| ((retval + 1 ) < INT_MAX) |] 
  &&  [| (retval = len) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (music_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full music_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Definition parse_music_partial_solve_wit_3 := parse_music_partial_solve_wit_3_pure -> parse_music_partial_solve_wit_3_aux.

Definition parse_music_partial_solve_wit_4 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((orig + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i orig i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_partial_solve_wit_5 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
.

Definition parse_music_partial_solve_wit_6 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
.

Definition parse_music_partial_solve_wit_7 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
.

Definition parse_music_partial_solve_wit_8 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((orig + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i orig i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_partial_solve_wit_9 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) |] 
  &&  [| (state = 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((orig + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i orig i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_partial_solve_wit_10 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (state = 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((orig + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i orig i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_partial_solve_wit_11 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 3) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (state = 3) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (state <> 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((orig + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i orig i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
.

Definition parse_music_partial_solve_wit_12 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
.

Definition parse_music_partial_solve_wit_13 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
.

Definition parse_music_partial_solve_wit_14 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (state: Z) (i: Z) (data: Z) (out: Z) ,
  [| (state = 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size (len + 1 ) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (state = 4) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_17_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 5) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_l = (music_prefix_output_z (i) (l))) |] 
  &&  [| (state = (music_prefix_state_z (i) (l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) (len + 1 ) )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_parse_music_safety_wit_1 : parse_music_safety_wit_1.
Axiom proof_of_parse_music_safety_wit_2 : parse_music_safety_wit_2.
Axiom proof_of_parse_music_safety_wit_3 : parse_music_safety_wit_3.
Axiom proof_of_parse_music_safety_wit_4 : parse_music_safety_wit_4.
Axiom proof_of_parse_music_safety_wit_5 : parse_music_safety_wit_5.
Axiom proof_of_parse_music_safety_wit_6 : parse_music_safety_wit_6.
Axiom proof_of_parse_music_safety_wit_7 : parse_music_safety_wit_7.
Axiom proof_of_parse_music_safety_wit_8 : parse_music_safety_wit_8.
Axiom proof_of_parse_music_safety_wit_9 : parse_music_safety_wit_9.
Axiom proof_of_parse_music_safety_wit_10 : parse_music_safety_wit_10.
Axiom proof_of_parse_music_safety_wit_11 : parse_music_safety_wit_11.
Axiom proof_of_parse_music_safety_wit_12 : parse_music_safety_wit_12.
Axiom proof_of_parse_music_safety_wit_13 : parse_music_safety_wit_13.
Axiom proof_of_parse_music_safety_wit_14 : parse_music_safety_wit_14.
Axiom proof_of_parse_music_safety_wit_15 : parse_music_safety_wit_15.
Axiom proof_of_parse_music_safety_wit_16 : parse_music_safety_wit_16.
Axiom proof_of_parse_music_safety_wit_17 : parse_music_safety_wit_17.
Axiom proof_of_parse_music_safety_wit_18 : parse_music_safety_wit_18.
Axiom proof_of_parse_music_safety_wit_19 : parse_music_safety_wit_19.
Axiom proof_of_parse_music_safety_wit_20 : parse_music_safety_wit_20.
Axiom proof_of_parse_music_safety_wit_21 : parse_music_safety_wit_21.
Axiom proof_of_parse_music_safety_wit_22 : parse_music_safety_wit_22.
Axiom proof_of_parse_music_safety_wit_23 : parse_music_safety_wit_23.
Axiom proof_of_parse_music_safety_wit_24 : parse_music_safety_wit_24.
Axiom proof_of_parse_music_safety_wit_25 : parse_music_safety_wit_25.
Axiom proof_of_parse_music_safety_wit_26 : parse_music_safety_wit_26.
Axiom proof_of_parse_music_safety_wit_27 : parse_music_safety_wit_27.
Axiom proof_of_parse_music_safety_wit_28 : parse_music_safety_wit_28.
Axiom proof_of_parse_music_safety_wit_29 : parse_music_safety_wit_29.
Axiom proof_of_parse_music_safety_wit_30 : parse_music_safety_wit_30.
Axiom proof_of_parse_music_safety_wit_31 : parse_music_safety_wit_31.
Axiom proof_of_parse_music_safety_wit_32 : parse_music_safety_wit_32.
Axiom proof_of_parse_music_safety_wit_33 : parse_music_safety_wit_33.
Axiom proof_of_parse_music_safety_wit_34 : parse_music_safety_wit_34.
Axiom proof_of_parse_music_safety_wit_35 : parse_music_safety_wit_35.
Axiom proof_of_parse_music_safety_wit_36 : parse_music_safety_wit_36.
Axiom proof_of_parse_music_safety_wit_37 : parse_music_safety_wit_37.
Axiom proof_of_parse_music_safety_wit_38 : parse_music_safety_wit_38.
Axiom proof_of_parse_music_safety_wit_39 : parse_music_safety_wit_39.
Axiom proof_of_parse_music_safety_wit_40 : parse_music_safety_wit_40.
Axiom proof_of_parse_music_safety_wit_41 : parse_music_safety_wit_41.
Axiom proof_of_parse_music_safety_wit_42 : parse_music_safety_wit_42.
Axiom proof_of_parse_music_safety_wit_43 : parse_music_safety_wit_43.
Axiom proof_of_parse_music_safety_wit_44 : parse_music_safety_wit_44.
Axiom proof_of_parse_music_safety_wit_45 : parse_music_safety_wit_45.
Axiom proof_of_parse_music_safety_wit_46 : parse_music_safety_wit_46.
Axiom proof_of_parse_music_safety_wit_47 : parse_music_safety_wit_47.
Axiom proof_of_parse_music_safety_wit_48 : parse_music_safety_wit_48.
Axiom proof_of_parse_music_safety_wit_49 : parse_music_safety_wit_49.
Axiom proof_of_parse_music_safety_wit_50 : parse_music_safety_wit_50.
Axiom proof_of_parse_music_safety_wit_51 : parse_music_safety_wit_51.
Axiom proof_of_parse_music_safety_wit_52 : parse_music_safety_wit_52.
Axiom proof_of_parse_music_safety_wit_53 : parse_music_safety_wit_53.
Axiom proof_of_parse_music_safety_wit_54 : parse_music_safety_wit_54.
Axiom proof_of_parse_music_safety_wit_55 : parse_music_safety_wit_55.
Axiom proof_of_parse_music_safety_wit_56 : parse_music_safety_wit_56.
Axiom proof_of_parse_music_safety_wit_57 : parse_music_safety_wit_57.
Axiom proof_of_parse_music_safety_wit_58 : parse_music_safety_wit_58.
Axiom proof_of_parse_music_safety_wit_59 : parse_music_safety_wit_59.
Axiom proof_of_parse_music_safety_wit_60 : parse_music_safety_wit_60.
Axiom proof_of_parse_music_entail_wit_1 : parse_music_entail_wit_1.
Axiom proof_of_parse_music_entail_wit_2_1 : parse_music_entail_wit_2_1.
Axiom proof_of_parse_music_entail_wit_2_2 : parse_music_entail_wit_2_2.
Axiom proof_of_parse_music_entail_wit_2_3 : parse_music_entail_wit_2_3.
Axiom proof_of_parse_music_entail_wit_2_4 : parse_music_entail_wit_2_4.
Axiom proof_of_parse_music_entail_wit_2_5 : parse_music_entail_wit_2_5.
Axiom proof_of_parse_music_entail_wit_2_6 : parse_music_entail_wit_2_6.
Axiom proof_of_parse_music_entail_wit_2_7 : parse_music_entail_wit_2_7.
Axiom proof_of_parse_music_entail_wit_2_8 : parse_music_entail_wit_2_8.
Axiom proof_of_parse_music_entail_wit_2_9 : parse_music_entail_wit_2_9.
Axiom proof_of_parse_music_entail_wit_2_10 : parse_music_entail_wit_2_10.
Axiom proof_of_parse_music_entail_wit_2_11 : parse_music_entail_wit_2_11.
Axiom proof_of_parse_music_entail_wit_2_12 : parse_music_entail_wit_2_12.
Axiom proof_of_parse_music_entail_wit_3 : parse_music_entail_wit_3.
Axiom proof_of_parse_music_entail_wit_4_1 : parse_music_entail_wit_4_1.
Axiom proof_of_parse_music_entail_wit_4_2 : parse_music_entail_wit_4_2.
Axiom proof_of_parse_music_entail_wit_4_3 : parse_music_entail_wit_4_3.
Axiom proof_of_parse_music_entail_wit_4_4 : parse_music_entail_wit_4_4.
Axiom proof_of_parse_music_return_wit_1 : parse_music_return_wit_1.
Axiom proof_of_parse_music_partial_solve_wit_1 : parse_music_partial_solve_wit_1.
Axiom proof_of_parse_music_partial_solve_wit_2 : parse_music_partial_solve_wit_2.
Axiom proof_of_parse_music_partial_solve_wit_3_pure : parse_music_partial_solve_wit_3_pure.
Axiom proof_of_parse_music_partial_solve_wit_3 : parse_music_partial_solve_wit_3.
Axiom proof_of_parse_music_partial_solve_wit_4 : parse_music_partial_solve_wit_4.
Axiom proof_of_parse_music_partial_solve_wit_5 : parse_music_partial_solve_wit_5.
Axiom proof_of_parse_music_partial_solve_wit_6 : parse_music_partial_solve_wit_6.
Axiom proof_of_parse_music_partial_solve_wit_7 : parse_music_partial_solve_wit_7.
Axiom proof_of_parse_music_partial_solve_wit_8 : parse_music_partial_solve_wit_8.
Axiom proof_of_parse_music_partial_solve_wit_9 : parse_music_partial_solve_wit_9.
Axiom proof_of_parse_music_partial_solve_wit_10 : parse_music_partial_solve_wit_10.
Axiom proof_of_parse_music_partial_solve_wit_11 : parse_music_partial_solve_wit_11.
Axiom proof_of_parse_music_partial_solve_wit_12 : parse_music_partial_solve_wit_12.
Axiom proof_of_parse_music_partial_solve_wit_13 : parse_music_partial_solve_wit_13.
Axiom proof_of_parse_music_partial_solve_wit_14 : parse_music_partial_solve_wit_14.

End VC_Correct.
