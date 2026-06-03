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
Require Import coins_6.
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

(*----- Function parse_nested_parens -----*)

Definition parse_nested_parens_safety_wit_1 := 
forall (paren_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = len) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (paren_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full paren_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_nested_parens_safety_wit_2 := 
forall (paren_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 = len) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (paren_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "level" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (IntArray.undef_full retval_3 retval_2 )
  **  (CharArray.full paren_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_nested_parens_safety_wit_3 := 
forall (paren_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 = len) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (paren_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "max_level" ) )) # Int  |->_)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (IntArray.undef_full retval_3 retval_2 )
  **  (CharArray.full paren_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_nested_parens_safety_wit_4 := 
forall (paren_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 = len) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (paren_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "in_group" ) )) # Int  |->_)
  **  ((( &( "max_level" ) )) # Int  |-> 0)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (IntArray.undef_full retval_3 retval_2 )
  **  (CharArray.full paren_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_nested_parens_safety_wit_5 := 
forall (paren_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 = len) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (paren_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "in_group" ) )) # Int  |-> 0)
  **  ((( &( "max_level" ) )) # Int  |-> 0)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (IntArray.undef_full retval_3 retval_2 )
  **  (CharArray.full paren_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_nested_parens_safety_wit_6 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> in_group)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition parse_nested_parens_safety_wit_7 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (in_group <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> max_level)
  **  (IntArray.undef_seg data (output_size + 1 ) len )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> in_group)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition parse_nested_parens_safety_wit_8 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (in_group <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> max_level)
  **  (IntArray.undef_seg data (output_size + 1 ) len )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> in_group)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_nested_parens_safety_wit_9 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (in_group <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> max_level)
  **  (IntArray.undef_seg data (output_size + 1 ) len )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> in_group)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_nested_parens_safety_wit_10 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (in_group <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> max_level)
  **  (IntArray.undef_seg data (output_size + 1 ) len )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> in_group)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_nested_parens_safety_wit_11 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (in_group <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> max_level)
  **  (IntArray.undef_seg data (output_size + 1 ) len )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> in_group)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  ((( &( "max_level" ) )) # Int  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_nested_parens_safety_wit_12 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> in_group)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_nested_parens_safety_wit_13 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> 1)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
|--
  [| (40 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 40) |]
.

Definition parse_nested_parens_safety_wit_14 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> 1)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
|--
  [| ((level + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (level + 1 )) |]
.

Definition parse_nested_parens_safety_wit_15 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> 1)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_nested_parens_safety_wit_16 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> 1)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition parse_nested_parens_safety_wit_17 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (level > 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> 1)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
|--
  [| ((level - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (level - 1 )) |]
.

Definition parse_nested_parens_safety_wit_18 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (level > 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> 1)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_nested_parens_safety_wit_19 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (out: Z) (data: Z) (i: Z) (in_group: Z) (level: Z) (max_level: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| ((output_size + in_group ) <= (i + 1 )) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z ((i + 1 )) (l))) |] 
  &&  [| (level = (paren_prefix_level_z ((i + 1 )) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= (i + 1 )) |] 
  &&  [| ((-(i + 1 )) <= level) |] 
  &&  [| (level <= (i + 1 )) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> in_group)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition parse_nested_parens_safety_wit_20 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (in_group <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> max_level)
  **  (IntArray.undef_seg data (output_size + 1 ) len )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> in_group)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition parse_nested_parens_safety_wit_21 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (in_group <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> max_level)
  **  (IntArray.undef_seg data (output_size + 1 ) len )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "in_group" ) )) # Int  |-> in_group)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "max_level" ) )) # Int  |-> max_level)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition parse_nested_parens_entail_wit_1 := 
forall (paren_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_3: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_3 = len) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (paren_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (IntArray.undef_full retval_2 retval_3 )
  **  (CharArray.full paren_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 0) |] 
  &&  [| ((output_size + 0 ) <= 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (0) (l))) |] 
  &&  [| (0 = (paren_prefix_in_group_z (0) (l))) |] 
  &&  [| (0 = (paren_prefix_level_z (0) (l))) |] 
  &&  [| (0 = (paren_prefix_max_z (0) (l))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| ((-0) <= 0) |] 
  &&  [| (0 <= 0) |]
  &&  ((( &( "paren_string" ) )) # Ptr  |-> orig)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg retval_2 0 output_size output_l )
  **  (IntArray.undef_seg retval_2 output_size len )
.

Definition parse_nested_parens_entail_wit_2_1 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (in_group: Z) (output_size_2: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| ((output_size_2 + in_group ) <= i) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (output_l_2 = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (in_group <> 0) |]
  &&  (((data + (output_size_2 * sizeof(INT) ) )) # Int  |-> max_level)
  **  (IntArray.undef_seg data (output_size_2 + 1 ) len )
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
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| ((output_size + 0 ) <= (i + 1 )) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (paren_prefix_in_group_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (paren_prefix_level_z ((i + 1 )) (l))) |] 
  &&  [| (0 = (paren_prefix_max_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((-(i + 1 )) <= 0) |] 
  &&  [| (0 <= (i + 1 )) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
.

Definition parse_nested_parens_entail_wit_2_2 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (in_group: Z) (output_size_2: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| ((output_size_2 + in_group ) <= i) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (output_l_2 = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (in_group = 0) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 len )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| ((output_size + in_group ) <= (i + 1 )) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z ((i + 1 )) (l))) |] 
  &&  [| (level = (paren_prefix_level_z ((i + 1 )) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= (i + 1 )) |] 
  &&  [| ((-(i + 1 )) <= level) |] 
  &&  [| (level <= (i + 1 )) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
.

Definition parse_nested_parens_entail_wit_2_3 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (in_group: Z) (output_size_2: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((level + 1 ) > max_level) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| ((output_size_2 + in_group ) <= i) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (output_l_2 = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 len )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| ((output_size + 1 ) <= (i + 1 )) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (1 = (paren_prefix_in_group_z ((i + 1 )) (l))) |] 
  &&  [| ((level + 1 ) = (paren_prefix_level_z ((i + 1 )) (l))) |] 
  &&  [| ((level + 1 ) = (paren_prefix_max_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (0 <= (level + 1 )) |] 
  &&  [| ((level + 1 ) <= (i + 1 )) |] 
  &&  [| ((-(i + 1 )) <= (level + 1 )) |] 
  &&  [| ((level + 1 ) <= (i + 1 )) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
.

Definition parse_nested_parens_entail_wit_2_4 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (in_group: Z) (output_size_2: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((level + 1 ) <= max_level) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 40) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| ((output_size_2 + in_group ) <= i) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (output_l_2 = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 len )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| ((output_size + 1 ) <= (i + 1 )) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (1 = (paren_prefix_in_group_z ((i + 1 )) (l))) |] 
  &&  [| ((level + 1 ) = (paren_prefix_level_z ((i + 1 )) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= (i + 1 )) |] 
  &&  [| ((-(i + 1 )) <= (level + 1 )) |] 
  &&  [| ((level + 1 ) <= (i + 1 )) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
.

Definition parse_nested_parens_entail_wit_2_5 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (in_group: Z) (output_size_2: Z) (i: Z) (data: Z) (out: Z) ,
  [| (level > 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| ((output_size_2 + in_group ) <= i) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (output_l_2 = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 len )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| ((output_size + 1 ) <= (i + 1 )) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (1 = (paren_prefix_in_group_z ((i + 1 )) (l))) |] 
  &&  [| ((level - 1 ) = (paren_prefix_level_z ((i + 1 )) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= (i + 1 )) |] 
  &&  [| ((-(i + 1 )) <= (level - 1 )) |] 
  &&  [| ((level - 1 ) <= (i + 1 )) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
.

Definition parse_nested_parens_entail_wit_2_6 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (in_group: Z) (output_size_2: Z) (i: Z) (data: Z) (out: Z) ,
  [| (level <= 0) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 40) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| ((output_size_2 + in_group ) <= i) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (output_l_2 = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 len )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| ((output_size + 1 ) <= (i + 1 )) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (1 = (paren_prefix_in_group_z ((i + 1 )) (l))) |] 
  &&  [| (level = (paren_prefix_level_z ((i + 1 )) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= (i + 1 )) |] 
  &&  [| ((-(i + 1 )) <= level) |] 
  &&  [| (level <= (i + 1 )) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
.

Definition parse_nested_parens_entail_wit_3 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (out: Z) (data: Z) (i: Z) (in_group: Z) (level: Z) (max_level: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < len) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= (i + 1 )) |] 
  &&  [| ((output_size_2 + in_group ) <= (i + 1 )) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (output_l_2 = (paren_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z ((i + 1 )) (l))) |] 
  &&  [| (level = (paren_prefix_level_z ((i + 1 )) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= (i + 1 )) |] 
  &&  [| ((-(i + 1 )) <= level) |] 
  &&  [| (level <= (i + 1 )) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 len )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| ((output_size + in_group ) <= (i + 1 )) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z ((i + 1 )) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z ((i + 1 )) (l))) |] 
  &&  [| (level = (paren_prefix_level_z ((i + 1 )) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= (i + 1 )) |] 
  &&  [| ((-(i + 1 )) <= level) |] 
  &&  [| (level <= (i + 1 )) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
.

Definition parse_nested_parens_entail_wit_4_1 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (in_group: Z) (output_size_2: Z) (i: Z) (data: Z) (out: Z) ,
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| ((output_size_2 + in_group ) <= i) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (output_l_2 = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (in_group <> 0) |]
  &&  (((data + (output_size_2 * sizeof(INT) ) )) # Int  |-> max_level)
  **  (IntArray.undef_seg data (output_size_2 + 1 ) len )
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
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (len) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (len) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (len) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= len) |] 
  &&  [| (output_l = (paren_final_output_z ((paren_prefix_output_z (len) (l))) ((paren_prefix_in_group_z (len) (l))) ((paren_prefix_max_z (len) (l))))) |]
  &&  ((( &( "i" ) )) # Int  |-> len)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
.

Definition parse_nested_parens_entail_wit_4_2 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l_2: (@list Z)) (in_group: Z) (output_size_2: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| ((output_size_2 + in_group ) <= i) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (output_l_2 = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (in_group = 0) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 len )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (len) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (len) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (len) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= len) |] 
  &&  [| (output_l = (paren_final_output_z ((paren_prefix_output_z (len) (l))) ((paren_prefix_in_group_z (len) (l))) ((paren_prefix_max_z (len) (l))))) |]
  &&  ((( &( "i" ) )) # Int  |-> len)
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
.

Definition parse_nested_parens_return_wit_1 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (out: Z) (data_2: Z) (in_group: Z) (level: Z) (max_level: Z) ,
  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (len) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (len) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (len) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= len) |] 
  &&  [| (output_l_2 = (paren_final_output_z ((paren_prefix_output_z (len) (l))) ((paren_prefix_in_group_z (len) (l))) ((paren_prefix_max_z (len) (l))))) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data_2 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data_2 output_size_2 len )
|--
  EX (data: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= len) |] 
  &&  [| (problem_6_spec_z l output_l ) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
.

Definition parse_nested_parens_partial_solve_wit_1 := 
forall (paren_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) ,
  [| (paren_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full paren_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (paren_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full paren_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition parse_nested_parens_partial_solve_wit_2 := 
forall (paren_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (paren_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full paren_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (retval <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (paren_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full paren_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition parse_nested_parens_partial_solve_wit_3_pure := 
forall (paren_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (paren_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full paren_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  [| (retval >= 0) |] 
  &&  [| (retval < INT_MAX) |]
.

Definition parse_nested_parens_partial_solve_wit_3_aux := 
forall (paren_string_pre: Z) (orig: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (paren_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full paren_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| (retval >= 0) |] 
  &&  [| (retval < INT_MAX) |] 
  &&  [| (retval = len) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= (len + 1 )) |] 
  &&  [| (paren_string_pre = orig) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full paren_string_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Definition parse_nested_parens_partial_solve_wit_3 := parse_nested_parens_partial_solve_wit_3_pure -> parse_nested_parens_partial_solve_wit_3_aux.

Definition parse_nested_parens_partial_solve_wit_4 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
|--
  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (((orig + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i orig i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
.

Definition parse_nested_parens_partial_solve_wit_5 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (in_group <> 0) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (in_group <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) len )
  **  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
.

Definition parse_nested_parens_partial_solve_wit_6 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
|--
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) |] 
  &&  [| (i < len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |]
  &&  (((orig + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i orig i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
.

Definition parse_nested_parens_partial_solve_wit_7 := 
forall (orig: Z) (len: Z) (l: (@list Z)) (max_level: Z) (level: Z) (output_l: (@list Z)) (in_group: Z) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (in_group <> 0) |]
  &&  (CharArray.full orig (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size len )
|--
  [| (0 <= (len + 1 )) |] 
  &&  [| (i >= len) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| ((len + 1 ) < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_6_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| ((output_size + in_group ) <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = (paren_prefix_output_z (i) (l))) |] 
  &&  [| (in_group = (paren_prefix_in_group_z (i) (l))) |] 
  &&  [| (level = (paren_prefix_level_z (i) (l))) |] 
  &&  [| (max_level = (paren_prefix_max_z (i) (l))) |] 
  &&  [| (0 <= in_group) |] 
  &&  [| (in_group <= 1) |] 
  &&  [| (0 <= max_level) |] 
  &&  [| (max_level <= i) |] 
  &&  [| ((-i) <= level) |] 
  &&  [| (level <= i) |] 
  &&  [| (in_group <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) len )
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

Axiom proof_of_parse_nested_parens_safety_wit_1 : parse_nested_parens_safety_wit_1.
Axiom proof_of_parse_nested_parens_safety_wit_2 : parse_nested_parens_safety_wit_2.
Axiom proof_of_parse_nested_parens_safety_wit_3 : parse_nested_parens_safety_wit_3.
Axiom proof_of_parse_nested_parens_safety_wit_4 : parse_nested_parens_safety_wit_4.
Axiom proof_of_parse_nested_parens_safety_wit_5 : parse_nested_parens_safety_wit_5.
Axiom proof_of_parse_nested_parens_safety_wit_6 : parse_nested_parens_safety_wit_6.
Axiom proof_of_parse_nested_parens_safety_wit_7 : parse_nested_parens_safety_wit_7.
Axiom proof_of_parse_nested_parens_safety_wit_8 : parse_nested_parens_safety_wit_8.
Axiom proof_of_parse_nested_parens_safety_wit_9 : parse_nested_parens_safety_wit_9.
Axiom proof_of_parse_nested_parens_safety_wit_10 : parse_nested_parens_safety_wit_10.
Axiom proof_of_parse_nested_parens_safety_wit_11 : parse_nested_parens_safety_wit_11.
Axiom proof_of_parse_nested_parens_safety_wit_12 : parse_nested_parens_safety_wit_12.
Axiom proof_of_parse_nested_parens_safety_wit_13 : parse_nested_parens_safety_wit_13.
Axiom proof_of_parse_nested_parens_safety_wit_14 : parse_nested_parens_safety_wit_14.
Axiom proof_of_parse_nested_parens_safety_wit_15 : parse_nested_parens_safety_wit_15.
Axiom proof_of_parse_nested_parens_safety_wit_16 : parse_nested_parens_safety_wit_16.
Axiom proof_of_parse_nested_parens_safety_wit_17 : parse_nested_parens_safety_wit_17.
Axiom proof_of_parse_nested_parens_safety_wit_18 : parse_nested_parens_safety_wit_18.
Axiom proof_of_parse_nested_parens_safety_wit_19 : parse_nested_parens_safety_wit_19.
Axiom proof_of_parse_nested_parens_safety_wit_20 : parse_nested_parens_safety_wit_20.
Axiom proof_of_parse_nested_parens_safety_wit_21 : parse_nested_parens_safety_wit_21.
Axiom proof_of_parse_nested_parens_entail_wit_1 : parse_nested_parens_entail_wit_1.
Axiom proof_of_parse_nested_parens_entail_wit_2_1 : parse_nested_parens_entail_wit_2_1.
Axiom proof_of_parse_nested_parens_entail_wit_2_2 : parse_nested_parens_entail_wit_2_2.
Axiom proof_of_parse_nested_parens_entail_wit_2_3 : parse_nested_parens_entail_wit_2_3.
Axiom proof_of_parse_nested_parens_entail_wit_2_4 : parse_nested_parens_entail_wit_2_4.
Axiom proof_of_parse_nested_parens_entail_wit_2_5 : parse_nested_parens_entail_wit_2_5.
Axiom proof_of_parse_nested_parens_entail_wit_2_6 : parse_nested_parens_entail_wit_2_6.
Axiom proof_of_parse_nested_parens_entail_wit_3 : parse_nested_parens_entail_wit_3.
Axiom proof_of_parse_nested_parens_entail_wit_4_1 : parse_nested_parens_entail_wit_4_1.
Axiom proof_of_parse_nested_parens_entail_wit_4_2 : parse_nested_parens_entail_wit_4_2.
Axiom proof_of_parse_nested_parens_return_wit_1 : parse_nested_parens_return_wit_1.
Axiom proof_of_parse_nested_parens_partial_solve_wit_1 : parse_nested_parens_partial_solve_wit_1.
Axiom proof_of_parse_nested_parens_partial_solve_wit_2 : parse_nested_parens_partial_solve_wit_2.
Axiom proof_of_parse_nested_parens_partial_solve_wit_3_pure : parse_nested_parens_partial_solve_wit_3_pure.
Axiom proof_of_parse_nested_parens_partial_solve_wit_3 : parse_nested_parens_partial_solve_wit_3.
Axiom proof_of_parse_nested_parens_partial_solve_wit_4 : parse_nested_parens_partial_solve_wit_4.
Axiom proof_of_parse_nested_parens_partial_solve_wit_5 : parse_nested_parens_partial_solve_wit_5.
Axiom proof_of_parse_nested_parens_partial_solve_wit_6 : parse_nested_parens_partial_solve_wit_6.
Axiom proof_of_parse_nested_parens_partial_solve_wit_7 : parse_nested_parens_partial_solve_wit_7.

End VC_Correct.
