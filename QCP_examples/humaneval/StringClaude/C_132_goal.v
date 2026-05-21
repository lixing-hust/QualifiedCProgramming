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
Require Import coins_132.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function is_nested -----*)

Definition is_nested_safety_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  ((( &( "state" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_nested_safety_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "state" ) )) # Int  |-> 0)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_nested_safety_wit_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_nested_safety_wit_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (state = 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| (91 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 91) |]
.

Definition is_nested_safety_wit_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 91) |] 
  &&  [| (state = 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_nested_safety_wit_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_nested_safety_wit_7 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (state = 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| (91 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 91) |]
.

Definition is_nested_safety_wit_8 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 91) |] 
  &&  [| (state = 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_nested_safety_wit_9 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_nested_safety_wit_10 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| (93 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 93) |]
.

Definition is_nested_safety_wit_11 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 93) |] 
  &&  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition is_nested_safety_wit_12 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition is_nested_safety_wit_13 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (state = 3) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| (93 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 93) |]
.

Definition is_nested_safety_wit_14 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 93) |] 
  &&  [| (state = 3) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition is_nested_safety_wit_15 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (state <> 3) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_nested_safety_wit_16 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 93) |] 
  &&  [| (state = 3) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_nested_safety_wit_17 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 93) |] 
  &&  [| (state = 3) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> 4)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_nested_safety_wit_18 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 93) |] 
  &&  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_nested_safety_wit_19 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 93) |] 
  &&  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> 3)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_nested_safety_wit_20 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 91) |] 
  &&  [| (state = 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_nested_safety_wit_21 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 91) |] 
  &&  [| (state = 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> 2)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_nested_safety_wit_22 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 91) |] 
  &&  [| (state = 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_nested_safety_wit_23 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 91) |] 
  &&  [| (state = 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> 1)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_nested_safety_wit_24 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition is_nested_safety_wit_25 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (state = 4) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_nested_safety_wit_26 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (state <> 4) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "state" ) )) # Int  |-> state)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_nested_entail_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= len) |] 
  &&  [| (0 = (subseq_state_prefix_z (0) (l))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 4) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_nested_entail_wit_2_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 91) |] 
  &&  [| (state = 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (1 = (subseq_state_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_nested_entail_wit_2_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 91) |] 
  &&  [| (state = 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (state = (subseq_state_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_nested_entail_wit_2_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 91) |] 
  &&  [| (state = 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (2 = (subseq_state_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= 2) |] 
  &&  [| (2 <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_nested_entail_wit_2_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 91) |] 
  &&  [| (state = 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (state = (subseq_state_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_nested_entail_wit_2_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 93) |] 
  &&  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (3 = (subseq_state_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= 3) |] 
  &&  [| (3 <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_nested_entail_wit_2_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 93) |] 
  &&  [| (state = 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (state = (subseq_state_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_nested_entail_wit_2_7 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) = 93) |] 
  &&  [| (state = 3) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (4 = (subseq_state_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= 4) |] 
  &&  [| (4 <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_nested_entail_wit_2_8 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 93) |] 
  &&  [| (state = 3) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (state = (subseq_state_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_nested_entail_wit_2_9 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (state <> 3) |] 
  &&  [| (state <> 2) |] 
  &&  [| (state <> 1) |] 
  &&  [| (state <> 0) |] 
  &&  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= len) |] 
  &&  [| (state = (subseq_state_prefix_z ((i + 1 )) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_nested_return_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (state <> 4) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_132_spec_z l 0 ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_nested_return_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (state = 4) |] 
  &&  [| (i >= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_132_spec_z l 1 ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_nested_partial_solve_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_nested_partial_solve_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (state: Z) (i: Z) ,
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (i < len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_132_pre_z l ) |] 
  &&  [| (ascii_range_z l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= len) |] 
  &&  [| (state = (subseq_state_prefix_z (i) (l))) |] 
  &&  [| (0 <= state) |] 
  &&  [| (state <= 4) |]
  &&  (((str_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i str_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_is_nested_safety_wit_1 : is_nested_safety_wit_1.
Axiom proof_of_is_nested_safety_wit_2 : is_nested_safety_wit_2.
Axiom proof_of_is_nested_safety_wit_3 : is_nested_safety_wit_3.
Axiom proof_of_is_nested_safety_wit_4 : is_nested_safety_wit_4.
Axiom proof_of_is_nested_safety_wit_5 : is_nested_safety_wit_5.
Axiom proof_of_is_nested_safety_wit_6 : is_nested_safety_wit_6.
Axiom proof_of_is_nested_safety_wit_7 : is_nested_safety_wit_7.
Axiom proof_of_is_nested_safety_wit_8 : is_nested_safety_wit_8.
Axiom proof_of_is_nested_safety_wit_9 : is_nested_safety_wit_9.
Axiom proof_of_is_nested_safety_wit_10 : is_nested_safety_wit_10.
Axiom proof_of_is_nested_safety_wit_11 : is_nested_safety_wit_11.
Axiom proof_of_is_nested_safety_wit_12 : is_nested_safety_wit_12.
Axiom proof_of_is_nested_safety_wit_13 : is_nested_safety_wit_13.
Axiom proof_of_is_nested_safety_wit_14 : is_nested_safety_wit_14.
Axiom proof_of_is_nested_safety_wit_15 : is_nested_safety_wit_15.
Axiom proof_of_is_nested_safety_wit_16 : is_nested_safety_wit_16.
Axiom proof_of_is_nested_safety_wit_17 : is_nested_safety_wit_17.
Axiom proof_of_is_nested_safety_wit_18 : is_nested_safety_wit_18.
Axiom proof_of_is_nested_safety_wit_19 : is_nested_safety_wit_19.
Axiom proof_of_is_nested_safety_wit_20 : is_nested_safety_wit_20.
Axiom proof_of_is_nested_safety_wit_21 : is_nested_safety_wit_21.
Axiom proof_of_is_nested_safety_wit_22 : is_nested_safety_wit_22.
Axiom proof_of_is_nested_safety_wit_23 : is_nested_safety_wit_23.
Axiom proof_of_is_nested_safety_wit_24 : is_nested_safety_wit_24.
Axiom proof_of_is_nested_safety_wit_25 : is_nested_safety_wit_25.
Axiom proof_of_is_nested_safety_wit_26 : is_nested_safety_wit_26.
Axiom proof_of_is_nested_entail_wit_1 : is_nested_entail_wit_1.
Axiom proof_of_is_nested_entail_wit_2_1 : is_nested_entail_wit_2_1.
Axiom proof_of_is_nested_entail_wit_2_2 : is_nested_entail_wit_2_2.
Axiom proof_of_is_nested_entail_wit_2_3 : is_nested_entail_wit_2_3.
Axiom proof_of_is_nested_entail_wit_2_4 : is_nested_entail_wit_2_4.
Axiom proof_of_is_nested_entail_wit_2_5 : is_nested_entail_wit_2_5.
Axiom proof_of_is_nested_entail_wit_2_6 : is_nested_entail_wit_2_6.
Axiom proof_of_is_nested_entail_wit_2_7 : is_nested_entail_wit_2_7.
Axiom proof_of_is_nested_entail_wit_2_8 : is_nested_entail_wit_2_8.
Axiom proof_of_is_nested_entail_wit_2_9 : is_nested_entail_wit_2_9.
Axiom proof_of_is_nested_return_wit_1 : is_nested_return_wit_1.
Axiom proof_of_is_nested_return_wit_2 : is_nested_return_wit_2.
Axiom proof_of_is_nested_partial_solve_wit_1 : is_nested_partial_solve_wit_1.
Axiom proof_of_is_nested_partial_solve_wit_2 : is_nested_partial_solve_wit_2.

End VC_Correct.
