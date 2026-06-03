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
Require Import coins_44.
Require Import coins_15.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function string_sequence -----*)

Definition string_sequence_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "cap" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (((12 * (n_pre + 1 ) ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((12 * (n_pre + 1 ) ) + 1 )) |]
.

Definition string_sequence_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "cap" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((12 * (n_pre + 1 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (12 * (n_pre + 1 ) )) |]
.

Definition string_sequence_safety_wit_3 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "cap" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre + 1 )) |]
.

Definition string_sequence_safety_wit_4 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "cap" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (12 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 12) |]
.

Definition string_sequence_safety_wit_5 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "cap" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_sequence_safety_wit_6 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "cap" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_sequence_safety_wit_7 := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  (CharArray.undef_full retval ((12 * (n_pre + 1 ) ) + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_sequence_safety_wit_8 := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval ((12 * (n_pre + 1 ) ) + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_sequence_safety_wit_9 := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval ((12 * (n_pre + 1 ) ) + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_sequence_safety_wit_10 := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval ((12 * (n_pre + 1 ) ) + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition string_sequence_safety_wit_11 := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) ((12 * (n_pre + 1 ) ) + 1 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_sequence_safety_wit_12 := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "t" ) )) # Int  |->_)
  **  (CharArray.undef_seg retval (0 + 1 ) ((12 * (n_pre + 1 ) ) + 1 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 1)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_sequence_safety_wit_13 := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "digits" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  (CharArray.undef_seg retval (0 + 1 ) ((12 * (n_pre + 1 ) ) + 1 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 1)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_sequence_safety_wit_14 := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "digits" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  (CharArray.undef_seg retval (0 + 1 ) ((12 * (n_pre + 1 ) ) + 1 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 1)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_sequence_safety_wit_15 := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "fill" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "digits" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  (CharArray.undef_seg retval (0 + 1 ) ((12 * (n_pre + 1 ) ) + 1 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 1)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_sequence_safety_wit_16 := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "fill" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "digits" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  (CharArray.undef_seg retval (0 + 1 ) ((12 * (n_pre + 1 ) ) + 1 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 1)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_sequence_safety_wit_17 := 
forall (n_pre: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (out_l: (@list Z)) (k: Z) (i: Z) (out: Z) (cap: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) <= cap) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> i)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k cap )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_sequence_safety_wit_18 := 
forall (n_pre: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (out_l: (@list Z)) (k: Z) (i: Z) (out: Z) (cap: Z) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) <= cap) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |] 
  &&  [| (base_count_state_z i 10 t digits ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k cap )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_sequence_safety_wit_19 := 
forall (n_pre: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (out_l: (@list Z)) (k: Z) (i: Z) (out: Z) (cap: Z) ,
  [| (t > 0) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) <= cap) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |] 
  &&  [| (base_count_state_z i 10 t digits ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k cap )
|--
  [| ((digits + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (digits + 1 )) |]
.

Definition string_sequence_safety_wit_20 := 
forall (n_pre: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (out_l: (@list Z)) (k: Z) (i: Z) (out: Z) (cap: Z) ,
  [| (t > 0) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) <= cap) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |] 
  &&  [| (base_count_state_z i 10 t digits ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k cap )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_sequence_safety_wit_21 := 
forall (n_pre: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (out_l: (@list Z)) (k: Z) (i: Z) (out: Z) (cap: Z) ,
  [| (t > 0) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) <= cap) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |] 
  &&  [| (base_count_state_z i 10 t digits ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> (digits + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k cap )
|--
  [| ((t <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition string_sequence_safety_wit_22 := 
forall (n_pre: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (out_l: (@list Z)) (k: Z) (i: Z) (out: Z) (cap: Z) ,
  [| (t > 0) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) <= cap) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |] 
  &&  [| (base_count_state_z i 10 t digits ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> (digits + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k cap )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition string_sequence_safety_wit_23 := 
forall (n_pre: Z) (out_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (t: Z) (j: Z) (fill: Z) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (((k + 1 ) + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k cap )
|--
  [| (32 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 32) |]
.

Definition string_sequence_safety_wit_24 := 
forall (n_pre: Z) (out_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (t: Z) (j: Z) (fill: Z) ,
  [| (0 <= k) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (((k + 1 ) + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition string_sequence_safety_wit_25 := 
forall (n_pre: Z) (out_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (t: Z) (j: Z) (fill: Z) ,
  [| (0 <= k) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (((k + 1 ) + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_sequence_safety_wit_26 := 
forall (n_pre: Z) (out_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (t: Z) (j: Z) (fill: Z) ,
  [| (0 <= k) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (((k + 1 ) + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_sequence_safety_wit_27 := 
forall (n_pre: Z) (fill: Z) (j: Z) (t: Z) (digits: Z) (k: Z) (prefix_l: (@list Z)) (i: Z) (out: Z) (cap: Z) ,
  [| (j < digits) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= digits) |] 
  &&  [| (fill = 0) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out (k + j ) (app ((app (prefix_l) ((cons (32) (nil))))) ((repeat_Z (0) (j)))) )
  **  (CharArray.undef_seg out (k + j ) cap )
|--
  [| ((k + j ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + j )) |]
.

Definition string_sequence_safety_wit_28 := 
forall (n_pre: Z) (fill: Z) (j: Z) (t: Z) (digits: Z) (k: Z) (prefix_l: (@list Z)) (i: Z) (out: Z) (cap: Z) ,
  [| (j < digits) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= digits) |] 
  &&  [| (fill = 0) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out (k + j ) (app ((app (prefix_l) ((cons (32) (nil))))) ((repeat_Z (0) (j)))) )
  **  (CharArray.undef_seg out (k + j ) cap )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_sequence_safety_wit_29 := 
forall (n_pre: Z) (fill: Z) (j: Z) (t: Z) (digits: Z) (k: Z) (prefix_l: (@list Z)) (i: Z) (out: Z) (cap: Z) ,
  [| (0 <= (k + j )) |] 
  &&  [| (j < digits) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= digits) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out ((k + j ) + 1 ) (app ((app ((app (prefix_l) ((cons (32) (nil))))) ((repeat_Z (0) (j))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out ((k + j ) + 1 ) cap )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition string_sequence_safety_wit_30 := 
forall (n_pre: Z) (digit_l: (@list Z)) (fill: Z) (t: Z) (j: Z) (digits: Z) (k: Z) (prefix_l: (@list Z)) (i: Z) (out: Z) (cap: Z) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill <= digits) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t fill digit_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out (k + digits ) (app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_sequence_safety_wit_31 := 
forall (n_pre: Z) (digit_l: (@list Z)) (fill: Z) (t: Z) (j: Z) (digits: Z) (k: Z) (prefix_l: (@list Z)) (i: Z) (out: Z) (cap: Z) ,
  [| (t > 0) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill <= digits) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t fill digit_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out (k + digits ) (app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  [| ((fill - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (fill - 1 )) |]
.

Definition string_sequence_safety_wit_32 := 
forall (n_pre: Z) (digit_l: (@list Z)) (fill: Z) (t: Z) (j: Z) (digits: Z) (k: Z) (prefix_l: (@list Z)) (i: Z) (out: Z) (cap: Z) ,
  [| (t > 0) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill <= digits) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t fill digit_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out (k + digits ) (app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition string_sequence_safety_wit_33 := 
forall (n_pre: Z) (prefix_l: (@list Z)) (digit_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (j: Z) (t: Z) (fill: Z) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 < t) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill < digits) |] 
  &&  [| (0 <= (k + fill )) |] 
  &&  [| ((k + fill ) < (k + digits )) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (0 <= (48 + (t % ( 10 ) ) )) |] 
  &&  [| ((48 + (t % ( 10 ) ) ) <= 127) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t (fill + 1 ) digit_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out (k + digits ) (app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  [| ((k + fill ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + fill )) |]
.

Definition string_sequence_safety_wit_34 := 
forall (n_pre: Z) (prefix_l: (@list Z)) (digit_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (j: Z) (t: Z) (fill: Z) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 < t) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill < digits) |] 
  &&  [| (0 <= (k + fill )) |] 
  &&  [| ((k + fill ) < (k + digits )) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (0 <= (48 + (t % ( 10 ) ) )) |] 
  &&  [| ((48 + (t % ( 10 ) ) ) <= 127) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t (fill + 1 ) digit_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out (k + digits ) (app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  [| ((48 + (t % ( 10 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (48 + (t % ( 10 ) ) )) |]
.

Definition string_sequence_safety_wit_35 := 
forall (n_pre: Z) (prefix_l: (@list Z)) (digit_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (j: Z) (t: Z) (fill: Z) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 < t) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill < digits) |] 
  &&  [| (0 <= (k + fill )) |] 
  &&  [| ((k + fill ) < (k + digits )) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (0 <= (48 + (t % ( 10 ) ) )) |] 
  &&  [| ((48 + (t % ( 10 ) ) ) <= 127) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t (fill + 1 ) digit_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out (k + digits ) (app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  [| ((t <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition string_sequence_safety_wit_36 := 
forall (n_pre: Z) (prefix_l: (@list Z)) (digit_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (j: Z) (t: Z) (fill: Z) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 < t) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill < digits) |] 
  &&  [| (0 <= (k + fill )) |] 
  &&  [| ((k + fill ) < (k + digits )) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (0 <= (48 + (t % ( 10 ) ) )) |] 
  &&  [| ((48 + (t % ( 10 ) ) ) <= 127) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t (fill + 1 ) digit_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out (k + digits ) (app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition string_sequence_safety_wit_37 := 
forall (n_pre: Z) (prefix_l: (@list Z)) (digit_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (j: Z) (t: Z) (fill: Z) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 < t) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill < digits) |] 
  &&  [| (0 <= (k + fill )) |] 
  &&  [| ((k + fill ) < (k + digits )) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (0 <= (48 + (t % ( 10 ) ) )) |] 
  &&  [| ((48 + (t % ( 10 ) ) ) <= 127) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t (fill + 1 ) digit_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full out (k + digits ) (app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition string_sequence_safety_wit_38 := 
forall (n_pre: Z) (prefix_l: (@list Z)) (digit_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (j: Z) (t: Z) (fill: Z) ,
  [| (0 <= (k + digits )) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 < t) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill < digits) |] 
  &&  [| (0 <= (k + fill )) |] 
  &&  [| ((k + fill ) < (k + digits )) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (0 <= (48 + (t % ( 10 ) ) )) |] 
  &&  [| ((48 + (t % ( 10 ) ) ) <= 127) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t (fill + 1 ) digit_l ) |]
  &&  (CharArray.full out (k + digits ) (replace_Znth ((k + fill )) ((48 + (t % ( 10 ) ) )) ((app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  [| ((t <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition string_sequence_safety_wit_39 := 
forall (n_pre: Z) (prefix_l: (@list Z)) (digit_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (j: Z) (t: Z) (fill: Z) ,
  [| (0 <= (k + digits )) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 < t) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill < digits) |] 
  &&  [| (0 <= (k + fill )) |] 
  &&  [| ((k + fill ) < (k + digits )) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (0 <= (48 + (t % ( 10 ) ) )) |] 
  &&  [| ((48 + (t % ( 10 ) ) ) <= 127) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t (fill + 1 ) digit_l ) |]
  &&  (CharArray.full out (k + digits ) (replace_Znth ((k + fill )) ((48 + (t % ( 10 ) ) )) ((app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition string_sequence_safety_wit_40 := 
forall (n_pre: Z) (out_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (t: Z) (fill: Z) (j: Z) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (out_l = (sequence_prefix_z ((i + 1 )))) |] 
  &&  [| ((k + digits ) = (Zlength (out_l))) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (fill = 0) |] 
  &&  [| (j = digits) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full out (k + digits ) out_l )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  [| ((k + digits ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + digits )) |]
.

Definition string_sequence_safety_wit_41 := 
forall (n_pre: Z) (out_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (t: Z) (fill: Z) (j: Z) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (out_l = (sequence_prefix_z ((i + 1 )))) |] 
  &&  [| ((k + digits ) = (Zlength (out_l))) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (fill = 0) |] 
  &&  [| (j = digits) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + digits ))
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full out (k + digits ) out_l )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition string_sequence_safety_wit_42 := 
forall (n_pre: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (out_l: (@list Z)) (k: Z) (i: Z) (out: Z) (cap: Z) ,
  [| (i > n_pre) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) <= cap) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k cap )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition string_sequence_entail_wit_1 := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) ((12 * (n_pre + 1 ) ) + 1 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  EX (out_l: (@list Z)) ,
  [| (((12 * (n_pre + 1 ) ) + 1 ) = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= (n_pre + 1 )) |] 
  &&  [| (1 = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (1))) |] 
  &&  [| ((1 + 1 ) <= ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 = 0) |]
  &&  (CharArray.full retval 1 out_l )
  **  (CharArray.undef_seg retval 1 ((12 * (n_pre + 1 ) ) + 1 ) )
.

Definition string_sequence_entail_wit_2 := 
forall (n_pre: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (out_l_2: (@list Z)) (k: Z) (i: Z) (out: Z) (cap: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (k = (Zlength (out_l_2))) |] 
  &&  [| (out_l_2 = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) <= cap) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out k out_l_2 )
  **  (CharArray.undef_seg out k cap )
|--
  EX (out_l: (@list Z)) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) <= cap) |] 
  &&  [| (0 <= i) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |] 
  &&  [| (base_count_state_z i 10 i 0 ) |]
  &&  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k cap )
.

Definition string_sequence_entail_wit_3 := 
forall (n_pre: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (out_l_2: (@list Z)) (k: Z) (i: Z) (out: Z) (cap: Z) ,
  [| (t > 0) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l_2))) |] 
  &&  [| (out_l_2 = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) <= cap) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |] 
  &&  [| (base_count_state_z i 10 t digits ) |]
  &&  (CharArray.full out k out_l_2 )
  **  (CharArray.undef_seg out k cap )
|--
  EX (out_l: (@list Z)) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) <= cap) |] 
  &&  [| (0 <= (t ÷ 10 )) |] 
  &&  [| (0 <= (digits + 1 )) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |] 
  &&  [| (base_count_state_z i 10 (t ÷ 10 ) (digits + 1 ) ) |]
  &&  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k cap )
.

Definition string_sequence_entail_wit_4 := 
forall (n_pre: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (out_l_2: (@list Z)) (k: Z) (i: Z) (out: Z) (cap: Z) ,
  [| (t <= 0) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l_2))) |] 
  &&  [| (out_l_2 = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) <= cap) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |] 
  &&  [| (base_count_state_z i 10 t digits ) |]
  &&  (CharArray.full out k out_l_2 )
  **  (CharArray.undef_seg out k cap )
|--
  EX (out_l: (@list Z)) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (((k + 1 ) + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k cap )
.

Definition string_sequence_entail_wit_5 := 
forall (n_pre: Z) (out_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (t: Z) (j: Z) (fill: Z) ,
  [| (0 <= k) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (((k + 1 ) + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) cap )
|--
  EX (prefix_l: (@list Z)) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (((k + 1 ) + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out ((k + 1 ) + 0 ) (app ((app (prefix_l) ((cons (32) (nil))))) ((repeat_Z (0) (0)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 0 ) cap )
.

Definition string_sequence_entail_wit_6 := 
forall (n_pre: Z) (fill: Z) (j: Z) (t: Z) (digits: Z) (k: Z) (prefix_l_2: (@list Z)) (i: Z) (out: Z) (cap: Z) ,
  [| (0 <= (k + j )) |] 
  &&  [| (j < digits) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l_2 = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l_2)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= digits) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out ((k + j ) + 1 ) (app ((app ((app (prefix_l_2) ((cons (32) (nil))))) ((repeat_Z (0) (j))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out ((k + j ) + 1 ) cap )
|--
  EX (prefix_l: (@list Z)) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= digits) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out (k + (j + 1 ) ) (app ((app (prefix_l) ((cons (32) (nil))))) ((repeat_Z (0) ((j + 1 ))))) )
  **  (CharArray.undef_seg out (k + (j + 1 ) ) cap )
.

Definition string_sequence_entail_wit_7 := 
forall (n_pre: Z) (fill: Z) (j: Z) (t: Z) (digits: Z) (k: Z) (prefix_l_2: (@list Z)) (i: Z) (out: Z) (cap: Z) ,
  [| (j >= digits) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l_2 = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l_2)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= digits) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out (k + j ) (app ((app (prefix_l_2) ((cons (32) (nil))))) ((repeat_Z (0) (j)))) )
  **  (CharArray.undef_seg out (k + j ) cap )
|--
  EX (digit_l: (@list Z))  (prefix_l: (@list Z)) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (j = digits) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (fill = 0) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 i digits digit_l ) |]
  &&  (CharArray.full out (k + digits ) (app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
.

Definition string_sequence_entail_wit_8 := 
forall (n_pre: Z) (prefix_l_2: (@list Z)) (digit_l_2: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (j: Z) (t: Z) (fill: Z) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l_2 = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l_2)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (j = digits) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (fill = 0) |] 
  &&  [| ((Zlength (digit_l_2)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 i digits digit_l_2 ) |]
  &&  (CharArray.full out (k + digits ) (app ((app (prefix_l_2) ((cons (32) (nil))))) (digit_l_2)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  EX (digit_l: (@list Z))  (prefix_l: (@list Z)) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 <= i) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits <= digits) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 i digits digit_l ) |]
  &&  (CharArray.full out (k + digits ) (app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
.

Definition string_sequence_entail_wit_9 := 
forall (n_pre: Z) (digit_l_2: (@list Z)) (fill: Z) (t: Z) (j: Z) (digits: Z) (k: Z) (prefix_l_2: (@list Z)) (i: Z) (out: Z) (cap: Z) ,
  [| (t > 0) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l_2 = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l_2)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill <= digits) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| ((Zlength (digit_l_2)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t fill digit_l_2 ) |]
  &&  (CharArray.full out (k + digits ) (app ((app (prefix_l_2) ((cons (32) (nil))))) (digit_l_2)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  EX (digit_l: (@list Z))  (prefix_l: (@list Z)) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 < t) |] 
  &&  [| (0 <= (fill - 1 )) |] 
  &&  [| ((fill - 1 ) < digits) |] 
  &&  [| (0 <= (k + (fill - 1 ) )) |] 
  &&  [| ((k + (fill - 1 ) ) < (k + digits )) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (0 <= (48 + (t % ( 10 ) ) )) |] 
  &&  [| ((48 + (t % ( 10 ) ) ) <= 127) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t ((fill - 1 ) + 1 ) digit_l ) |]
  &&  (CharArray.full out (k + digits ) (app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
.

Definition string_sequence_entail_wit_10 := 
forall (n_pre: Z) (prefix_l_2: (@list Z)) (digit_l_2: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (j: Z) (t: Z) (fill: Z) ,
  [| (0 <= (k + digits )) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l_2 = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l_2)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 < t) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill < digits) |] 
  &&  [| (0 <= (k + fill )) |] 
  &&  [| ((k + fill ) < (k + digits )) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (0 <= (48 + (t % ( 10 ) ) )) |] 
  &&  [| ((48 + (t % ( 10 ) ) ) <= 127) |] 
  &&  [| ((Zlength (digit_l_2)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t (fill + 1 ) digit_l_2 ) |]
  &&  (CharArray.full out (k + digits ) (replace_Znth ((k + fill )) ((48 + (t % ( 10 ) ) )) ((app ((app (prefix_l_2) ((cons (32) (nil))))) (digit_l_2)))) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  EX (digit_l: (@list Z))  (prefix_l: (@list Z)) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 <= (t ÷ 10 )) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill <= digits) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 (t ÷ 10 ) fill digit_l ) |]
  &&  (CharArray.full out (k + digits ) (app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
.

Definition string_sequence_entail_wit_11 := 
forall (n_pre: Z) (digit_l: (@list Z)) (fill: Z) (t: Z) (j: Z) (digits: Z) (k: Z) (prefix_l: (@list Z)) (i: Z) (out: Z) (cap: Z) ,
  [| (t <= 0) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill <= digits) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t fill digit_l ) |]
  &&  (CharArray.full out (k + digits ) (app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  EX (out_l: (@list Z)) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (out_l = (sequence_prefix_z ((i + 1 )))) |] 
  &&  [| ((k + digits ) = (Zlength (out_l))) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (fill = 0) |] 
  &&  [| (j = digits) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |]
  &&  (CharArray.full out (k + digits ) out_l )
  **  (CharArray.undef_seg out (k + digits ) cap )
.

Definition string_sequence_entail_wit_12 := 
forall (n_pre: Z) (out_l_2: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (t: Z) (fill: Z) (j: Z) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (out_l_2 = (sequence_prefix_z ((i + 1 )))) |] 
  &&  [| ((k + digits ) = (Zlength (out_l_2))) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (fill = 0) |] 
  &&  [| (j = digits) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |]
  &&  (CharArray.full out (k + digits ) out_l_2 )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  EX (out_l: (@list Z)) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (n_pre + 1 )) |] 
  &&  [| ((k + digits ) = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z ((i + 1 )))) |] 
  &&  [| (((k + digits ) + 1 ) <= cap) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out (k + digits ) out_l )
  **  (CharArray.undef_seg out (k + digits ) cap )
.

Definition string_sequence_entail_wit_13 := 
forall (n_pre: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (out_l_2: (@list Z)) (k: Z) (i: Z) (out: Z) (cap: Z) ,
  [| (0 <= k) |] 
  &&  [| (i > n_pre) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (k = (Zlength (out_l_2))) |] 
  &&  [| (out_l_2 = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) <= cap) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) cap )
|--
  EX (out_l: (@list Z)) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_output_z (n_pre))) |] 
  &&  [| (i = (n_pre + 1 )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (problem_15_spec_z n_pre out_l ) |]
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) cap )
.

Definition string_sequence_return_wit_1 := 
forall (n_pre: Z) (out_l_2: (@list Z)) (len_2: Z) (cap_2: Z) (out: Z) (i: Z) ,
  [| (cap_2 = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (len_2 = (Zlength (out_l_2))) |] 
  &&  [| (out_l_2 = (sequence_output_z (n_pre))) |] 
  &&  [| (i = (n_pre + 1 )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (problem_15_spec_z n_pre out_l_2 ) |]
  &&  (CharArray.full out (len_2 + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (len_2 + 1 ) cap_2 )
|--
  EX (out_l: (@list Z))  (len: Z)  (cap: Z) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (len = (Zlength (out_l))) |] 
  &&  [| (problem_15_spec_z n_pre out_l ) |]
  &&  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (len + 1 ) cap )
.

Definition string_sequence_partial_solve_wit_1_pure := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (((12 * (n_pre + 1 ) ) + 1 ) > 0) |]
.

Definition string_sequence_partial_solve_wit_1_aux := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  emp
|--
  [| (((12 * (n_pre + 1 ) ) + 1 ) > 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  emp
.

Definition string_sequence_partial_solve_wit_1 := string_sequence_partial_solve_wit_1_pure -> string_sequence_partial_solve_wit_1_aux.

Definition string_sequence_partial_solve_wit_2 := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  (CharArray.undef_full retval ((12 * (n_pre + 1 ) ) + 1 ) )
|--
  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |]
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 ((12 * (n_pre + 1 ) ) + 1 ) )
.

Definition string_sequence_partial_solve_wit_3 := 
forall (n_pre: Z) (out_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (t: Z) (j: Z) (fill: Z) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (((k + 1 ) + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k cap )
|--
  [| (0 <= k) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (((k + 1 ) + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |]
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k cap )
  **  (CharArray.full out k out_l )
.

Definition string_sequence_partial_solve_wit_4 := 
forall (n_pre: Z) (fill: Z) (j: Z) (t: Z) (digits: Z) (k: Z) (prefix_l: (@list Z)) (i: Z) (out: Z) (cap: Z) ,
  [| (j < digits) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= digits) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out (k + j ) (app ((app (prefix_l) ((cons (32) (nil))))) ((repeat_Z (0) (j)))) )
  **  (CharArray.undef_seg out (k + j ) cap )
|--
  [| (0 <= (k + j )) |] 
  &&  [| (j < digits) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (t = 0) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= digits) |] 
  &&  [| (fill = 0) |]
  &&  (((out + ((k + j ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (k + j ) (k + j ) cap )
  **  (CharArray.full out (k + j ) (app ((app (prefix_l) ((cons (32) (nil))))) ((repeat_Z (0) (j)))) )
.

Definition string_sequence_partial_solve_wit_5 := 
forall (n_pre: Z) (prefix_l: (@list Z)) (digit_l: (@list Z)) (cap: Z) (out: Z) (i: Z) (k: Z) (digits: Z) (j: Z) (t: Z) (fill: Z) ,
  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 < t) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill < digits) |] 
  &&  [| (0 <= (k + fill )) |] 
  &&  [| ((k + fill ) < (k + digits )) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (0 <= (48 + (t % ( 10 ) ) )) |] 
  &&  [| ((48 + (t % ( 10 ) ) ) <= 127) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t (fill + 1 ) digit_l ) |]
  &&  (CharArray.full out (k + digits ) (app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  [| (0 <= (k + digits )) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (prefix_l = (sequence_prefix_z (i))) |] 
  &&  [| (k = ((Zlength (prefix_l)) + 1 )) |] 
  &&  [| (digits = (Zlength ((base_digits_z (i) (10))))) |] 
  &&  [| (0 <= k) |] 
  &&  [| (j = digits) |] 
  &&  [| (0 < t) |] 
  &&  [| (0 <= fill) |] 
  &&  [| (fill < digits) |] 
  &&  [| (0 <= (k + fill )) |] 
  &&  [| ((k + fill ) < (k + digits )) |] 
  &&  [| ((k + digits ) < cap) |] 
  &&  [| (0 <= (48 + (t % ( 10 ) ) )) |] 
  &&  [| ((48 + (t % ( 10 ) ) ) <= 127) |] 
  &&  [| ((Zlength (digit_l)) = digits) |] 
  &&  [| (base_fill_full_state_z i 10 t (fill + 1 ) digit_l ) |]
  &&  (((out + ((k + fill ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i out (k + fill ) 0 (k + digits ) (app ((app (prefix_l) ((cons (32) (nil))))) (digit_l)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
.

Definition string_sequence_partial_solve_wit_6 := 
forall (n_pre: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (out_l: (@list Z)) (k: Z) (i: Z) (out: Z) (cap: Z) ,
  [| (i > n_pre) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) <= cap) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |]
  &&  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k cap )
|--
  [| (0 <= k) |] 
  &&  [| (i > n_pre) |] 
  &&  [| (cap = ((12 * (n_pre + 1 ) ) + 1 )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) |] 
  &&  [| (problem_15_pre_z n_pre ) |] 
  &&  [| (sequence_output_bound_z n_pre ) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (k = (Zlength (out_l))) |] 
  &&  [| (out_l = (sequence_prefix_z (i))) |] 
  &&  [| ((k + 1 ) <= cap) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (0 <= j) |] 
  &&  [| (fill = 0) |]
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k cap )
  **  (CharArray.full out k out_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_string_sequence_safety_wit_1 : string_sequence_safety_wit_1.
Axiom proof_of_string_sequence_safety_wit_2 : string_sequence_safety_wit_2.
Axiom proof_of_string_sequence_safety_wit_3 : string_sequence_safety_wit_3.
Axiom proof_of_string_sequence_safety_wit_4 : string_sequence_safety_wit_4.
Axiom proof_of_string_sequence_safety_wit_5 : string_sequence_safety_wit_5.
Axiom proof_of_string_sequence_safety_wit_6 : string_sequence_safety_wit_6.
Axiom proof_of_string_sequence_safety_wit_7 : string_sequence_safety_wit_7.
Axiom proof_of_string_sequence_safety_wit_8 : string_sequence_safety_wit_8.
Axiom proof_of_string_sequence_safety_wit_9 : string_sequence_safety_wit_9.
Axiom proof_of_string_sequence_safety_wit_10 : string_sequence_safety_wit_10.
Axiom proof_of_string_sequence_safety_wit_11 : string_sequence_safety_wit_11.
Axiom proof_of_string_sequence_safety_wit_12 : string_sequence_safety_wit_12.
Axiom proof_of_string_sequence_safety_wit_13 : string_sequence_safety_wit_13.
Axiom proof_of_string_sequence_safety_wit_14 : string_sequence_safety_wit_14.
Axiom proof_of_string_sequence_safety_wit_15 : string_sequence_safety_wit_15.
Axiom proof_of_string_sequence_safety_wit_16 : string_sequence_safety_wit_16.
Axiom proof_of_string_sequence_safety_wit_17 : string_sequence_safety_wit_17.
Axiom proof_of_string_sequence_safety_wit_18 : string_sequence_safety_wit_18.
Axiom proof_of_string_sequence_safety_wit_19 : string_sequence_safety_wit_19.
Axiom proof_of_string_sequence_safety_wit_20 : string_sequence_safety_wit_20.
Axiom proof_of_string_sequence_safety_wit_21 : string_sequence_safety_wit_21.
Axiom proof_of_string_sequence_safety_wit_22 : string_sequence_safety_wit_22.
Axiom proof_of_string_sequence_safety_wit_23 : string_sequence_safety_wit_23.
Axiom proof_of_string_sequence_safety_wit_24 : string_sequence_safety_wit_24.
Axiom proof_of_string_sequence_safety_wit_25 : string_sequence_safety_wit_25.
Axiom proof_of_string_sequence_safety_wit_26 : string_sequence_safety_wit_26.
Axiom proof_of_string_sequence_safety_wit_27 : string_sequence_safety_wit_27.
Axiom proof_of_string_sequence_safety_wit_28 : string_sequence_safety_wit_28.
Axiom proof_of_string_sequence_safety_wit_29 : string_sequence_safety_wit_29.
Axiom proof_of_string_sequence_safety_wit_30 : string_sequence_safety_wit_30.
Axiom proof_of_string_sequence_safety_wit_31 : string_sequence_safety_wit_31.
Axiom proof_of_string_sequence_safety_wit_32 : string_sequence_safety_wit_32.
Axiom proof_of_string_sequence_safety_wit_33 : string_sequence_safety_wit_33.
Axiom proof_of_string_sequence_safety_wit_34 : string_sequence_safety_wit_34.
Axiom proof_of_string_sequence_safety_wit_35 : string_sequence_safety_wit_35.
Axiom proof_of_string_sequence_safety_wit_36 : string_sequence_safety_wit_36.
Axiom proof_of_string_sequence_safety_wit_37 : string_sequence_safety_wit_37.
Axiom proof_of_string_sequence_safety_wit_38 : string_sequence_safety_wit_38.
Axiom proof_of_string_sequence_safety_wit_39 : string_sequence_safety_wit_39.
Axiom proof_of_string_sequence_safety_wit_40 : string_sequence_safety_wit_40.
Axiom proof_of_string_sequence_safety_wit_41 : string_sequence_safety_wit_41.
Axiom proof_of_string_sequence_safety_wit_42 : string_sequence_safety_wit_42.
Axiom proof_of_string_sequence_entail_wit_1 : string_sequence_entail_wit_1.
Axiom proof_of_string_sequence_entail_wit_2 : string_sequence_entail_wit_2.
Axiom proof_of_string_sequence_entail_wit_3 : string_sequence_entail_wit_3.
Axiom proof_of_string_sequence_entail_wit_4 : string_sequence_entail_wit_4.
Axiom proof_of_string_sequence_entail_wit_5 : string_sequence_entail_wit_5.
Axiom proof_of_string_sequence_entail_wit_6 : string_sequence_entail_wit_6.
Axiom proof_of_string_sequence_entail_wit_7 : string_sequence_entail_wit_7.
Axiom proof_of_string_sequence_entail_wit_8 : string_sequence_entail_wit_8.
Axiom proof_of_string_sequence_entail_wit_9 : string_sequence_entail_wit_9.
Axiom proof_of_string_sequence_entail_wit_10 : string_sequence_entail_wit_10.
Axiom proof_of_string_sequence_entail_wit_11 : string_sequence_entail_wit_11.
Axiom proof_of_string_sequence_entail_wit_12 : string_sequence_entail_wit_12.
Axiom proof_of_string_sequence_entail_wit_13 : string_sequence_entail_wit_13.
Axiom proof_of_string_sequence_return_wit_1 : string_sequence_return_wit_1.
Axiom proof_of_string_sequence_partial_solve_wit_1_pure : string_sequence_partial_solve_wit_1_pure.
Axiom proof_of_string_sequence_partial_solve_wit_1 : string_sequence_partial_solve_wit_1.
Axiom proof_of_string_sequence_partial_solve_wit_2 : string_sequence_partial_solve_wit_2.
Axiom proof_of_string_sequence_partial_solve_wit_3 : string_sequence_partial_solve_wit_3.
Axiom proof_of_string_sequence_partial_solve_wit_4 : string_sequence_partial_solve_wit_4.
Axiom proof_of_string_sequence_partial_solve_wit_5 : string_sequence_partial_solve_wit_5.
Axiom proof_of_string_sequence_partial_solve_wit_6 : string_sequence_partial_solve_wit_6.

End VC_Correct.
