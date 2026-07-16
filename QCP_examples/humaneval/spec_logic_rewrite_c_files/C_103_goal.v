Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
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
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_103.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function to_binary_string -----*)

Definition to_binary_string_safety_wit_1 := 
forall (num_pre: Z) (PreH1 : (0 <= num_pre)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (binary_safe_103 num_pre )) ,
  ((( &( "bits" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition to_binary_string_safety_wit_2 := 
forall (num_pre: Z) (PreH1 : (0 <= num_pre)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (binary_safe_103 num_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Int  |-> num_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition to_binary_string_safety_wit_3 := 
forall (num_pre: Z) (PreH1 : (0 <= num_pre)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (binary_safe_103 num_pre )) ,
  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> num_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition to_binary_string_safety_wit_4 := 
forall (num_pre: Z) (PreH1 : (num_pre = 0)) (PreH2 : (0 <= num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (binary_safe_103 num_pre )) ,
  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> num_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition to_binary_string_safety_wit_5 := 
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (binary_safe_103 num_pre )) ,
  (CharArray.undef_full retval 2 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> num_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition to_binary_string_safety_wit_6 := 
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (binary_safe_103 num_pre )) ,
  (CharArray.undef_full retval 2 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> num_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition to_binary_string_safety_wit_7 := 
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (binary_safe_103 num_pre )) ,
  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> num_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition to_binary_string_safety_wit_8 := 
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (binary_safe_103 num_pre )) ,
  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> num_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition to_binary_string_safety_wit_9 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (0 <= x)) (PreH4 : (0 <= bits)) (PreH5 : (out = 0)) (PreH6 : (binary_safe_103 num_pre )) (PreH7 : (binary_count_state_z_103 num_pre x bits )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition to_binary_string_safety_wit_10 := 
(
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_count_state_z_103 num_pre x bits )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((bits + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bits + 1 )) ”
) \/
(
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_count_state_z_103 num_pre x bits )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((bits + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bits + 1 )) ”
).

Definition to_binary_string_safety_wit_10_split_goal_1 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_count_state_z_103 num_pre x bits )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((bits + 1 ) <= INT_MAX) ”
.

Definition to_binary_string_safety_wit_10_split_goal_2 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_count_state_z_103 num_pre x bits )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((INT_MIN) <= (bits + 1 )) ”
.

Definition to_binary_string_safety_wit_11 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_count_state_z_103 num_pre x bits )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition to_binary_string_safety_wit_12 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_count_state_z_103 num_pre x bits )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> (bits + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((x <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition to_binary_string_safety_wit_13 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_count_state_z_103 num_pre x bits )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> (bits + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition to_binary_string_safety_wit_14 := 
(
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_103 (num_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((bits + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bits + 1 )) ”
) \/
(
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_103 (num_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((bits + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bits + 1 )) ”
).

Definition to_binary_string_safety_wit_14_split_goal_1 := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_103 (num_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((bits + 1 ) <= INT_MAX) ”
.

Definition to_binary_string_safety_wit_14_split_goal_2 := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_103 (num_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((INT_MIN) <= (bits + 1 )) ”
.

Definition to_binary_string_safety_wit_15 := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_103 (num_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition to_binary_string_safety_wit_16 := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_103 (num_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (binary_safe_103 num_pre )) ,
  (CharArray.undef_full retval (bits + 1 ) )
  **  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition to_binary_string_safety_wit_17 := 
forall (num_pre: Z) (suffix: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (0 <= num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 <= bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition to_binary_string_safety_wit_18 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix )
|--
  “ ((bits - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bits - 1 )) ”
.

Definition to_binary_string_safety_wit_19 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition to_binary_string_safety_wit_20 := 
(
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix )
|--
  “ ((48 + (num % ( 2 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (48 + (num % ( 2 ) ) )) ”
) \/
(
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix )
|--
  “ ((48 + (num % ( 2 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (48 + (num % ( 2 ) ) )) ”
).

Definition to_binary_string_safety_wit_20_split_goal_1 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix )
|--
  “ ((48 + (num % ( 2 ) ) ) <= INT_MAX) ”
.

Definition to_binary_string_safety_wit_20_split_goal_2 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix )
|--
  “ ((INT_MIN) <= (48 + (num % ( 2 ) ) )) ”
.

Definition to_binary_string_safety_wit_21 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix )
|--
  “ ((num <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition to_binary_string_safety_wit_22 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition to_binary_string_safety_wit_23 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition to_binary_string_safety_wit_24 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix)))) = (((binary_length_z_103 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_103 (num_pre)) + 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )
|--
  “ ((bits - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bits - 1 )) ”
.

Definition to_binary_string_safety_wit_25 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix)))) = (((binary_length_z_103 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_103 (num_pre)) + 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition to_binary_string_safety_wit_26 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix)))) = (((binary_length_z_103 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> (bits - 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_103 (num_pre)) + 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )
|--
  “ ((num <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition to_binary_string_safety_wit_27 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix)))) = (((binary_length_z_103 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> (bits - 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_103 (num_pre)) + 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition to_binary_string_entail_wit_1 := 
(
forall (num_pre: Z) (PreH1 : (num_pre <> 0)) (PreH2 : (0 <= num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (binary_safe_103 num_pre )) ,
  TT && emp 
|--
  “ (0 < num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (0 <= num_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (binary_safe_103 num_pre ) ” 
  &&  “ (binary_count_state_z_103 num_pre num_pre 0 ) ”
  &&  emp
) \/
(
forall (num_pre: Z) (PreH1 : (num_pre <> 0)) (PreH2 : (0 <= num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (binary_safe_103 num_pre )) ,
  TT && emp 
|--
  “ (binary_count_state_z_103 num_pre num_pre 0 ) ”
  &&  emp
).

Definition to_binary_string_entail_wit_1_split_goal_1 := 
forall (num_pre: Z) (PreH1 : (num_pre <> 0)) (PreH2 : (0 <= num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (binary_safe_103 num_pre )) ,
  TT && emp 
|--
  “ (binary_count_state_z_103 num_pre num_pre 0 ) ”
.

Definition to_binary_string_entail_wit_2 := 
(
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_count_state_z_103 num_pre x bits )) ,
  TT && emp 
|--
  “ (0 < num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (0 <= (x ÷ 2 )) ” 
  &&  “ (0 <= (bits + 1 )) ” 
  &&  “ (out = 0) ” 
  &&  “ (binary_safe_103 num_pre ) ” 
  &&  “ (binary_count_state_z_103 num_pre (x ÷ 2 ) (bits + 1 ) ) ”
  &&  emp
) \/
(
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_count_state_z_103 num_pre x bits )) ,
  TT && emp 
|--
  “ (binary_count_state_z_103 num_pre (x ÷ 2 ) (bits + 1 ) ) ” 
  &&  “ (0 <= (x ÷ 2 )) ”
  &&  emp
).

Definition to_binary_string_entail_wit_2_split_goal_1 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_count_state_z_103 num_pre x bits )) ,
  TT && emp 
|--
  “ (binary_count_state_z_103 num_pre (x ÷ 2 ) (bits + 1 ) ) ”
.

Definition to_binary_string_entail_wit_2_split_goal_2 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_count_state_z_103 num_pre x bits )) ,
  TT && emp 
|--
  “ (0 <= (x ÷ 2 )) ”
.

Definition to_binary_string_entail_wit_3 := 
(
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x <= 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_count_state_z_103 num_pre x bits )) ,
  TT && emp 
|--
  “ (0 < num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_103 (num_pre))) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (out = 0) ” 
  &&  “ (binary_safe_103 num_pre ) ”
  &&  emp
) \/
(
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x <= 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_count_state_z_103 num_pre x bits )) ,
  TT && emp 
|--
  “ (1 <= bits) ” 
  &&  “ (bits = (binary_length_z_103 (num_pre))) ”
  &&  emp
).

Definition to_binary_string_entail_wit_3_split_goal_1 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x <= 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_count_state_z_103 num_pre x bits )) ,
  TT && emp 
|--
  “ (1 <= bits) ”
.

Definition to_binary_string_entail_wit_3_split_goal_2 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x <= 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_count_state_z_103 num_pre x bits )) ,
  TT && emp 
|--
  “ (bits = (binary_length_z_103 (num_pre))) ”
.

Definition to_binary_string_entail_wit_4 := 
(
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_103 (num_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (binary_safe_103 num_pre )) ,
  (((retval + (bits * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_missing_i retval bits 0 (bits + 1 ) )
|--
  “ (0 < num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_103 (num_pre))) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (binary_safe_103 num_pre ) ” 
  &&  “ (binary_backfill_state_z_103 num_pre num_pre bits (cons (0) ((@nil Z))) ) ”
  &&  (CharArray.undef_seg retval 0 bits )
  **  (CharArray.seg retval bits (bits + 1 ) (cons (0) ((@nil Z))) )
) \/
(
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_103 (num_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (binary_safe_103 num_pre )) ,
  (((retval + (bits * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_missing_i retval bits 0 (bits + 1 ) )
|--
  “ (binary_backfill_state_z_103 num_pre num_pre bits (cons (0) ((@nil Z))) ) ”
  &&  (CharArray.undef_full retval bits )
  **  (CharArray.seg retval bits (bits + 1 ) (cons (0) ((@nil Z))) )
).

Definition to_binary_string_entail_wit_4_split_goal_1 := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_103 (num_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (binary_safe_103 num_pre )) ,
  (((retval + (bits * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_missing_i retval bits 0 (bits + 1 ) )
|--
  “ (binary_backfill_state_z_103 num_pre num_pre bits (cons (0) ((@nil Z))) ) ”
.

Definition to_binary_string_entail_wit_4_split_goal_spatial := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_103 (num_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (binary_safe_103 num_pre )) ,
  (((retval + (bits * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_missing_i retval bits 0 (bits + 1 ) )
|--
  (CharArray.undef_full retval bits )
  **  (CharArray.seg retval bits (bits + 1 ) (cons (0) ((@nil Z))) )
.

Definition to_binary_string_entail_wit_5 := 
(
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_103 (num_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out <> 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_backfill_state_z_103 num_pre num_pre bits (cons (0) ((@nil Z))) )) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits (bits + 1 ) (cons (0) ((@nil Z))) )
|--
  EX (suffix: (@list Z)) ,
  “ (0 <= num_pre) ” 
  &&  “ (num_pre <= num_pre) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= (binary_length_z_103 (num_pre))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_103 num_pre ) ” 
  &&  “ (binary_backfill_state_z_103 num_pre num_pre bits suffix ) ” 
  &&  “ ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits )) ”
  &&  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix )
) \/
(
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_103 (num_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out <> 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (binary_backfill_state_z_103 num_pre num_pre bits (cons (0) ((@nil Z))) )) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits (bits + 1 ) (cons (0) ((@nil Z))) )
|--
  EX (suffix: (@list Z)) ,
  “ (0 <= num_pre) ” 
  &&  “ (num_pre <= num_pre) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= (binary_length_z_103 (num_pre))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_103 num_pre ) ” 
  &&  “ (binary_backfill_state_z_103 num_pre num_pre bits suffix ) ” 
  &&  “ ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits )) ”
  &&  (CharArray.undef_full out bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix )
).

Definition to_binary_string_entail_wit_6 := 
(
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num > 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= INT_MAX)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_103 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_103 num_pre )) (PreH11 : (binary_backfill_state_z_103 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix_2 )
|--
  EX (suffix: (@list Z)) ,
  “ (0 < num) ” 
  &&  “ (num <= num_pre) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (0 < bits) ” 
  &&  “ (bits <= (binary_length_z_103 (num_pre))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_103 num_pre ) ” 
  &&  “ (binary_backfill_state_z_103 num_pre num bits suffix ) ” 
  &&  “ ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits )) ”
  &&  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix )
) \/
(
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num > 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= INT_MAX)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_103 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_103 num_pre )) (PreH11 : (binary_backfill_state_z_103 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
|--
  “ (0 < bits) ”
  &&  (CharArray.undef_full out bits )
).

Definition to_binary_string_entail_wit_6_split_goal_1 := 
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num > 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= INT_MAX)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_103 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_103 num_pre )) (PreH11 : (binary_backfill_state_z_103 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
|--
  “ (0 < bits) ”
.

Definition to_binary_string_entail_wit_6_split_goal_spatial := 
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num > 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= INT_MAX)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_103 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_103 num_pre )) (PreH11 : (binary_backfill_state_z_103 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
|--
  (CharArray.undef_full out bits )
.

Definition to_binary_string_entail_wit_7 := 
(
forall (num_pre: Z) (suffix_2: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre num bits suffix_2 )) (PreH11 : ((Zlength (suffix_2)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  (((out + ((bits - 1 ) * sizeof(CHAR) ) )) # Char  |-> (signed_last_nbits ((48 + (num % ( 2 ) ) )) (8)))
  **  (CharArray.undef_missing_i out (bits - 1 ) 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix_2 )
|--
  EX (suffix: (@list Z)) ,
  “ (0 < num) ” 
  &&  “ (num <= num_pre) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (0 < bits) ” 
  &&  “ (bits <= (binary_length_z_103 (num_pre))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_103 num_pre ) ” 
  &&  “ (binary_backfill_state_z_103 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) ) ” 
  &&  “ ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix)))) = (((binary_length_z_103 (num_pre)) + 1 ) - (bits - 1 ) )) ”
  &&  (CharArray.undef_seg out 0 (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_103 (num_pre)) + 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )
) \/
(
forall (num_pre: Z) (suffix_2: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre num bits suffix_2 )) (PreH11 : ((Zlength (suffix_2)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  (((out + ((bits - 1 ) * sizeof(CHAR) ) )) # Char  |-> (signed_last_nbits ((48 + (num % ( 2 ) ) )) (8)))
  **  (CharArray.undef_missing_i out (bits - 1 ) 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix_2 )
|--
  EX (suffix: (@list Z)) ,
  “ (0 < num) ” 
  &&  “ (num <= num_pre) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (0 < bits) ” 
  &&  “ (bits <= (binary_length_z_103 (num_pre))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_103 num_pre ) ” 
  &&  “ (binary_backfill_state_z_103 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) ) ” 
  &&  “ ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix)))) = (((binary_length_z_103 (num_pre)) + 1 ) - (bits - 1 ) )) ”
  &&  (CharArray.undef_full out (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_103 (num_pre)) + 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )
).

Definition to_binary_string_entail_wit_8 := 
(
forall (num_pre: Z) (suffix_2: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix_2)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix_2)))) = (((binary_length_z_103 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  (CharArray.undef_seg out 0 (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_103 (num_pre)) + 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix_2)) )
|--
  EX (suffix: (@list Z)) ,
  “ (0 <= (num ÷ 2 )) ” 
  &&  “ ((num ÷ 2 ) <= num_pre) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (0 <= (bits - 1 )) ” 
  &&  “ ((bits - 1 ) <= (binary_length_z_103 (num_pre))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_103 num_pre ) ” 
  &&  “ (binary_backfill_state_z_103 num_pre (num ÷ 2 ) (bits - 1 ) suffix ) ” 
  &&  “ ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - (bits - 1 ) )) ”
  &&  (CharArray.undef_seg out 0 (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_103 (num_pre)) + 1 ) suffix )
) \/
(
forall (num_pre: Z) (suffix_2: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix_2)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix_2)))) = (((binary_length_z_103 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  (CharArray.undef_seg out 0 (bits - 1 ) )
|--
  “ ((num ÷ 2 ) <= num_pre) ” 
  &&  “ (0 <= (num ÷ 2 )) ”
  &&  (CharArray.undef_full out (bits - 1 ) )
).

Definition to_binary_string_entail_wit_8_split_goal_1 := 
forall (num_pre: Z) (suffix_2: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix_2)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix_2)))) = (((binary_length_z_103 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  (CharArray.undef_seg out 0 (bits - 1 ) )
|--
  “ ((num ÷ 2 ) <= num_pre) ”
.

Definition to_binary_string_entail_wit_8_split_goal_2 := 
forall (num_pre: Z) (suffix_2: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix_2)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix_2)))) = (((binary_length_z_103 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  (CharArray.undef_seg out 0 (bits - 1 ) )
|--
  “ (0 <= (num ÷ 2 )) ”
.

Definition to_binary_string_entail_wit_8_split_goal_spatial := 
forall (num_pre: Z) (suffix_2: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix_2)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix_2)))) = (((binary_length_z_103 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  (CharArray.undef_seg out 0 (bits - 1 ) )
|--
  (CharArray.undef_full out (bits - 1 ) )
.

Definition to_binary_string_entail_wit_9 := 
(
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num <= 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= INT_MAX)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_103 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_103 num_pre )) (PreH11 : (binary_backfill_state_z_103 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix_2 )
|--
  EX (suffix: (@list Z)) ,
  “ (num = 0) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_103 num_pre ) ” 
  &&  “ (suffix = (app ((binary_output_z_103 (num_pre))) ((cons (0) ((@nil Z)))))) ” 
  &&  “ ((Zlength (suffix)) = ((binary_length_z_103 (num_pre)) + 1 )) ”
  &&  (CharArray.seg out 0 ((binary_length_z_103 (num_pre)) + 1 ) suffix )
) \/
(
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num <= 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= INT_MAX)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_103 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_103 num_pre )) (PreH11 : (binary_backfill_state_z_103 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix_2 )
|--
  “ ((Zlength ((app ((binary_output_z_103 (num_pre))) ((cons (0) ((@nil Z))))))) = ((binary_length_z_103 (num_pre)) + 1 )) ” 
  &&  “ (bits = 0) ”
  &&  (CharArray.seg out 0 ((binary_length_z_103 (num_pre)) + 1 ) (app ((binary_output_z_103 (num_pre))) ((cons (0) ((@nil Z))))) )
).

Definition to_binary_string_entail_wit_9_split_goal_1 := 
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num <= 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= INT_MAX)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_103 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_103 num_pre )) (PreH11 : (binary_backfill_state_z_103 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix_2 )
|--
  “ ((Zlength ((app ((binary_output_z_103 (num_pre))) ((cons (0) ((@nil Z))))))) = ((binary_length_z_103 (num_pre)) + 1 )) ”
.

Definition to_binary_string_entail_wit_9_split_goal_2 := 
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num <= 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= INT_MAX)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_103 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_103 num_pre )) (PreH11 : (binary_backfill_state_z_103 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix_2 )
|--
  “ (bits = 0) ”
.

Definition to_binary_string_entail_wit_9_split_goal_spatial := 
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num <= 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= INT_MAX)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_103 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_103 num_pre )) (PreH11 : (binary_backfill_state_z_103 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix_2 )
|--
  (CharArray.seg out 0 ((binary_length_z_103 (num_pre)) + 1 ) (app ((binary_output_z_103 (num_pre))) ((cons (0) ((@nil Z))))) )
.

Definition to_binary_string_return_wit_1 := 
(
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (num = 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = 0)) (PreH6 : (out <> 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (suffix = (app ((binary_output_z_103 (num_pre))) ((cons (0) ((@nil Z))))))) (PreH9 : ((Zlength (suffix)) = ((binary_length_z_103 (num_pre)) + 1 ))) ,
  (CharArray.seg out 0 ((binary_length_z_103 (num_pre)) + 1 ) suffix )
|--
  EX (out_l: (@list Z))  (len: Z) ,
  “ (len = (Zlength (out_l))) ” 
  &&  “ (len = (binary_length_z_103 (num_pre))) ” 
  &&  “ (out_l = (binary_output_z_103 (num_pre))) ”
  &&  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
) \/
(
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (num = 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = 0)) (PreH6 : (out <> 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (suffix = (app ((binary_output_z_103 (num_pre))) ((cons (0) ((@nil Z))))))) (PreH9 : ((Zlength (suffix)) = ((binary_length_z_103 (num_pre)) + 1 ))) ,
  (CharArray.seg out 0 ((binary_length_z_103 (num_pre)) + 1 ) suffix )
|--
  “ ((Zlength ((binary_output_z_103 (num_pre)))) = (binary_length_z_103 (num_pre))) ”
  &&  (CharArray.full out ((Zlength ((binary_output_z_103 (num_pre)))) + 1 ) (app ((binary_output_z_103 (num_pre))) ((cons (0) ((@nil Z))))) )
).

Definition to_binary_string_return_wit_1_split_goal_1 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (num = 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = 0)) (PreH6 : (out <> 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (suffix = (app ((binary_output_z_103 (num_pre))) ((cons (0) ((@nil Z))))))) (PreH9 : ((Zlength (suffix)) = ((binary_length_z_103 (num_pre)) + 1 ))) ,
  (CharArray.seg out 0 ((binary_length_z_103 (num_pre)) + 1 ) suffix )
|--
  “ ((Zlength ((binary_output_z_103 (num_pre)))) = (binary_length_z_103 (num_pre))) ”
.

Definition to_binary_string_return_wit_1_split_goal_spatial := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (num = 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = 0)) (PreH6 : (out <> 0)) (PreH7 : (binary_safe_103 num_pre )) (PreH8 : (suffix = (app ((binary_output_z_103 (num_pre))) ((cons (0) ((@nil Z))))))) (PreH9 : ((Zlength (suffix)) = ((binary_length_z_103 (num_pre)) + 1 ))) ,
  (CharArray.seg out 0 ((binary_length_z_103 (num_pre)) + 1 ) suffix )
|--
  (CharArray.full out ((Zlength ((binary_output_z_103 (num_pre)))) + 1 ) (app ((binary_output_z_103 (num_pre))) ((cons (0) ((@nil Z))))) )
.

Definition to_binary_string_return_wit_2 := 
(
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (binary_safe_103 num_pre )) ,
  (CharArray.undef_seg retval (1 + 1 ) 2 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  EX (out_l: (@list Z))  (len: Z) ,
  “ (len = (Zlength (out_l))) ” 
  &&  “ (len = (binary_length_z_103 (num_pre))) ” 
  &&  “ (out_l = (binary_output_z_103 (num_pre))) ”
  &&  (CharArray.full retval (len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
) \/
(
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (binary_safe_103 num_pre )) ,
  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  “ ((Zlength ((binary_output_z_103 (num_pre)))) = (binary_length_z_103 (num_pre))) ”
  &&  (CharArray.full retval ((Zlength ((binary_output_z_103 (num_pre)))) + 1 ) (app ((binary_output_z_103 (num_pre))) ((cons (0) ((@nil Z))))) )
).

Definition to_binary_string_return_wit_2_split_goal_1 := 
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (binary_safe_103 num_pre )) ,
  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  “ ((Zlength ((binary_output_z_103 (num_pre)))) = (binary_length_z_103 (num_pre))) ”
.

Definition to_binary_string_return_wit_2_split_goal_spatial := 
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (binary_safe_103 num_pre )) ,
  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  (CharArray.full retval ((Zlength ((binary_output_z_103 (num_pre)))) + 1 ) (app ((binary_output_z_103 (num_pre))) ((cons (0) ((@nil Z))))) )
.

Definition to_binary_string_partial_solve_wit_1_pure := 
forall (num_pre: Z) (PreH1 : (num_pre = 0)) (PreH2 : (0 <= num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (binary_safe_103 num_pre )) ,
  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> num_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (2 > 0) ” 
  &&  “ (2 < INT_MAX) ”
.

Definition to_binary_string_partial_solve_wit_1_aux := 
forall (num_pre: Z) (PreH1 : (num_pre = 0)) (PreH2 : (0 <= num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (binary_safe_103 num_pre )) ,
  TT && emp 
|--
  “ (2 > 0) ” 
  &&  “ (2 < INT_MAX) ” 
  &&  “ (num_pre = 0) ” 
  &&  “ (0 <= num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (binary_safe_103 num_pre ) ”
  &&  emp
.

Definition to_binary_string_partial_solve_wit_1 := to_binary_string_partial_solve_wit_1_pure -> to_binary_string_partial_solve_wit_1_aux.

Definition to_binary_string_partial_solve_wit_2 := 
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (binary_safe_103 num_pre )) ,
  (CharArray.undef_full retval 2 )
|--
  “ (retval <> 0) ” 
  &&  “ (num_pre = 0) ” 
  &&  “ (0 <= num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (binary_safe_103 num_pre ) ”
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 2 )
.

Definition to_binary_string_partial_solve_wit_3 := 
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (binary_safe_103 num_pre )) ,
  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  “ (retval <> 0) ” 
  &&  “ (num_pre = 0) ” 
  &&  “ (0 <= num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (binary_safe_103 num_pre ) ”
  &&  (((retval + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
.

Definition to_binary_string_partial_solve_wit_4_pure := 
(
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_103 (num_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((bits + 1 ) > 0) ” 
  &&  “ ((bits + 1 ) < INT_MAX) ”
) \/
(
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (bits <= INT_MAX)) (PreH2 : (x <= INT_MAX)) (PreH3 : (bits >= INT_MIN)) (PreH4 : (x >= INT_MIN)) (PreH5 : (num_pre >= INT_MIN)) (PreH6 : (0 < num_pre)) (PreH7 : (num_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_103 (num_pre)))) (PreH10 : (1 <= bits)) (PreH11 : (out = 0)) (PreH12 : (binary_safe_103 num_pre )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((bits + 1 ) < INT_MAX) ”
).

Definition to_binary_string_partial_solve_wit_4_pure_split_goal_1 := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (bits <= INT_MAX)) (PreH2 : (x <= INT_MAX)) (PreH3 : (bits >= INT_MIN)) (PreH4 : (x >= INT_MIN)) (PreH5 : (num_pre >= INT_MIN)) (PreH6 : (0 < num_pre)) (PreH7 : (num_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_103 (num_pre)))) (PreH10 : (1 <= bits)) (PreH11 : (out = 0)) (PreH12 : (binary_safe_103 num_pre )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((bits + 1 ) < INT_MAX) ”
.

Definition to_binary_string_partial_solve_wit_4_aux := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_103 (num_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_103 num_pre )) ,
  TT && emp 
|--
  “ ((bits + 1 ) > 0) ” 
  &&  “ ((bits + 1 ) < INT_MAX) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_103 (num_pre))) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (out = 0) ” 
  &&  “ (binary_safe_103 num_pre ) ”
  &&  emp
.

Definition to_binary_string_partial_solve_wit_4 := to_binary_string_partial_solve_wit_4_pure -> to_binary_string_partial_solve_wit_4_aux.

Definition to_binary_string_partial_solve_wit_5 := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_103 (num_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (binary_safe_103 num_pre )) ,
  (CharArray.undef_full retval (bits + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_103 (num_pre))) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (out = 0) ” 
  &&  “ (binary_safe_103 num_pre ) ”
  &&  (((retval + (bits * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval bits 0 (bits + 1 ) )
.

Definition to_binary_string_partial_solve_wit_6 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_103 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_103 num_pre )) (PreH10 : (binary_backfill_state_z_103 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix )
|--
  “ (0 < num) ” 
  &&  “ (num <= num_pre) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (0 < bits) ” 
  &&  “ (bits <= (binary_length_z_103 (num_pre))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_103 num_pre ) ” 
  &&  “ (binary_backfill_state_z_103 num_pre num bits suffix ) ” 
  &&  “ ((Zlength (suffix)) = (((binary_length_z_103 (num_pre)) + 1 ) - bits )) ”
  &&  (((out + ((bits - 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (bits - 1 ) 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_103 (num_pre)) + 1 ) suffix )
.

(*----- Function rounded_avg -----*)

Definition rounded_avg_safety_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (n_pre > m_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 < m_pre)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : ((n_pre + m_pre ) <= INT_MAX)) (PreH7 : (problem_103_pre_z n_pre m_pre )) (PreH8 : (rounded_avg_safe_103 n_pre m_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition rounded_avg_safety_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre > m_pre)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 < m_pre)) (PreH6 : (m_pre <= INT_MAX)) (PreH7 : ((n_pre + m_pre ) <= INT_MAX)) (PreH8 : (problem_103_pre_z n_pre m_pre )) (PreH9 : (rounded_avg_safe_103 n_pre m_pre )) ,
  (CharArray.undef_full retval 3 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rounded_avg_safety_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre > m_pre)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 < m_pre)) (PreH6 : (m_pre <= INT_MAX)) (PreH7 : ((n_pre + m_pre ) <= INT_MAX)) (PreH8 : (problem_103_pre_z n_pre m_pre )) (PreH9 : (rounded_avg_safe_103 n_pre m_pre )) ,
  (CharArray.undef_full retval 3 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (45 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 45) ”
.

Definition rounded_avg_safety_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre > m_pre)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 < m_pre)) (PreH6 : (m_pre <= INT_MAX)) (PreH7 : ((n_pre + m_pre ) <= INT_MAX)) (PreH8 : (problem_103_pre_z n_pre m_pre )) (PreH9 : (rounded_avg_safe_103 n_pre m_pre )) ,
  (CharArray.undef_seg retval (0 + 1 ) 3 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rounded_avg_safety_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre > m_pre)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 < m_pre)) (PreH6 : (m_pre <= INT_MAX)) (PreH7 : ((n_pre + m_pre ) <= INT_MAX)) (PreH8 : (problem_103_pre_z n_pre m_pre )) (PreH9 : (rounded_avg_safe_103 n_pre m_pre )) ,
  (CharArray.undef_seg retval (0 + 1 ) 3 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (49 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 49) ”
.

Definition rounded_avg_safety_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre > m_pre)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 < m_pre)) (PreH6 : (m_pre <= INT_MAX)) (PreH7 : ((n_pre + m_pre ) <= INT_MAX)) (PreH8 : (problem_103_pre_z n_pre m_pre )) (PreH9 : (rounded_avg_safe_103 n_pre m_pre )) ,
  (CharArray.undef_seg retval (1 + 1 ) 3 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 49)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition rounded_avg_safety_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre > m_pre)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 < m_pre)) (PreH6 : (m_pre <= INT_MAX)) (PreH7 : ((n_pre + m_pre ) <= INT_MAX)) (PreH8 : (problem_103_pre_z n_pre m_pre )) (PreH9 : (rounded_avg_safe_103 n_pre m_pre )) ,
  (CharArray.undef_seg retval (1 + 1 ) 3 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 49)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rounded_avg_safety_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (n_pre <= m_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 < m_pre)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : ((n_pre + m_pre ) <= INT_MAX)) (PreH7 : (problem_103_pre_z n_pre m_pre )) (PreH8 : (rounded_avg_safe_103 n_pre m_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((m_pre + n_pre ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition rounded_avg_safety_wit_9 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (n_pre <= m_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 < m_pre)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : ((n_pre + m_pre ) <= INT_MAX)) (PreH7 : (problem_103_pre_z n_pre m_pre )) (PreH8 : (rounded_avg_safe_103 n_pre m_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((m_pre + n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (m_pre + n_pre )) ”
.

Definition rounded_avg_safety_wit_10 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (n_pre <= m_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 < m_pre)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : ((n_pre + m_pre ) <= INT_MAX)) (PreH7 : (problem_103_pre_z n_pre m_pre )) (PreH8 : (rounded_avg_safe_103 n_pre m_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition rounded_avg_return_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (out_l_2: (@list Z)) (len_2: Z) (retval: Z) (PreH1 : (len_2 = (Zlength (out_l_2)))) (PreH2 : (len_2 = (binary_length_z_103 (((m_pre + n_pre ) ÷ 2 ))))) (PreH3 : (out_l_2 = (binary_output_z_103 (((m_pre + n_pre ) ÷ 2 ))))) (PreH4 : (n_pre <= m_pre)) (PreH5 : (0 < n_pre)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (0 < m_pre)) (PreH8 : (m_pre <= INT_MAX)) (PreH9 : ((n_pre + m_pre ) <= INT_MAX)) (PreH10 : (problem_103_pre_z n_pre m_pre )) (PreH11 : (rounded_avg_safe_103 n_pre m_pre )) ,
  (CharArray.full retval (len_2 + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
|--
  EX (out_l: (@list Z))  (len: Z) ,
  “ (len = (Zlength (out_l))) ” 
  &&  “ (problem_103_spec_z n_pre m_pre out_l ) ”
  &&  (CharArray.full retval (len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (out_l_2: (@list Z)) (len_2: Z) (retval: Z) (PreH1 : (0 <= (len_2 + 1 ))) (PreH2 : (len_2 = (Zlength (out_l_2)))) (PreH3 : (len_2 = (binary_length_z_103 (((m_pre + n_pre ) ÷ 2 ))))) (PreH4 : (out_l_2 = (binary_output_z_103 (((m_pre + n_pre ) ÷ 2 ))))) (PreH5 : (n_pre <= m_pre)) (PreH6 : (0 < n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 < m_pre)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : ((n_pre + m_pre ) <= INT_MAX)) (PreH11 : (problem_103_pre_z n_pre m_pre )) (PreH12 : (rounded_avg_safe_103 n_pre m_pre )) ,
  (CharArray.full retval (len_2 + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
|--
  EX (out_l: (@list Z)) ,
  “ (problem_103_spec_z n_pre m_pre out_l ) ”
  &&  (CharArray.full retval ((Zlength (out_l)) + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
).

Definition rounded_avg_return_wit_2 := 
(
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre > m_pre)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 < m_pre)) (PreH6 : (m_pre <= INT_MAX)) (PreH7 : ((n_pre + m_pre ) <= INT_MAX)) (PreH8 : (problem_103_pre_z n_pre m_pre )) (PreH9 : (rounded_avg_safe_103 n_pre m_pre )) ,
  (CharArray.undef_seg retval (2 + 1 ) 3 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 49)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
|--
  EX (out_l: (@list Z))  (len: Z) ,
  “ (len = (Zlength (out_l))) ” 
  &&  “ (problem_103_spec_z n_pre m_pre out_l ) ”
  &&  (CharArray.full retval (len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre > m_pre)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 < m_pre)) (PreH6 : (m_pre <= INT_MAX)) (PreH7 : ((n_pre + m_pre ) <= INT_MAX)) (PreH8 : (problem_103_pre_z n_pre m_pre )) (PreH9 : (rounded_avg_safe_103 n_pre m_pre )) ,
  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 49)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
|--
  EX (out_l: (@list Z)) ,
  “ (problem_103_spec_z n_pre m_pre out_l ) ”
  &&  (CharArray.full retval ((Zlength (out_l)) + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
).

Definition rounded_avg_partial_solve_wit_1_pure := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (n_pre > m_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 < m_pre)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : ((n_pre + m_pre ) <= INT_MAX)) (PreH7 : (problem_103_pre_z n_pre m_pre )) (PreH8 : (rounded_avg_safe_103 n_pre m_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (3 > 0) ” 
  &&  “ (3 < INT_MAX) ”
.

Definition rounded_avg_partial_solve_wit_1_aux := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (n_pre > m_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 < m_pre)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : ((n_pre + m_pre ) <= INT_MAX)) (PreH7 : (problem_103_pre_z n_pre m_pre )) (PreH8 : (rounded_avg_safe_103 n_pre m_pre )) ,
  TT && emp 
|--
  “ (3 > 0) ” 
  &&  “ (3 < INT_MAX) ” 
  &&  “ (n_pre > m_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ ((n_pre + m_pre ) <= INT_MAX) ” 
  &&  “ (problem_103_pre_z n_pre m_pre ) ” 
  &&  “ (rounded_avg_safe_103 n_pre m_pre ) ”
  &&  emp
.

Definition rounded_avg_partial_solve_wit_1 := rounded_avg_partial_solve_wit_1_pure -> rounded_avg_partial_solve_wit_1_aux.

Definition rounded_avg_partial_solve_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre > m_pre)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 < m_pre)) (PreH6 : (m_pre <= INT_MAX)) (PreH7 : ((n_pre + m_pre ) <= INT_MAX)) (PreH8 : (problem_103_pre_z n_pre m_pre )) (PreH9 : (rounded_avg_safe_103 n_pre m_pre )) ,
  (CharArray.undef_full retval 3 )
|--
  “ (retval <> 0) ” 
  &&  “ (n_pre > m_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ ((n_pre + m_pre ) <= INT_MAX) ” 
  &&  “ (problem_103_pre_z n_pre m_pre ) ” 
  &&  “ (rounded_avg_safe_103 n_pre m_pre ) ”
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 3 )
.

Definition rounded_avg_partial_solve_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre > m_pre)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 < m_pre)) (PreH6 : (m_pre <= INT_MAX)) (PreH7 : ((n_pre + m_pre ) <= INT_MAX)) (PreH8 : (problem_103_pre_z n_pre m_pre )) (PreH9 : (rounded_avg_safe_103 n_pre m_pre )) ,
  (CharArray.undef_seg retval (0 + 1 ) 3 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
|--
  “ (retval <> 0) ” 
  &&  “ (n_pre > m_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ ((n_pre + m_pre ) <= INT_MAX) ” 
  &&  “ (problem_103_pre_z n_pre m_pre ) ” 
  &&  “ (rounded_avg_safe_103 n_pre m_pre ) ”
  &&  (((retval + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 (0 + 1 ) 3 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
.

Definition rounded_avg_partial_solve_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (n_pre > m_pre)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 < m_pre)) (PreH6 : (m_pre <= INT_MAX)) (PreH7 : ((n_pre + m_pre ) <= INT_MAX)) (PreH8 : (problem_103_pre_z n_pre m_pre )) (PreH9 : (rounded_avg_safe_103 n_pre m_pre )) ,
  (CharArray.undef_seg retval (1 + 1 ) 3 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 49)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
|--
  “ (retval <> 0) ” 
  &&  “ (n_pre > m_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ ((n_pre + m_pre ) <= INT_MAX) ” 
  &&  “ (problem_103_pre_z n_pre m_pre ) ” 
  &&  “ (rounded_avg_safe_103 n_pre m_pre ) ”
  &&  (((retval + (2 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 2 (1 + 1 ) 3 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 49)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
.

Definition rounded_avg_partial_solve_wit_5_pure := 
(
forall (m_pre: Z) (n_pre: Z) (PreH1 : (n_pre <= m_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 < m_pre)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : ((n_pre + m_pre ) <= INT_MAX)) (PreH7 : (problem_103_pre_z n_pre m_pre )) (PreH8 : (rounded_avg_safe_103 n_pre m_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "num" ) )) # Int  |-> ((m_pre + n_pre ) ÷ 2 ))
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (binary_safe_103 ((m_pre + n_pre ) ÷ 2 ) ) ” 
  &&  “ (((m_pre + n_pre ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (0 <= ((m_pre + n_pre ) ÷ 2 )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (PreH1 : (((m_pre + n_pre ) ÷ 2 ) <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (m_pre >= INT_MIN)) (PreH4 : (((m_pre + n_pre ) ÷ 2 ) >= INT_MIN)) (PreH5 : (n_pre <= m_pre)) (PreH6 : (0 < n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 < m_pre)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : ((n_pre + m_pre ) <= INT_MAX)) (PreH11 : (problem_103_pre_z n_pre m_pre )) (PreH12 : (rounded_avg_safe_103 n_pre m_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "num" ) )) # Int  |-> ((m_pre + n_pre ) ÷ 2 ))
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= ((m_pre + n_pre ) ÷ 2 )) ” 
  &&  “ (binary_safe_103 ((m_pre + n_pre ) ÷ 2 ) ) ”
).

Definition rounded_avg_partial_solve_wit_5_pure_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (((m_pre + n_pre ) ÷ 2 ) <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (m_pre >= INT_MIN)) (PreH4 : (((m_pre + n_pre ) ÷ 2 ) >= INT_MIN)) (PreH5 : (n_pre <= m_pre)) (PreH6 : (0 < n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 < m_pre)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : ((n_pre + m_pre ) <= INT_MAX)) (PreH11 : (problem_103_pre_z n_pre m_pre )) (PreH12 : (rounded_avg_safe_103 n_pre m_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "num" ) )) # Int  |-> ((m_pre + n_pre ) ÷ 2 ))
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= ((m_pre + n_pre ) ÷ 2 )) ”
.

Definition rounded_avg_partial_solve_wit_5_pure_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (((m_pre + n_pre ) ÷ 2 ) <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (m_pre >= INT_MIN)) (PreH4 : (((m_pre + n_pre ) ÷ 2 ) >= INT_MIN)) (PreH5 : (n_pre <= m_pre)) (PreH6 : (0 < n_pre)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (0 < m_pre)) (PreH9 : (m_pre <= INT_MAX)) (PreH10 : ((n_pre + m_pre ) <= INT_MAX)) (PreH11 : (problem_103_pre_z n_pre m_pre )) (PreH12 : (rounded_avg_safe_103 n_pre m_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "num" ) )) # Int  |-> ((m_pre + n_pre ) ÷ 2 ))
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (binary_safe_103 ((m_pre + n_pre ) ÷ 2 ) ) ”
.

Definition rounded_avg_partial_solve_wit_5_aux := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (n_pre <= m_pre)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (0 < m_pre)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : ((n_pre + m_pre ) <= INT_MAX)) (PreH7 : (problem_103_pre_z n_pre m_pre )) (PreH8 : (rounded_avg_safe_103 n_pre m_pre )) ,
  TT && emp 
|--
  “ (binary_safe_103 ((m_pre + n_pre ) ÷ 2 ) ) ” 
  &&  “ (((m_pre + n_pre ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (0 <= ((m_pre + n_pre ) ÷ 2 )) ” 
  &&  “ (n_pre <= m_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ ((n_pre + m_pre ) <= INT_MAX) ” 
  &&  “ (problem_103_pre_z n_pre m_pre ) ” 
  &&  “ (rounded_avg_safe_103 n_pre m_pre ) ”
  &&  emp
.

Definition rounded_avg_partial_solve_wit_5 := rounded_avg_partial_solve_wit_5_pure -> rounded_avg_partial_solve_wit_5_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_to_binary_string_safety_wit_1 : to_binary_string_safety_wit_1.
Axiom proof_of_to_binary_string_safety_wit_2 : to_binary_string_safety_wit_2.
Axiom proof_of_to_binary_string_safety_wit_3 : to_binary_string_safety_wit_3.
Axiom proof_of_to_binary_string_safety_wit_4 : to_binary_string_safety_wit_4.
Axiom proof_of_to_binary_string_safety_wit_5 : to_binary_string_safety_wit_5.
Axiom proof_of_to_binary_string_safety_wit_6 : to_binary_string_safety_wit_6.
Axiom proof_of_to_binary_string_safety_wit_7 : to_binary_string_safety_wit_7.
Axiom proof_of_to_binary_string_safety_wit_8 : to_binary_string_safety_wit_8.
Axiom proof_of_to_binary_string_safety_wit_9 : to_binary_string_safety_wit_9.
Axiom proof_of_to_binary_string_safety_wit_10 : to_binary_string_safety_wit_10.
Axiom proof_of_to_binary_string_safety_wit_11 : to_binary_string_safety_wit_11.
Axiom proof_of_to_binary_string_safety_wit_12 : to_binary_string_safety_wit_12.
Axiom proof_of_to_binary_string_safety_wit_13 : to_binary_string_safety_wit_13.
Axiom proof_of_to_binary_string_safety_wit_14 : to_binary_string_safety_wit_14.
Axiom proof_of_to_binary_string_safety_wit_15 : to_binary_string_safety_wit_15.
Axiom proof_of_to_binary_string_safety_wit_16 : to_binary_string_safety_wit_16.
Axiom proof_of_to_binary_string_safety_wit_17 : to_binary_string_safety_wit_17.
Axiom proof_of_to_binary_string_safety_wit_18 : to_binary_string_safety_wit_18.
Axiom proof_of_to_binary_string_safety_wit_19 : to_binary_string_safety_wit_19.
Axiom proof_of_to_binary_string_safety_wit_20 : to_binary_string_safety_wit_20.
Axiom proof_of_to_binary_string_safety_wit_21 : to_binary_string_safety_wit_21.
Axiom proof_of_to_binary_string_safety_wit_22 : to_binary_string_safety_wit_22.
Axiom proof_of_to_binary_string_safety_wit_23 : to_binary_string_safety_wit_23.
Axiom proof_of_to_binary_string_safety_wit_24 : to_binary_string_safety_wit_24.
Axiom proof_of_to_binary_string_safety_wit_25 : to_binary_string_safety_wit_25.
Axiom proof_of_to_binary_string_safety_wit_26 : to_binary_string_safety_wit_26.
Axiom proof_of_to_binary_string_safety_wit_27 : to_binary_string_safety_wit_27.
Axiom proof_of_to_binary_string_entail_wit_1 : to_binary_string_entail_wit_1.
Axiom proof_of_to_binary_string_entail_wit_2 : to_binary_string_entail_wit_2.
Axiom proof_of_to_binary_string_entail_wit_3 : to_binary_string_entail_wit_3.
Axiom proof_of_to_binary_string_entail_wit_4 : to_binary_string_entail_wit_4.
Axiom proof_of_to_binary_string_entail_wit_5 : to_binary_string_entail_wit_5.
Axiom proof_of_to_binary_string_entail_wit_6 : to_binary_string_entail_wit_6.
Axiom proof_of_to_binary_string_entail_wit_7 : to_binary_string_entail_wit_7.
Axiom proof_of_to_binary_string_entail_wit_8 : to_binary_string_entail_wit_8.
Axiom proof_of_to_binary_string_entail_wit_9 : to_binary_string_entail_wit_9.
Axiom proof_of_to_binary_string_return_wit_1 : to_binary_string_return_wit_1.
Axiom proof_of_to_binary_string_return_wit_2 : to_binary_string_return_wit_2.
Axiom proof_of_to_binary_string_partial_solve_wit_1_pure : to_binary_string_partial_solve_wit_1_pure.
Axiom proof_of_to_binary_string_partial_solve_wit_1 : to_binary_string_partial_solve_wit_1.
Axiom proof_of_to_binary_string_partial_solve_wit_2 : to_binary_string_partial_solve_wit_2.
Axiom proof_of_to_binary_string_partial_solve_wit_3 : to_binary_string_partial_solve_wit_3.
Axiom proof_of_to_binary_string_partial_solve_wit_4_pure : to_binary_string_partial_solve_wit_4_pure.
Axiom proof_of_to_binary_string_partial_solve_wit_4 : to_binary_string_partial_solve_wit_4.
Axiom proof_of_to_binary_string_partial_solve_wit_5 : to_binary_string_partial_solve_wit_5.
Axiom proof_of_to_binary_string_partial_solve_wit_6 : to_binary_string_partial_solve_wit_6.
Axiom proof_of_rounded_avg_safety_wit_1 : rounded_avg_safety_wit_1.
Axiom proof_of_rounded_avg_safety_wit_2 : rounded_avg_safety_wit_2.
Axiom proof_of_rounded_avg_safety_wit_3 : rounded_avg_safety_wit_3.
Axiom proof_of_rounded_avg_safety_wit_4 : rounded_avg_safety_wit_4.
Axiom proof_of_rounded_avg_safety_wit_5 : rounded_avg_safety_wit_5.
Axiom proof_of_rounded_avg_safety_wit_6 : rounded_avg_safety_wit_6.
Axiom proof_of_rounded_avg_safety_wit_7 : rounded_avg_safety_wit_7.
Axiom proof_of_rounded_avg_safety_wit_8 : rounded_avg_safety_wit_8.
Axiom proof_of_rounded_avg_safety_wit_9 : rounded_avg_safety_wit_9.
Axiom proof_of_rounded_avg_safety_wit_10 : rounded_avg_safety_wit_10.
Axiom proof_of_rounded_avg_return_wit_1 : rounded_avg_return_wit_1.
Axiom proof_of_rounded_avg_return_wit_2 : rounded_avg_return_wit_2.
Axiom proof_of_rounded_avg_partial_solve_wit_1_pure : rounded_avg_partial_solve_wit_1_pure.
Axiom proof_of_rounded_avg_partial_solve_wit_1 : rounded_avg_partial_solve_wit_1.
Axiom proof_of_rounded_avg_partial_solve_wit_2 : rounded_avg_partial_solve_wit_2.
Axiom proof_of_rounded_avg_partial_solve_wit_3 : rounded_avg_partial_solve_wit_3.
Axiom proof_of_rounded_avg_partial_solve_wit_4 : rounded_avg_partial_solve_wit_4.
Axiom proof_of_rounded_avg_partial_solve_wit_5_pure : rounded_avg_partial_solve_wit_5_pure.
Axiom proof_of_rounded_avg_partial_solve_wit_5 : rounded_avg_partial_solve_wit_5.

End VC_Correct.
