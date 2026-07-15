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
Require Import coins_84.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function to_binary_string -----*)

Definition to_binary_string_safety_wit_1 := 
forall (num_pre: Z) (PreH1 : (0 <= num_pre)) (PreH2 : (num_pre <= 36)) (PreH3 : (binary_safe_84 num_pre )) (PreH4 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  ((( &( "bits" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition to_binary_string_safety_wit_2 := 
forall (num_pre: Z) (PreH1 : (0 <= num_pre)) (PreH2 : (num_pre <= 36)) (PreH3 : (binary_safe_84 num_pre )) (PreH4 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Int  |-> num_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition to_binary_string_safety_wit_3 := 
forall (num_pre: Z) (PreH1 : (0 <= num_pre)) (PreH2 : (num_pre <= 36)) (PreH3 : (binary_safe_84 num_pre )) (PreH4 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> num_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition to_binary_string_safety_wit_4 := 
forall (num_pre: Z) (PreH1 : (num_pre = 0)) (PreH2 : (0 <= num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (binary_safe_84 num_pre )) (PreH5 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> num_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition to_binary_string_safety_wit_5 := 
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (binary_safe_84 num_pre )) (PreH6 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
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
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (binary_safe_84 num_pre )) (PreH6 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
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
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (binary_safe_84 num_pre )) (PreH6 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
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
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (binary_safe_84 num_pre )) (PreH6 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
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
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= 36)) (PreH3 : (0 <= x)) (PreH4 : (0 <= bits)) (PreH5 : (out = 0)) (PreH6 : (binary_safe_84 num_pre )) (PreH7 : (binary_count_state_z_84 num_pre x bits )) ,
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
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((bits + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bits + 1 )) ”
) \/
(
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((bits + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bits + 1 )) ”
).

Definition to_binary_string_safety_wit_10_split_goal_1 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((bits + 1 ) <= INT_MAX) ”
.

Definition to_binary_string_safety_wit_10_split_goal_2 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((INT_MIN) <= (bits + 1 )) ”
.

Definition to_binary_string_safety_wit_11 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition to_binary_string_safety_wit_12 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> (bits + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((x <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition to_binary_string_safety_wit_13 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> (bits + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition to_binary_string_safety_wit_14 := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= 36)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_84 (num_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((bits + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bits + 1 )) ”
.

Definition to_binary_string_safety_wit_15 := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= 36)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_84 (num_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition to_binary_string_safety_wit_16 := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_84 (num_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (binary_safe_84 num_pre )) (PreH9 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
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
forall (num_pre: Z) (suffix: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (0 <= num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 <= bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition to_binary_string_safety_wit_18 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix )
|--
  “ ((bits - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bits - 1 )) ”
.

Definition to_binary_string_safety_wit_19 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition to_binary_string_safety_wit_20 := 
(
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix )
|--
  “ ((48 + (num % ( 2 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (48 + (num % ( 2 ) ) )) ”
) \/
(
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix )
|--
  “ ((48 + (num % ( 2 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (48 + (num % ( 2 ) ) )) ”
).

Definition to_binary_string_safety_wit_20_split_goal_1 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix )
|--
  “ ((48 + (num % ( 2 ) ) ) <= INT_MAX) ”
.

Definition to_binary_string_safety_wit_20_split_goal_2 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix )
|--
  “ ((INT_MIN) <= (48 + (num % ( 2 ) ) )) ”
.

Definition to_binary_string_safety_wit_21 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix )
|--
  “ ((num <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition to_binary_string_safety_wit_22 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition to_binary_string_safety_wit_23 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition to_binary_string_safety_wit_24 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix)))) = (((binary_length_z_84 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_84 (num_pre)) + 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )
|--
  “ ((bits - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bits - 1 )) ”
.

Definition to_binary_string_safety_wit_25 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix)))) = (((binary_length_z_84 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_84 (num_pre)) + 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition to_binary_string_safety_wit_26 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix)))) = (((binary_length_z_84 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> (bits - 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_84 (num_pre)) + 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )
|--
  “ ((num <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition to_binary_string_safety_wit_27 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix)))) = (((binary_length_z_84 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> (bits - 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out 0 (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_84 (num_pre)) + 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition to_binary_string_entail_wit_1 := 
(
forall (num_pre: Z) (PreH1 : (num_pre <> 0)) (PreH2 : (0 <= num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (binary_safe_84 num_pre )) (PreH5 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 < num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (0 <= num_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (binary_count_state_z_84 num_pre num_pre 0 ) ”
  &&  emp
) \/
(
forall (num_pre: Z) (PreH1 : (num_pre <> 0)) (PreH2 : (0 <= num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (binary_safe_84 num_pre )) (PreH5 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (binary_count_state_z_84 num_pre num_pre 0 ) ”
  &&  emp
).

Definition to_binary_string_entail_wit_1_split_goal_1 := 
forall (num_pre: Z) (PreH1 : (num_pre <> 0)) (PreH2 : (0 <= num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (binary_safe_84 num_pre )) (PreH5 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (binary_count_state_z_84 num_pre num_pre 0 ) ”
.

Definition to_binary_string_entail_wit_2 := 
(
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  TT && emp 
|--
  “ (0 < num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (0 <= (x ÷ 2 )) ” 
  &&  “ (0 <= (bits + 1 )) ” 
  &&  “ (out = 0) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (binary_count_state_z_84 num_pre (x ÷ 2 ) (bits + 1 ) ) ”
  &&  emp
) \/
(
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  TT && emp 
|--
  “ (binary_count_state_z_84 num_pre (x ÷ 2 ) (bits + 1 ) ) ” 
  &&  “ (0 <= (x ÷ 2 )) ”
  &&  emp
).

Definition to_binary_string_entail_wit_2_split_goal_1 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  TT && emp 
|--
  “ (binary_count_state_z_84 num_pre (x ÷ 2 ) (bits + 1 ) ) ”
.

Definition to_binary_string_entail_wit_2_split_goal_2 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  TT && emp 
|--
  “ (0 <= (x ÷ 2 )) ”
.

Definition to_binary_string_entail_wit_3 := 
(
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x <= 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  TT && emp 
|--
  “ (0 < num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_84 (num_pre))) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (out = 0) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX) ”
  &&  emp
) \/
(
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x <= 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  TT && emp 
|--
  “ (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (bits = (binary_length_z_84 (num_pre))) ”
  &&  emp
).

Definition to_binary_string_entail_wit_3_split_goal_1 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x <= 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  TT && emp 
|--
  “ (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX) ”
.

Definition to_binary_string_entail_wit_3_split_goal_2 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x <= 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  TT && emp 
|--
  “ (1 <= bits) ”
.

Definition to_binary_string_entail_wit_3_split_goal_3 := 
forall (num_pre: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x <= 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_count_state_z_84 num_pre x bits )) ,
  TT && emp 
|--
  “ (bits = (binary_length_z_84 (num_pre))) ”
.

Definition to_binary_string_entail_wit_4 := 
(
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_84 (num_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (binary_safe_84 num_pre )) (PreH9 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  (((retval + (bits * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_missing_i retval bits 0 (bits + 1 ) )
|--
  “ (0 < num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_84 (num_pre))) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (binary_backfill_state_z_84 num_pre num_pre bits (cons (0) ((@nil Z))) ) ”
  &&  (CharArray.undef_seg retval 0 bits )
  **  (CharArray.seg retval bits (bits + 1 ) (cons (0) ((@nil Z))) )
) \/
(
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_84 (num_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (binary_safe_84 num_pre )) (PreH9 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  (((retval + (bits * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_missing_i retval bits 0 (bits + 1 ) )
|--
  “ (binary_backfill_state_z_84 num_pre num_pre bits (cons (0) ((@nil Z))) ) ”
  &&  (CharArray.undef_full retval bits )
  **  (CharArray.seg retval bits (bits + 1 ) (cons (0) ((@nil Z))) )
).

Definition to_binary_string_entail_wit_4_split_goal_1 := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_84 (num_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (binary_safe_84 num_pre )) (PreH9 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  (((retval + (bits * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_missing_i retval bits 0 (bits + 1 ) )
|--
  “ (binary_backfill_state_z_84 num_pre num_pre bits (cons (0) ((@nil Z))) ) ”
.

Definition to_binary_string_entail_wit_4_split_goal_spatial := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_84 (num_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (binary_safe_84 num_pre )) (PreH9 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  (((retval + (bits * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.undef_missing_i retval bits 0 (bits + 1 ) )
|--
  (CharArray.undef_full retval bits )
  **  (CharArray.seg retval bits (bits + 1 ) (cons (0) ((@nil Z))) )
.

Definition to_binary_string_entail_wit_5 := 
(
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= 36)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_84 (num_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out <> 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_backfill_state_z_84 num_pre num_pre bits (cons (0) ((@nil Z))) )) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits (bits + 1 ) (cons (0) ((@nil Z))) )
|--
  EX (suffix: (@list Z)) ,
  “ (0 <= num_pre) ” 
  &&  “ (num_pre <= num_pre) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (x = 0) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= (binary_length_z_84 (num_pre))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (binary_backfill_state_z_84 num_pre num_pre bits suffix ) ” 
  &&  “ ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits )) ”
  &&  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix )
) \/
(
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= 36)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_84 (num_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out <> 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (binary_backfill_state_z_84 num_pre num_pre bits (cons (0) ((@nil Z))) )) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits (bits + 1 ) (cons (0) ((@nil Z))) )
|--
  EX (suffix: (@list Z)) ,
  “ (0 <= num_pre) ” 
  &&  “ (num_pre <= num_pre) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (x = 0) ” 
  &&  “ (0 <= bits) ” 
  &&  “ (bits <= (binary_length_z_84 (num_pre))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (binary_backfill_state_z_84 num_pre num_pre bits suffix ) ” 
  &&  “ ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits )) ”
  &&  (CharArray.undef_full out bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix )
).

Definition to_binary_string_entail_wit_6 := 
(
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num > 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= 36)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_84 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_84 num_pre )) (PreH11 : (binary_backfill_state_z_84 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix_2 )
|--
  EX (suffix: (@list Z)) ,
  “ (0 < num) ” 
  &&  “ (num <= num_pre) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (x = 0) ” 
  &&  “ (0 < bits) ” 
  &&  “ (bits <= (binary_length_z_84 (num_pre))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (binary_backfill_state_z_84 num_pre num bits suffix ) ” 
  &&  “ ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits )) ”
  &&  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix )
) \/
(
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num > 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= 36)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_84 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_84 num_pre )) (PreH11 : (binary_backfill_state_z_84 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
|--
  “ (0 < bits) ”
  &&  (CharArray.undef_full out bits )
).

Definition to_binary_string_entail_wit_6_split_goal_1 := 
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num > 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= 36)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_84 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_84 num_pre )) (PreH11 : (binary_backfill_state_z_84 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
|--
  “ (0 < bits) ”
.

Definition to_binary_string_entail_wit_6_split_goal_spatial := 
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num > 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= 36)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_84 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_84 num_pre )) (PreH11 : (binary_backfill_state_z_84 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
|--
  (CharArray.undef_full out bits )
.

Definition to_binary_string_entail_wit_7 := 
(
forall (num_pre: Z) (suffix_2: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre num bits suffix_2 )) (PreH11 : ((Zlength (suffix_2)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  (((out + ((bits - 1 ) * sizeof(CHAR) ) )) # Char  |-> (signed_last_nbits ((48 + (num % ( 2 ) ) )) (8)))
  **  (CharArray.undef_missing_i out (bits - 1 ) 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix_2 )
|--
  EX (suffix: (@list Z)) ,
  “ (0 < num) ” 
  &&  “ (num <= num_pre) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (x = 0) ” 
  &&  “ (0 < bits) ” 
  &&  “ (bits <= (binary_length_z_84 (num_pre))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (binary_backfill_state_z_84 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) ) ” 
  &&  “ ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix)))) = (((binary_length_z_84 (num_pre)) + 1 ) - (bits - 1 ) )) ”
  &&  (CharArray.undef_seg out 0 (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_84 (num_pre)) + 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )
) \/
(
forall (num_pre: Z) (suffix_2: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre num bits suffix_2 )) (PreH11 : ((Zlength (suffix_2)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  (((out + ((bits - 1 ) * sizeof(CHAR) ) )) # Char  |-> (signed_last_nbits ((48 + (num % ( 2 ) ) )) (8)))
  **  (CharArray.undef_missing_i out (bits - 1 ) 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix_2 )
|--
  EX (suffix: (@list Z)) ,
  “ (0 < num) ” 
  &&  “ (num <= num_pre) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (x = 0) ” 
  &&  “ (0 < bits) ” 
  &&  “ (bits <= (binary_length_z_84 (num_pre))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (binary_backfill_state_z_84 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) ) ” 
  &&  “ ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix)))) = (((binary_length_z_84 (num_pre)) + 1 ) - (bits - 1 ) )) ”
  &&  (CharArray.undef_full out (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_84 (num_pre)) + 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix)) )
).

Definition to_binary_string_entail_wit_8 := 
(
forall (num_pre: Z) (suffix_2: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix_2)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix_2)))) = (((binary_length_z_84 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  (CharArray.undef_seg out 0 (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_84 (num_pre)) + 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix_2)) )
|--
  EX (suffix: (@list Z)) ,
  “ (0 <= (num ÷ 2 )) ” 
  &&  “ ((num ÷ 2 ) <= num_pre) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (x = 0) ” 
  &&  “ (0 <= (bits - 1 )) ” 
  &&  “ ((bits - 1 ) <= (binary_length_z_84 (num_pre))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (binary_backfill_state_z_84 num_pre (num ÷ 2 ) (bits - 1 ) suffix ) ” 
  &&  “ ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - (bits - 1 ) )) ”
  &&  (CharArray.undef_seg out 0 (bits - 1 ) )
  **  (CharArray.seg out (bits - 1 ) ((binary_length_z_84 (num_pre)) + 1 ) suffix )
) \/
(
forall (num_pre: Z) (suffix_2: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix_2)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix_2)))) = (((binary_length_z_84 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  (CharArray.undef_seg out 0 (bits - 1 ) )
|--
  “ ((num ÷ 2 ) <= num_pre) ” 
  &&  “ (0 <= (num ÷ 2 )) ”
  &&  (CharArray.undef_full out (bits - 1 ) )
).

Definition to_binary_string_entail_wit_8_split_goal_1 := 
forall (num_pre: Z) (suffix_2: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix_2)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix_2)))) = (((binary_length_z_84 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  (CharArray.undef_seg out 0 (bits - 1 ) )
|--
  “ ((num ÷ 2 ) <= num_pre) ”
.

Definition to_binary_string_entail_wit_8_split_goal_2 := 
forall (num_pre: Z) (suffix_2: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix_2)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix_2)))) = (((binary_length_z_84 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  (CharArray.undef_seg out 0 (bits - 1 ) )
|--
  “ (0 <= (num ÷ 2 )) ”
.

Definition to_binary_string_entail_wit_8_split_goal_spatial := 
forall (num_pre: Z) (suffix_2: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre (num ÷ 2 ) (bits - 1 ) (cons ((48 + (num % ( 2 ) ) )) (suffix_2)) )) (PreH11 : ((Zlength ((cons ((48 + (num % ( 2 ) ) )) (suffix_2)))) = (((binary_length_z_84 (num_pre)) + 1 ) - (bits - 1 ) ))) ,
  (CharArray.undef_seg out 0 (bits - 1 ) )
|--
  (CharArray.undef_full out (bits - 1 ) )
.

Definition to_binary_string_entail_wit_9 := 
(
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num <= 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= 36)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_84 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_84 num_pre )) (PreH11 : (binary_backfill_state_z_84 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix_2 )
|--
  EX (suffix: (@list Z)) ,
  “ (num = 0) ” 
  &&  “ (num_pre > 0) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (suffix = (app ((binary_output_z_84 (num_pre))) ((cons (0) ((@nil Z)))))) ” 
  &&  “ ((Zlength (suffix)) = ((binary_length_z_84 (num_pre)) + 1 )) ”
  &&  (CharArray.seg out 0 ((binary_length_z_84 (num_pre)) + 1 ) suffix )
) \/
(
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num <= 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= 36)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_84 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_84 num_pre )) (PreH11 : (binary_backfill_state_z_84 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix_2 )
|--
  “ ((Zlength ((app ((binary_output_z_84 (num_pre))) ((cons (0) ((@nil Z))))))) = ((binary_length_z_84 (num_pre)) + 1 )) ” 
  &&  “ (bits = 0) ”
  &&  (CharArray.seg out 0 ((binary_length_z_84 (num_pre)) + 1 ) (app ((binary_output_z_84 (num_pre))) ((cons (0) ((@nil Z))))) )
).

Definition to_binary_string_entail_wit_9_split_goal_1 := 
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num <= 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= 36)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_84 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_84 num_pre )) (PreH11 : (binary_backfill_state_z_84 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix_2 )
|--
  “ ((Zlength ((app ((binary_output_z_84 (num_pre))) ((cons (0) ((@nil Z))))))) = ((binary_length_z_84 (num_pre)) + 1 )) ”
.

Definition to_binary_string_entail_wit_9_split_goal_2 := 
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num <= 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= 36)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_84 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_84 num_pre )) (PreH11 : (binary_backfill_state_z_84 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix_2 )
|--
  “ (bits = 0) ”
.

Definition to_binary_string_entail_wit_9_split_goal_spatial := 
forall (num_pre: Z) (suffix_2: (@list Z)) (out: Z) (bits: Z) (x: Z) (num: Z) (PreH1 : (num <= 0)) (PreH2 : (0 <= num)) (PreH3 : (num <= num_pre)) (PreH4 : (0 < num_pre)) (PreH5 : (num_pre <= 36)) (PreH6 : (x = 0)) (PreH7 : (0 <= bits)) (PreH8 : (bits <= (binary_length_z_84 (num_pre)))) (PreH9 : (out <> 0)) (PreH10 : (binary_safe_84 num_pre )) (PreH11 : (binary_backfill_state_z_84 num_pre num bits suffix_2 )) (PreH12 : ((Zlength (suffix_2)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix_2 )
|--
  (CharArray.seg out 0 ((binary_length_z_84 (num_pre)) + 1 ) (app ((binary_output_z_84 (num_pre))) ((cons (0) ((@nil Z))))) )
.

Definition to_binary_string_return_wit_1 := 
(
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (num = 0)) (PreH2 : (num_pre > 0)) (PreH3 : (num_pre <= 36)) (PreH4 : (x = 0)) (PreH5 : (bits = 0)) (PreH6 : (out <> 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (suffix = (app ((binary_output_z_84 (num_pre))) ((cons (0) ((@nil Z))))))) (PreH9 : ((Zlength (suffix)) = ((binary_length_z_84 (num_pre)) + 1 ))) ,
  (CharArray.seg out 0 ((binary_length_z_84 (num_pre)) + 1 ) suffix )
|--
  EX (out_l: (@list Z))  (len: Z) ,
  “ (len = (Zlength (out_l))) ” 
  &&  “ (len = (binary_length_z_84 (num_pre))) ” 
  &&  “ (out_l = (binary_output_z_84 (num_pre))) ”
  &&  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
) \/
(
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (num = 0)) (PreH2 : (num_pre > 0)) (PreH3 : (num_pre <= 36)) (PreH4 : (x = 0)) (PreH5 : (bits = 0)) (PreH6 : (out <> 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (suffix = (app ((binary_output_z_84 (num_pre))) ((cons (0) ((@nil Z))))))) (PreH9 : ((Zlength (suffix)) = ((binary_length_z_84 (num_pre)) + 1 ))) ,
  (CharArray.seg out 0 ((binary_length_z_84 (num_pre)) + 1 ) suffix )
|--
  “ ((Zlength ((binary_output_z_84 (num_pre)))) = (binary_length_z_84 (num_pre))) ”
  &&  (CharArray.full out ((Zlength ((binary_output_z_84 (num_pre)))) + 1 ) (app ((binary_output_z_84 (num_pre))) ((cons (0) ((@nil Z))))) )
).

Definition to_binary_string_return_wit_1_split_goal_1 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (num = 0)) (PreH2 : (num_pre > 0)) (PreH3 : (num_pre <= 36)) (PreH4 : (x = 0)) (PreH5 : (bits = 0)) (PreH6 : (out <> 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (suffix = (app ((binary_output_z_84 (num_pre))) ((cons (0) ((@nil Z))))))) (PreH9 : ((Zlength (suffix)) = ((binary_length_z_84 (num_pre)) + 1 ))) ,
  (CharArray.seg out 0 ((binary_length_z_84 (num_pre)) + 1 ) suffix )
|--
  “ ((Zlength ((binary_output_z_84 (num_pre)))) = (binary_length_z_84 (num_pre))) ”
.

Definition to_binary_string_return_wit_1_split_goal_spatial := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (num = 0)) (PreH2 : (num_pre > 0)) (PreH3 : (num_pre <= 36)) (PreH4 : (x = 0)) (PreH5 : (bits = 0)) (PreH6 : (out <> 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (suffix = (app ((binary_output_z_84 (num_pre))) ((cons (0) ((@nil Z))))))) (PreH9 : ((Zlength (suffix)) = ((binary_length_z_84 (num_pre)) + 1 ))) ,
  (CharArray.seg out 0 ((binary_length_z_84 (num_pre)) + 1 ) suffix )
|--
  (CharArray.full out ((Zlength ((binary_output_z_84 (num_pre)))) + 1 ) (app ((binary_output_z_84 (num_pre))) ((cons (0) ((@nil Z))))) )
.

Definition to_binary_string_return_wit_2 := 
(
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (binary_safe_84 num_pre )) (PreH6 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (1 + 1 ) 2 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  EX (out_l: (@list Z))  (len: Z) ,
  “ (len = (Zlength (out_l))) ” 
  &&  “ (len = (binary_length_z_84 (num_pre))) ” 
  &&  “ (out_l = (binary_output_z_84 (num_pre))) ”
  &&  (CharArray.full retval (len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
) \/
(
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (binary_safe_84 num_pre )) (PreH6 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  “ ((Zlength ((binary_output_z_84 (num_pre)))) = (binary_length_z_84 (num_pre))) ”
  &&  (CharArray.full retval ((Zlength ((binary_output_z_84 (num_pre)))) + 1 ) (app ((binary_output_z_84 (num_pre))) ((cons (0) ((@nil Z))))) )
).

Definition to_binary_string_return_wit_2_split_goal_1 := 
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (binary_safe_84 num_pre )) (PreH6 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  “ ((Zlength ((binary_output_z_84 (num_pre)))) = (binary_length_z_84 (num_pre))) ”
.

Definition to_binary_string_return_wit_2_split_goal_spatial := 
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (binary_safe_84 num_pre )) (PreH6 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  (CharArray.full retval ((Zlength ((binary_output_z_84 (num_pre)))) + 1 ) (app ((binary_output_z_84 (num_pre))) ((cons (0) ((@nil Z))))) )
.

Definition to_binary_string_partial_solve_wit_1_pure := 
forall (num_pre: Z) (PreH1 : (num_pre = 0)) (PreH2 : (0 <= num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (binary_safe_84 num_pre )) (PreH5 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> num_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (2 > 0) ”
.

Definition to_binary_string_partial_solve_wit_1_aux := 
forall (num_pre: Z) (PreH1 : (num_pre = 0)) (PreH2 : (0 <= num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (binary_safe_84 num_pre )) (PreH5 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (2 > 0) ” 
  &&  “ (num_pre = 0) ” 
  &&  “ (0 <= num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX) ”
  &&  emp
.

Definition to_binary_string_partial_solve_wit_1 := to_binary_string_partial_solve_wit_1_pure -> to_binary_string_partial_solve_wit_1_aux.

Definition to_binary_string_partial_solve_wit_2 := 
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (binary_safe_84 num_pre )) (PreH6 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval 2 )
|--
  “ (retval <> 0) ” 
  &&  “ (num_pre = 0) ” 
  &&  “ (0 <= num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX) ”
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 2 )
.

Definition to_binary_string_partial_solve_wit_3 := 
forall (num_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (num_pre = 0)) (PreH3 : (0 <= num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (binary_safe_84 num_pre )) (PreH6 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  “ (retval <> 0) ” 
  &&  “ (num_pre = 0) ” 
  &&  “ (0 <= num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX) ”
  &&  (((retval + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
.

Definition to_binary_string_partial_solve_wit_4_pure := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= 36)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_84 (num_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  ((( &( "num" ) )) # Int  |-> num_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((bits + 1 ) > 0) ”
.

Definition to_binary_string_partial_solve_wit_4_aux := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num_pre)) (PreH2 : (num_pre <= 36)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_84 (num_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (binary_safe_84 num_pre )) (PreH8 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  TT && emp 
|--
  “ ((bits + 1 ) > 0) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_84 (num_pre))) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (out = 0) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX) ”
  &&  emp
.

Definition to_binary_string_partial_solve_wit_4 := to_binary_string_partial_solve_wit_4_pure -> to_binary_string_partial_solve_wit_4_aux.

Definition to_binary_string_partial_solve_wit_5 := 
forall (num_pre: Z) (x: Z) (bits: Z) (out: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 < num_pre)) (PreH3 : (num_pre <= 36)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_84 (num_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (binary_safe_84 num_pre )) (PreH9 : (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval (bits + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_84 (num_pre))) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (out = 0) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (((binary_length_z_84 (num_pre)) + 1 ) < INT_MAX) ”
  &&  (((retval + (bits * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval bits 0 (bits + 1 ) )
.

Definition to_binary_string_partial_solve_wit_6 := 
forall (num_pre: Z) (suffix: (@list Z)) (num: Z) (x: Z) (bits: Z) (out: Z) (PreH1 : (0 < num)) (PreH2 : (num <= num_pre)) (PreH3 : (0 < num_pre)) (PreH4 : (num_pre <= 36)) (PreH5 : (x = 0)) (PreH6 : (0 < bits)) (PreH7 : (bits <= (binary_length_z_84 (num_pre)))) (PreH8 : (out <> 0)) (PreH9 : (binary_safe_84 num_pre )) (PreH10 : (binary_backfill_state_z_84 num_pre num bits suffix )) (PreH11 : ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits ))) ,
  (CharArray.undef_seg out 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix )
|--
  “ (0 < num) ” 
  &&  “ (num <= num_pre) ” 
  &&  “ (0 < num_pre) ” 
  &&  “ (num_pre <= 36) ” 
  &&  “ (x = 0) ” 
  &&  “ (0 < bits) ” 
  &&  “ (bits <= (binary_length_z_84 (num_pre))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (binary_safe_84 num_pre ) ” 
  &&  “ (binary_backfill_state_z_84 num_pre num bits suffix ) ” 
  &&  “ ((Zlength (suffix)) = (((binary_length_z_84 (num_pre)) + 1 ) - bits )) ”
  &&  (((out + ((bits - 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (bits - 1 ) 0 bits )
  **  (CharArray.seg out bits ((binary_length_z_84 (num_pre)) + 1 ) suffix )
.

(*----- Function solve -----*)

Definition solve_safety_wit_1 := 
forall (N_pre: Z) (PreH1 : (0 <= N_pre)) (PreH2 : (N_pre <= 10000)) (PreH3 : (problem_84_pre_z N_pre )) (PreH4 : (solve_safe_84 N_pre )) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "N" ) )) # Int  |-> N_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_2 := 
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (0 <= N)) (PreH2 : (N <= N_pre)) (PreH3 : (0 <= N_pre)) (PreH4 : (N_pre <= 10000)) (PreH5 : (0 <= sum)) (PreH6 : (sum <= 36)) (PreH7 : (problem_84_pre_z N_pre )) (PreH8 : (solve_safe_84 N_pre )) (PreH9 : (digit_sum_state_z_84 N_pre N sum )) ,
  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_3 := 
(
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N > 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (N % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (N % ( 10 ) ) )) ”
) \/
(
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N > 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (N % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (N % ( 10 ) ) )) ”
).

Definition solve_safety_wit_3_split_goal_1 := 
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N > 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (N % ( 10 ) ) ) <= INT_MAX) ”
.

Definition solve_safety_wit_3_split_goal_2 := 
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N > 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= (sum + (N % ( 10 ) ) )) ”
.

Definition solve_safety_wit_4 := 
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N > 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((N <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition solve_safety_wit_5 := 
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N > 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition solve_safety_wit_6 := 
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N > 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (N % ( 10 ) ) ))
|--
  “ ((N <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition solve_safety_wit_7 := 
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N > 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (N % ( 10 ) ) ))
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition solve_entail_wit_1 := 
(
forall (N_pre: Z) (PreH1 : (0 <= N_pre)) (PreH2 : (N_pre <= 10000)) (PreH3 : (problem_84_pre_z N_pre )) (PreH4 : (solve_safe_84 N_pre )) ,
  TT && emp 
|--
  “ (0 <= N_pre) ” 
  &&  “ (N_pre <= N_pre) ” 
  &&  “ (0 <= N_pre) ” 
  &&  “ (N_pre <= 10000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 36) ” 
  &&  “ (problem_84_pre_z N_pre ) ” 
  &&  “ (solve_safe_84 N_pre ) ” 
  &&  “ (digit_sum_state_z_84 N_pre N_pre 0 ) ”
  &&  emp
) \/
(
forall (N_pre: Z) (PreH1 : (0 <= N_pre)) (PreH2 : (N_pre <= 10000)) (PreH3 : (problem_84_pre_z N_pre )) (PreH4 : (solve_safe_84 N_pre )) ,
  TT && emp 
|--
  “ (digit_sum_state_z_84 N_pre N_pre 0 ) ”
  &&  emp
).

Definition solve_entail_wit_1_split_goal_1 := 
forall (N_pre: Z) (PreH1 : (0 <= N_pre)) (PreH2 : (N_pre <= 10000)) (PreH3 : (problem_84_pre_z N_pre )) (PreH4 : (solve_safe_84 N_pre )) ,
  TT && emp 
|--
  “ (digit_sum_state_z_84 N_pre N_pre 0 ) ”
.

Definition solve_entail_wit_2 := 
(
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N > 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  TT && emp 
|--
  “ (0 <= (N ÷ 10 )) ” 
  &&  “ ((N ÷ 10 ) <= N_pre) ” 
  &&  “ (0 <= N_pre) ” 
  &&  “ (N_pre <= 10000) ” 
  &&  “ (0 <= (sum + (N % ( 10 ) ) )) ” 
  &&  “ ((sum + (N % ( 10 ) ) ) <= 36) ” 
  &&  “ (problem_84_pre_z N_pre ) ” 
  &&  “ (solve_safe_84 N_pre ) ” 
  &&  “ (digit_sum_state_z_84 N_pre (N ÷ 10 ) (sum + (N % ( 10 ) ) ) ) ”
  &&  emp
) \/
(
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N > 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  TT && emp 
|--
  “ (digit_sum_state_z_84 N_pre (N ÷ 10 ) (sum + (N % ( 10 ) ) ) ) ” 
  &&  “ ((sum + (N % ( 10 ) ) ) <= 36) ” 
  &&  “ (0 <= (sum + (N % ( 10 ) ) )) ” 
  &&  “ ((N ÷ 10 ) <= N_pre) ” 
  &&  “ (0 <= (N ÷ 10 )) ”
  &&  emp
).

Definition solve_entail_wit_2_split_goal_1 := 
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N > 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  TT && emp 
|--
  “ (digit_sum_state_z_84 N_pre (N ÷ 10 ) (sum + (N % ( 10 ) ) ) ) ”
.

Definition solve_entail_wit_2_split_goal_2 := 
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N > 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  TT && emp 
|--
  “ ((sum + (N % ( 10 ) ) ) <= 36) ”
.

Definition solve_entail_wit_2_split_goal_3 := 
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N > 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  TT && emp 
|--
  “ (0 <= (sum + (N % ( 10 ) ) )) ”
.

Definition solve_entail_wit_2_split_goal_4 := 
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N > 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  TT && emp 
|--
  “ ((N ÷ 10 ) <= N_pre) ”
.

Definition solve_entail_wit_2_split_goal_5 := 
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N > 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  TT && emp 
|--
  “ (0 <= (N ÷ 10 )) ”
.

Definition solve_entail_wit_3 := 
(
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N <= 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  TT && emp 
|--
  “ (N = 0) ” 
  &&  “ (0 <= N_pre) ” 
  &&  “ (N_pre <= 10000) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= 36) ” 
  &&  “ (problem_84_pre_z N_pre ) ” 
  &&  “ (solve_safe_84 N_pre ) ” 
  &&  “ (sum = (digit_sum_z_84 (N_pre))) ” 
  &&  “ (binary_safe_84 sum ) ”
  &&  emp
) \/
(
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N <= 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  TT && emp 
|--
  “ (binary_safe_84 sum ) ” 
  &&  “ (sum = (digit_sum_z_84 (N_pre))) ”
  &&  emp
).

Definition solve_entail_wit_3_split_goal_1 := 
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N <= 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  TT && emp 
|--
  “ (binary_safe_84 sum ) ”
.

Definition solve_entail_wit_3_split_goal_2 := 
forall (N_pre: Z) (sum: Z) (N: Z) (PreH1 : (N <= 0)) (PreH2 : (0 <= N)) (PreH3 : (N <= N_pre)) (PreH4 : (0 <= N_pre)) (PreH5 : (N_pre <= 10000)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= 36)) (PreH8 : (problem_84_pre_z N_pre )) (PreH9 : (solve_safe_84 N_pre )) (PreH10 : (digit_sum_state_z_84 N_pre N sum )) ,
  TT && emp 
|--
  “ (sum = (digit_sum_z_84 (N_pre))) ”
.

Definition solve_return_wit_1 := 
(
forall (N_pre: Z) (N: Z) (sum: Z) (out_l_2: (@list Z)) (len_2: Z) (retval: Z) (PreH1 : (len_2 = (Zlength (out_l_2)))) (PreH2 : (len_2 = (binary_length_z_84 (sum)))) (PreH3 : (out_l_2 = (binary_output_z_84 (sum)))) (PreH4 : (N = 0)) (PreH5 : (0 <= N_pre)) (PreH6 : (N_pre <= 10000)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= 36)) (PreH9 : (problem_84_pre_z N_pre )) (PreH10 : (solve_safe_84 N_pre )) (PreH11 : (sum = (digit_sum_z_84 (N_pre)))) (PreH12 : (binary_safe_84 sum )) ,
  (CharArray.full retval (len_2 + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
|--
  EX (out_l: (@list Z))  (len: Z) ,
  “ (len = (Zlength (out_l))) ” 
  &&  “ (problem_84_spec_z N_pre out_l ) ”
  &&  (CharArray.full retval (len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
) \/
(
forall (N_pre: Z) (N: Z) (sum: Z) (out_l_2: (@list Z)) (len_2: Z) (retval: Z) (PreH1 : (0 <= (len_2 + 1 ))) (PreH2 : (len_2 = (Zlength (out_l_2)))) (PreH3 : (len_2 = (binary_length_z_84 (sum)))) (PreH4 : (out_l_2 = (binary_output_z_84 (sum)))) (PreH5 : (N = 0)) (PreH6 : (0 <= N_pre)) (PreH7 : (N_pre <= 10000)) (PreH8 : (0 <= sum)) (PreH9 : (sum <= 36)) (PreH10 : (problem_84_pre_z N_pre )) (PreH11 : (solve_safe_84 N_pre )) (PreH12 : (sum = (digit_sum_z_84 (N_pre)))) (PreH13 : (binary_safe_84 sum )) ,
  (CharArray.full retval (len_2 + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
|--
  EX (out_l: (@list Z)) ,
  “ (problem_84_spec_z N_pre out_l ) ”
  &&  (CharArray.full retval ((Zlength (out_l)) + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
).

Definition solve_partial_solve_wit_1_pure := 
(
forall (N_pre: Z) (N: Z) (sum: Z) (PreH1 : (N = 0)) (PreH2 : (0 <= N_pre)) (PreH3 : (N_pre <= 10000)) (PreH4 : (0 <= sum)) (PreH5 : (sum <= 36)) (PreH6 : (problem_84_pre_z N_pre )) (PreH7 : (solve_safe_84 N_pre )) (PreH8 : (sum = (digit_sum_z_84 (N_pre)))) (PreH9 : (binary_safe_84 sum )) ,
  ((( &( "result" ) )) # Ptr  |->_)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (0 <= sum) ” 
  &&  “ (sum <= 36) ” 
  &&  “ (binary_safe_84 sum ) ” 
  &&  “ (((binary_length_z_84 (sum)) + 1 ) < INT_MAX) ”
) \/
(
forall (N_pre: Z) (N: Z) (sum: Z) (PreH1 : (sum <= INT_MAX)) (PreH2 : (N <= INT_MAX)) (PreH3 : (sum >= INT_MIN)) (PreH4 : (N >= INT_MIN)) (PreH5 : (N = 0)) (PreH6 : (0 <= N_pre)) (PreH7 : (N_pre <= 10000)) (PreH8 : (0 <= sum)) (PreH9 : (sum <= 36)) (PreH10 : (problem_84_pre_z N_pre )) (PreH11 : (solve_safe_84 N_pre )) (PreH12 : (sum = (digit_sum_z_84 (N_pre)))) (PreH13 : (binary_safe_84 sum )) ,
  ((( &( "result" ) )) # Ptr  |->_)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((binary_length_z_84 (sum)) + 1 ) < INT_MAX) ”
).

Definition solve_partial_solve_wit_1_pure_split_goal_1 := 
forall (N_pre: Z) (N: Z) (sum: Z) (PreH1 : (sum <= INT_MAX)) (PreH2 : (N <= INT_MAX)) (PreH3 : (sum >= INT_MIN)) (PreH4 : (N >= INT_MIN)) (PreH5 : (N = 0)) (PreH6 : (0 <= N_pre)) (PreH7 : (N_pre <= 10000)) (PreH8 : (0 <= sum)) (PreH9 : (sum <= 36)) (PreH10 : (problem_84_pre_z N_pre )) (PreH11 : (solve_safe_84 N_pre )) (PreH12 : (sum = (digit_sum_z_84 (N_pre)))) (PreH13 : (binary_safe_84 sum )) ,
  ((( &( "result" ) )) # Ptr  |->_)
  **  ((( &( "N" ) )) # Int  |-> N)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((binary_length_z_84 (sum)) + 1 ) < INT_MAX) ”
.

Definition solve_partial_solve_wit_1_aux := 
forall (N_pre: Z) (N: Z) (sum: Z) (PreH1 : (N = 0)) (PreH2 : (0 <= N_pre)) (PreH3 : (N_pre <= 10000)) (PreH4 : (0 <= sum)) (PreH5 : (sum <= 36)) (PreH6 : (problem_84_pre_z N_pre )) (PreH7 : (solve_safe_84 N_pre )) (PreH8 : (sum = (digit_sum_z_84 (N_pre)))) (PreH9 : (binary_safe_84 sum )) ,
  TT && emp 
|--
  “ (0 <= sum) ” 
  &&  “ (sum <= 36) ” 
  &&  “ (binary_safe_84 sum ) ” 
  &&  “ (((binary_length_z_84 (sum)) + 1 ) < INT_MAX) ” 
  &&  “ (N = 0) ” 
  &&  “ (0 <= N_pre) ” 
  &&  “ (N_pre <= 10000) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= 36) ” 
  &&  “ (problem_84_pre_z N_pre ) ” 
  &&  “ (solve_safe_84 N_pre ) ” 
  &&  “ (sum = (digit_sum_z_84 (N_pre))) ” 
  &&  “ (binary_safe_84 sum ) ”
  &&  emp
.

Definition solve_partial_solve_wit_1 := solve_partial_solve_wit_1_pure -> solve_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

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
Axiom proof_of_solve_safety_wit_1 : solve_safety_wit_1.
Axiom proof_of_solve_safety_wit_2 : solve_safety_wit_2.
Axiom proof_of_solve_safety_wit_3 : solve_safety_wit_3.
Axiom proof_of_solve_safety_wit_4 : solve_safety_wit_4.
Axiom proof_of_solve_safety_wit_5 : solve_safety_wit_5.
Axiom proof_of_solve_safety_wit_6 : solve_safety_wit_6.
Axiom proof_of_solve_safety_wit_7 : solve_safety_wit_7.
Axiom proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Axiom proof_of_solve_entail_wit_2 : solve_entail_wit_2.
Axiom proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Axiom proof_of_solve_return_wit_1 : solve_return_wit_1.
Axiom proof_of_solve_partial_solve_wit_1_pure : solve_partial_solve_wit_1_pure.
Axiom proof_of_solve_partial_solve_wit_1 : solve_partial_solve_wit_1.

End VC_Correct.
