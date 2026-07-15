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
Require Import coins_79.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function decimal_to_binary -----*)

Definition decimal_to_binary_safety_wit_1 := 
forall (decimal_pre: Z) (PreH1 : (0 <= decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (problem_79_pre_z decimal_pre )) (PreH4 : (binary_safe_79 decimal_pre )) (PreH5 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  ((( &( "bits" ) )) # Int  |->_)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decimal_to_binary_safety_wit_2 := 
forall (decimal_pre: Z) (PreH1 : (0 <= decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (problem_79_pre_z decimal_pre )) (PreH4 : (binary_safe_79 decimal_pre )) (PreH5 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decimal_to_binary_safety_wit_3 := 
forall (decimal_pre: Z) (PreH1 : (0 <= decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (problem_79_pre_z decimal_pre )) (PreH4 : (binary_safe_79 decimal_pre )) (PreH5 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decimal_to_binary_safety_wit_4 := 
forall (decimal_pre: Z) (PreH1 : (0 <= decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (problem_79_pre_z decimal_pre )) (PreH4 : (binary_safe_79 decimal_pre )) (PreH5 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  ((( &( "divisor" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition decimal_to_binary_safety_wit_5 := 
forall (decimal_pre: Z) (PreH1 : (0 <= decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (problem_79_pre_z decimal_pre )) (PreH4 : (binary_safe_79 decimal_pre )) (PreH5 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition decimal_to_binary_safety_wit_6 := 
forall (decimal_pre: Z) (PreH1 : (0 <= decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (problem_79_pre_z decimal_pre )) (PreH4 : (binary_safe_79 decimal_pre )) (PreH5 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decimal_to_binary_safety_wit_7 := 
forall (decimal_pre: Z) (PreH1 : (decimal_pre = 0)) (PreH2 : (0 <= decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (problem_79_pre_z decimal_pre )) (PreH5 : (binary_safe_79 decimal_pre )) (PreH6 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (6 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 6) ”
.

Definition decimal_to_binary_safety_wit_8 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_full retval 6 )
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decimal_to_binary_safety_wit_9 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_full retval 6 )
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition decimal_to_binary_safety_wit_10 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (0 + 1 ) 6 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition decimal_to_binary_safety_wit_11 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (0 + 1 ) 6 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (98 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 98) ”
.

Definition decimal_to_binary_safety_wit_12 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (1 + 1 ) 6 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition decimal_to_binary_safety_wit_13 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (1 + 1 ) 6 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition decimal_to_binary_safety_wit_14 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (2 + 1 ) 6 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition decimal_to_binary_safety_wit_15 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (2 + 1 ) 6 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition decimal_to_binary_safety_wit_16 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (3 + 1 ) 6 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition decimal_to_binary_safety_wit_17 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (3 + 1 ) 6 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (98 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 98) ”
.

Definition decimal_to_binary_safety_wit_18 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (4 + 1 ) 6 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition decimal_to_binary_safety_wit_19 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (4 + 1 ) 6 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decimal_to_binary_safety_wit_20 := 
forall (decimal_pre: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (0 <= x)) (PreH4 : (0 <= bits)) (PreH5 : (out = 0)) (PreH6 : (pos = 0)) (PreH7 : (divisor = 1)) (PreH8 : (i = 1)) (PreH9 : (problem_79_pre_z decimal_pre )) (PreH10 : (binary_safe_79 decimal_pre )) (PreH11 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH12 : (binary_count_state_z_79 decimal_pre x bits )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decimal_to_binary_safety_wit_21 := 
(
forall (decimal_pre: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (divisor = 1)) (PreH9 : (i = 1)) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH13 : (binary_count_state_z_79 decimal_pre x bits )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((bits + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bits + 1 )) ”
) \/
(
forall (decimal_pre: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (divisor = 1)) (PreH9 : (i = 1)) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH13 : (binary_count_state_z_79 decimal_pre x bits )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((bits + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bits + 1 )) ”
).

Definition decimal_to_binary_safety_wit_21_split_goal_1 := 
forall (decimal_pre: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (divisor = 1)) (PreH9 : (i = 1)) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH13 : (binary_count_state_z_79 decimal_pre x bits )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((bits + 1 ) <= INT_MAX) ”
.

Definition decimal_to_binary_safety_wit_21_split_goal_2 := 
forall (decimal_pre: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (divisor = 1)) (PreH9 : (i = 1)) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH13 : (binary_count_state_z_79 decimal_pre x bits )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((INT_MIN) <= (bits + 1 )) ”
.

Definition decimal_to_binary_safety_wit_22 := 
forall (decimal_pre: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (divisor = 1)) (PreH9 : (i = 1)) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH13 : (binary_count_state_z_79 decimal_pre x bits )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition decimal_to_binary_safety_wit_23 := 
forall (decimal_pre: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (divisor = 1)) (PreH9 : (i = 1)) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH13 : (binary_count_state_z_79 decimal_pre x bits )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> (bits + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((x <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition decimal_to_binary_safety_wit_24 := 
forall (decimal_pre: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (divisor = 1)) (PreH9 : (i = 1)) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH13 : (binary_count_state_z_79 decimal_pre x bits )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> (bits + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition decimal_to_binary_safety_wit_25 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (out: Z) (pos: Z) (i: Z) (divisor: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (1 <= i)) (PreH9 : (i < bits)) (PreH10 : (1 <= divisor)) (PreH11 : (divisor <= INT_MAX)) (PreH12 : ((divisor * 2 ) <= INT_MAX)) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_divisor_state_z_79 decimal_pre i divisor )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
|--
  “ ((divisor * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (divisor * 2 )) ”
.

Definition decimal_to_binary_safety_wit_26 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (out: Z) (pos: Z) (i: Z) (divisor: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (1 <= i)) (PreH9 : (i < bits)) (PreH10 : (1 <= divisor)) (PreH11 : (divisor <= INT_MAX)) (PreH12 : ((divisor * 2 ) <= INT_MAX)) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_divisor_state_z_79 decimal_pre i divisor )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition decimal_to_binary_safety_wit_27 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (out: Z) (pos: Z) (i: Z) (divisor: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (1 <= i)) (PreH9 : (i < bits)) (PreH10 : (1 <= divisor)) (PreH11 : (divisor <= INT_MAX)) (PreH12 : ((divisor * 2 ) <= INT_MAX)) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_divisor_state_z_79 decimal_pre i divisor )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "divisor" ) )) # Int  |-> (divisor * 2 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition decimal_to_binary_safety_wit_28 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (out: Z) (pos: Z) (i: Z) (divisor: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (1 <= i)) (PreH9 : (i < bits)) (PreH10 : (1 <= divisor)) (PreH11 : (divisor <= INT_MAX)) (PreH12 : ((divisor * 2 ) <= INT_MAX)) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_divisor_state_z_79 decimal_pre i divisor )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "divisor" ) )) # Int  |-> (divisor * 2 ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition decimal_to_binary_safety_wit_29 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (i: Z) (divisor: Z) (out: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (i = bits)) (PreH6 : (1 <= bits)) (PreH7 : (1 <= divisor)) (PreH8 : (divisor <= INT_MAX)) (PreH9 : (out = 0)) (PreH10 : (pos = 0)) (PreH11 : (problem_79_pre_z decimal_pre )) (PreH12 : (binary_safe_79 decimal_pre )) (PreH13 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH14 : (binary_divisor_state_z_79 decimal_pre bits divisor )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
|--
  “ ((bits + 5 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bits + 5 )) ”
.

Definition decimal_to_binary_safety_wit_30 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (i: Z) (divisor: Z) (out: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (i = bits)) (PreH6 : (1 <= bits)) (PreH7 : (1 <= divisor)) (PreH8 : (divisor <= INT_MAX)) (PreH9 : (out = 0)) (PreH10 : (pos = 0)) (PreH11 : (problem_79_pre_z decimal_pre )) (PreH12 : (binary_safe_79 decimal_pre )) (PreH13 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH14 : (binary_divisor_state_z_79 decimal_pre bits divisor )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition decimal_to_binary_safety_wit_31 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (i: Z) (divisor: Z) (out: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (i = bits)) (PreH7 : (1 <= divisor)) (PreH8 : (divisor <= INT_MAX)) (PreH9 : (binary_divisor_state_z_79 decimal_pre bits divisor )) (PreH10 : (out <> 0)) (PreH11 : (pos = 0)) (PreH12 : (0 < (bits + 5 ))) (PreH13 : ((bits + 5 ) < INT_MAX)) (PreH14 : (1 < (bits + 5 ))) (PreH15 : (problem_79_pre_z decimal_pre )) (PreH16 : (binary_safe_79 decimal_pre )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  (CharArray.undef_full out (bits + 5 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decimal_to_binary_safety_wit_32 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (i: Z) (divisor: Z) (out: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (i = bits)) (PreH7 : (1 <= divisor)) (PreH8 : (divisor <= INT_MAX)) (PreH9 : (binary_divisor_state_z_79 decimal_pre bits divisor )) (PreH10 : (out <> 0)) (PreH11 : (pos = 0)) (PreH12 : (0 < (bits + 5 ))) (PreH13 : ((bits + 5 ) < INT_MAX)) (PreH14 : (1 < (bits + 5 ))) (PreH15 : (problem_79_pre_z decimal_pre )) (PreH16 : (binary_safe_79 decimal_pre )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  (CharArray.undef_full out (bits + 5 ) )
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition decimal_to_binary_safety_wit_33 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (i: Z) (divisor: Z) (out: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (i = bits)) (PreH7 : (1 <= divisor)) (PreH8 : (divisor <= INT_MAX)) (PreH9 : (binary_divisor_state_z_79 decimal_pre bits divisor )) (PreH10 : (out <> 0)) (PreH11 : (pos = 0)) (PreH12 : (0 < (bits + 5 ))) (PreH13 : ((bits + 5 ) < INT_MAX)) (PreH14 : (1 < (bits + 5 ))) (PreH15 : (problem_79_pre_z decimal_pre )) (PreH16 : (binary_safe_79 decimal_pre )) ,
  (CharArray.undef_seg out (0 + 1 ) (bits + 5 ) )
  **  (((out + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition decimal_to_binary_safety_wit_34 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (i: Z) (divisor: Z) (out: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (i = bits)) (PreH7 : (1 <= divisor)) (PreH8 : (divisor <= INT_MAX)) (PreH9 : (binary_divisor_state_z_79 decimal_pre bits divisor )) (PreH10 : (out <> 0)) (PreH11 : (pos = 0)) (PreH12 : (0 < (bits + 5 ))) (PreH13 : ((bits + 5 ) < INT_MAX)) (PreH14 : (1 < (bits + 5 ))) (PreH15 : (problem_79_pre_z decimal_pre )) (PreH16 : (binary_safe_79 decimal_pre )) ,
  (CharArray.undef_seg out (0 + 1 ) (bits + 5 ) )
  **  (((out + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
|--
  “ (98 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 98) ”
.

Definition decimal_to_binary_safety_wit_35 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (i: Z) (divisor: Z) (out: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (i = bits)) (PreH7 : (1 <= divisor)) (PreH8 : (divisor <= INT_MAX)) (PreH9 : (binary_divisor_state_z_79 decimal_pre bits divisor )) (PreH10 : (out <> 0)) (PreH11 : (pos = 0)) (PreH12 : (0 < (bits + 5 ))) (PreH13 : ((bits + 5 ) < INT_MAX)) (PreH14 : (1 < (bits + 5 ))) (PreH15 : (problem_79_pre_z decimal_pre )) (PreH16 : (binary_safe_79 decimal_pre )) ,
  (CharArray.undef_seg out (1 + 1 ) (bits + 5 ) )
  **  (((out + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((out + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition decimal_to_binary_safety_wit_36 := 
forall (decimal_pre: Z) (out: Z) (out_l: (@list Z)) (pos: Z) (divisor: Z) (i: Z) (bits: Z) (x: Z) (decimal: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (0 < decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (x = 0)) (PreH6 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH7 : (i = bits)) (PreH8 : (0 <= divisor)) (PreH9 : (divisor <= INT_MAX)) (PreH10 : (2 <= pos)) (PreH11 : (pos <= (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH16 : ((Zlength (out_l)) = pos)) ,
  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decimal_to_binary_safety_wit_37 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (divisor: Z) (decimal: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (divisor <= decimal)) (PreH2 : (0 < divisor)) (PreH3 : (0 <= decimal)) (PreH4 : (decimal <= decimal_pre)) (PreH5 : (0 < decimal_pre)) (PreH6 : (decimal_pre <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos < (bits + 5 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH15 : ((Zlength (out_l)) = pos)) ,
  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  “ (49 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 49) ”
.

Definition decimal_to_binary_safety_wit_38 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (divisor: Z) (decimal: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (divisor <= decimal)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH16 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (49) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((decimal - divisor ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (decimal - divisor )) ”
.

Definition decimal_to_binary_safety_wit_39 := 
(
forall (decimal_pre: Z) (out_l: (@list Z)) (divisor: Z) (decimal: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (divisor <= decimal)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH16 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (49) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "decimal" ) )) # Int  |-> (decimal - divisor ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
) \/
(
forall (decimal_pre: Z) (out_l: (@list Z)) (divisor: Z) (decimal: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (divisor <= decimal)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH16 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (49) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "decimal" ) )) # Int  |-> (decimal - divisor ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
).

Definition decimal_to_binary_safety_wit_39_split_goal_1 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (divisor: Z) (decimal: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (divisor <= decimal)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH16 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (49) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "decimal" ) )) # Int  |-> (decimal - divisor ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((pos + 1 ) <= INT_MAX) ”
.

Definition decimal_to_binary_safety_wit_39_split_goal_2 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (divisor: Z) (decimal: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (divisor <= decimal)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH16 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (49) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "decimal" ) )) # Int  |-> (decimal - divisor ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((INT_MIN) <= (pos + 1 )) ”
.

Definition decimal_to_binary_safety_wit_40 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (divisor: Z) (decimal: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (divisor <= decimal)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH16 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (49) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "decimal" ) )) # Int  |-> (decimal - divisor ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition decimal_to_binary_safety_wit_41 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (0 < decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (0 < divisor)) (PreH6 : (divisor <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos <= (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l )) (PreH15 : ((Zlength (out_l)) = pos)) ,
  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  “ ((divisor <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition decimal_to_binary_safety_wit_42 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (0 < decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (0 < divisor)) (PreH6 : (divisor <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos <= (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l )) (PreH15 : ((Zlength (out_l)) = pos)) ,
  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition decimal_to_binary_safety_wit_43 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (decimal < divisor)) (PreH2 : (0 < divisor)) (PreH3 : (0 <= decimal)) (PreH4 : (decimal <= decimal_pre)) (PreH5 : (0 < decimal_pre)) (PreH6 : (decimal_pre <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos < (bits + 5 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH15 : ((Zlength (out_l)) = pos)) ,
  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition decimal_to_binary_safety_wit_44 := 
(
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (decimal < divisor)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH16 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (48) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
) \/
(
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (decimal < divisor)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH16 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (48) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
).

Definition decimal_to_binary_safety_wit_44_split_goal_1 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (decimal < divisor)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH16 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (48) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((pos + 1 ) <= INT_MAX) ”
.

Definition decimal_to_binary_safety_wit_44_split_goal_2 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (decimal < divisor)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH16 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (48) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((INT_MIN) <= (pos + 1 )) ”
.

Definition decimal_to_binary_safety_wit_45 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (decimal < divisor)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH16 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (48) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition decimal_to_binary_safety_wit_46 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (0 < decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (0 < divisor)) (PreH6 : (divisor <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos <= (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l )) (PreH15 : ((Zlength (out_l)) = pos)) ,
  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  “ ((divisor <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition decimal_to_binary_safety_wit_47 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (0 < decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (0 < divisor)) (PreH6 : (divisor <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos <= (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l )) (PreH15 : ((Zlength (out_l)) = pos)) ,
  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition decimal_to_binary_safety_wit_48 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (divisor = 0)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH6 : (i = bits)) (PreH7 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH8 : (pos = (bits + 2 ))) (PreH9 : (problem_79_pre_z decimal_pre )) (PreH10 : (binary_safe_79 decimal_pre )) (PreH11 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH12 : ((Zlength (out_l)) = pos)) ,
  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition decimal_to_binary_safety_wit_49 := 
(
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (0 <= decimal)) (PreH3 : (decimal <= decimal_pre)) (PreH4 : (divisor = 0)) (PreH5 : (x = 0)) (PreH6 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH7 : (i = bits)) (PreH8 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH9 : (pos = (bits + 2 ))) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH13 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (100) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
) \/
(
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (0 <= decimal)) (PreH3 : (decimal <= decimal_pre)) (PreH4 : (divisor = 0)) (PreH5 : (x = 0)) (PreH6 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH7 : (i = bits)) (PreH8 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH9 : (pos = (bits + 2 ))) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH13 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (100) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
).

Definition decimal_to_binary_safety_wit_49_split_goal_1 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (0 <= decimal)) (PreH3 : (decimal <= decimal_pre)) (PreH4 : (divisor = 0)) (PreH5 : (x = 0)) (PreH6 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH7 : (i = bits)) (PreH8 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH9 : (pos = (bits + 2 ))) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH13 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (100) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((pos + 1 ) <= INT_MAX) ”
.

Definition decimal_to_binary_safety_wit_49_split_goal_2 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (0 <= decimal)) (PreH3 : (decimal <= decimal_pre)) (PreH4 : (divisor = 0)) (PreH5 : (x = 0)) (PreH6 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH7 : (i = bits)) (PreH8 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH9 : (pos = (bits + 2 ))) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH13 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (100) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((INT_MIN) <= (pos + 1 )) ”
.

Definition decimal_to_binary_safety_wit_50 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (0 <= decimal)) (PreH3 : (decimal <= decimal_pre)) (PreH4 : (divisor = 0)) (PreH5 : (x = 0)) (PreH6 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH7 : (i = bits)) (PreH8 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH9 : (pos = (bits + 2 ))) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH13 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (100) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition decimal_to_binary_safety_wit_51 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (0 <= decimal)) (PreH3 : (decimal <= decimal_pre)) (PreH4 : (divisor = 0)) (PreH5 : (x = 0)) (PreH6 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH7 : (i = bits)) (PreH8 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH9 : (pos = (bits + 2 ))) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH13 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (100) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> (pos + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (98 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 98) ”
.

Definition decimal_to_binary_safety_wit_52 := 
(
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= (pos + 1 ))) (PreH2 : (0 <= pos)) (PreH3 : (0 <= decimal)) (PreH4 : (decimal <= decimal_pre)) (PreH5 : (divisor = 0)) (PreH6 : (x = 0)) (PreH7 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH8 : (i = bits)) (PreH9 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH10 : (pos = (bits + 2 ))) (PreH11 : (problem_79_pre_z decimal_pre )) (PreH12 : (binary_safe_79 decimal_pre )) (PreH13 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH14 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out ((pos + 1 ) + 1 ) (app ((app (out_l) ((cons (100) ((@nil Z)))))) ((cons (98) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((pos + 1 ) + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> (pos + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (((pos + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((pos + 1 ) + 1 )) ”
) \/
(
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= (pos + 1 ))) (PreH2 : (0 <= pos)) (PreH3 : (0 <= decimal)) (PreH4 : (decimal <= decimal_pre)) (PreH5 : (divisor = 0)) (PreH6 : (x = 0)) (PreH7 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH8 : (i = bits)) (PreH9 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH10 : (pos = (bits + 2 ))) (PreH11 : (problem_79_pre_z decimal_pre )) (PreH12 : (binary_safe_79 decimal_pre )) (PreH13 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH14 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out ((pos + 1 ) + 1 ) (app ((app (out_l) ((cons (100) ((@nil Z)))))) ((cons (98) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((pos + 1 ) + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> (pos + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (((pos + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((pos + 1 ) + 1 )) ”
).

Definition decimal_to_binary_safety_wit_52_split_goal_1 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= (pos + 1 ))) (PreH2 : (0 <= pos)) (PreH3 : (0 <= decimal)) (PreH4 : (decimal <= decimal_pre)) (PreH5 : (divisor = 0)) (PreH6 : (x = 0)) (PreH7 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH8 : (i = bits)) (PreH9 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH10 : (pos = (bits + 2 ))) (PreH11 : (problem_79_pre_z decimal_pre )) (PreH12 : (binary_safe_79 decimal_pre )) (PreH13 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH14 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out ((pos + 1 ) + 1 ) (app ((app (out_l) ((cons (100) ((@nil Z)))))) ((cons (98) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((pos + 1 ) + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> (pos + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (((pos + 1 ) + 1 ) <= INT_MAX) ”
.

Definition decimal_to_binary_safety_wit_52_split_goal_2 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= (pos + 1 ))) (PreH2 : (0 <= pos)) (PreH3 : (0 <= decimal)) (PreH4 : (decimal <= decimal_pre)) (PreH5 : (divisor = 0)) (PreH6 : (x = 0)) (PreH7 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH8 : (i = bits)) (PreH9 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH10 : (pos = (bits + 2 ))) (PreH11 : (problem_79_pre_z decimal_pre )) (PreH12 : (binary_safe_79 decimal_pre )) (PreH13 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH14 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out ((pos + 1 ) + 1 ) (app ((app (out_l) ((cons (100) ((@nil Z)))))) ((cons (98) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((pos + 1 ) + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> (pos + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((INT_MIN) <= ((pos + 1 ) + 1 )) ”
.

Definition decimal_to_binary_safety_wit_53 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= (pos + 1 ))) (PreH2 : (0 <= pos)) (PreH3 : (0 <= decimal)) (PreH4 : (decimal <= decimal_pre)) (PreH5 : (divisor = 0)) (PreH6 : (x = 0)) (PreH7 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH8 : (i = bits)) (PreH9 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH10 : (pos = (bits + 2 ))) (PreH11 : (problem_79_pre_z decimal_pre )) (PreH12 : (binary_safe_79 decimal_pre )) (PreH13 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH14 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out ((pos + 1 ) + 1 ) (app ((app (out_l) ((cons (100) ((@nil Z)))))) ((cons (98) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((pos + 1 ) + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> (pos + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition decimal_to_binary_safety_wit_54 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= (pos + 1 ))) (PreH2 : (0 <= pos)) (PreH3 : (0 <= decimal)) (PreH4 : (decimal <= decimal_pre)) (PreH5 : (divisor = 0)) (PreH6 : (x = 0)) (PreH7 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH8 : (i = bits)) (PreH9 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH10 : (pos = (bits + 2 ))) (PreH11 : (problem_79_pre_z decimal_pre )) (PreH12 : (binary_safe_79 decimal_pre )) (PreH13 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH14 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out ((pos + 1 ) + 1 ) (app ((app (out_l) ((cons (100) ((@nil Z)))))) ((cons (98) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((pos + 1 ) + 1 ) (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pos" ) )) # Int  |-> ((pos + 1 ) + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decimal_to_binary_entail_wit_1 := 
(
forall (decimal_pre: Z) (PreH1 : (decimal_pre <> 0)) (PreH2 : (0 <= decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (problem_79_pre_z decimal_pre )) (PreH5 : (binary_safe_79 decimal_pre )) (PreH6 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (0 <= decimal_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ (1 = 1) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ” 
  &&  “ (binary_count_state_z_79 decimal_pre decimal_pre 0 ) ”
  &&  emp
) \/
(
forall (decimal_pre: Z) (PreH1 : (decimal_pre <> 0)) (PreH2 : (0 <= decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (problem_79_pre_z decimal_pre )) (PreH5 : (binary_safe_79 decimal_pre )) (PreH6 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (binary_count_state_z_79 decimal_pre decimal_pre 0 ) ”
  &&  emp
).

Definition decimal_to_binary_entail_wit_1_split_goal_1 := 
forall (decimal_pre: Z) (PreH1 : (decimal_pre <> 0)) (PreH2 : (0 <= decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (problem_79_pre_z decimal_pre )) (PreH5 : (binary_safe_79 decimal_pre )) (PreH6 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (binary_count_state_z_79 decimal_pre decimal_pre 0 ) ”
.

Definition decimal_to_binary_entail_wit_2 := 
(
forall (decimal_pre: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (divisor = 1)) (PreH9 : (i = 1)) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH13 : (binary_count_state_z_79 decimal_pre x bits )) ,
  TT && emp 
|--
  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (0 <= (x ÷ 2 )) ” 
  &&  “ (0 <= (bits + 1 )) ” 
  &&  “ (out = 0) ” 
  &&  “ (pos = 0) ” 
  &&  “ (divisor = 1) ” 
  &&  “ (i = 1) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ” 
  &&  “ (binary_count_state_z_79 decimal_pre (x ÷ 2 ) (bits + 1 ) ) ”
  &&  emp
) \/
(
forall (decimal_pre: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (divisor = 1)) (PreH9 : (i = 1)) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH13 : (binary_count_state_z_79 decimal_pre x bits )) ,
  TT && emp 
|--
  “ (binary_count_state_z_79 decimal_pre (x ÷ 2 ) (bits + 1 ) ) ” 
  &&  “ (0 <= (x ÷ 2 )) ”
  &&  emp
).

Definition decimal_to_binary_entail_wit_2_split_goal_1 := 
forall (decimal_pre: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (divisor = 1)) (PreH9 : (i = 1)) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH13 : (binary_count_state_z_79 decimal_pre x bits )) ,
  TT && emp 
|--
  “ (binary_count_state_z_79 decimal_pre (x ÷ 2 ) (bits + 1 ) ) ”
.

Definition decimal_to_binary_entail_wit_2_split_goal_2 := 
forall (decimal_pre: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x > 0)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (divisor = 1)) (PreH9 : (i = 1)) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH13 : (binary_count_state_z_79 decimal_pre x bits )) ,
  TT && emp 
|--
  “ (0 <= (x ÷ 2 )) ”
.

Definition decimal_to_binary_entail_wit_3 := 
(
forall (decimal_pre: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x <= 0)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (divisor = 1)) (PreH9 : (i = 1)) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH13 : (binary_count_state_z_79 decimal_pre x bits )) ,
  TT && emp 
|--
  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (out = 0) ” 
  &&  “ (pos = 0) ” 
  &&  “ (divisor = 1) ” 
  &&  “ (i = 1) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ”
  &&  emp
) \/
(
forall (decimal_pre: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x <= 0)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (divisor = 1)) (PreH9 : (i = 1)) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH13 : (binary_count_state_z_79 decimal_pre x bits )) ,
  TT && emp 
|--
  “ (bits = (binary_length_z_79 (decimal_pre))) ”
  &&  emp
).

Definition decimal_to_binary_entail_wit_3_split_goal_1 := 
forall (decimal_pre: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (x <= 0)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (0 <= x)) (PreH5 : (0 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (divisor = 1)) (PreH9 : (i = 1)) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH13 : (binary_count_state_z_79 decimal_pre x bits )) ,
  TT && emp 
|--
  “ (bits = (binary_length_z_79 (decimal_pre))) ”
.

Definition decimal_to_binary_entail_wit_4 := 
(
forall (decimal_pre: Z) (x: Z) (bits: Z) (out: Z) (pos: Z) (divisor: Z) (i: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (out = 0)) (PreH6 : (pos = 0)) (PreH7 : (divisor = 1)) (PreH8 : (i = 1)) (PreH9 : (problem_79_pre_z decimal_pre )) (PreH10 : (binary_safe_79 decimal_pre )) (PreH11 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (out = 0) ” 
  &&  “ (pos = 0) ” 
  &&  “ (divisor = 1) ” 
  &&  “ (i = 1) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ” 
  &&  “ (binary_divisor_state_z_79 decimal_pre i divisor ) ”
  &&  emp
) \/
(
forall (decimal_pre: Z) (x: Z) (bits: Z) (out: Z) (pos: Z) (divisor: Z) (i: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (out = 0)) (PreH6 : (pos = 0)) (PreH7 : (divisor = 1)) (PreH8 : (i = 1)) (PreH9 : (problem_79_pre_z decimal_pre )) (PreH10 : (binary_safe_79 decimal_pre )) (PreH11 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (binary_divisor_state_z_79 decimal_pre i divisor ) ” 
  &&  “ (1 <= bits) ”
  &&  emp
).

Definition decimal_to_binary_entail_wit_4_split_goal_1 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (out: Z) (pos: Z) (divisor: Z) (i: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (out = 0)) (PreH6 : (pos = 0)) (PreH7 : (divisor = 1)) (PreH8 : (i = 1)) (PreH9 : (problem_79_pre_z decimal_pre )) (PreH10 : (binary_safe_79 decimal_pre )) (PreH11 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (binary_divisor_state_z_79 decimal_pre i divisor ) ”
.

Definition decimal_to_binary_entail_wit_4_split_goal_2 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (out: Z) (pos: Z) (divisor: Z) (i: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (out = 0)) (PreH6 : (pos = 0)) (PreH7 : (divisor = 1)) (PreH8 : (i = 1)) (PreH9 : (problem_79_pre_z decimal_pre )) (PreH10 : (binary_safe_79 decimal_pre )) (PreH11 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (1 <= bits) ”
.

Definition decimal_to_binary_entail_wit_5 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (out: Z) (pos: Z) (divisor: Z) (i: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (divisor = 1)) (PreH9 : (i = 1)) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH13 : (binary_divisor_state_z_79 decimal_pre i divisor )) ,
  TT && emp 
|--
  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (out = 0) ” 
  &&  “ (pos = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= bits) ” 
  &&  “ (1 <= divisor) ” 
  &&  “ (divisor <= INT_MAX) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ” 
  &&  “ (binary_divisor_state_z_79 decimal_pre i divisor ) ”
  &&  emp
.

Definition decimal_to_binary_entail_wit_6 := 
(
forall (decimal_pre: Z) (divisor: Z) (i: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (i < bits)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (pos = 0)) (PreH9 : (1 <= i)) (PreH10 : (i <= bits)) (PreH11 : (1 <= divisor)) (PreH12 : (divisor <= INT_MAX)) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_divisor_state_z_79 decimal_pre i divisor )) ,
  TT && emp 
|--
  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (out = 0) ” 
  &&  “ (pos = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < bits) ” 
  &&  “ (1 <= divisor) ” 
  &&  “ (divisor <= INT_MAX) ” 
  &&  “ ((divisor * 2 ) <= INT_MAX) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ” 
  &&  “ (binary_divisor_state_z_79 decimal_pre i divisor ) ”
  &&  emp
) \/
(
forall (decimal_pre: Z) (divisor: Z) (i: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (i < bits)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (pos = 0)) (PreH9 : (1 <= i)) (PreH10 : (i <= bits)) (PreH11 : (1 <= divisor)) (PreH12 : (divisor <= INT_MAX)) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_divisor_state_z_79 decimal_pre i divisor )) ,
  TT && emp 
|--
  “ ((divisor * 2 ) <= INT_MAX) ”
  &&  emp
).

Definition decimal_to_binary_entail_wit_6_split_goal_1 := 
forall (decimal_pre: Z) (divisor: Z) (i: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (i < bits)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (pos = 0)) (PreH9 : (1 <= i)) (PreH10 : (i <= bits)) (PreH11 : (1 <= divisor)) (PreH12 : (divisor <= INT_MAX)) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_divisor_state_z_79 decimal_pre i divisor )) ,
  TT && emp 
|--
  “ ((divisor * 2 ) <= INT_MAX) ”
.

Definition decimal_to_binary_entail_wit_7 := 
(
forall (decimal_pre: Z) (x: Z) (bits: Z) (out: Z) (pos: Z) (i: Z) (divisor: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (1 <= i)) (PreH9 : (i < bits)) (PreH10 : (1 <= divisor)) (PreH11 : (divisor <= INT_MAX)) (PreH12 : ((divisor * 2 ) <= INT_MAX)) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_divisor_state_z_79 decimal_pre i divisor )) ,
  TT && emp 
|--
  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (out = 0) ” 
  &&  “ (pos = 0) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= bits) ” 
  &&  “ (1 <= (divisor * 2 )) ” 
  &&  “ ((divisor * 2 ) <= INT_MAX) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ” 
  &&  “ (binary_divisor_state_z_79 decimal_pre (i + 1 ) (divisor * 2 ) ) ”
  &&  emp
) \/
(
forall (decimal_pre: Z) (x: Z) (bits: Z) (out: Z) (pos: Z) (i: Z) (divisor: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (1 <= i)) (PreH9 : (i < bits)) (PreH10 : (1 <= divisor)) (PreH11 : (divisor <= INT_MAX)) (PreH12 : ((divisor * 2 ) <= INT_MAX)) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_divisor_state_z_79 decimal_pre i divisor )) ,
  TT && emp 
|--
  “ (binary_divisor_state_z_79 decimal_pre (i + 1 ) (divisor * 2 ) ) ”
  &&  emp
).

Definition decimal_to_binary_entail_wit_7_split_goal_1 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (out: Z) (pos: Z) (i: Z) (divisor: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (out = 0)) (PreH7 : (pos = 0)) (PreH8 : (1 <= i)) (PreH9 : (i < bits)) (PreH10 : (1 <= divisor)) (PreH11 : (divisor <= INT_MAX)) (PreH12 : ((divisor * 2 ) <= INT_MAX)) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_divisor_state_z_79 decimal_pre i divisor )) ,
  TT && emp 
|--
  “ (binary_divisor_state_z_79 decimal_pre (i + 1 ) (divisor * 2 ) ) ”
.

Definition decimal_to_binary_entail_wit_8 := 
(
forall (decimal_pre: Z) (divisor: Z) (i: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (i >= bits)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (pos = 0)) (PreH9 : (1 <= i)) (PreH10 : (i <= bits)) (PreH11 : (1 <= divisor)) (PreH12 : (divisor <= INT_MAX)) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_divisor_state_z_79 decimal_pre i divisor )) ,
  TT && emp 
|--
  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (1 <= divisor) ” 
  &&  “ (divisor <= INT_MAX) ” 
  &&  “ (out = 0) ” 
  &&  “ (pos = 0) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ” 
  &&  “ (binary_divisor_state_z_79 decimal_pre bits divisor ) ”
  &&  emp
) \/
(
forall (decimal_pre: Z) (divisor: Z) (i: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (i >= bits)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (pos = 0)) (PreH9 : (1 <= i)) (PreH10 : (i <= bits)) (PreH11 : (1 <= divisor)) (PreH12 : (divisor <= INT_MAX)) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_divisor_state_z_79 decimal_pre i divisor )) ,
  TT && emp 
|--
  “ (binary_divisor_state_z_79 decimal_pre bits divisor ) ”
  &&  emp
).

Definition decimal_to_binary_entail_wit_8_split_goal_1 := 
forall (decimal_pre: Z) (divisor: Z) (i: Z) (pos: Z) (out: Z) (bits: Z) (x: Z) (PreH1 : (i >= bits)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH6 : (1 <= bits)) (PreH7 : (out = 0)) (PreH8 : (pos = 0)) (PreH9 : (1 <= i)) (PreH10 : (i <= bits)) (PreH11 : (1 <= divisor)) (PreH12 : (divisor <= INT_MAX)) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_divisor_state_z_79 decimal_pre i divisor )) ,
  TT && emp 
|--
  “ (binary_divisor_state_z_79 decimal_pre bits divisor ) ”
.

Definition decimal_to_binary_entail_wit_9 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (i: Z) (divisor: Z) (out: Z) (pos: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 < decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH6 : (i = bits)) (PreH7 : (1 <= bits)) (PreH8 : (1 <= divisor)) (PreH9 : (divisor <= INT_MAX)) (PreH10 : (out = 0)) (PreH11 : (pos = 0)) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH15 : (binary_divisor_state_z_79 decimal_pre bits divisor )) ,
  (CharArray.undef_full retval (bits + 5 ) )
|--
  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (i = bits) ” 
  &&  “ (1 <= divisor) ” 
  &&  “ (divisor <= INT_MAX) ” 
  &&  “ (binary_divisor_state_z_79 decimal_pre bits divisor ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (pos = 0) ” 
  &&  “ (0 < (bits + 5 )) ” 
  &&  “ ((bits + 5 ) < INT_MAX) ” 
  &&  “ (1 < (bits + 5 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ”
  &&  (CharArray.undef_full retval (bits + 5 ) )
.

Definition decimal_to_binary_entail_wit_10 := 
(
forall (decimal_pre: Z) (x: Z) (bits: Z) (i: Z) (divisor: Z) (out: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (i = bits)) (PreH7 : (1 <= divisor)) (PreH8 : (divisor <= INT_MAX)) (PreH9 : (binary_divisor_state_z_79 decimal_pre bits divisor )) (PreH10 : (out <> 0)) (PreH11 : (pos = 0)) (PreH12 : (0 < (bits + 5 ))) (PreH13 : ((bits + 5 ) < INT_MAX)) (PreH14 : (1 < (bits + 5 ))) (PreH15 : (problem_79_pre_z decimal_pre )) (PreH16 : (binary_safe_79 decimal_pre )) ,
  (CharArray.undef_seg out (1 + 1 ) (bits + 5 ) )
  **  (((out + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((out + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  EX (out_l: (@list Z)) ,
  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (1 <= divisor) ” 
  &&  “ (divisor <= INT_MAX) ” 
  &&  “ (2 = 2) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal_pre divisor 2 out_l ) ” 
  &&  “ ((Zlength (out_l)) = 2) ”
  &&  (CharArray.full out 2 out_l )
  **  (CharArray.undef_seg out 2 (bits + 5 ) )
) \/
(
forall (decimal_pre: Z) (x: Z) (bits: Z) (i: Z) (divisor: Z) (out: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (i = bits)) (PreH7 : (1 <= divisor)) (PreH8 : (divisor <= INT_MAX)) (PreH9 : (binary_divisor_state_z_79 decimal_pre bits divisor )) (PreH10 : (out <> 0)) (PreH11 : (pos = 0)) (PreH12 : (0 < (bits + 5 ))) (PreH13 : ((bits + 5 ) < INT_MAX)) (PreH14 : (1 < (bits + 5 ))) (PreH15 : (problem_79_pre_z decimal_pre )) (PreH16 : (binary_safe_79 decimal_pre )) ,
  (((out + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((out + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  EX (out_l: (@list Z)) ,
  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (1 <= divisor) ” 
  &&  “ (divisor <= INT_MAX) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal_pre divisor 2 out_l ) ” 
  &&  “ ((Zlength (out_l)) = 2) ”
  &&  (CharArray.full out 2 out_l )
).

Definition decimal_to_binary_entail_wit_11 := 
(
forall (decimal_pre: Z) (out_l_2: (@list Z)) (x: Z) (bits: Z) (i: Z) (divisor: Z) (pos: Z) (out: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (i = bits)) (PreH6 : (1 <= divisor)) (PreH7 : (divisor <= INT_MAX)) (PreH8 : (pos = 2)) (PreH9 : (problem_79_pre_z decimal_pre )) (PreH10 : (binary_safe_79 decimal_pre )) (PreH11 : (binary_write_state_z_79 decimal_pre decimal_pre divisor pos out_l_2 )) (PreH12 : ((Zlength (out_l_2)) = pos)) ,
  (CharArray.full out pos out_l_2 )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= decimal_pre) ” 
  &&  “ (decimal_pre <= decimal_pre) ” 
  &&  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (0 <= divisor) ” 
  &&  “ (divisor <= INT_MAX) ” 
  &&  “ (2 <= pos) ” 
  &&  “ (pos <= (bits + 2 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal_pre divisor pos out_l ) ” 
  &&  “ ((Zlength (out_l)) = pos) ”
  &&  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
) \/
(
forall (decimal_pre: Z) (out_l_2: (@list Z)) (x: Z) (bits: Z) (i: Z) (divisor: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (i = bits)) (PreH6 : (1 <= divisor)) (PreH7 : (divisor <= INT_MAX)) (PreH8 : (pos = 2)) (PreH9 : (problem_79_pre_z decimal_pre )) (PreH10 : (binary_safe_79 decimal_pre )) (PreH11 : (binary_write_state_z_79 decimal_pre decimal_pre divisor pos out_l_2 )) (PreH12 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ” 
  &&  “ (pos <= (bits + 2 )) ”
  &&  emp
).

Definition decimal_to_binary_entail_wit_11_split_goal_1 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (x: Z) (bits: Z) (i: Z) (divisor: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (i = bits)) (PreH6 : (1 <= divisor)) (PreH7 : (divisor <= INT_MAX)) (PreH8 : (pos = 2)) (PreH9 : (problem_79_pre_z decimal_pre )) (PreH10 : (binary_safe_79 decimal_pre )) (PreH11 : (binary_write_state_z_79 decimal_pre decimal_pre divisor pos out_l_2 )) (PreH12 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ”
.

Definition decimal_to_binary_entail_wit_11_split_goal_2 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (x: Z) (bits: Z) (i: Z) (divisor: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (i = bits)) (PreH6 : (1 <= divisor)) (PreH7 : (divisor <= INT_MAX)) (PreH8 : (pos = 2)) (PreH9 : (problem_79_pre_z decimal_pre )) (PreH10 : (binary_safe_79 decimal_pre )) (PreH11 : (binary_write_state_z_79 decimal_pre decimal_pre divisor pos out_l_2 )) (PreH12 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ (pos <= (bits + 2 )) ”
.

Definition decimal_to_binary_entail_wit_12 := 
forall (decimal_pre: Z) (out: Z) (out_l_2: (@list Z)) (pos: Z) (divisor: Z) (i: Z) (bits: Z) (x: Z) (decimal: Z) (PreH1 : (decimal >= divisor)) (PreH2 : (divisor > 0)) (PreH3 : (0 <= decimal)) (PreH4 : (decimal <= decimal_pre)) (PreH5 : (0 < decimal_pre)) (PreH6 : (decimal_pre <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (0 <= divisor)) (PreH11 : (divisor <= INT_MAX)) (PreH12 : (2 <= pos)) (PreH13 : (pos <= (bits + 2 ))) (PreH14 : (problem_79_pre_z decimal_pre )) (PreH15 : (binary_safe_79 decimal_pre )) (PreH16 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH17 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH18 : ((Zlength (out_l_2)) = pos)) ,
  (CharArray.full out pos out_l_2 )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (divisor <= decimal) ” 
  &&  “ (0 < divisor) ” 
  &&  “ (0 <= decimal) ” 
  &&  “ (decimal <= decimal_pre) ” 
  &&  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (2 <= pos) ” 
  &&  “ (pos < (bits + 5 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal divisor pos out_l ) ” 
  &&  “ ((Zlength (out_l)) = pos) ”
  &&  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
.

Definition decimal_to_binary_entail_wit_13 := 
(
forall (decimal_pre: Z) (out_l_2: (@list Z)) (divisor: Z) (decimal: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (divisor <= decimal)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l_2) ((cons (49) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= (decimal - divisor )) ” 
  &&  “ ((decimal - divisor ) <= decimal_pre) ” 
  &&  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (0 < divisor) ” 
  &&  “ (divisor <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (2 <= (pos + 1 )) ” 
  &&  “ ((pos + 1 ) <= (bits + 2 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (binary_write_state_z_79 decimal_pre (decimal - divisor ) (divisor ÷ 2 ) (pos + 1 ) out_l ) ” 
  &&  “ ((Zlength (out_l)) = (pos + 1 )) ”
  &&  (CharArray.full out (pos + 1 ) out_l )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
) \/
(
forall (decimal_pre: Z) (out_l_2: (@list Z)) (divisor: Z) (decimal: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= pos)) (PreH2 : (divisor <= decimal)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ ((Zlength ((app (out_l_2) ((cons (49) ((@nil Z))))))) = (pos + 1 )) ” 
  &&  “ (binary_write_state_z_79 decimal_pre (decimal - divisor ) (divisor ÷ 2 ) (pos + 1 ) (app (out_l_2) ((cons (49) ((@nil Z))))) ) ” 
  &&  “ ((pos + 1 ) <= (bits + 2 )) ”
  &&  emp
).

Definition decimal_to_binary_entail_wit_13_split_goal_1 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (divisor: Z) (decimal: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= pos)) (PreH2 : (divisor <= decimal)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ ((Zlength ((app (out_l_2) ((cons (49) ((@nil Z))))))) = (pos + 1 )) ”
.

Definition decimal_to_binary_entail_wit_13_split_goal_2 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (divisor: Z) (decimal: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= pos)) (PreH2 : (divisor <= decimal)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ (binary_write_state_z_79 decimal_pre (decimal - divisor ) (divisor ÷ 2 ) (pos + 1 ) (app (out_l_2) ((cons (49) ((@nil Z))))) ) ”
.

Definition decimal_to_binary_entail_wit_13_split_goal_3 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (divisor: Z) (decimal: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= pos)) (PreH2 : (divisor <= decimal)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ ((pos + 1 ) <= (bits + 2 )) ”
.

Definition decimal_to_binary_entail_wit_14 := 
forall (decimal_pre: Z) (out: Z) (out_l_2: (@list Z)) (pos: Z) (divisor: Z) (i: Z) (bits: Z) (x: Z) (decimal: Z) (PreH1 : (decimal < divisor)) (PreH2 : (divisor > 0)) (PreH3 : (0 <= decimal)) (PreH4 : (decimal <= decimal_pre)) (PreH5 : (0 < decimal_pre)) (PreH6 : (decimal_pre <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (0 <= divisor)) (PreH11 : (divisor <= INT_MAX)) (PreH12 : (2 <= pos)) (PreH13 : (pos <= (bits + 2 ))) (PreH14 : (problem_79_pre_z decimal_pre )) (PreH15 : (binary_safe_79 decimal_pre )) (PreH16 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH17 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH18 : ((Zlength (out_l_2)) = pos)) ,
  (CharArray.full out pos out_l_2 )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (decimal < divisor) ” 
  &&  “ (0 < divisor) ” 
  &&  “ (0 <= decimal) ” 
  &&  “ (decimal <= decimal_pre) ” 
  &&  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (2 <= pos) ” 
  &&  “ (pos < (bits + 5 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal divisor pos out_l ) ” 
  &&  “ ((Zlength (out_l)) = pos) ”
  &&  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
.

Definition decimal_to_binary_entail_wit_15 := 
(
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (decimal < divisor)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l_2) ((cons (48) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= decimal) ” 
  &&  “ (decimal <= decimal_pre) ” 
  &&  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (0 < divisor) ” 
  &&  “ (divisor <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (2 <= (pos + 1 )) ” 
  &&  “ ((pos + 1 ) <= (bits + 2 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) (pos + 1 ) out_l ) ” 
  &&  “ ((Zlength (out_l)) = (pos + 1 )) ”
  &&  (CharArray.full out (pos + 1 ) out_l )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
) \/
(
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= pos)) (PreH2 : (decimal < divisor)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ ((Zlength ((app (out_l_2) ((cons (48) ((@nil Z))))))) = (pos + 1 )) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) (pos + 1 ) (app (out_l_2) ((cons (48) ((@nil Z))))) ) ” 
  &&  “ ((pos + 1 ) <= (bits + 2 )) ” 
  &&  “ (divisor <= INT_MAX) ”
  &&  emp
).

Definition decimal_to_binary_entail_wit_15_split_goal_1 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= pos)) (PreH2 : (decimal < divisor)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ ((Zlength ((app (out_l_2) ((cons (48) ((@nil Z))))))) = (pos + 1 )) ”
.

Definition decimal_to_binary_entail_wit_15_split_goal_2 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= pos)) (PreH2 : (decimal < divisor)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) (pos + 1 ) (app (out_l_2) ((cons (48) ((@nil Z))))) ) ”
.

Definition decimal_to_binary_entail_wit_15_split_goal_3 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= pos)) (PreH2 : (decimal < divisor)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ ((pos + 1 ) <= (bits + 2 )) ”
.

Definition decimal_to_binary_entail_wit_15_split_goal_4 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= pos)) (PreH2 : (decimal < divisor)) (PreH3 : (0 < divisor)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (0 < decimal_pre)) (PreH7 : (decimal_pre <= INT_MAX)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (2 <= pos)) (PreH12 : (pos < (bits + 5 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ (divisor <= INT_MAX) ”
.

Definition decimal_to_binary_entail_wit_16_1 := 
(
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (0 < decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (0 < divisor)) (PreH6 : (divisor <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos <= (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = pos)) ,
  (CharArray.full out pos out_l_2 )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= decimal) ” 
  &&  “ (decimal <= decimal_pre) ” 
  &&  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (0 <= (divisor ÷ 2 )) ” 
  &&  “ ((divisor ÷ 2 ) <= INT_MAX) ” 
  &&  “ (2 <= pos) ” 
  &&  “ (pos <= (bits + 2 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l ) ” 
  &&  “ ((Zlength (out_l)) = pos) ”
  &&  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
) \/
(
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (0 < decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (0 < divisor)) (PreH6 : (divisor <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos <= (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ” 
  &&  “ ((divisor ÷ 2 ) <= INT_MAX) ” 
  &&  “ (0 <= (divisor ÷ 2 )) ”
  &&  emp
).

Definition decimal_to_binary_entail_wit_16_1_split_goal_1 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (0 < decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (0 < divisor)) (PreH6 : (divisor <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos <= (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ”
.

Definition decimal_to_binary_entail_wit_16_1_split_goal_2 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (0 < decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (0 < divisor)) (PreH6 : (divisor <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos <= (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ ((divisor ÷ 2 ) <= INT_MAX) ”
.

Definition decimal_to_binary_entail_wit_16_1_split_goal_3 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (0 < decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (0 < divisor)) (PreH6 : (divisor <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos <= (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ (0 <= (divisor ÷ 2 )) ”
.

Definition decimal_to_binary_entail_wit_16_2 := 
(
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (0 < decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (0 < divisor)) (PreH6 : (divisor <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos <= (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = pos)) ,
  (CharArray.full out pos out_l_2 )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= decimal) ” 
  &&  “ (decimal <= decimal_pre) ” 
  &&  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (0 <= (divisor ÷ 2 )) ” 
  &&  “ ((divisor ÷ 2 ) <= INT_MAX) ” 
  &&  “ (2 <= pos) ” 
  &&  “ (pos <= (bits + 2 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l ) ” 
  &&  “ ((Zlength (out_l)) = pos) ”
  &&  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
) \/
(
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (0 < decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (0 < divisor)) (PreH6 : (divisor <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos <= (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ” 
  &&  “ ((divisor ÷ 2 ) <= INT_MAX) ” 
  &&  “ (0 <= (divisor ÷ 2 )) ”
  &&  emp
).

Definition decimal_to_binary_entail_wit_16_2_split_goal_1 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (0 < decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (0 < divisor)) (PreH6 : (divisor <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos <= (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ”
.

Definition decimal_to_binary_entail_wit_16_2_split_goal_2 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (0 < decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (0 < divisor)) (PreH6 : (divisor <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos <= (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ ((divisor ÷ 2 ) <= INT_MAX) ”
.

Definition decimal_to_binary_entail_wit_16_2_split_goal_3 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (0 < decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (0 < divisor)) (PreH6 : (divisor <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos <= (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal (divisor ÷ 2 ) pos out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ (0 <= (divisor ÷ 2 )) ”
.

Definition decimal_to_binary_entail_wit_17 := 
(
forall (decimal_pre: Z) (out: Z) (out_l_2: (@list Z)) (pos: Z) (divisor: Z) (i: Z) (bits: Z) (x: Z) (decimal: Z) (PreH1 : (divisor <= 0)) (PreH2 : (0 <= decimal)) (PreH3 : (decimal <= decimal_pre)) (PreH4 : (0 < decimal_pre)) (PreH5 : (decimal_pre <= INT_MAX)) (PreH6 : (x = 0)) (PreH7 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH8 : (i = bits)) (PreH9 : (0 <= divisor)) (PreH10 : (divisor <= INT_MAX)) (PreH11 : (2 <= pos)) (PreH12 : (pos <= (bits + 2 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH17 : ((Zlength (out_l_2)) = pos)) ,
  (CharArray.full out pos out_l_2 )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= decimal) ” 
  &&  “ (decimal <= decimal_pre) ” 
  &&  “ (divisor = 0) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre))))) ” 
  &&  “ (pos = (bits + 2 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal divisor pos out_l ) ” 
  &&  “ ((Zlength (out_l)) = pos) ”
  &&  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
) \/
(
forall (decimal_pre: Z) (out_l_2: (@list Z)) (pos: Z) (divisor: Z) (i: Z) (bits: Z) (x: Z) (decimal: Z) (PreH1 : (divisor <= 0)) (PreH2 : (0 <= decimal)) (PreH3 : (decimal <= decimal_pre)) (PreH4 : (0 < decimal_pre)) (PreH5 : (decimal_pre <= INT_MAX)) (PreH6 : (x = 0)) (PreH7 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH8 : (i = bits)) (PreH9 : (0 <= divisor)) (PreH10 : (divisor <= INT_MAX)) (PreH11 : (2 <= pos)) (PreH12 : (pos <= (bits + 2 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH17 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ ((Zlength ((app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) = pos) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal divisor pos (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))) ) ” 
  &&  “ (pos = (bits + 2 )) ” 
  &&  “ (out_l_2 = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre))))) ”
  &&  emp
).

Definition decimal_to_binary_entail_wit_17_split_goal_1 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (pos: Z) (divisor: Z) (i: Z) (bits: Z) (x: Z) (decimal: Z) (PreH1 : (divisor <= 0)) (PreH2 : (0 <= decimal)) (PreH3 : (decimal <= decimal_pre)) (PreH4 : (0 < decimal_pre)) (PreH5 : (decimal_pre <= INT_MAX)) (PreH6 : (x = 0)) (PreH7 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH8 : (i = bits)) (PreH9 : (0 <= divisor)) (PreH10 : (divisor <= INT_MAX)) (PreH11 : (2 <= pos)) (PreH12 : (pos <= (bits + 2 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH17 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ ((Zlength ((app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) = pos) ”
.

Definition decimal_to_binary_entail_wit_17_split_goal_2 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (pos: Z) (divisor: Z) (i: Z) (bits: Z) (x: Z) (decimal: Z) (PreH1 : (divisor <= 0)) (PreH2 : (0 <= decimal)) (PreH3 : (decimal <= decimal_pre)) (PreH4 : (0 < decimal_pre)) (PreH5 : (decimal_pre <= INT_MAX)) (PreH6 : (x = 0)) (PreH7 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH8 : (i = bits)) (PreH9 : (0 <= divisor)) (PreH10 : (divisor <= INT_MAX)) (PreH11 : (2 <= pos)) (PreH12 : (pos <= (bits + 2 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH17 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ (binary_write_state_z_79 decimal_pre decimal divisor pos (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))) ) ”
.

Definition decimal_to_binary_entail_wit_17_split_goal_3 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (pos: Z) (divisor: Z) (i: Z) (bits: Z) (x: Z) (decimal: Z) (PreH1 : (divisor <= 0)) (PreH2 : (0 <= decimal)) (PreH3 : (decimal <= decimal_pre)) (PreH4 : (0 < decimal_pre)) (PreH5 : (decimal_pre <= INT_MAX)) (PreH6 : (x = 0)) (PreH7 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH8 : (i = bits)) (PreH9 : (0 <= divisor)) (PreH10 : (divisor <= INT_MAX)) (PreH11 : (2 <= pos)) (PreH12 : (pos <= (bits + 2 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH17 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ (pos = (bits + 2 )) ”
.

Definition decimal_to_binary_entail_wit_17_split_goal_4 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (pos: Z) (divisor: Z) (i: Z) (bits: Z) (x: Z) (decimal: Z) (PreH1 : (divisor <= 0)) (PreH2 : (0 <= decimal)) (PreH3 : (decimal <= decimal_pre)) (PreH4 : (0 < decimal_pre)) (PreH5 : (decimal_pre <= INT_MAX)) (PreH6 : (x = 0)) (PreH7 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH8 : (i = bits)) (PreH9 : (0 <= divisor)) (PreH10 : (divisor <= INT_MAX)) (PreH11 : (2 <= pos)) (PreH12 : (pos <= (bits + 2 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH16 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH17 : ((Zlength (out_l_2)) = pos)) ,
  TT && emp 
|--
  “ (out_l_2 = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre))))) ”
.

Definition decimal_to_binary_return_wit_1 := 
(
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= ((pos + 1 ) + 1 ))) (PreH2 : (0 <= (pos + 1 ))) (PreH3 : (0 <= pos)) (PreH4 : (0 <= decimal)) (PreH5 : (decimal <= decimal_pre)) (PreH6 : (divisor = 0)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (out_l_2 = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH11 : (pos = (bits + 2 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = pos)) ,
  (CharArray.full out (((pos + 1 ) + 1 ) + 1 ) (app ((app ((app (out_l_2) ((cons (100) ((@nil Z)))))) ((cons (98) ((@nil Z)))))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (((pos + 1 ) + 1 ) + 1 ) (bits + 5 ) )
|--
  EX (out_l: (@list Z))  (len: Z) ,
  “ (len = (Zlength (out_l))) ” 
  &&  “ (len = ((binary_length_z_79 (decimal_pre)) + 4 )) ” 
  &&  “ (out_l = (decorated_binary_output_z_79 (decimal_pre))) ” 
  &&  “ (problem_79_spec_z decimal_pre out_l ) ”
  &&  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
) \/
(
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= (((pos + 1 ) + 1 ) + 1 ))) (PreH2 : (0 <= ((pos + 1 ) + 1 ))) (PreH3 : (0 <= (pos + 1 ))) (PreH4 : (0 <= pos)) (PreH5 : (0 <= decimal)) (PreH6 : (decimal <= decimal_pre)) (PreH7 : (divisor = 0)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (out_l_2 = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH12 : (pos = (bits + 2 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = pos)) ,
  (CharArray.full out (((pos + 1 ) + 1 ) + 1 ) (app ((app ((app (out_l_2) ((cons (100) ((@nil Z)))))) ((cons (98) ((@nil Z)))))) ((cons (0) ((@nil Z))))) )
|--
  “ (problem_79_spec_z decimal_pre (decorated_binary_output_z_79 (decimal_pre)) ) ” 
  &&  “ ((Zlength ((decorated_binary_output_z_79 (decimal_pre)))) = ((binary_length_z_79 (decimal_pre)) + 4 )) ”
  &&  (CharArray.full out ((Zlength ((decorated_binary_output_z_79 (decimal_pre)))) + 1 ) (app ((decorated_binary_output_z_79 (decimal_pre))) ((cons (0) ((@nil Z))))) )
).

Definition decimal_to_binary_return_wit_1_split_goal_1 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= (((pos + 1 ) + 1 ) + 1 ))) (PreH2 : (0 <= ((pos + 1 ) + 1 ))) (PreH3 : (0 <= (pos + 1 ))) (PreH4 : (0 <= pos)) (PreH5 : (0 <= decimal)) (PreH6 : (decimal <= decimal_pre)) (PreH7 : (divisor = 0)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (out_l_2 = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH12 : (pos = (bits + 2 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = pos)) ,
  (CharArray.full out (((pos + 1 ) + 1 ) + 1 ) (app ((app ((app (out_l_2) ((cons (100) ((@nil Z)))))) ((cons (98) ((@nil Z)))))) ((cons (0) ((@nil Z))))) )
|--
  “ (problem_79_spec_z decimal_pre (decorated_binary_output_z_79 (decimal_pre)) ) ”
.

Definition decimal_to_binary_return_wit_1_split_goal_2 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= (((pos + 1 ) + 1 ) + 1 ))) (PreH2 : (0 <= ((pos + 1 ) + 1 ))) (PreH3 : (0 <= (pos + 1 ))) (PreH4 : (0 <= pos)) (PreH5 : (0 <= decimal)) (PreH6 : (decimal <= decimal_pre)) (PreH7 : (divisor = 0)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (out_l_2 = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH12 : (pos = (bits + 2 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = pos)) ,
  (CharArray.full out (((pos + 1 ) + 1 ) + 1 ) (app ((app ((app (out_l_2) ((cons (100) ((@nil Z)))))) ((cons (98) ((@nil Z)))))) ((cons (0) ((@nil Z))))) )
|--
  “ ((Zlength ((decorated_binary_output_z_79 (decimal_pre)))) = ((binary_length_z_79 (decimal_pre)) + 4 )) ”
.

Definition decimal_to_binary_return_wit_1_split_goal_spatial := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= (((pos + 1 ) + 1 ) + 1 ))) (PreH2 : (0 <= ((pos + 1 ) + 1 ))) (PreH3 : (0 <= (pos + 1 ))) (PreH4 : (0 <= pos)) (PreH5 : (0 <= decimal)) (PreH6 : (decimal <= decimal_pre)) (PreH7 : (divisor = 0)) (PreH8 : (x = 0)) (PreH9 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH10 : (i = bits)) (PreH11 : (out_l_2 = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH12 : (pos = (bits + 2 ))) (PreH13 : (problem_79_pre_z decimal_pre )) (PreH14 : (binary_safe_79 decimal_pre )) (PreH15 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = pos)) ,
  (CharArray.full out (((pos + 1 ) + 1 ) + 1 ) (app ((app ((app (out_l_2) ((cons (100) ((@nil Z)))))) ((cons (98) ((@nil Z)))))) ((cons (0) ((@nil Z))))) )
|--
  (CharArray.full out ((Zlength ((decorated_binary_output_z_79 (decimal_pre)))) + 1 ) (app ((decorated_binary_output_z_79 (decimal_pre))) ((cons (0) ((@nil Z))))) )
.

Definition decimal_to_binary_return_wit_2 := 
(
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (5 + 1 ) 6 )
  **  (((retval + (5 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  EX (out_l: (@list Z))  (len: Z) ,
  “ (len = (Zlength (out_l))) ” 
  &&  “ (len = ((binary_length_z_79 (decimal_pre)) + 4 )) ” 
  &&  “ (out_l = (decorated_binary_output_z_79 (decimal_pre))) ” 
  &&  “ (problem_79_spec_z decimal_pre out_l ) ”
  &&  (CharArray.full retval (len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
) \/
(
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (((retval + (5 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  “ (problem_79_spec_z decimal_pre (decorated_binary_output_z_79 (decimal_pre)) ) ” 
  &&  “ ((Zlength ((decorated_binary_output_z_79 (decimal_pre)))) = ((binary_length_z_79 (decimal_pre)) + 4 )) ”
  &&  (CharArray.full retval ((Zlength ((decorated_binary_output_z_79 (decimal_pre)))) + 1 ) (app ((decorated_binary_output_z_79 (decimal_pre))) ((cons (0) ((@nil Z))))) )
).

Definition decimal_to_binary_return_wit_2_split_goal_1 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (((retval + (5 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  “ (problem_79_spec_z decimal_pre (decorated_binary_output_z_79 (decimal_pre)) ) ”
.

Definition decimal_to_binary_return_wit_2_split_goal_2 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (((retval + (5 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  “ ((Zlength ((decorated_binary_output_z_79 (decimal_pre)))) = ((binary_length_z_79 (decimal_pre)) + 4 )) ”
.

Definition decimal_to_binary_return_wit_2_split_goal_spatial := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (((retval + (5 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  (CharArray.full retval ((Zlength ((decorated_binary_output_z_79 (decimal_pre)))) + 1 ) (app ((decorated_binary_output_z_79 (decimal_pre))) ((cons (0) ((@nil Z))))) )
.

Definition decimal_to_binary_partial_solve_wit_1_pure := 
forall (decimal_pre: Z) (PreH1 : (decimal_pre = 0)) (PreH2 : (0 <= decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (problem_79_pre_z decimal_pre )) (PreH5 : (binary_safe_79 decimal_pre )) (PreH6 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "divisor" ) )) # Int  |-> 1)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  “ (6 > 0) ”
.

Definition decimal_to_binary_partial_solve_wit_1_aux := 
forall (decimal_pre: Z) (PreH1 : (decimal_pre = 0)) (PreH2 : (0 <= decimal_pre)) (PreH3 : (decimal_pre <= INT_MAX)) (PreH4 : (problem_79_pre_z decimal_pre )) (PreH5 : (binary_safe_79 decimal_pre )) (PreH6 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  TT && emp 
|--
  “ (6 > 0) ” 
  &&  “ (decimal_pre = 0) ” 
  &&  “ (0 <= decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ”
  &&  emp
.

Definition decimal_to_binary_partial_solve_wit_1 := decimal_to_binary_partial_solve_wit_1_pure -> decimal_to_binary_partial_solve_wit_1_aux.

Definition decimal_to_binary_partial_solve_wit_2 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_full retval 6 )
|--
  “ (retval <> 0) ” 
  &&  “ (decimal_pre = 0) ” 
  &&  “ (0 <= decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ”
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 6 )
.

Definition decimal_to_binary_partial_solve_wit_3 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (0 + 1 ) 6 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  “ (retval <> 0) ” 
  &&  “ (decimal_pre = 0) ” 
  &&  “ (0 <= decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ”
  &&  (((retval + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 (0 + 1 ) 6 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
.

Definition decimal_to_binary_partial_solve_wit_4 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (1 + 1 ) 6 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  “ (retval <> 0) ” 
  &&  “ (decimal_pre = 0) ” 
  &&  “ (0 <= decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ”
  &&  (((retval + (2 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 2 (1 + 1 ) 6 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
.

Definition decimal_to_binary_partial_solve_wit_5 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (2 + 1 ) 6 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  “ (retval <> 0) ” 
  &&  “ (decimal_pre = 0) ” 
  &&  “ (0 <= decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ”
  &&  (((retval + (3 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 3 (2 + 1 ) 6 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
.

Definition decimal_to_binary_partial_solve_wit_6 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (3 + 1 ) 6 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  “ (retval <> 0) ” 
  &&  “ (decimal_pre = 0) ” 
  &&  “ (0 <= decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ”
  &&  (((retval + (4 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 4 (3 + 1 ) 6 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
.

Definition decimal_to_binary_partial_solve_wit_7 := 
forall (decimal_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (decimal_pre = 0)) (PreH3 : (0 <= decimal_pre)) (PreH4 : (decimal_pre <= INT_MAX)) (PreH5 : (problem_79_pre_z decimal_pre )) (PreH6 : (binary_safe_79 decimal_pre )) (PreH7 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) ,
  (CharArray.undef_seg retval (4 + 1 ) 6 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  “ (retval <> 0) ” 
  &&  “ (decimal_pre = 0) ” 
  &&  “ (0 <= decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ”
  &&  (((retval + (5 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 5 (4 + 1 ) 6 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
.

Definition decimal_to_binary_partial_solve_wit_8_pure := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (i: Z) (divisor: Z) (out: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (i = bits)) (PreH6 : (1 <= bits)) (PreH7 : (1 <= divisor)) (PreH8 : (divisor <= INT_MAX)) (PreH9 : (out = 0)) (PreH10 : (pos = 0)) (PreH11 : (problem_79_pre_z decimal_pre )) (PreH12 : (binary_safe_79 decimal_pre )) (PreH13 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH14 : (binary_divisor_state_z_79 decimal_pre bits divisor )) ,
  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "divisor" ) )) # Int  |-> divisor)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "pos" ) )) # Int  |-> pos)
|--
  “ ((bits + 5 ) > 0) ”
.

Definition decimal_to_binary_partial_solve_wit_8_aux := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (i: Z) (divisor: Z) (out: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (i = bits)) (PreH6 : (1 <= bits)) (PreH7 : (1 <= divisor)) (PreH8 : (divisor <= INT_MAX)) (PreH9 : (out = 0)) (PreH10 : (pos = 0)) (PreH11 : (problem_79_pre_z decimal_pre )) (PreH12 : (binary_safe_79 decimal_pre )) (PreH13 : (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX)) (PreH14 : (binary_divisor_state_z_79 decimal_pre bits divisor )) ,
  TT && emp 
|--
  “ ((bits + 5 ) > 0) ” 
  &&  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (1 <= divisor) ” 
  &&  “ (divisor <= INT_MAX) ” 
  &&  “ (out = 0) ” 
  &&  “ (pos = 0) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (((binary_length_z_79 (decimal_pre)) + 5 ) < INT_MAX) ” 
  &&  “ (binary_divisor_state_z_79 decimal_pre bits divisor ) ”
  &&  emp
.

Definition decimal_to_binary_partial_solve_wit_8 := decimal_to_binary_partial_solve_wit_8_pure -> decimal_to_binary_partial_solve_wit_8_aux.

Definition decimal_to_binary_partial_solve_wit_9 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (i: Z) (divisor: Z) (out: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (i = bits)) (PreH7 : (1 <= divisor)) (PreH8 : (divisor <= INT_MAX)) (PreH9 : (binary_divisor_state_z_79 decimal_pre bits divisor )) (PreH10 : (out <> 0)) (PreH11 : (pos = 0)) (PreH12 : (0 < (bits + 5 ))) (PreH13 : ((bits + 5 ) < INT_MAX)) (PreH14 : (1 < (bits + 5 ))) (PreH15 : (problem_79_pre_z decimal_pre )) (PreH16 : (binary_safe_79 decimal_pre )) ,
  (CharArray.undef_full out (bits + 5 ) )
|--
  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (i = bits) ” 
  &&  “ (1 <= divisor) ” 
  &&  “ (divisor <= INT_MAX) ” 
  &&  “ (binary_divisor_state_z_79 decimal_pre bits divisor ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (pos = 0) ” 
  &&  “ (0 < (bits + 5 )) ” 
  &&  “ ((bits + 5 ) < INT_MAX) ” 
  &&  “ (1 < (bits + 5 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ”
  &&  (((out + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out 0 0 (bits + 5 ) )
.

Definition decimal_to_binary_partial_solve_wit_10 := 
forall (decimal_pre: Z) (x: Z) (bits: Z) (i: Z) (divisor: Z) (out: Z) (pos: Z) (PreH1 : (0 < decimal_pre)) (PreH2 : (decimal_pre <= INT_MAX)) (PreH3 : (x = 0)) (PreH4 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH5 : (1 <= bits)) (PreH6 : (i = bits)) (PreH7 : (1 <= divisor)) (PreH8 : (divisor <= INT_MAX)) (PreH9 : (binary_divisor_state_z_79 decimal_pre bits divisor )) (PreH10 : (out <> 0)) (PreH11 : (pos = 0)) (PreH12 : (0 < (bits + 5 ))) (PreH13 : ((bits + 5 ) < INT_MAX)) (PreH14 : (1 < (bits + 5 ))) (PreH15 : (problem_79_pre_z decimal_pre )) (PreH16 : (binary_safe_79 decimal_pre )) ,
  (CharArray.undef_seg out (0 + 1 ) (bits + 5 ) )
  **  (((out + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (1 <= bits) ” 
  &&  “ (i = bits) ” 
  &&  “ (1 <= divisor) ” 
  &&  “ (divisor <= INT_MAX) ” 
  &&  “ (binary_divisor_state_z_79 decimal_pre bits divisor ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (pos = 0) ” 
  &&  “ (0 < (bits + 5 )) ” 
  &&  “ ((bits + 5 ) < INT_MAX) ” 
  &&  “ (1 < (bits + 5 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ”
  &&  (((out + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out 1 (0 + 1 ) (bits + 5 ) )
  **  (((out + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
.

Definition decimal_to_binary_partial_solve_wit_11 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (divisor: Z) (decimal: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (divisor <= decimal)) (PreH2 : (0 < divisor)) (PreH3 : (0 <= decimal)) (PreH4 : (decimal <= decimal_pre)) (PreH5 : (0 < decimal_pre)) (PreH6 : (decimal_pre <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos < (bits + 5 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH15 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  “ (0 <= pos) ” 
  &&  “ (divisor <= decimal) ” 
  &&  “ (0 < divisor) ” 
  &&  “ (0 <= decimal) ” 
  &&  “ (decimal <= decimal_pre) ” 
  &&  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (2 <= pos) ” 
  &&  “ (pos < (bits + 5 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal divisor pos out_l ) ” 
  &&  “ ((Zlength (out_l)) = pos) ”
  &&  (((out + (pos * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out pos pos (bits + 5 ) )
  **  (CharArray.full out pos out_l )
.

Definition decimal_to_binary_partial_solve_wit_12 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (decimal < divisor)) (PreH2 : (0 < divisor)) (PreH3 : (0 <= decimal)) (PreH4 : (decimal <= decimal_pre)) (PreH5 : (0 < decimal_pre)) (PreH6 : (decimal_pre <= INT_MAX)) (PreH7 : (x = 0)) (PreH8 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH9 : (i = bits)) (PreH10 : (2 <= pos)) (PreH11 : (pos < (bits + 5 ))) (PreH12 : (problem_79_pre_z decimal_pre )) (PreH13 : (binary_safe_79 decimal_pre )) (PreH14 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH15 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  “ (0 <= pos) ” 
  &&  “ (decimal < divisor) ” 
  &&  “ (0 < divisor) ” 
  &&  “ (0 <= decimal) ” 
  &&  “ (decimal <= decimal_pre) ” 
  &&  “ (0 < decimal_pre) ” 
  &&  “ (decimal_pre <= INT_MAX) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (2 <= pos) ” 
  &&  “ (pos < (bits + 5 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal divisor pos out_l ) ” 
  &&  “ ((Zlength (out_l)) = pos) ”
  &&  (((out + (pos * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out pos pos (bits + 5 ) )
  **  (CharArray.full out pos out_l )
.

Definition decimal_to_binary_partial_solve_wit_13 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= decimal)) (PreH2 : (decimal <= decimal_pre)) (PreH3 : (divisor = 0)) (PreH4 : (x = 0)) (PreH5 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH6 : (i = bits)) (PreH7 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH8 : (pos = (bits + 2 ))) (PreH9 : (problem_79_pre_z decimal_pre )) (PreH10 : (binary_safe_79 decimal_pre )) (PreH11 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH12 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out pos out_l )
  **  (CharArray.undef_seg out pos (bits + 5 ) )
|--
  “ (0 <= pos) ” 
  &&  “ (0 <= decimal) ” 
  &&  “ (decimal <= decimal_pre) ” 
  &&  “ (divisor = 0) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre))))) ” 
  &&  “ (pos = (bits + 2 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal divisor pos out_l ) ” 
  &&  “ ((Zlength (out_l)) = pos) ”
  &&  (((out + (pos * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out pos pos (bits + 5 ) )
  **  (CharArray.full out pos out_l )
.

Definition decimal_to_binary_partial_solve_wit_14 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= pos)) (PreH2 : (0 <= decimal)) (PreH3 : (decimal <= decimal_pre)) (PreH4 : (divisor = 0)) (PreH5 : (x = 0)) (PreH6 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH7 : (i = bits)) (PreH8 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH9 : (pos = (bits + 2 ))) (PreH10 : (problem_79_pre_z decimal_pre )) (PreH11 : (binary_safe_79 decimal_pre )) (PreH12 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH13 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (100) ((@nil Z))))) )
  **  (CharArray.undef_seg out (pos + 1 ) (bits + 5 ) )
|--
  “ (0 <= (pos + 1 )) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (0 <= decimal) ” 
  &&  “ (decimal <= decimal_pre) ” 
  &&  “ (divisor = 0) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre))))) ” 
  &&  “ (pos = (bits + 2 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal divisor pos out_l ) ” 
  &&  “ ((Zlength (out_l)) = pos) ”
  &&  (((out + ((pos + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (pos + 1 ) (pos + 1 ) (bits + 5 ) )
  **  (CharArray.full out (pos + 1 ) (app (out_l) ((cons (100) ((@nil Z))))) )
.

Definition decimal_to_binary_partial_solve_wit_15 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (decimal: Z) (divisor: Z) (x: Z) (bits: Z) (i: Z) (pos: Z) (out: Z) (PreH1 : (0 <= (pos + 1 ))) (PreH2 : (0 <= pos)) (PreH3 : (0 <= decimal)) (PreH4 : (decimal <= decimal_pre)) (PreH5 : (divisor = 0)) (PreH6 : (x = 0)) (PreH7 : (bits = (binary_length_z_79 (decimal_pre)))) (PreH8 : (i = bits)) (PreH9 : (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre)))))) (PreH10 : (pos = (bits + 2 ))) (PreH11 : (problem_79_pre_z decimal_pre )) (PreH12 : (binary_safe_79 decimal_pre )) (PreH13 : (binary_write_state_z_79 decimal_pre decimal divisor pos out_l )) (PreH14 : ((Zlength (out_l)) = pos)) ,
  (CharArray.full out ((pos + 1 ) + 1 ) (app ((app (out_l) ((cons (100) ((@nil Z)))))) ((cons (98) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((pos + 1 ) + 1 ) (bits + 5 ) )
|--
  “ (0 <= ((pos + 1 ) + 1 )) ” 
  &&  “ (0 <= (pos + 1 )) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (0 <= decimal) ” 
  &&  “ (decimal <= decimal_pre) ” 
  &&  “ (divisor = 0) ” 
  &&  “ (x = 0) ” 
  &&  “ (bits = (binary_length_z_79 (decimal_pre))) ” 
  &&  “ (i = bits) ” 
  &&  “ (out_l = (app ((cons (100) ((cons (98) ((@nil Z)))))) ((binary_payload_z_79 (decimal_pre))))) ” 
  &&  “ (pos = (bits + 2 )) ” 
  &&  “ (problem_79_pre_z decimal_pre ) ” 
  &&  “ (binary_safe_79 decimal_pre ) ” 
  &&  “ (binary_write_state_z_79 decimal_pre decimal divisor pos out_l ) ” 
  &&  “ ((Zlength (out_l)) = pos) ”
  &&  (((out + (((pos + 1 ) + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out ((pos + 1 ) + 1 ) ((pos + 1 ) + 1 ) (bits + 5 ) )
  **  (CharArray.full out ((pos + 1 ) + 1 ) (app ((app (out_l) ((cons (100) ((@nil Z)))))) ((cons (98) ((@nil Z))))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_decimal_to_binary_safety_wit_1 : decimal_to_binary_safety_wit_1.
Axiom proof_of_decimal_to_binary_safety_wit_2 : decimal_to_binary_safety_wit_2.
Axiom proof_of_decimal_to_binary_safety_wit_3 : decimal_to_binary_safety_wit_3.
Axiom proof_of_decimal_to_binary_safety_wit_4 : decimal_to_binary_safety_wit_4.
Axiom proof_of_decimal_to_binary_safety_wit_5 : decimal_to_binary_safety_wit_5.
Axiom proof_of_decimal_to_binary_safety_wit_6 : decimal_to_binary_safety_wit_6.
Axiom proof_of_decimal_to_binary_safety_wit_7 : decimal_to_binary_safety_wit_7.
Axiom proof_of_decimal_to_binary_safety_wit_8 : decimal_to_binary_safety_wit_8.
Axiom proof_of_decimal_to_binary_safety_wit_9 : decimal_to_binary_safety_wit_9.
Axiom proof_of_decimal_to_binary_safety_wit_10 : decimal_to_binary_safety_wit_10.
Axiom proof_of_decimal_to_binary_safety_wit_11 : decimal_to_binary_safety_wit_11.
Axiom proof_of_decimal_to_binary_safety_wit_12 : decimal_to_binary_safety_wit_12.
Axiom proof_of_decimal_to_binary_safety_wit_13 : decimal_to_binary_safety_wit_13.
Axiom proof_of_decimal_to_binary_safety_wit_14 : decimal_to_binary_safety_wit_14.
Axiom proof_of_decimal_to_binary_safety_wit_15 : decimal_to_binary_safety_wit_15.
Axiom proof_of_decimal_to_binary_safety_wit_16 : decimal_to_binary_safety_wit_16.
Axiom proof_of_decimal_to_binary_safety_wit_17 : decimal_to_binary_safety_wit_17.
Axiom proof_of_decimal_to_binary_safety_wit_18 : decimal_to_binary_safety_wit_18.
Axiom proof_of_decimal_to_binary_safety_wit_19 : decimal_to_binary_safety_wit_19.
Axiom proof_of_decimal_to_binary_safety_wit_20 : decimal_to_binary_safety_wit_20.
Axiom proof_of_decimal_to_binary_safety_wit_21 : decimal_to_binary_safety_wit_21.
Axiom proof_of_decimal_to_binary_safety_wit_22 : decimal_to_binary_safety_wit_22.
Axiom proof_of_decimal_to_binary_safety_wit_23 : decimal_to_binary_safety_wit_23.
Axiom proof_of_decimal_to_binary_safety_wit_24 : decimal_to_binary_safety_wit_24.
Axiom proof_of_decimal_to_binary_safety_wit_25 : decimal_to_binary_safety_wit_25.
Axiom proof_of_decimal_to_binary_safety_wit_26 : decimal_to_binary_safety_wit_26.
Axiom proof_of_decimal_to_binary_safety_wit_27 : decimal_to_binary_safety_wit_27.
Axiom proof_of_decimal_to_binary_safety_wit_28 : decimal_to_binary_safety_wit_28.
Axiom proof_of_decimal_to_binary_safety_wit_29 : decimal_to_binary_safety_wit_29.
Axiom proof_of_decimal_to_binary_safety_wit_30 : decimal_to_binary_safety_wit_30.
Axiom proof_of_decimal_to_binary_safety_wit_31 : decimal_to_binary_safety_wit_31.
Axiom proof_of_decimal_to_binary_safety_wit_32 : decimal_to_binary_safety_wit_32.
Axiom proof_of_decimal_to_binary_safety_wit_33 : decimal_to_binary_safety_wit_33.
Axiom proof_of_decimal_to_binary_safety_wit_34 : decimal_to_binary_safety_wit_34.
Axiom proof_of_decimal_to_binary_safety_wit_35 : decimal_to_binary_safety_wit_35.
Axiom proof_of_decimal_to_binary_safety_wit_36 : decimal_to_binary_safety_wit_36.
Axiom proof_of_decimal_to_binary_safety_wit_37 : decimal_to_binary_safety_wit_37.
Axiom proof_of_decimal_to_binary_safety_wit_38 : decimal_to_binary_safety_wit_38.
Axiom proof_of_decimal_to_binary_safety_wit_39 : decimal_to_binary_safety_wit_39.
Axiom proof_of_decimal_to_binary_safety_wit_40 : decimal_to_binary_safety_wit_40.
Axiom proof_of_decimal_to_binary_safety_wit_41 : decimal_to_binary_safety_wit_41.
Axiom proof_of_decimal_to_binary_safety_wit_42 : decimal_to_binary_safety_wit_42.
Axiom proof_of_decimal_to_binary_safety_wit_43 : decimal_to_binary_safety_wit_43.
Axiom proof_of_decimal_to_binary_safety_wit_44 : decimal_to_binary_safety_wit_44.
Axiom proof_of_decimal_to_binary_safety_wit_45 : decimal_to_binary_safety_wit_45.
Axiom proof_of_decimal_to_binary_safety_wit_46 : decimal_to_binary_safety_wit_46.
Axiom proof_of_decimal_to_binary_safety_wit_47 : decimal_to_binary_safety_wit_47.
Axiom proof_of_decimal_to_binary_safety_wit_48 : decimal_to_binary_safety_wit_48.
Axiom proof_of_decimal_to_binary_safety_wit_49 : decimal_to_binary_safety_wit_49.
Axiom proof_of_decimal_to_binary_safety_wit_50 : decimal_to_binary_safety_wit_50.
Axiom proof_of_decimal_to_binary_safety_wit_51 : decimal_to_binary_safety_wit_51.
Axiom proof_of_decimal_to_binary_safety_wit_52 : decimal_to_binary_safety_wit_52.
Axiom proof_of_decimal_to_binary_safety_wit_53 : decimal_to_binary_safety_wit_53.
Axiom proof_of_decimal_to_binary_safety_wit_54 : decimal_to_binary_safety_wit_54.
Axiom proof_of_decimal_to_binary_entail_wit_1 : decimal_to_binary_entail_wit_1.
Axiom proof_of_decimal_to_binary_entail_wit_2 : decimal_to_binary_entail_wit_2.
Axiom proof_of_decimal_to_binary_entail_wit_3 : decimal_to_binary_entail_wit_3.
Axiom proof_of_decimal_to_binary_entail_wit_4 : decimal_to_binary_entail_wit_4.
Axiom proof_of_decimal_to_binary_entail_wit_5 : decimal_to_binary_entail_wit_5.
Axiom proof_of_decimal_to_binary_entail_wit_6 : decimal_to_binary_entail_wit_6.
Axiom proof_of_decimal_to_binary_entail_wit_7 : decimal_to_binary_entail_wit_7.
Axiom proof_of_decimal_to_binary_entail_wit_8 : decimal_to_binary_entail_wit_8.
Axiom proof_of_decimal_to_binary_entail_wit_9 : decimal_to_binary_entail_wit_9.
Axiom proof_of_decimal_to_binary_entail_wit_10 : decimal_to_binary_entail_wit_10.
Axiom proof_of_decimal_to_binary_entail_wit_11 : decimal_to_binary_entail_wit_11.
Axiom proof_of_decimal_to_binary_entail_wit_12 : decimal_to_binary_entail_wit_12.
Axiom proof_of_decimal_to_binary_entail_wit_13 : decimal_to_binary_entail_wit_13.
Axiom proof_of_decimal_to_binary_entail_wit_14 : decimal_to_binary_entail_wit_14.
Axiom proof_of_decimal_to_binary_entail_wit_15 : decimal_to_binary_entail_wit_15.
Axiom proof_of_decimal_to_binary_entail_wit_16_1 : decimal_to_binary_entail_wit_16_1.
Axiom proof_of_decimal_to_binary_entail_wit_16_2 : decimal_to_binary_entail_wit_16_2.
Axiom proof_of_decimal_to_binary_entail_wit_17 : decimal_to_binary_entail_wit_17.
Axiom proof_of_decimal_to_binary_return_wit_1 : decimal_to_binary_return_wit_1.
Axiom proof_of_decimal_to_binary_return_wit_2 : decimal_to_binary_return_wit_2.
Axiom proof_of_decimal_to_binary_partial_solve_wit_1_pure : decimal_to_binary_partial_solve_wit_1_pure.
Axiom proof_of_decimal_to_binary_partial_solve_wit_1 : decimal_to_binary_partial_solve_wit_1.
Axiom proof_of_decimal_to_binary_partial_solve_wit_2 : decimal_to_binary_partial_solve_wit_2.
Axiom proof_of_decimal_to_binary_partial_solve_wit_3 : decimal_to_binary_partial_solve_wit_3.
Axiom proof_of_decimal_to_binary_partial_solve_wit_4 : decimal_to_binary_partial_solve_wit_4.
Axiom proof_of_decimal_to_binary_partial_solve_wit_5 : decimal_to_binary_partial_solve_wit_5.
Axiom proof_of_decimal_to_binary_partial_solve_wit_6 : decimal_to_binary_partial_solve_wit_6.
Axiom proof_of_decimal_to_binary_partial_solve_wit_7 : decimal_to_binary_partial_solve_wit_7.
Axiom proof_of_decimal_to_binary_partial_solve_wit_8_pure : decimal_to_binary_partial_solve_wit_8_pure.
Axiom proof_of_decimal_to_binary_partial_solve_wit_8 : decimal_to_binary_partial_solve_wit_8.
Axiom proof_of_decimal_to_binary_partial_solve_wit_9 : decimal_to_binary_partial_solve_wit_9.
Axiom proof_of_decimal_to_binary_partial_solve_wit_10 : decimal_to_binary_partial_solve_wit_10.
Axiom proof_of_decimal_to_binary_partial_solve_wit_11 : decimal_to_binary_partial_solve_wit_11.
Axiom proof_of_decimal_to_binary_partial_solve_wit_12 : decimal_to_binary_partial_solve_wit_12.
Axiom proof_of_decimal_to_binary_partial_solve_wit_13 : decimal_to_binary_partial_solve_wit_13.
Axiom proof_of_decimal_to_binary_partial_solve_wit_14 : decimal_to_binary_partial_solve_wit_14.
Axiom proof_of_decimal_to_binary_partial_solve_wit_15 : decimal_to_binary_partial_solve_wit_15.

End VC_Correct.
