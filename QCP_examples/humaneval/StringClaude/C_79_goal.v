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
Require Import coins_79.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function decimal_to_binary -----*)

Definition decimal_to_binary_safety_wit_1 := 
forall (decimal_pre: Z) ,
  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition decimal_to_binary_safety_wit_2 := 
forall (decimal_pre: Z) ,
  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  ((( &( "out_zero" ) )) # Ptr  |->_)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition decimal_to_binary_safety_wit_3 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_full retval 6 )
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition decimal_to_binary_safety_wit_4 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_full retval 6 )
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (100 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 100) |]
.

Definition decimal_to_binary_safety_wit_5 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) 6 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition decimal_to_binary_safety_wit_6 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) 6 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (98 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 98) |]
.

Definition decimal_to_binary_safety_wit_7 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (1 + 1 ) 6 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition decimal_to_binary_safety_wit_8 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (1 + 1 ) 6 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition decimal_to_binary_safety_wit_9 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (2 + 1 ) 6 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition decimal_to_binary_safety_wit_10 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (2 + 1 ) 6 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (100 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 100) |]
.

Definition decimal_to_binary_safety_wit_11 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (3 + 1 ) 6 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition decimal_to_binary_safety_wit_12 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (3 + 1 ) 6 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (98 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 98) |]
.

Definition decimal_to_binary_safety_wit_13 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (4 + 1 ) 6 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition decimal_to_binary_safety_wit_14 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (4 + 1 ) 6 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "out_zero" ) )) # Ptr  |-> retval)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition decimal_to_binary_safety_wit_15 := 
forall (decimal_pre: Z) ,
  [| (decimal_pre <> 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  ((( &( "bits" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> decimal_pre)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition decimal_to_binary_safety_wit_16 := 
forall (decimal_pre: Z) ,
  [| (decimal_pre <> 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  ((( &( "total" ) )) # Int  |->_)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> decimal_pre)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition decimal_to_binary_safety_wit_17 := 
forall (decimal_pre: Z) ,
  [| (decimal_pre <> 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "total" ) )) # Int  |-> 0)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> decimal_pre)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition decimal_to_binary_safety_wit_18 := 
forall (decimal_pre: Z) ,
  [| (decimal_pre <> 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "num" ) )) # Int  |-> decimal_pre)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "total" ) )) # Int  |-> 0)
  **  ((( &( "bits" ) )) # Int  |-> 0)
  **  ((( &( "x" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> decimal_pre)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition decimal_to_binary_safety_wit_19 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition decimal_to_binary_safety_wit_20 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) ,
  [| (x > 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
|--
  [| ((bits + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (bits + 1 )) |]
.

Definition decimal_to_binary_safety_wit_21 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) ,
  [| (x > 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition decimal_to_binary_safety_wit_22 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) ,
  [| (x > 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> (bits + 1 ))
|--
  [| ((x <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition decimal_to_binary_safety_wit_23 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) ,
  [| (x > 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> (bits + 1 ))
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition decimal_to_binary_safety_wit_24 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) ,
  [| (x <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "total" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
|--
  [| ((bits + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (bits + 5 )) |]
.

Definition decimal_to_binary_safety_wit_25 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) ,
  [| (x <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "total" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition decimal_to_binary_safety_wit_26 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (x <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  (CharArray.undef_full retval (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "total" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition decimal_to_binary_safety_wit_27 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (x <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  (CharArray.undef_full retval (bits + 5 ) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "total" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
|--
  [| (100 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 100) |]
.

Definition decimal_to_binary_safety_wit_28 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (x <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) (bits + 5 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "total" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition decimal_to_binary_safety_wit_29 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (x <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) (bits + 5 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "total" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
|--
  [| (98 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 98) |]
.

Definition decimal_to_binary_safety_wit_30 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (x <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  (CharArray.undef_seg retval (1 + 1 ) (bits + 5 ) )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "total" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition decimal_to_binary_safety_wit_31 := 
forall (decimal_pre: Z) (out: Z) (i: Z) (bits: Z) (total: Z) (x: Z) (num: Z) (orig: Z) ,
  [| (i < total) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= total) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.seg out 2 (i + 2 ) (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg out (i + 2 ) (total + 5 ) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| ((i + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 2 )) |]
.

Definition decimal_to_binary_safety_wit_32 := 
forall (decimal_pre: Z) (out: Z) (i: Z) (bits: Z) (total: Z) (x: Z) (num: Z) (orig: Z) ,
  [| (i < total) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= total) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.seg out 2 (i + 2 ) (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg out (i + 2 ) (total + 5 ) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition decimal_to_binary_safety_wit_33 := 
forall (decimal_pre: Z) (out: Z) (i: Z) (bits: Z) (total: Z) (x: Z) (num: Z) (orig: Z) ,
  [| (i < total) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= total) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.seg out 2 (i + 2 ) (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg out (i + 2 ) (total + 5 ) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition decimal_to_binary_safety_wit_34 := 
forall (decimal_pre: Z) (out: Z) (i: Z) (bits: Z) (total: Z) (x: Z) (num: Z) (orig: Z) ,
  [| (0 <= 2) |] 
  &&  [| (i < total) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= total) |]
  &&  (CharArray.undef_seg out ((i + 2 ) + 1 ) (total + 5 ) )
  **  (((out + ((i + 2 ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.seg out 2 (i + 2 ) (repeat_Z (0) (i)) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition decimal_to_binary_safety_wit_35 := 
forall (decimal_pre: Z) (out: Z) (i: Z) (bits: Z) (total: Z) (x: Z) (num: Z) (orig: Z) ,
  [| (0 <= 2) |] 
  &&  [| (i < total) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= total) |]
  &&  (CharArray.undef_seg out ((i + 2 ) + 1 ) (total + 5 ) )
  **  (((out + ((i + 2 ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.seg out 2 (i + 2 ) (repeat_Z (0) (i)) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition decimal_to_binary_safety_wit_36 := 
forall (decimal_pre: Z) (orig: Z) (num: Z) (x: Z) (total: Z) (bits: Z) (i: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 4 ) )
  **  (CharArray.undef_seg out (total + 4 ) (total + 5 ) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| ((total + 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (total + 4 )) |]
.

Definition decimal_to_binary_safety_wit_37 := 
forall (decimal_pre: Z) (orig: Z) (num: Z) (x: Z) (total: Z) (bits: Z) (i: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 4 ) )
  **  (CharArray.undef_seg out (total + 4 ) (total + 5 ) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition decimal_to_binary_safety_wit_38 := 
forall (decimal_pre: Z) (orig: Z) (num: Z) (x: Z) (total: Z) (bits: Z) (i: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 4 ) )
  **  (CharArray.undef_seg out (total + 4 ) (total + 5 ) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition decimal_to_binary_safety_wit_39 := 
forall (decimal_pre: Z) (orig: Z) (num: Z) (x: Z) (total: Z) (bits: Z) (i: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 3 ) )
  **  (CharArray.undef_seg out (total + 3 ) (total + 4 ) )
  **  (CharArray.seg out (total + 4 ) (total + 5 ) (cons (0) (nil)) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| ((total + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (total + 3 )) |]
.

Definition decimal_to_binary_safety_wit_40 := 
forall (decimal_pre: Z) (orig: Z) (num: Z) (x: Z) (total: Z) (bits: Z) (i: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 3 ) )
  **  (CharArray.undef_seg out (total + 3 ) (total + 4 ) )
  **  (CharArray.seg out (total + 4 ) (total + 5 ) (cons (0) (nil)) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition decimal_to_binary_safety_wit_41 := 
forall (decimal_pre: Z) (orig: Z) (num: Z) (x: Z) (total: Z) (bits: Z) (i: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 3 ) )
  **  (CharArray.undef_seg out (total + 3 ) (total + 4 ) )
  **  (CharArray.seg out (total + 4 ) (total + 5 ) (cons (0) (nil)) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (98 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 98) |]
.

Definition decimal_to_binary_safety_wit_42 := 
forall (decimal_pre: Z) (orig: Z) (num: Z) (x: Z) (total: Z) (bits: Z) (i: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 3 ) )
  **  (CharArray.seg out (total + 3 ) (total + 5 ) (cons (98) ((cons (0) (nil)))) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| ((total + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (total + 2 )) |]
.

Definition decimal_to_binary_safety_wit_43 := 
forall (decimal_pre: Z) (orig: Z) (num: Z) (x: Z) (total: Z) (bits: Z) (i: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 3 ) )
  **  (CharArray.seg out (total + 3 ) (total + 5 ) (cons (98) ((cons (0) (nil)))) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition decimal_to_binary_safety_wit_44 := 
forall (decimal_pre: Z) (orig: Z) (num: Z) (x: Z) (total: Z) (bits: Z) (i: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 3 ) )
  **  (CharArray.seg out (total + 3 ) (total + 5 ) (cons (98) ((cons (0) (nil)))) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (100 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 100) |]
.

Definition decimal_to_binary_safety_wit_45 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (orig: Z) (num: Z) (x: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (i = total) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z decimal_pre decimal_pre bits out_l ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| ((total + 5 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (total + 5 )) |]
.

Definition decimal_to_binary_safety_wit_46 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (orig: Z) (num: Z) (x: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (i = total) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z decimal_pre decimal_pre bits out_l ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition decimal_to_binary_safety_wit_47 := 
forall (decimal_pre: Z) (out: Z) (out_l: (@list Z)) (num: Z) (bits: Z) (total: Z) (i: Z) (x: Z) (orig: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num bits out_l ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition decimal_to_binary_safety_wit_48 := 
forall (decimal_pre: Z) (out: Z) (out_l: (@list Z)) (num: Z) (bits: Z) (total: Z) (i: Z) (x: Z) (orig: Z) ,
  [| (num > 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num bits out_l ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| ((bits - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (bits - 1 )) |]
.

Definition decimal_to_binary_safety_wit_49 := 
forall (decimal_pre: Z) (out: Z) (out_l: (@list Z)) (num: Z) (bits: Z) (total: Z) (i: Z) (x: Z) (orig: Z) ,
  [| (num > 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num bits out_l ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition decimal_to_binary_safety_wit_50 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (orig: Z) (x: Z) (num: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 < num) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| ((bits + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (bits + 2 )) |]
.

Definition decimal_to_binary_safety_wit_51 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (orig: Z) (x: Z) (num: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 < num) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition decimal_to_binary_safety_wit_52 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (orig: Z) (x: Z) (num: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 < num) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| ((48 + (num % ( 2 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (48 + (num % ( 2 ) ) )) |]
.

Definition decimal_to_binary_safety_wit_53 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (orig: Z) (x: Z) (num: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 < num) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| ((num <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition decimal_to_binary_safety_wit_54 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (orig: Z) (x: Z) (num: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 < num) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition decimal_to_binary_safety_wit_55 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (orig: Z) (x: Z) (num: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 < num) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition decimal_to_binary_safety_wit_56 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (orig: Z) (x: Z) (num: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 <= (total + 5 )) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 < num) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  (CharArray.full out (total + 5 ) (replace_Znth ((bits + 2 )) ((signed_last_nbits ((48 + (num % ( 2 ) ) )) (8))) ((app (out_l) ((cons (0) (nil)))))) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((num <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition decimal_to_binary_safety_wit_57 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (orig: Z) (x: Z) (num: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 <= (total + 5 )) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 < num) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  (CharArray.full out (total + 5 ) (replace_Znth ((bits + 2 )) ((signed_last_nbits ((48 + (num % ( 2 ) ) )) (8))) ((app (out_l) ((cons (0) (nil)))))) )
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "bits" ) )) # Int  |-> bits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition decimal_to_binary_entail_wit_1 := 
forall (decimal_pre: Z) ,
  [| (decimal_pre <> 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  emp
|--
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (decimal_pre = decimal_pre) |] 
  &&  [| (decimal_pre = decimal_pre) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre decimal_pre 0 ) |]
  &&  emp
.

Definition decimal_to_binary_entail_wit_2 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) ,
  [| (x > 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  emp
|--
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= (x ÷ 2 )) |] 
  &&  [| (0 <= (bits + 1 )) |] 
  &&  [| ((bits + 1 ) < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre (x ÷ 2 ) (bits + 1 ) ) |]
  &&  emp
.

Definition decimal_to_binary_entail_wit_3 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (x <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  (CharArray.undef_seg retval (1 + 1 ) (bits + 5 ) )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (bits = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = bits) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= bits) |]
  &&  (CharArray.seg retval 2 (0 + 2 ) (repeat_Z (0) (0)) )
  **  (CharArray.undef_seg retval (0 + 2 ) (bits + 5 ) )
  **  (CharArray.full retval 2 (cons (100) ((cons (98) (nil)))) )
.

Definition decimal_to_binary_entail_wit_4 := 
forall (decimal_pre: Z) (out: Z) (i: Z) (bits: Z) (total: Z) (x: Z) (num: Z) (orig: Z) ,
  [| (0 <= 2) |] 
  &&  [| (i < total) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= total) |]
  &&  (CharArray.undef_seg out ((i + 2 ) + 1 ) (total + 5 ) )
  **  (((out + ((i + 2 ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.seg out 2 (i + 2 ) (repeat_Z (0) (i)) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= total) |]
  &&  (CharArray.seg out 2 ((i + 1 ) + 2 ) (repeat_Z (0) ((i + 1 ))) )
  **  (CharArray.undef_seg out ((i + 1 ) + 2 ) (total + 5 ) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
.

Definition decimal_to_binary_entail_wit_5 := 
forall (decimal_pre: Z) (out: Z) (i: Z) (bits: Z) (total: Z) (x: Z) (num: Z) (orig: Z) ,
  [| (i >= total) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= total) |]
  &&  (CharArray.seg out 2 (i + 2 ) (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg out (i + 2 ) (total + 5 ) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 4 ) )
  **  (CharArray.undef_seg out (total + 4 ) (total + 5 ) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
.

Definition decimal_to_binary_entail_wit_6 := 
forall (decimal_pre: Z) (orig: Z) (num: Z) (x: Z) (total: Z) (bits: Z) (i: Z) (out: Z) ,
  [| (0 <= 2) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  (CharArray.undef_seg out ((total + 4 ) + 1 ) (total + 5 ) )
  **  (((out + ((total + 4 ) * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 4 ) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 3 ) )
  **  (CharArray.undef_seg out (total + 3 ) (total + 4 ) )
  **  (CharArray.seg out (total + 4 ) (total + 5 ) (cons (0) (nil)) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
.

Definition decimal_to_binary_entail_wit_7 := 
forall (decimal_pre: Z) (orig: Z) (num: Z) (x: Z) (total: Z) (bits: Z) (i: Z) (out: Z) ,
  [| (0 <= 2) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  (CharArray.undef_seg out ((total + 3 ) + 1 ) (total + 4 ) )
  **  (((out + ((total + 3 ) * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 3 ) )
  **  (CharArray.seg out (total + 4 ) (total + 5 ) (cons (0) (nil)) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 3 ) )
  **  (CharArray.seg out (total + 3 ) (total + 5 ) (cons (98) ((cons (0) (nil)))) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
.

Definition decimal_to_binary_entail_wit_8 := 
forall (decimal_pre: Z) (orig: Z) (num: Z) (x: Z) (total: Z) (bits: Z) (i: Z) (out: Z) ,
  [| (0 <= 2) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  (CharArray.undef_seg out ((total + 2 ) + 1 ) (total + 3 ) )
  **  (((out + ((total + 2 ) * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.seg out (total + 3 ) (total + 5 ) (cons (98) ((cons (0) (nil)))) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (i = total) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z decimal_pre decimal_pre bits out_l ) |]
  &&  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition decimal_to_binary_entail_wit_9 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (orig: Z) (num: Z) (x: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (i = total) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| ((Zlength (out_l_2)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z decimal_pre decimal_pre bits out_l_2 ) |]
  &&  (CharArray.full out (total + 5 ) (app (out_l_2) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| ((total + 5 ) = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num bits out_l ) |]
  &&  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition decimal_to_binary_entail_wit_10 := 
forall (decimal_pre: Z) (out: Z) (out_l_2: (@list Z)) (num: Z) (bits: Z) (total: Z) (i: Z) (x: Z) (orig: Z) ,
  [| (num > 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l_2)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num bits out_l_2 ) |]
  &&  (CharArray.full out (total + 5 ) (app (out_l_2) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 < num) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= (bits - 1 )) |] 
  &&  [| ((bits - 1 ) < total) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num ((bits - 1 ) + 1 ) out_l ) |]
  &&  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition decimal_to_binary_entail_wit_11 := 
forall (decimal_pre: Z) (out_l_2: (@list Z)) (orig: Z) (x: Z) (num: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 <= (total + 5 )) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 < num) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l_2)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num (bits + 1 ) out_l_2 ) |]
  &&  (CharArray.full out (total + 5 ) (replace_Znth ((bits + 2 )) ((signed_last_nbits ((48 + (num % ( 2 ) ) )) (8))) ((app (out_l_2) ((cons (0) (nil)))))) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits <= total) |] 
  &&  [| (0 <= (num ÷ 2 )) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig (num ÷ 2 ) bits out_l ) |]
  &&  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition decimal_to_binary_return_wit_1 := 
forall (decimal_pre: Z) (out: Z) (out_l_2: (@list Z)) (num: Z) (bits: Z) (total: Z) (i: Z) (x: Z) (orig: Z) ,
  [| (num <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l_2)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num bits out_l_2 ) |]
  &&  (CharArray.full out (total + 5 ) (app (out_l_2) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z))  (len: Z) ,
  [| (1 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (out_l)) = len) |] 
  &&  [| (problem_79_spec_z decimal_pre out_l ) |]
  &&  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition decimal_to_binary_return_wit_2 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (5 + 1 ) 6 )
  **  (((retval + (5 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  EX (out_l: (@list Z))  (len: Z) ,
  [| (1 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (out_l)) = len) |] 
  &&  [| (problem_79_spec_z decimal_pre out_l ) |]
  &&  (CharArray.full retval (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition decimal_to_binary_partial_solve_wit_1_pure := 
forall (decimal_pre: Z) ,
  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  ((( &( "out_zero" ) )) # Ptr  |->_)
  **  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
|--
  [| (6 > 0) |]
.

Definition decimal_to_binary_partial_solve_wit_1_aux := 
forall (decimal_pre: Z) ,
  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  emp
|--
  [| (6 > 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  emp
.

Definition decimal_to_binary_partial_solve_wit_1 := decimal_to_binary_partial_solve_wit_1_pure -> decimal_to_binary_partial_solve_wit_1_aux.

Definition decimal_to_binary_partial_solve_wit_2 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_full retval 6 )
|--
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 6 )
.

Definition decimal_to_binary_partial_solve_wit_3 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) 6 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (((retval + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 (0 + 1 ) 6 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
.

Definition decimal_to_binary_partial_solve_wit_4 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (1 + 1 ) 6 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (((retval + (2 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 2 (1 + 1 ) 6 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
.

Definition decimal_to_binary_partial_solve_wit_5 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (2 + 1 ) 6 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (((retval + (3 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 3 (2 + 1 ) 6 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
.

Definition decimal_to_binary_partial_solve_wit_6 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (3 + 1 ) 6 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (((retval + (4 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 4 (3 + 1 ) 6 )
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
.

Definition decimal_to_binary_partial_solve_wit_7 := 
forall (decimal_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (CharArray.undef_seg retval (4 + 1 ) 6 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  [| (retval <> 0) |] 
  &&  [| (decimal_pre = 0) |] 
  &&  [| (0 <= decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (problem_79_pre_z decimal_pre ) |]
  &&  (((retval + (5 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 5 (4 + 1 ) 6 )
  **  (((retval + (4 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (3 * sizeof(CHAR) ) )) # Char  |-> 100)
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 98)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
.

Definition decimal_to_binary_partial_solve_wit_8_pure := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) ,
  [| (x <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  ((( &( "decimal" ) )) # Int  |-> decimal_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "total" ) )) # Int  |-> bits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "bits" ) )) # Int  |-> bits)
|--
  [| ((bits + 5 ) > 0) |]
.

Definition decimal_to_binary_partial_solve_wit_8_aux := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) ,
  [| (x <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  emp
|--
  [| ((bits + 5 ) > 0) |] 
  &&  [| (x <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  emp
.

Definition decimal_to_binary_partial_solve_wit_8 := decimal_to_binary_partial_solve_wit_8_pure -> decimal_to_binary_partial_solve_wit_8_aux.

Definition decimal_to_binary_partial_solve_wit_9 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (x <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  (CharArray.undef_full retval (bits + 5 ) )
|--
  [| (retval <> 0) |] 
  &&  [| (x <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 (bits + 5 ) )
.

Definition decimal_to_binary_partial_solve_wit_10 := 
forall (decimal_pre: Z) (bits: Z) (x: Z) (out: Z) (i: Z) (total: Z) (num: Z) (orig: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (x <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) (bits + 5 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
|--
  [| (retval <> 0) |] 
  &&  [| (x <= 0) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (0 <= x) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < INT_MAX) |] 
  &&  [| (binary_count_state_z decimal_pre x bits ) |]
  &&  (((retval + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 (0 + 1 ) (bits + 5 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 100)
.

Definition decimal_to_binary_partial_solve_wit_11 := 
forall (decimal_pre: Z) (out: Z) (i: Z) (bits: Z) (total: Z) (x: Z) (num: Z) (orig: Z) ,
  [| (i < total) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= total) |]
  &&  (CharArray.seg out 2 (i + 2 ) (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg out (i + 2 ) (total + 5 ) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (0 <= 2) |] 
  &&  [| (i < total) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= total) |]
  &&  (((out + ((i + 2 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (i + 2 ) (i + 2 ) (total + 5 ) )
  **  (CharArray.seg out 2 (i + 2 ) (repeat_Z (0) (i)) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
.

Definition decimal_to_binary_partial_solve_wit_12 := 
forall (decimal_pre: Z) (orig: Z) (num: Z) (x: Z) (total: Z) (bits: Z) (i: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 4 ) )
  **  (CharArray.undef_seg out (total + 4 ) (total + 5 ) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (0 <= 2) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  (((out + ((total + 4 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (total + 4 ) (total + 4 ) (total + 5 ) )
  **  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 4 ) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
.

Definition decimal_to_binary_partial_solve_wit_13 := 
forall (decimal_pre: Z) (orig: Z) (num: Z) (x: Z) (total: Z) (bits: Z) (i: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 3 ) )
  **  (CharArray.undef_seg out (total + 3 ) (total + 4 ) )
  **  (CharArray.seg out (total + 4 ) (total + 5 ) (cons (0) (nil)) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (0 <= 2) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  (((out + ((total + 3 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (total + 3 ) (total + 3 ) (total + 4 ) )
  **  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 3 ) )
  **  (CharArray.seg out (total + 4 ) (total + 5 ) (cons (0) (nil)) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
.

Definition decimal_to_binary_partial_solve_wit_14 := 
forall (decimal_pre: Z) (orig: Z) (num: Z) (x: Z) (total: Z) (bits: Z) (i: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.undef_seg out (total + 2 ) (total + 3 ) )
  **  (CharArray.seg out (total + 3 ) (total + 5 ) (cons (98) ((cons (0) (nil)))) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
|--
  [| (0 <= 2) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (num = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (decimal_pre))))) |] 
  &&  [| (bits = total) |] 
  &&  [| (i = total) |]
  &&  (((out + ((total + 2 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (total + 2 ) (total + 2 ) (total + 3 ) )
  **  (CharArray.seg out 2 (total + 2 ) (repeat_Z (0) (total)) )
  **  (CharArray.seg out (total + 3 ) (total + 5 ) (cons (98) ((cons (0) (nil)))) )
  **  (CharArray.full out 2 (cons (100) ((cons (98) (nil)))) )
.

Definition decimal_to_binary_partial_solve_wit_15 := 
forall (decimal_pre: Z) (out_l: (@list Z)) (orig: Z) (x: Z) (num: Z) (i: Z) (total: Z) (bits: Z) (out: Z) ,
  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 < num) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  (CharArray.full out (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (0 <= (total + 5 )) |] 
  &&  [| (0 < decimal_pre) |] 
  &&  [| ((decimal_pre + 5 ) < INT_MAX) |] 
  &&  [| (orig = decimal_pre) |] 
  &&  [| (x = 0) |] 
  &&  [| (0 < num) |] 
  &&  [| (i = (total + 5 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= bits) |] 
  &&  [| (bits < total) |] 
  &&  [| ((Zlength (out_l)) = (total + 4 )) |] 
  &&  [| (decimal_binary_full_state_z orig num (bits + 1 ) out_l ) |]
  &&  (((out + ((bits + 2 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i out (bits + 2 ) 0 (total + 5 ) (app (out_l) ((cons (0) (nil)))) )
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
Axiom proof_of_decimal_to_binary_safety_wit_55 : decimal_to_binary_safety_wit_55.
Axiom proof_of_decimal_to_binary_safety_wit_56 : decimal_to_binary_safety_wit_56.
Axiom proof_of_decimal_to_binary_safety_wit_57 : decimal_to_binary_safety_wit_57.
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
