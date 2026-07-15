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
Require Import coins_65.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function circular_shift -----*)

Definition circular_shift_safety_wit_1 := 
forall (shift_pre: Z) (x_pre: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (problem_65_pre_z x_pre shift_pre )) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  ((( &( "buf" ) )) # Ptr  |->_)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition circular_shift_safety_wit_2 := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (problem_65_pre_z x_pre shift_pre )) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  (CharArray.undef_full retval 64 )
  **  ((( &( "buf" ) )) # Ptr  |-> retval)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition circular_shift_safety_wit_3 := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (problem_65_pre_z x_pre shift_pre )) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  ((( &( "tmp" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval 64 )
  **  ((( &( "buf" ) )) # Ptr  |-> retval)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition circular_shift_safety_wit_4 := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (problem_65_pre_z x_pre shift_pre )) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "tmp" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval 64 )
  **  ((( &( "buf" ) )) # Ptr  |-> retval)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition circular_shift_safety_wit_5 := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (problem_65_pre_z x_pre shift_pre )) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  ((( &( "fill" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "tmp" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval 64 )
  **  ((( &( "buf" ) )) # Ptr  |-> retval)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition circular_shift_safety_wit_6 := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (problem_65_pre_z x_pre shift_pre )) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  ((( &( "fill" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "tmp" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval 64 )
  **  ((( &( "buf" ) )) # Ptr  |-> retval)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition circular_shift_safety_wit_7 := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (x_pre = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  ((( &( "fill" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "tmp" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval 64 )
  **  ((( &( "buf" ) )) # Ptr  |-> retval)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition circular_shift_safety_wit_8 := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (x_pre = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  ((( &( "fill" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "tmp" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval 64 )
  **  ((( &( "buf" ) )) # Ptr  |-> retval)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition circular_shift_safety_wit_9 := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (x_pre = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  (CharArray.undef_seg retval (0 + 1 ) 64 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "fill" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "tmp" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  ((( &( "buf" ) )) # Ptr  |-> retval)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition circular_shift_safety_wit_10 := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (x_pre = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  (CharArray.undef_seg retval (0 + 1 ) 64 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "fill" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "tmp" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  ((( &( "buf" ) )) # Ptr  |-> retval)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition circular_shift_safety_wit_11 := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (x_pre = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  (CharArray.undef_seg retval (1 + 1 ) 64 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "fill" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "tmp" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  ((( &( "buf" ) )) # Ptr  |-> retval)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition circular_shift_safety_wit_12 := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (fill: Z) (i: Z) (n: Z) (tmp: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH6 : (problem_65_pre_z x_pre shift_pre )) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= n)) (PreH9 : (n < 64)) (PreH10 : (i = 0)) (PreH11 : (fill = 0)) (PreH12 : (base_count_state_z_65 x_pre 10 tmp n )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.undef_full buf 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition circular_shift_safety_wit_13 := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (fill: Z) (i: Z) (n: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= n)) (PreH10 : (n < 64)) (PreH11 : (i = 0)) (PreH12 : (fill = 0)) (PreH13 : (base_count_state_z_65 x_pre 10 tmp n )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.undef_full buf 64 )
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n + 1 )) ”
.

Definition circular_shift_safety_wit_14 := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (fill: Z) (i: Z) (n: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= n)) (PreH10 : (n < 64)) (PreH11 : (i = 0)) (PreH12 : (fill = 0)) (PreH13 : (base_count_state_z_65 x_pre 10 tmp n )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.undef_full buf 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition circular_shift_safety_wit_15 := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (fill: Z) (i: Z) (n: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= n)) (PreH10 : (n < 64)) (PreH11 : (i = 0)) (PreH12 : (fill = 0)) (PreH13 : (base_count_state_z_65 x_pre 10 tmp n )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "n" ) )) # Int  |-> (n + 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.undef_full buf 64 )
|--
  “ ((tmp <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition circular_shift_safety_wit_16 := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (fill: Z) (i: Z) (n: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= n)) (PreH10 : (n < 64)) (PreH11 : (i = 0)) (PreH12 : (fill = 0)) (PreH13 : (base_count_state_z_65 x_pre 10 tmp n )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "n" ) )) # Int  |-> (n + 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.undef_full buf 64 )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition circular_shift_safety_wit_17 := 
forall (shift_pre: Z) (x_pre: Z) (n: Z) (tmp: Z) (i: Z) (fill: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (tmp = 0)) (PreH9 : (i = 0)) (PreH10 : (fill = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.undef_full buf 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition circular_shift_safety_wit_18 := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (i: Z) (fill: Z) (tmp: Z) (n: Z) (PreH1 : (i <= n)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (tmp = 0)) (PreH10 : (fill = 0)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n + 1 ))) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf i (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg buf i 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition circular_shift_safety_wit_19 := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (i: Z) (fill: Z) (tmp: Z) (n: Z) (PreH1 : (i <= n)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (tmp = 0)) (PreH10 : (fill = 0)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n + 1 ))) ,
  (CharArray.full buf (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (i + 1 ) 64 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition circular_shift_safety_wit_20 := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (out_l: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (n: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (i = (n + 1 ))) (PreH9 : (0 <= tmp)) (PreH10 : (0 <= fill)) (PreH11 : (fill <= n)) (PreH12 : ((Zlength (out_l)) = n)) (PreH13 : (base_fill_full_state_z_65 x_pre 10 tmp fill out_l )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition circular_shift_safety_wit_21 := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (out_l: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (n: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (i = (n + 1 ))) (PreH10 : (0 <= tmp)) (PreH11 : (0 <= fill)) (PreH12 : (fill <= n)) (PreH13 : ((Zlength (out_l)) = n)) (PreH14 : (base_fill_full_state_z_65 x_pre 10 tmp fill out_l )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ ((fill - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (fill - 1 )) ”
.

Definition circular_shift_safety_wit_22 := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (out_l: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (n: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (i = (n + 1 ))) (PreH10 : (0 <= tmp)) (PreH11 : (0 <= fill)) (PreH12 : (fill <= n)) (PreH13 : ((Zlength (out_l)) = n)) (PreH14 : (base_fill_full_state_z_65 x_pre 10 tmp fill out_l )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition circular_shift_safety_wit_23 := 
(
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (n: Z) (i: Z) (tmp: Z) (fill: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (i = (n + 1 ))) (PreH9 : (0 < tmp)) (PreH10 : (0 <= fill)) (PreH11 : (fill < n)) (PreH12 : ((Zlength (out_l)) = n)) (PreH13 : (base_fill_full_state_z_65 x_pre 10 tmp (fill + 1 ) out_l )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ ((48 + (tmp % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (48 + (tmp % ( 10 ) ) )) ”
) \/
(
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (n: Z) (i: Z) (tmp: Z) (fill: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (i = (n + 1 ))) (PreH9 : (0 < tmp)) (PreH10 : (0 <= fill)) (PreH11 : (fill < n)) (PreH12 : ((Zlength (out_l)) = n)) (PreH13 : (base_fill_full_state_z_65 x_pre 10 tmp (fill + 1 ) out_l )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ ((48 + (tmp % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (48 + (tmp % ( 10 ) ) )) ”
).

Definition circular_shift_safety_wit_23_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (n: Z) (i: Z) (tmp: Z) (fill: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (i = (n + 1 ))) (PreH9 : (0 < tmp)) (PreH10 : (0 <= fill)) (PreH11 : (fill < n)) (PreH12 : ((Zlength (out_l)) = n)) (PreH13 : (base_fill_full_state_z_65 x_pre 10 tmp (fill + 1 ) out_l )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ ((48 + (tmp % ( 10 ) ) ) <= INT_MAX) ”
.

Definition circular_shift_safety_wit_23_split_goal_2 := 
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (n: Z) (i: Z) (tmp: Z) (fill: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (i = (n + 1 ))) (PreH9 : (0 < tmp)) (PreH10 : (0 <= fill)) (PreH11 : (fill < n)) (PreH12 : ((Zlength (out_l)) = n)) (PreH13 : (base_fill_full_state_z_65 x_pre 10 tmp (fill + 1 ) out_l )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ ((INT_MIN) <= (48 + (tmp % ( 10 ) ) )) ”
.

Definition circular_shift_safety_wit_24 := 
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (n: Z) (i: Z) (tmp: Z) (fill: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (i = (n + 1 ))) (PreH9 : (0 < tmp)) (PreH10 : (0 <= fill)) (PreH11 : (fill < n)) (PreH12 : ((Zlength (out_l)) = n)) (PreH13 : (base_fill_full_state_z_65 x_pre 10 tmp (fill + 1 ) out_l )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ ((tmp <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition circular_shift_safety_wit_25 := 
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (n: Z) (i: Z) (tmp: Z) (fill: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (i = (n + 1 ))) (PreH9 : (0 < tmp)) (PreH10 : (0 <= fill)) (PreH11 : (fill < n)) (PreH12 : ((Zlength (out_l)) = n)) (PreH13 : (base_fill_full_state_z_65 x_pre 10 tmp (fill + 1 ) out_l )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition circular_shift_safety_wit_26 := 
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (n: Z) (i: Z) (tmp: Z) (fill: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (i = (n + 1 ))) (PreH9 : (0 < tmp)) (PreH10 : (0 <= fill)) (PreH11 : (fill < n)) (PreH12 : ((Zlength (out_l)) = n)) (PreH13 : (base_fill_full_state_z_65 x_pre 10 tmp (fill + 1 ) out_l )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition circular_shift_safety_wit_27 := 
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (n: Z) (i: Z) (tmp: Z) (fill: Z) (buf: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (i = (n + 1 ))) (PreH10 : (0 < tmp)) (PreH11 : (0 <= fill)) (PreH12 : (fill < n)) (PreH13 : ((Zlength (out_l)) = n)) (PreH14 : (base_fill_full_state_z_65 x_pre 10 tmp (fill + 1 ) out_l )) ,
  (CharArray.full buf (n + 1 ) (replace_Znth (fill) ((signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8))) ((app (out_l) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ ((tmp <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition circular_shift_safety_wit_28 := 
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (n: Z) (i: Z) (tmp: Z) (fill: Z) (buf: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (i = (n + 1 ))) (PreH10 : (0 < tmp)) (PreH11 : (0 <= fill)) (PreH12 : (fill < n)) (PreH13 : ((Zlength (out_l)) = n)) (PreH14 : (base_fill_full_state_z_65 x_pre 10 tmp (fill + 1 ) out_l )) ,
  (CharArray.full buf (n + 1 ) (replace_Znth (fill) ((signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8))) ((app (out_l) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition circular_shift_safety_wit_29 := 
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (buf: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (0 <= tmp)) (PreH6 : (0 <= i)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (problem_65_pre_z x_pre shift_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n + 1 )) ”
.

Definition circular_shift_safety_wit_30 := 
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (buf: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (0 <= tmp)) (PreH6 : (0 <= i)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (problem_65_pre_z x_pre shift_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition circular_shift_safety_wit_31 := 
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (buf: Z) (retval: Z) (PreH1 : (n < shift_pre)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (0 <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : (0 <= shift_pre)) (PreH7 : (shift_pre <= INT_MAX)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= i)) (PreH10 : (0 <= fill)) (PreH11 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH12 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH13 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.undef_full retval (n + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition circular_shift_safety_wit_32 := 
forall (shift_pre: Z) (x_pre: Z) (out: Z) (buf: Z) (out_l: (@list Z)) (n: Z) (fill: Z) (i: Z) (tmp: Z) (PreH1 : (i < n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= i)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n < shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l )) (PreH15 : ((Zlength (out_l)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((n - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n - 1 ) - i )) ”
.

Definition circular_shift_safety_wit_33 := 
forall (shift_pre: Z) (x_pre: Z) (out: Z) (buf: Z) (out_l: (@list Z)) (n: Z) (fill: Z) (i: Z) (tmp: Z) (PreH1 : (i < n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= i)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n < shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l )) (PreH15 : ((Zlength (out_l)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition circular_shift_safety_wit_34 := 
forall (shift_pre: Z) (x_pre: Z) (out: Z) (buf: Z) (out_l: (@list Z)) (n: Z) (fill: Z) (i: Z) (tmp: Z) (PreH1 : (i < n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= i)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n < shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l )) (PreH15 : ((Zlength (out_l)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition circular_shift_safety_wit_35 := 
forall (shift_pre: Z) (x_pre: Z) (out: Z) (buf: Z) (out_l: (@list Z)) (n: Z) (fill: Z) (i: Z) (tmp: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < n)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= i)) (PreH9 : (0 <= fill)) (PreH10 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH11 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH12 : (n < shift_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l )) (PreH16 : ((Zlength (out_l)) = i)) (PreH17 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((Znth ((n - 1 ) - i ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition circular_shift_safety_wit_36 := 
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (buf: Z) (retval: Z) (PreH1 : (n >= shift_pre)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (0 <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : (0 <= shift_pre)) (PreH7 : (shift_pre <= INT_MAX)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= i)) (PreH10 : (0 <= fill)) (PreH11 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH12 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH13 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.undef_full retval (n + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition circular_shift_safety_wit_37 := 
forall (shift_pre: Z) (x_pre: Z) (out: Z) (buf: Z) (out_l: (@list Z)) (i: Z) (n: Z) (fill: Z) (tmp: Z) (PreH1 : (i < n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (n >= shift_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l )) (PreH14 : ((Zlength (out_l)) = i)) (PreH15 : (problem_65_pre_z x_pre shift_pre )) ,
  ((( &( "src" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (((n - shift_pre ) + i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n - shift_pre ) + i )) ”
.

Definition circular_shift_safety_wit_38 := 
forall (shift_pre: Z) (x_pre: Z) (out: Z) (buf: Z) (out_l: (@list Z)) (i: Z) (n: Z) (fill: Z) (tmp: Z) (PreH1 : (i < n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (n >= shift_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l )) (PreH14 : ((Zlength (out_l)) = i)) (PreH15 : (problem_65_pre_z x_pre shift_pre )) ,
  ((( &( "src" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((n - shift_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - shift_pre )) ”
.

Definition circular_shift_safety_wit_39 := 
forall (shift_pre: Z) (x_pre: Z) (out: Z) (buf: Z) (out_l: (@list Z)) (i: Z) (n: Z) (fill: Z) (tmp: Z) (PreH1 : (((n - shift_pre ) + i ) >= n)) (PreH2 : (i < n)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n >= shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l )) (PreH15 : ((Zlength (out_l)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  ((( &( "src" ) )) # Int  |-> ((n - shift_pre ) + i ))
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ ((((n - shift_pre ) + i ) - n ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((n - shift_pre ) + i ) - n )) ”
.

Definition circular_shift_safety_wit_40 := 
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (tmp: Z) (fill: Z) (n: Z) (i: Z) (src: Z) (buf: Z) (out: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (n >= shift_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n)) (PreH13 : (0 <= src)) (PreH14 : (src < n)) (PreH15 : (src = (((n - shift_pre ) + i ) % ( n ) ))) (PreH16 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l )) (PreH17 : ((Zlength (out_l)) = i)) (PreH18 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((Znth src (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition circular_shift_safety_wit_41 := 
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (tmp: Z) (fill: Z) (i: Z) (n: Z) (buf: Z) (out: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (0 <= tmp)) (PreH6 : (0 <= fill)) (PreH7 : (i = n)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (circular_shift_prefix_z_65 x_pre shift_pre n out_l )) (PreH11 : (out_l = (circular_shift_output_z_65 (x_pre) (shift_pre)))) (PreH12 : ((Zlength (out_l)) = n)) (PreH13 : (problem_65_pre_z x_pre shift_pre )) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out n out_l )
  **  (CharArray.undef_seg out n (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition circular_shift_entail_wit_1 := 
(
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (x_pre = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  (CharArray.undef_seg retval (1 + 1 ) 64 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  “ (x_pre = 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (CharArray.full retval (1 + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg retval (1 + 1 ) 64 )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (x_pre = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  “ (1 = (Zlength ((decimal_digits_z_65 (x_pre))))) ”
  &&  (CharArray.full retval (1 + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
).

Definition circular_shift_entail_wit_1_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (x_pre = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  “ (1 = (Zlength ((decimal_digits_z_65 (x_pre))))) ”
.

Definition circular_shift_entail_wit_1_split_goal_spatial := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (x_pre = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  (CharArray.full retval (1 + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
.

Definition circular_shift_entail_wit_2 := 
(
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  (CharArray.undef_full retval 64 )
|--
  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 64) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (base_count_state_z_65 x_pre 10 x_pre 0 ) ”
  &&  (CharArray.undef_full retval 64 )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  (CharArray.undef_full retval 64 )
|--
  “ (base_count_state_z_65 x_pre 10 x_pre 0 ) ”
  &&  (CharArray.undef_full retval 64 )
).

Definition circular_shift_entail_wit_2_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  (CharArray.undef_full retval 64 )
|--
  “ (base_count_state_z_65 x_pre 10 x_pre 0 ) ”
.

Definition circular_shift_entail_wit_2_split_goal_spatial := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  (CharArray.undef_full retval 64 )
|--
  (CharArray.undef_full retval 64 )
.

Definition circular_shift_entail_wit_3 := 
(
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (fill: Z) (i: Z) (n: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= n)) (PreH10 : (n < 64)) (PreH11 : (i = 0)) (PreH12 : (fill = 0)) (PreH13 : (base_count_state_z_65 x_pre 10 tmp n )) ,
  (CharArray.undef_full buf 64 )
|--
  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (0 <= (tmp ÷ 10 )) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ ((n + 1 ) < 64) ” 
  &&  “ (i = 0) ” 
  &&  “ (fill = 0) ” 
  &&  “ (base_count_state_z_65 x_pre 10 (tmp ÷ 10 ) (n + 1 ) ) ”
  &&  (CharArray.undef_full buf 64 )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (fill: Z) (i: Z) (n: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= n)) (PreH10 : (n < 64)) (PreH11 : (i = 0)) (PreH12 : (fill = 0)) (PreH13 : (base_count_state_z_65 x_pre 10 tmp n )) ,
  (CharArray.undef_full buf 64 )
|--
  “ (base_count_state_z_65 x_pre 10 (tmp ÷ 10 ) (n + 1 ) ) ” 
  &&  “ ((n + 1 ) < 64) ” 
  &&  “ (0 <= (tmp ÷ 10 )) ”
  &&  (CharArray.undef_full buf 64 )
).

Definition circular_shift_entail_wit_3_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (fill: Z) (i: Z) (n: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= n)) (PreH10 : (n < 64)) (PreH11 : (i = 0)) (PreH12 : (fill = 0)) (PreH13 : (base_count_state_z_65 x_pre 10 tmp n )) ,
  (CharArray.undef_full buf 64 )
|--
  “ (base_count_state_z_65 x_pre 10 (tmp ÷ 10 ) (n + 1 ) ) ”
.

Definition circular_shift_entail_wit_3_split_goal_2 := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (fill: Z) (i: Z) (n: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= n)) (PreH10 : (n < 64)) (PreH11 : (i = 0)) (PreH12 : (fill = 0)) (PreH13 : (base_count_state_z_65 x_pre 10 tmp n )) ,
  (CharArray.undef_full buf 64 )
|--
  “ ((n + 1 ) < 64) ”
.

Definition circular_shift_entail_wit_3_split_goal_3 := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (fill: Z) (i: Z) (n: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= n)) (PreH10 : (n < 64)) (PreH11 : (i = 0)) (PreH12 : (fill = 0)) (PreH13 : (base_count_state_z_65 x_pre 10 tmp n )) ,
  (CharArray.undef_full buf 64 )
|--
  “ (0 <= (tmp ÷ 10 )) ”
.

Definition circular_shift_entail_wit_3_split_goal_spatial := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (fill: Z) (i: Z) (n: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= n)) (PreH10 : (n < 64)) (PreH11 : (i = 0)) (PreH12 : (fill = 0)) (PreH13 : (base_count_state_z_65 x_pre 10 tmp n )) ,
  (CharArray.undef_full buf 64 )
|--
  (CharArray.undef_full buf 64 )
.

Definition circular_shift_entail_wit_4 := 
(
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (fill: Z) (i: Z) (n: Z) (tmp: Z) (PreH1 : (tmp <= 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= n)) (PreH10 : (n < 64)) (PreH11 : (i = 0)) (PreH12 : (fill = 0)) (PreH13 : (base_count_state_z_65 x_pre 10 tmp n )) ,
  (CharArray.undef_full buf 64 )
|--
  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (fill = 0) ”
  &&  (CharArray.undef_full buf 64 )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (fill: Z) (i: Z) (n: Z) (tmp: Z) (PreH1 : (tmp <= 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= n)) (PreH10 : (n < 64)) (PreH11 : (i = 0)) (PreH12 : (fill = 0)) (PreH13 : (base_count_state_z_65 x_pre 10 tmp n )) ,
  (CharArray.undef_full buf 64 )
|--
  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ”
  &&  (CharArray.undef_full buf 64 )
).

Definition circular_shift_entail_wit_4_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (fill: Z) (i: Z) (n: Z) (tmp: Z) (PreH1 : (tmp <= 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= n)) (PreH10 : (n < 64)) (PreH11 : (i = 0)) (PreH12 : (fill = 0)) (PreH13 : (base_count_state_z_65 x_pre 10 tmp n )) ,
  (CharArray.undef_full buf 64 )
|--
  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ”
.

Definition circular_shift_entail_wit_4_split_goal_spatial := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (fill: Z) (i: Z) (n: Z) (tmp: Z) (PreH1 : (tmp <= 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= n)) (PreH10 : (n < 64)) (PreH11 : (i = 0)) (PreH12 : (fill = 0)) (PreH13 : (base_count_state_z_65 x_pre 10 tmp n )) ,
  (CharArray.undef_full buf 64 )
|--
  (CharArray.undef_full buf 64 )
.

Definition circular_shift_entail_wit_5 := 
(
forall (shift_pre: Z) (x_pre: Z) (n: Z) (tmp: Z) (i: Z) (fill: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (tmp = 0)) (PreH9 : (i = 0)) (PreH10 : (fill = 0)) ,
  (CharArray.undef_full buf 64 )
|--
  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (fill = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n + 1 )) ”
  &&  (CharArray.full buf 0 (repeat_Z (0) (0)) )
  **  (CharArray.undef_seg buf 0 64 )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (n: Z) (tmp: Z) (i: Z) (fill: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (tmp = 0)) (PreH9 : (i = 0)) (PreH10 : (fill = 0)) ,
  (CharArray.undef_full buf 64 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ ((repeat_Z (0) (0)) = (@nil Z)) ”
  &&  (CharArray.undef_full buf 64 )
).

Definition circular_shift_entail_wit_5_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (n: Z) (tmp: Z) (i: Z) (fill: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (tmp = 0)) (PreH9 : (i = 0)) (PreH10 : (fill = 0)) ,
  (CharArray.undef_full buf 64 )
|--
  “ (0 <= (n + 1 )) ”
.

Definition circular_shift_entail_wit_5_split_goal_2 := 
forall (shift_pre: Z) (x_pre: Z) (n: Z) (tmp: Z) (i: Z) (fill: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (tmp = 0)) (PreH9 : (i = 0)) (PreH10 : (fill = 0)) ,
  (CharArray.undef_full buf 64 )
|--
  “ ((repeat_Z (0) (0)) = (@nil Z)) ”
.

Definition circular_shift_entail_wit_5_split_goal_spatial := 
forall (shift_pre: Z) (x_pre: Z) (n: Z) (tmp: Z) (i: Z) (fill: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (tmp = 0)) (PreH9 : (i = 0)) (PreH10 : (fill = 0)) ,
  (CharArray.undef_full buf 64 )
|--
  (CharArray.undef_full buf 64 )
.

Definition circular_shift_entail_wit_6 := 
(
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (i: Z) (fill: Z) (tmp: Z) (n: Z) (PreH1 : (i <= n)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (tmp = 0)) (PreH10 : (fill = 0)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n + 1 ))) ,
  (CharArray.full buf (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (i + 1 ) 64 )
|--
  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (fill = 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ”
  &&  (CharArray.full buf (i + 1 ) (repeat_Z (0) ((i + 1 ))) )
  **  (CharArray.undef_seg buf (i + 1 ) 64 )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (i: Z) (fill: Z) (tmp: Z) (n: Z) (PreH1 : (i <= n)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (tmp = 0)) (PreH10 : (fill = 0)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n + 1 ))) ,
  TT && emp 
|--
  “ ((app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) = (repeat_Z (0) ((i + 1 )))) ”
  &&  emp
).

Definition circular_shift_entail_wit_6_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (i: Z) (fill: Z) (tmp: Z) (n: Z) (PreH1 : (i <= n)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (tmp = 0)) (PreH10 : (fill = 0)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n + 1 ))) ,
  TT && emp 
|--
  “ ((app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) = (repeat_Z (0) ((i + 1 )))) ”
.

Definition circular_shift_entail_wit_7 := 
(
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (i: Z) (fill: Z) (tmp: Z) (n: Z) (PreH1 : (i > n)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (tmp = 0)) (PreH10 : (fill = 0)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n + 1 ))) ,
  (CharArray.full buf i (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg buf i 64 )
|--
  EX (out_l: (@list Z)) ,
  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (i = (n + 1 )) ” 
  &&  “ (fill = 0) ” 
  &&  “ ((Zlength (out_l)) = n) ” 
  &&  “ (base_fill_full_state_z_65 x_pre 10 x_pre n out_l ) ”
  &&  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (i: Z) (fill: Z) (tmp: Z) (n: Z) (PreH1 : (i > n)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (tmp = 0)) (PreH10 : (fill = 0)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n + 1 ))) ,
  (CharArray.full buf i (repeat_Z (0) (i)) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (i = (n + 1 )) ” 
  &&  “ (fill = 0) ” 
  &&  “ ((Zlength (out_l)) = n) ” 
  &&  “ (base_fill_full_state_z_65 x_pre 10 x_pre n out_l ) ”
  &&  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
).

Definition circular_shift_entail_wit_8 := 
(
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (n: Z) (tmp: Z) (i: Z) (fill: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (tmp = 0)) (PreH9 : (i = (n + 1 ))) (PreH10 : (fill = 0)) (PreH11 : ((Zlength (out_l_2)) = n)) (PreH12 : (base_fill_full_state_z_65 x_pre 10 x_pre n out_l_2 )) ,
  (CharArray.full buf (n + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  EX (out_l: (@list Z)) ,
  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (i = (n + 1 )) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n) ” 
  &&  “ ((Zlength (out_l)) = n) ” 
  &&  “ (base_fill_full_state_z_65 x_pre 10 x_pre n out_l ) ”
  &&  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (n: Z) (tmp: Z) (i: Z) (fill: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (tmp = 0)) (PreH9 : (i = (n + 1 ))) (PreH10 : (fill = 0)) (PreH11 : ((Zlength (out_l_2)) = n)) (PreH12 : (base_fill_full_state_z_65 x_pre 10 x_pre n out_l_2 )) ,
  TT && emp 
|--
  EX (out_l: (@list Z)) ,
  “ ((app (out_l_2) ((cons (0) ((@nil Z))))) = (app (out_l) ((cons (0) ((@nil Z)))))) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (i = (n + 1 )) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n) ” 
  &&  “ ((Zlength (out_l)) = n) ” 
  &&  “ (base_fill_full_state_z_65 x_pre 10 x_pre n out_l ) ”
  &&  emp
).

Definition circular_shift_entail_wit_9 := 
(
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (out_l_2: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (n: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (i = (n + 1 ))) (PreH10 : (0 <= tmp)) (PreH11 : (0 <= fill)) (PreH12 : (fill <= n)) (PreH13 : ((Zlength (out_l_2)) = n)) (PreH14 : (base_fill_full_state_z_65 x_pre 10 tmp fill out_l_2 )) ,
  (CharArray.full buf (n + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  EX (out_l: (@list Z)) ,
  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (i = (n + 1 )) ” 
  &&  “ (0 < tmp) ” 
  &&  “ (0 <= (fill - 1 )) ” 
  &&  “ ((fill - 1 ) < n) ” 
  &&  “ ((Zlength (out_l)) = n) ” 
  &&  “ (base_fill_full_state_z_65 x_pre 10 tmp ((fill - 1 ) + 1 ) out_l ) ”
  &&  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (n: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (i = (n + 1 ))) (PreH10 : (0 <= tmp)) (PreH11 : (0 <= fill)) (PreH12 : (fill <= n)) (PreH13 : ((Zlength (out_l_2)) = n)) (PreH14 : (base_fill_full_state_z_65 x_pre 10 tmp fill out_l_2 )) ,
  TT && emp 
|--
  EX (out_l: (@list Z)) ,
  “ ((app (out_l_2) ((cons (0) ((@nil Z))))) = (app (out_l) ((cons (0) ((@nil Z)))))) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (i = (n + 1 )) ” 
  &&  “ (0 < tmp) ” 
  &&  “ (0 <= (fill - 1 )) ” 
  &&  “ ((fill - 1 ) < n) ” 
  &&  “ ((Zlength (out_l)) = n) ” 
  &&  “ (base_fill_full_state_z_65 x_pre 10 tmp ((fill - 1 ) + 1 ) out_l ) ”
  &&  emp
).

Definition circular_shift_entail_wit_10 := 
(
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (n: Z) (i: Z) (tmp: Z) (fill: Z) (buf: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (i = (n + 1 ))) (PreH10 : (0 < tmp)) (PreH11 : (0 <= fill)) (PreH12 : (fill < n)) (PreH13 : ((Zlength (out_l_2)) = n)) (PreH14 : (base_fill_full_state_z_65 x_pre 10 tmp (fill + 1 ) out_l_2 )) ,
  (CharArray.full buf (n + 1 ) (replace_Znth (fill) ((signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8))) ((app (out_l_2) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  EX (out_l: (@list Z)) ,
  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (i = (n + 1 )) ” 
  &&  “ (0 <= (tmp ÷ 10 )) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= n) ” 
  &&  “ ((Zlength (out_l)) = n) ” 
  &&  “ (base_fill_full_state_z_65 x_pre 10 (tmp ÷ 10 ) fill out_l ) ”
  &&  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (n: Z) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (i = (n + 1 ))) (PreH10 : (0 < tmp)) (PreH11 : (0 <= fill)) (PreH12 : (fill < n)) (PreH13 : ((Zlength (out_l_2)) = n)) (PreH14 : (base_fill_full_state_z_65 x_pre 10 tmp (fill + 1 ) out_l_2 )) ,
  TT && emp 
|--
  EX (out_l: (@list Z)) ,
  “ ((replace_Znth (fill) ((signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8))) ((app (out_l_2) ((cons (0) ((@nil Z))))))) = (app (out_l) ((cons (0) ((@nil Z)))))) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (i = (n + 1 )) ” 
  &&  “ (0 <= (tmp ÷ 10 )) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= n) ” 
  &&  “ ((Zlength (out_l)) = n) ” 
  &&  “ (base_fill_full_state_z_65 x_pre 10 (tmp ÷ 10 ) fill out_l ) ”
  &&  emp
).

Definition circular_shift_entail_wit_11 := 
(
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (out_l_2: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (n: Z) (PreH1 : (tmp <= 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (i = (n + 1 ))) (PreH10 : (0 <= tmp)) (PreH11 : (0 <= fill)) (PreH12 : (fill <= n)) (PreH13 : ((Zlength (out_l_2)) = n)) (PreH14 : (base_fill_full_state_z_65 x_pre 10 tmp fill out_l_2 )) ,
  (CharArray.full buf (n + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  EX (out_l: (@list Z)) ,
  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (fill = 0) ” 
  &&  “ (i = (n + 1 )) ” 
  &&  “ (out_l = (decimal_digits_z_65 (x_pre))) ” 
  &&  “ ((Zlength (out_l)) = n) ”
  &&  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (n: Z) (PreH1 : (tmp <= 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (i = (n + 1 ))) (PreH10 : (0 <= tmp)) (PreH11 : (0 <= fill)) (PreH12 : (fill <= n)) (PreH13 : ((Zlength (out_l_2)) = n)) (PreH14 : (base_fill_full_state_z_65 x_pre 10 tmp fill out_l_2 )) ,
  TT && emp 
|--
  “ (fill = 0) ” 
  &&  “ ((app (out_l_2) ((cons (0) ((@nil Z))))) = (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z)))))) ”
  &&  emp
).

Definition circular_shift_entail_wit_11_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (n: Z) (PreH1 : (tmp <= 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (i = (n + 1 ))) (PreH10 : (0 <= tmp)) (PreH11 : (0 <= fill)) (PreH12 : (fill <= n)) (PreH13 : ((Zlength (out_l_2)) = n)) (PreH14 : (base_fill_full_state_z_65 x_pre 10 tmp fill out_l_2 )) ,
  TT && emp 
|--
  “ (fill = 0) ”
.

Definition circular_shift_entail_wit_11_split_goal_2 := 
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (n: Z) (PreH1 : (tmp <= 0)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (i = (n + 1 ))) (PreH10 : (0 <= tmp)) (PreH11 : (0 <= fill)) (PreH12 : (fill <= n)) (PreH13 : ((Zlength (out_l_2)) = n)) (PreH14 : (base_fill_full_state_z_65 x_pre 10 tmp fill out_l_2 )) ,
  TT && emp 
|--
  “ ((app (out_l_2) ((cons (0) ((@nil Z))))) = (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z)))))) ”
.

Definition circular_shift_entail_wit_12_1 := 
(
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (n: Z) (tmp: Z) (fill: Z) (i: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (tmp = 0)) (PreH9 : (fill = 0)) (PreH10 : (i = (n + 1 ))) (PreH11 : (out_l = (decimal_digits_z_65 (x_pre)))) (PreH12 : ((Zlength (out_l)) = n)) ,
  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (n: Z) (tmp: Z) (fill: Z) (i: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (tmp = 0)) (PreH9 : (fill = 0)) (PreH10 : (i = (n + 1 ))) (PreH11 : (out_l = (decimal_digits_z_65 (x_pre)))) (PreH12 : ((Zlength (out_l)) = n)) ,
  TT && emp 
|--
  “ (0 <= i) ”
  &&  emp
).

Definition circular_shift_entail_wit_12_1_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (n: Z) (tmp: Z) (fill: Z) (i: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (tmp = 0)) (PreH9 : (fill = 0)) (PreH10 : (i = (n + 1 ))) (PreH11 : (out_l = (decimal_digits_z_65 (x_pre)))) (PreH12 : ((Zlength (out_l)) = n)) ,
  TT && emp 
|--
  “ (0 <= i) ”
.

Definition circular_shift_entail_wit_12_2 := 
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (buf: Z) (PreH1 : (x_pre = 0)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (tmp = 0)) (PreH7 : (i = 0)) (PreH8 : (fill = 0)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
.

Definition circular_shift_entail_wit_13 := 
(
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (buf: Z) (retval: Z) (PreH1 : (n < shift_pre)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (0 <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : (0 <= shift_pre)) (PreH7 : (shift_pre <= INT_MAX)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= i)) (PreH10 : (0 <= fill)) (PreH11 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH12 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH13 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.undef_full retval (n + 1 ) )
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (n < shift_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre 0 out_l ) ” 
  &&  “ ((Zlength (out_l)) = 0) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (n + 1 ) )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (retval: Z) (PreH1 : (n < shift_pre)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (0 <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : (0 <= shift_pre)) (PreH7 : (shift_pre <= INT_MAX)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= i)) (PreH10 : (0 <= fill)) (PreH11 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH12 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH13 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.undef_full retval (n + 1 ) )
|--
  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre 0 (@nil Z) ) ” 
  &&  “ (0 <= n) ”
  &&  (CharArray.undef_full retval (n + 1 ) )
).

Definition circular_shift_entail_wit_13_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (retval: Z) (PreH1 : (n < shift_pre)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (0 <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : (0 <= shift_pre)) (PreH7 : (shift_pre <= INT_MAX)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= i)) (PreH10 : (0 <= fill)) (PreH11 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH12 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH13 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.undef_full retval (n + 1 ) )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition circular_shift_entail_wit_13_split_goal_2 := 
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (retval: Z) (PreH1 : (n < shift_pre)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (0 <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : (0 <= shift_pre)) (PreH7 : (shift_pre <= INT_MAX)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= i)) (PreH10 : (0 <= fill)) (PreH11 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH12 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH13 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.undef_full retval (n + 1 ) )
|--
  “ (circular_shift_prefix_z_65 x_pre shift_pre 0 (@nil Z) ) ”
.

Definition circular_shift_entail_wit_13_split_goal_3 := 
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (retval: Z) (PreH1 : (n < shift_pre)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (0 <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : (0 <= shift_pre)) (PreH7 : (shift_pre <= INT_MAX)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= i)) (PreH10 : (0 <= fill)) (PreH11 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH12 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH13 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.undef_full retval (n + 1 ) )
|--
  “ (0 <= n) ”
.

Definition circular_shift_entail_wit_13_split_goal_spatial := 
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (retval: Z) (PreH1 : (n < shift_pre)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (0 <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : (0 <= shift_pre)) (PreH7 : (shift_pre <= INT_MAX)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= i)) (PreH10 : (0 <= fill)) (PreH11 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH12 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH13 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.undef_full retval (n + 1 ) )
|--
  (CharArray.undef_full retval (n + 1 ) )
.

Definition circular_shift_entail_wit_14 := 
(
forall (shift_pre: Z) (x_pre: Z) (out: Z) (buf: Z) (out_l_2: (@list Z)) (n: Z) (fill: Z) (i: Z) (tmp: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < n)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= i)) (PreH9 : (0 <= fill)) (PreH10 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH11 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH12 : (n < shift_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = i)) (PreH17 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((Znth ((n - 1 ) - i ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (n < shift_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre (i + 1 ) out_l ) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (n: Z) (fill: Z) (i: Z) (tmp: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < n)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= i)) (PreH9 : (0 <= fill)) (PreH10 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH11 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH12 : (n < shift_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = i)) (PreH17 : (problem_65_pre_z x_pre shift_pre )) ,
  TT && emp 
|--
  “ ((Zlength ((app (out_l_2) ((cons ((Znth ((n - 1 ) - i ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre (i + 1 ) (app (out_l_2) ((cons ((Znth ((n - 1 ) - i ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) ) ”
  &&  emp
).

Definition circular_shift_entail_wit_14_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (n: Z) (fill: Z) (i: Z) (tmp: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < n)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= i)) (PreH9 : (0 <= fill)) (PreH10 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH11 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH12 : (n < shift_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = i)) (PreH17 : (problem_65_pre_z x_pre shift_pre )) ,
  TT && emp 
|--
  “ ((Zlength ((app (out_l_2) ((cons ((Znth ((n - 1 ) - i ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))))) = (i + 1 )) ”
.

Definition circular_shift_entail_wit_14_split_goal_2 := 
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (n: Z) (fill: Z) (i: Z) (tmp: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (i < n)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= i)) (PreH9 : (0 <= fill)) (PreH10 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH11 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH12 : (n < shift_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= n)) (PreH15 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH16 : ((Zlength (out_l_2)) = i)) (PreH17 : (problem_65_pre_z x_pre shift_pre )) ,
  TT && emp 
|--
  “ (circular_shift_prefix_z_65 x_pre shift_pre (i + 1 ) (app (out_l_2) ((cons ((Znth ((n - 1 ) - i ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) ) ”
.

Definition circular_shift_entail_wit_15 := 
(
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (buf: Z) (retval: Z) (PreH1 : (n >= shift_pre)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (0 <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : (0 <= shift_pre)) (PreH7 : (shift_pre <= INT_MAX)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= i)) (PreH10 : (0 <= fill)) (PreH11 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH12 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH13 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.undef_full retval (n + 1 ) )
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (n >= shift_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre 0 out_l ) ” 
  &&  “ ((Zlength (out_l)) = 0) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (n + 1 ) )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (retval: Z) (PreH1 : (n >= shift_pre)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (0 <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : (0 <= shift_pre)) (PreH7 : (shift_pre <= INT_MAX)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= i)) (PreH10 : (0 <= fill)) (PreH11 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH12 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH13 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.undef_full retval (n + 1 ) )
|--
  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre 0 (@nil Z) ) ”
  &&  (CharArray.undef_full retval (n + 1 ) )
).

Definition circular_shift_entail_wit_15_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (retval: Z) (PreH1 : (n >= shift_pre)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (0 <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : (0 <= shift_pre)) (PreH7 : (shift_pre <= INT_MAX)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= i)) (PreH10 : (0 <= fill)) (PreH11 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH12 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH13 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.undef_full retval (n + 1 ) )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition circular_shift_entail_wit_15_split_goal_2 := 
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (retval: Z) (PreH1 : (n >= shift_pre)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (0 <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : (0 <= shift_pre)) (PreH7 : (shift_pre <= INT_MAX)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= i)) (PreH10 : (0 <= fill)) (PreH11 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH12 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH13 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.undef_full retval (n + 1 ) )
|--
  “ (circular_shift_prefix_z_65 x_pre shift_pre 0 (@nil Z) ) ”
.

Definition circular_shift_entail_wit_15_split_goal_spatial := 
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (retval: Z) (PreH1 : (n >= shift_pre)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (0 <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : (0 <= shift_pre)) (PreH7 : (shift_pre <= INT_MAX)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= i)) (PreH10 : (0 <= fill)) (PreH11 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH12 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH13 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.undef_full retval (n + 1 ) )
|--
  (CharArray.undef_full retval (n + 1 ) )
.

Definition circular_shift_entail_wit_16_1 := 
(
forall (shift_pre: Z) (x_pre: Z) (out: Z) (buf: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (fill: Z) (tmp: Z) (PreH1 : (((n - shift_pre ) + i ) < n)) (PreH2 : (i < n)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n >= shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out i out_l_2 )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (n >= shift_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= ((n - shift_pre ) + i )) ” 
  &&  “ (((n - shift_pre ) + i ) < n) ” 
  &&  “ (((n - shift_pre ) + i ) = (((n - shift_pre ) + i ) % ( n ) )) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre i out_l ) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (fill: Z) (tmp: Z) (PreH1 : (((n - shift_pre ) + i ) < n)) (PreH2 : (i < n)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n >= shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  TT && emp 
|--
  “ (((n - shift_pre ) + i ) = (((n - shift_pre ) + i ) % ( n ) )) ”
  &&  emp
).

Definition circular_shift_entail_wit_16_1_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (fill: Z) (tmp: Z) (PreH1 : (((n - shift_pre ) + i ) < n)) (PreH2 : (i < n)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n >= shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  TT && emp 
|--
  “ (((n - shift_pre ) + i ) = (((n - shift_pre ) + i ) % ( n ) )) ”
.

Definition circular_shift_entail_wit_16_2 := 
(
forall (shift_pre: Z) (x_pre: Z) (out: Z) (buf: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (fill: Z) (tmp: Z) (PreH1 : (((n - shift_pre ) + i ) >= n)) (PreH2 : (i < n)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n >= shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out i out_l_2 )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (n >= shift_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (((n - shift_pre ) + i ) - n )) ” 
  &&  “ ((((n - shift_pre ) + i ) - n ) < n) ” 
  &&  “ ((((n - shift_pre ) + i ) - n ) = (((n - shift_pre ) + i ) % ( n ) )) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre i out_l ) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (fill: Z) (tmp: Z) (PreH1 : (((n - shift_pre ) + i ) >= n)) (PreH2 : (i < n)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n >= shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  TT && emp 
|--
  “ ((((n - shift_pre ) + i ) - n ) = (((n - shift_pre ) + i ) % ( n ) )) ”
  &&  emp
).

Definition circular_shift_entail_wit_16_2_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (fill: Z) (tmp: Z) (PreH1 : (((n - shift_pre ) + i ) >= n)) (PreH2 : (i < n)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n >= shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  TT && emp 
|--
  “ ((((n - shift_pre ) + i ) - n ) = (((n - shift_pre ) + i ) % ( n ) )) ”
.

Definition circular_shift_entail_wit_17 := 
(
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (tmp: Z) (fill: Z) (n: Z) (i: Z) (src: Z) (buf: Z) (out: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (n >= shift_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n)) (PreH13 : (0 <= src)) (PreH14 : (src < n)) (PreH15 : (src = (((n - shift_pre ) + i ) % ( n ) ))) (PreH16 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH17 : ((Zlength (out_l_2)) = i)) (PreH18 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((Znth src (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (n >= shift_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre (i + 1 ) out_l ) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (n + 1 ) )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (tmp: Z) (fill: Z) (n: Z) (i: Z) (src: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (n >= shift_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n)) (PreH13 : (0 <= src)) (PreH14 : (src < n)) (PreH15 : (src = (((n - shift_pre ) + i ) % ( n ) ))) (PreH16 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH17 : ((Zlength (out_l_2)) = i)) (PreH18 : (problem_65_pre_z x_pre shift_pre )) ,
  TT && emp 
|--
  “ ((Zlength ((app (out_l_2) ((cons ((Znth src (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre (i + 1 ) (app (out_l_2) ((cons ((Znth src (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) ) ”
  &&  emp
).

Definition circular_shift_entail_wit_17_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (tmp: Z) (fill: Z) (n: Z) (i: Z) (src: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (n >= shift_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n)) (PreH13 : (0 <= src)) (PreH14 : (src < n)) (PreH15 : (src = (((n - shift_pre ) + i ) % ( n ) ))) (PreH16 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH17 : ((Zlength (out_l_2)) = i)) (PreH18 : (problem_65_pre_z x_pre shift_pre )) ,
  TT && emp 
|--
  “ ((Zlength ((app (out_l_2) ((cons ((Znth src (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))))) = (i + 1 )) ”
.

Definition circular_shift_entail_wit_17_split_goal_2 := 
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (tmp: Z) (fill: Z) (n: Z) (i: Z) (src: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (n >= shift_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n)) (PreH13 : (0 <= src)) (PreH14 : (src < n)) (PreH15 : (src = (((n - shift_pre ) + i ) % ( n ) ))) (PreH16 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH17 : ((Zlength (out_l_2)) = i)) (PreH18 : (problem_65_pre_z x_pre shift_pre )) ,
  TT && emp 
|--
  “ (circular_shift_prefix_z_65 x_pre shift_pre (i + 1 ) (app (out_l_2) ((cons ((Znth src (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) ) ”
.

Definition circular_shift_entail_wit_18_1 := 
(
forall (shift_pre: Z) (x_pre: Z) (out: Z) (buf: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (fill: Z) (tmp: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (n >= shift_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH14 : ((Zlength (out_l_2)) = i)) (PreH15 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out i out_l_2 )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (i = n) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre n out_l ) ” 
  &&  “ (out_l = (circular_shift_output_z_65 (x_pre) (shift_pre))) ” 
  &&  “ ((Zlength (out_l)) = n) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out n out_l )
  **  (CharArray.undef_seg out n (n + 1 ) )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (out: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (fill: Z) (tmp: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (n >= shift_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH14 : ((Zlength (out_l_2)) = i)) (PreH15 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full out i out_l_2 )
|--
  “ ((Zlength ((circular_shift_output_z_65 (x_pre) (shift_pre)))) = n) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre n (circular_shift_output_z_65 (x_pre) (shift_pre)) ) ”
  &&  (CharArray.full out n (circular_shift_output_z_65 (x_pre) (shift_pre)) )
).

Definition circular_shift_entail_wit_18_1_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (out: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (fill: Z) (tmp: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (n >= shift_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH14 : ((Zlength (out_l_2)) = i)) (PreH15 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full out i out_l_2 )
|--
  “ ((Zlength ((circular_shift_output_z_65 (x_pre) (shift_pre)))) = n) ”
.

Definition circular_shift_entail_wit_18_1_split_goal_2 := 
forall (shift_pre: Z) (x_pre: Z) (out: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (fill: Z) (tmp: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (n >= shift_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH14 : ((Zlength (out_l_2)) = i)) (PreH15 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full out i out_l_2 )
|--
  “ (circular_shift_prefix_z_65 x_pre shift_pre n (circular_shift_output_z_65 (x_pre) (shift_pre)) ) ”
.

Definition circular_shift_entail_wit_18_1_split_goal_spatial := 
forall (shift_pre: Z) (x_pre: Z) (out: Z) (out_l_2: (@list Z)) (i: Z) (n: Z) (fill: Z) (tmp: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (n >= shift_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n)) (PreH13 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH14 : ((Zlength (out_l_2)) = i)) (PreH15 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full out i out_l_2 )
|--
  (CharArray.full out n (circular_shift_output_z_65 (x_pre) (shift_pre)) )
.

Definition circular_shift_entail_wit_18_2 := 
(
forall (shift_pre: Z) (x_pre: Z) (out: Z) (buf: Z) (out_l_2: (@list Z)) (n: Z) (fill: Z) (i: Z) (tmp: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= i)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n < shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out i out_l_2 )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (i = n) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre n out_l ) ” 
  &&  “ (out_l = (circular_shift_output_z_65 (x_pre) (shift_pre))) ” 
  &&  “ ((Zlength (out_l)) = n) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out n out_l )
  **  (CharArray.undef_seg out n (n + 1 ) )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (out: Z) (out_l_2: (@list Z)) (n: Z) (fill: Z) (i: Z) (tmp: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= i)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n < shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full out i out_l_2 )
|--
  “ ((Zlength ((circular_shift_output_z_65 (x_pre) (shift_pre)))) = n) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre n (circular_shift_output_z_65 (x_pre) (shift_pre)) ) ”
  &&  (CharArray.full out n (circular_shift_output_z_65 (x_pre) (shift_pre)) )
).

Definition circular_shift_entail_wit_18_2_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (out: Z) (out_l_2: (@list Z)) (n: Z) (fill: Z) (i: Z) (tmp: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= i)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n < shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full out i out_l_2 )
|--
  “ ((Zlength ((circular_shift_output_z_65 (x_pre) (shift_pre)))) = n) ”
.

Definition circular_shift_entail_wit_18_2_split_goal_2 := 
forall (shift_pre: Z) (x_pre: Z) (out: Z) (out_l_2: (@list Z)) (n: Z) (fill: Z) (i: Z) (tmp: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= i)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n < shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full out i out_l_2 )
|--
  “ (circular_shift_prefix_z_65 x_pre shift_pre n (circular_shift_output_z_65 (x_pre) (shift_pre)) ) ”
.

Definition circular_shift_entail_wit_18_2_split_goal_spatial := 
forall (shift_pre: Z) (x_pre: Z) (out: Z) (out_l_2: (@list Z)) (n: Z) (fill: Z) (i: Z) (tmp: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= i)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n < shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l_2 )) (PreH15 : ((Zlength (out_l_2)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full out i out_l_2 )
|--
  (CharArray.full out n (circular_shift_output_z_65 (x_pre) (shift_pre)) )
.

Definition circular_shift_return_wit_1 := 
(
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (tmp: Z) (fill: Z) (i: Z) (n: Z) (buf: Z) (out: Z) (PreH1 : (0 <= n)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= fill)) (PreH9 : (i = n)) (PreH10 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH11 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH12 : (circular_shift_prefix_z_65 x_pre shift_pre n out_l_2 )) (PreH13 : (out_l_2 = (circular_shift_output_z_65 (x_pre) (shift_pre)))) (PreH14 : ((Zlength (out_l_2)) = n)) (PreH15 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full out (n + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (n + 1 ) (n + 1 ) )
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  EX (scratch: Z)  (out_l: (@list Z))  (len: Z) ,
  “ (len = (Zlength (out_l))) ” 
  &&  “ (len = (Zlength ((circular_shift_output_z_65 (x_pre) (shift_pre))))) ” 
  &&  “ (problem_65_spec_z x_pre shift_pre out_l ) ”
  &&  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full scratch ((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg scratch ((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) 64 )
) \/
(
forall (shift_pre: Z) (x_pre: Z) (out_l_2: (@list Z)) (tmp: Z) (fill: Z) (i: Z) (n: Z) (buf: Z) (out: Z) (PreH1 : (0 <= n)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= fill)) (PreH9 : (i = n)) (PreH10 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH11 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH12 : (circular_shift_prefix_z_65 x_pre shift_pre n out_l_2 )) (PreH13 : (out_l_2 = (circular_shift_output_z_65 (x_pre) (shift_pre)))) (PreH14 : ((Zlength (out_l_2)) = n)) (PreH15 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full out (n + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  EX (scratch: Z)  (out_l: (@list Z)) ,
  “ ((Zlength (out_l)) = (Zlength ((circular_shift_output_z_65 (x_pre) (shift_pre))))) ” 
  &&  “ (problem_65_spec_z x_pre shift_pre out_l ) ”
  &&  (CharArray.full out ((Zlength (out_l)) + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full scratch ((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg scratch ((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) 64 )
).

Definition circular_shift_partial_solve_wit_1_pure := 
forall (shift_pre: Z) (x_pre: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (problem_65_pre_z x_pre shift_pre )) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  ((( &( "buf" ) )) # Ptr  |->_)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (64 > 0) ”
.

Definition circular_shift_partial_solve_wit_1_aux := 
forall (shift_pre: Z) (x_pre: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (problem_65_pre_z x_pre shift_pre )) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  TT && emp 
|--
  “ (64 > 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ”
  &&  emp
.

Definition circular_shift_partial_solve_wit_1 := circular_shift_partial_solve_wit_1_pure -> circular_shift_partial_solve_wit_1_aux.

Definition circular_shift_partial_solve_wit_2 := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (x_pre = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  (CharArray.undef_full retval 64 )
|--
  “ (x_pre = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ”
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 64 )
.

Definition circular_shift_partial_solve_wit_3 := 
forall (shift_pre: Z) (x_pre: Z) (retval: Z) (PreH1 : (x_pre = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : (0 <= shift_pre)) (PreH6 : (shift_pre <= INT_MAX)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) ,
  (CharArray.undef_seg retval (0 + 1 ) 64 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  “ (x_pre = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ”
  &&  (((retval + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 (0 + 1 ) 64 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
.

Definition circular_shift_partial_solve_wit_4 := 
forall (shift_pre: Z) (x_pre: Z) (buf: Z) (i: Z) (fill: Z) (tmp: Z) (n: Z) (PreH1 : (i <= n)) (PreH2 : (0 < x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH7 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH8 : (problem_65_pre_z x_pre shift_pre )) (PreH9 : (tmp = 0)) (PreH10 : (fill = 0)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n + 1 ))) ,
  (CharArray.full buf i (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg buf i 64 )
|--
  “ (i <= n) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (fill = 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n + 1 )) ”
  &&  (((buf + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i buf i i 64 )
  **  (CharArray.full buf i (repeat_Z (0) (i)) )
.

Definition circular_shift_partial_solve_wit_5 := 
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (n: Z) (i: Z) (tmp: Z) (fill: Z) (buf: Z) (PreH1 : (0 < x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH6 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH7 : (problem_65_pre_z x_pre shift_pre )) (PreH8 : (i = (n + 1 ))) (PreH9 : (0 < tmp)) (PreH10 : (0 <= fill)) (PreH11 : (fill < n)) (PreH12 : ((Zlength (out_l)) = n)) (PreH13 : (base_fill_full_state_z_65 x_pre 10 tmp (fill + 1 ) out_l )) ,
  (CharArray.full buf (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ” 
  &&  “ (i = (n + 1 )) ” 
  &&  “ (0 < tmp) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill < n) ” 
  &&  “ ((Zlength (out_l)) = n) ” 
  &&  “ (base_fill_full_state_z_65 x_pre 10 tmp (fill + 1 ) out_l ) ”
  &&  (((buf + (fill * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i buf fill 0 (n + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
.

Definition circular_shift_partial_solve_wit_6_pure := 
(
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (buf: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (0 <= tmp)) (PreH6 : (0 <= i)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (problem_65_pre_z x_pre shift_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ ((n + 1 ) > 0) ”
) \/
(
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (buf: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (fill <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (tmp <= INT_MAX)) (PreH5 : (n >= INT_MIN)) (PreH6 : (fill >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (tmp >= INT_MIN)) (PreH9 : (shift_pre >= INT_MIN)) (PreH10 : (x_pre >= INT_MIN)) (PreH11 : (0 <= (n + 1 ))) (PreH12 : (0 <= x_pre)) (PreH13 : (x_pre <= INT_MAX)) (PreH14 : (0 <= shift_pre)) (PreH15 : (shift_pre <= INT_MAX)) (PreH16 : (0 <= tmp)) (PreH17 : (0 <= i)) (PreH18 : (0 <= fill)) (PreH19 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH20 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH21 : (problem_65_pre_z x_pre shift_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ ((n + 1 ) > 0) ”
).

Definition circular_shift_partial_solve_wit_6_pure_split_goal_1 := 
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (buf: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (fill <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (tmp <= INT_MAX)) (PreH5 : (n >= INT_MIN)) (PreH6 : (fill >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (tmp >= INT_MIN)) (PreH9 : (shift_pre >= INT_MIN)) (PreH10 : (x_pre >= INT_MIN)) (PreH11 : (0 <= (n + 1 ))) (PreH12 : (0 <= x_pre)) (PreH13 : (x_pre <= INT_MAX)) (PreH14 : (0 <= shift_pre)) (PreH15 : (shift_pre <= INT_MAX)) (PreH16 : (0 <= tmp)) (PreH17 : (0 <= i)) (PreH18 : (0 <= fill)) (PreH19 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH20 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH21 : (problem_65_pre_z x_pre shift_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "buf" ) )) # Ptr  |-> buf)
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ ((n + 1 ) > 0) ”
.

Definition circular_shift_partial_solve_wit_6_aux := 
forall (shift_pre: Z) (x_pre: Z) (tmp: Z) (i: Z) (fill: Z) (n: Z) (buf: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (0 <= tmp)) (PreH6 : (0 <= i)) (PreH7 : (0 <= fill)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
|--
  “ ((n + 1 ) > 0) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
.

Definition circular_shift_partial_solve_wit_6 := circular_shift_partial_solve_wit_6_pure -> circular_shift_partial_solve_wit_6_aux.

Definition circular_shift_partial_solve_wit_7 := 
forall (shift_pre: Z) (x_pre: Z) (out: Z) (buf: Z) (out_l: (@list Z)) (n: Z) (fill: Z) (i: Z) (tmp: Z) (PreH1 : (i < n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= i)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n < shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l )) (PreH15 : ((Zlength (out_l)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (i < n) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (n < shift_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre i out_l ) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (((buf + (((n - 1 ) - i ) * sizeof(CHAR) ) )) # Char  |-> (Znth ((n - 1 ) - i ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i buf ((n - 1 ) - i ) 0 (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
.

Definition circular_shift_partial_solve_wit_8 := 
forall (shift_pre: Z) (x_pre: Z) (out: Z) (buf: Z) (out_l: (@list Z)) (n: Z) (fill: Z) (i: Z) (tmp: Z) (PreH1 : (i < n)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (0 <= shift_pre)) (PreH5 : (shift_pre <= INT_MAX)) (PreH6 : (0 <= tmp)) (PreH7 : (0 <= i)) (PreH8 : (0 <= fill)) (PreH9 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH10 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH11 : (n < shift_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n)) (PreH14 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l )) (PreH15 : ((Zlength (out_l)) = i)) (PreH16 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (n < shift_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre i out_l ) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (n + 1 ) )
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out i out_l )
.

Definition circular_shift_partial_solve_wit_9 := 
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (tmp: Z) (fill: Z) (n: Z) (i: Z) (src: Z) (buf: Z) (out: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (0 <= tmp)) (PreH6 : (0 <= fill)) (PreH7 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH9 : (n >= shift_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n)) (PreH12 : (0 <= src)) (PreH13 : (src < n)) (PreH14 : (src = (((n - shift_pre ) + i ) % ( n ) ))) (PreH15 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l )) (PreH16 : ((Zlength (out_l)) = i)) (PreH17 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (n >= shift_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= src) ” 
  &&  “ (src < n) ” 
  &&  “ (src = (((n - shift_pre ) + i ) % ( n ) )) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre i out_l ) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (((buf + (src * sizeof(CHAR) ) )) # Char  |-> (Znth src (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i buf src 0 (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
.

Definition circular_shift_partial_solve_wit_10 := 
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (tmp: Z) (fill: Z) (n: Z) (i: Z) (src: Z) (buf: Z) (out: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (0 <= tmp)) (PreH6 : (0 <= fill)) (PreH7 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH8 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH9 : (n >= shift_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n)) (PreH12 : (0 <= src)) (PreH13 : (src < n)) (PreH14 : (src = (((n - shift_pre ) + i ) % ( n ) ))) (PreH15 : (circular_shift_prefix_z_65 x_pre shift_pre i out_l )) (PreH16 : ((Zlength (out_l)) = i)) (PreH17 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (n + 1 ) )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (n >= shift_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= src) ” 
  &&  “ (src < n) ” 
  &&  “ (src = (((n - shift_pre ) + i ) % ( n ) )) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre i out_l ) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (n + 1 ) )
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out i out_l )
.

Definition circular_shift_partial_solve_wit_11 := 
forall (shift_pre: Z) (x_pre: Z) (out_l: (@list Z)) (tmp: Z) (fill: Z) (i: Z) (n: Z) (buf: Z) (out: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (0 <= shift_pre)) (PreH4 : (shift_pre <= INT_MAX)) (PreH5 : (0 <= tmp)) (PreH6 : (0 <= fill)) (PreH7 : (i = n)) (PreH8 : (n = (Zlength ((decimal_digits_z_65 (x_pre)))))) (PreH9 : (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64)) (PreH10 : (circular_shift_prefix_z_65 x_pre shift_pre n out_l )) (PreH11 : (out_l = (circular_shift_output_z_65 (x_pre) (shift_pre)))) (PreH12 : ((Zlength (out_l)) = n)) (PreH13 : (problem_65_pre_z x_pre shift_pre )) ,
  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out n out_l )
  **  (CharArray.undef_seg out n (n + 1 ) )
|--
  “ (0 <= n) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre <= INT_MAX) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (i = n) ” 
  &&  “ (n = (Zlength ((decimal_digits_z_65 (x_pre))))) ” 
  &&  “ (((Zlength ((decimal_digits_z_65 (x_pre)))) + 1 ) < 64) ” 
  &&  “ (circular_shift_prefix_z_65 x_pre shift_pre n out_l ) ” 
  &&  “ (out_l = (circular_shift_output_z_65 (x_pre) (shift_pre))) ” 
  &&  “ ((Zlength (out_l)) = n) ” 
  &&  “ (problem_65_pre_z x_pre shift_pre ) ”
  &&  (((out + (n * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out n n (n + 1 ) )
  **  (CharArray.full buf (n + 1 ) (app ((decimal_digits_z_65 (x_pre))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf (n + 1 ) 64 )
  **  (CharArray.full out n out_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_circular_shift_safety_wit_1 : circular_shift_safety_wit_1.
Axiom proof_of_circular_shift_safety_wit_2 : circular_shift_safety_wit_2.
Axiom proof_of_circular_shift_safety_wit_3 : circular_shift_safety_wit_3.
Axiom proof_of_circular_shift_safety_wit_4 : circular_shift_safety_wit_4.
Axiom proof_of_circular_shift_safety_wit_5 : circular_shift_safety_wit_5.
Axiom proof_of_circular_shift_safety_wit_6 : circular_shift_safety_wit_6.
Axiom proof_of_circular_shift_safety_wit_7 : circular_shift_safety_wit_7.
Axiom proof_of_circular_shift_safety_wit_8 : circular_shift_safety_wit_8.
Axiom proof_of_circular_shift_safety_wit_9 : circular_shift_safety_wit_9.
Axiom proof_of_circular_shift_safety_wit_10 : circular_shift_safety_wit_10.
Axiom proof_of_circular_shift_safety_wit_11 : circular_shift_safety_wit_11.
Axiom proof_of_circular_shift_safety_wit_12 : circular_shift_safety_wit_12.
Axiom proof_of_circular_shift_safety_wit_13 : circular_shift_safety_wit_13.
Axiom proof_of_circular_shift_safety_wit_14 : circular_shift_safety_wit_14.
Axiom proof_of_circular_shift_safety_wit_15 : circular_shift_safety_wit_15.
Axiom proof_of_circular_shift_safety_wit_16 : circular_shift_safety_wit_16.
Axiom proof_of_circular_shift_safety_wit_17 : circular_shift_safety_wit_17.
Axiom proof_of_circular_shift_safety_wit_18 : circular_shift_safety_wit_18.
Axiom proof_of_circular_shift_safety_wit_19 : circular_shift_safety_wit_19.
Axiom proof_of_circular_shift_safety_wit_20 : circular_shift_safety_wit_20.
Axiom proof_of_circular_shift_safety_wit_21 : circular_shift_safety_wit_21.
Axiom proof_of_circular_shift_safety_wit_22 : circular_shift_safety_wit_22.
Axiom proof_of_circular_shift_safety_wit_23 : circular_shift_safety_wit_23.
Axiom proof_of_circular_shift_safety_wit_24 : circular_shift_safety_wit_24.
Axiom proof_of_circular_shift_safety_wit_25 : circular_shift_safety_wit_25.
Axiom proof_of_circular_shift_safety_wit_26 : circular_shift_safety_wit_26.
Axiom proof_of_circular_shift_safety_wit_27 : circular_shift_safety_wit_27.
Axiom proof_of_circular_shift_safety_wit_28 : circular_shift_safety_wit_28.
Axiom proof_of_circular_shift_safety_wit_29 : circular_shift_safety_wit_29.
Axiom proof_of_circular_shift_safety_wit_30 : circular_shift_safety_wit_30.
Axiom proof_of_circular_shift_safety_wit_31 : circular_shift_safety_wit_31.
Axiom proof_of_circular_shift_safety_wit_32 : circular_shift_safety_wit_32.
Axiom proof_of_circular_shift_safety_wit_33 : circular_shift_safety_wit_33.
Axiom proof_of_circular_shift_safety_wit_34 : circular_shift_safety_wit_34.
Axiom proof_of_circular_shift_safety_wit_35 : circular_shift_safety_wit_35.
Axiom proof_of_circular_shift_safety_wit_36 : circular_shift_safety_wit_36.
Axiom proof_of_circular_shift_safety_wit_37 : circular_shift_safety_wit_37.
Axiom proof_of_circular_shift_safety_wit_38 : circular_shift_safety_wit_38.
Axiom proof_of_circular_shift_safety_wit_39 : circular_shift_safety_wit_39.
Axiom proof_of_circular_shift_safety_wit_40 : circular_shift_safety_wit_40.
Axiom proof_of_circular_shift_safety_wit_41 : circular_shift_safety_wit_41.
Axiom proof_of_circular_shift_entail_wit_1 : circular_shift_entail_wit_1.
Axiom proof_of_circular_shift_entail_wit_2 : circular_shift_entail_wit_2.
Axiom proof_of_circular_shift_entail_wit_3 : circular_shift_entail_wit_3.
Axiom proof_of_circular_shift_entail_wit_4 : circular_shift_entail_wit_4.
Axiom proof_of_circular_shift_entail_wit_5 : circular_shift_entail_wit_5.
Axiom proof_of_circular_shift_entail_wit_6 : circular_shift_entail_wit_6.
Axiom proof_of_circular_shift_entail_wit_7 : circular_shift_entail_wit_7.
Axiom proof_of_circular_shift_entail_wit_8 : circular_shift_entail_wit_8.
Axiom proof_of_circular_shift_entail_wit_9 : circular_shift_entail_wit_9.
Axiom proof_of_circular_shift_entail_wit_10 : circular_shift_entail_wit_10.
Axiom proof_of_circular_shift_entail_wit_11 : circular_shift_entail_wit_11.
Axiom proof_of_circular_shift_entail_wit_12_1 : circular_shift_entail_wit_12_1.
Axiom proof_of_circular_shift_entail_wit_12_2 : circular_shift_entail_wit_12_2.
Axiom proof_of_circular_shift_entail_wit_13 : circular_shift_entail_wit_13.
Axiom proof_of_circular_shift_entail_wit_14 : circular_shift_entail_wit_14.
Axiom proof_of_circular_shift_entail_wit_15 : circular_shift_entail_wit_15.
Axiom proof_of_circular_shift_entail_wit_16_1 : circular_shift_entail_wit_16_1.
Axiom proof_of_circular_shift_entail_wit_16_2 : circular_shift_entail_wit_16_2.
Axiom proof_of_circular_shift_entail_wit_17 : circular_shift_entail_wit_17.
Axiom proof_of_circular_shift_entail_wit_18_1 : circular_shift_entail_wit_18_1.
Axiom proof_of_circular_shift_entail_wit_18_2 : circular_shift_entail_wit_18_2.
Axiom proof_of_circular_shift_return_wit_1 : circular_shift_return_wit_1.
Axiom proof_of_circular_shift_partial_solve_wit_1_pure : circular_shift_partial_solve_wit_1_pure.
Axiom proof_of_circular_shift_partial_solve_wit_1 : circular_shift_partial_solve_wit_1.
Axiom proof_of_circular_shift_partial_solve_wit_2 : circular_shift_partial_solve_wit_2.
Axiom proof_of_circular_shift_partial_solve_wit_3 : circular_shift_partial_solve_wit_3.
Axiom proof_of_circular_shift_partial_solve_wit_4 : circular_shift_partial_solve_wit_4.
Axiom proof_of_circular_shift_partial_solve_wit_5 : circular_shift_partial_solve_wit_5.
Axiom proof_of_circular_shift_partial_solve_wit_6_pure : circular_shift_partial_solve_wit_6_pure.
Axiom proof_of_circular_shift_partial_solve_wit_6 : circular_shift_partial_solve_wit_6.
Axiom proof_of_circular_shift_partial_solve_wit_7 : circular_shift_partial_solve_wit_7.
Axiom proof_of_circular_shift_partial_solve_wit_8 : circular_shift_partial_solve_wit_8.
Axiom proof_of_circular_shift_partial_solve_wit_9 : circular_shift_partial_solve_wit_9.
Axiom proof_of_circular_shift_partial_solve_wit_10 : circular_shift_partial_solve_wit_10.
Axiom proof_of_circular_shift_partial_solve_wit_11 : circular_shift_partial_solve_wit_11.

End VC_Correct.
