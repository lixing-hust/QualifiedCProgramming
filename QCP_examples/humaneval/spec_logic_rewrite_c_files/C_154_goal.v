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
Require Import coins_154.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function cycpattern_check -----*)

Definition cycpattern_check_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (b_l)))) (PreH2 : (0 <= ((string_length (b_l)) + 1 ))) (PreH3 : (0 <= ((string_length (a_l)) + 1 ))) (PreH4 : (a_pre = a0)) (PreH5 : (b_pre = b0)) (PreH6 : (problem_154_pre_z a_l b_l )) (PreH7 : (valid_string a_l )) (PreH8 : (valid_string b_l )) (PreH9 : ((string_length (a_l)) < INT_MAX)) (PreH10 : (((string_length (b_l)) + 1 ) < INT_MAX)) ,
  ((( &( "rotate" ) )) # Ptr  |->_)
  **  (store_string b_pre b_l )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition cycpattern_check_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (b_l)))) (PreH2 : (0 <= ((string_length (b_l)) + 1 ))) (PreH3 : (0 <= ((string_length (a_l)) + 1 ))) (PreH4 : (a_pre = a0)) (PreH5 : (b_pre = b0)) (PreH6 : (problem_154_pre_z a_l b_l )) (PreH7 : (valid_string a_l )) (PreH8 : (valid_string b_l )) (PreH9 : ((string_length (a_l)) < INT_MAX)) (PreH10 : (((string_length (b_l)) + 1 ) < INT_MAX)) ,
  ((( &( "rotate" ) )) # Ptr  |->_)
  **  (store_string b_pre b_l )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cycpattern_check_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (b_l)))) (PreH3 : (0 <= ((string_length (b_l)) + 1 ))) (PreH4 : (0 <= ((string_length (a_l)) + 1 ))) (PreH5 : (a_pre = a0)) (PreH6 : (b_pre = b0)) (PreH7 : (problem_154_pre_z a_l b_l )) (PreH8 : (valid_string a_l )) (PreH9 : (valid_string b_l )) (PreH10 : ((string_length (a_l)) < INT_MAX)) (PreH11 : (((string_length (b_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full b_pre ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  ((( &( "rotate" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cycpattern_check_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (b_l)))) (PreH4 : (0 <= ((string_length (b_l)) + 1 ))) (PreH5 : (0 <= ((string_length (a_l)) + 1 ))) (PreH6 : (a_pre = a0)) (PreH7 : (b_pre = b0)) (PreH8 : (problem_154_pre_z a_l b_l )) (PreH9 : (valid_string a_l )) (PreH10 : (valid_string b_l )) (PreH11 : ((string_length (a_l)) < INT_MAX)) (PreH12 : (((string_length (b_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full b_pre ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  ((( &( "rotate" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ False ”
.

Definition cycpattern_check_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (b_l)))) (PreH4 : (0 <= ((string_length (b_l)) + 1 ))) (PreH5 : (0 <= ((string_length (a_l)) + 1 ))) (PreH6 : (a_pre = a0)) (PreH7 : (b_pre = b0)) (PreH8 : (problem_154_pre_z a_l b_l )) (PreH9 : (valid_string a_l )) (PreH10 : (valid_string b_l )) (PreH11 : ((string_length (a_l)) < INT_MAX)) (PreH12 : (((string_length (b_l)) + 1 ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full b_pre ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  ((( &( "rotate" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cycpattern_check_safety_wit_6 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (rotate <> 0)) (PreH5 : ((n + 1 ) < INT_MAX)) (PreH6 : (valid_string a_l )) (PreH7 : (valid_string b_l )) (PreH8 : ((string_length (a_l)) < INT_MAX)) (PreH9 : (n = (string_length (b_l)))) (PreH10 : (rotation_scan_state_154 a_l b_l i )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cycpattern_check_safety_wit_7 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (j < n)) (PreH2 : (0 <= j)) (PreH3 : (j <= n)) (PreH4 : (0 < n)) (PreH5 : (0 <= i)) (PreH6 : (i < n)) (PreH7 : (rotate <> 0)) (PreH8 : ((n + 1 ) < INT_MAX)) (PreH9 : (valid_string a_l )) (PreH10 : (valid_string b_l )) (PreH11 : ((string_length (a_l)) < INT_MAX)) (PreH12 : (n = (string_length (b_l)))) (PreH13 : (rotation_scan_state_154 a_l b_l i )) (PreH14 : (rotation_prefix_154 b_l i j rotate_l )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.full rotate j rotate_l )
  **  (CharArray.undef_seg rotate j (n + 1 ) )
|--
  “ ((n - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - i )) ”
.

Definition cycpattern_check_safety_wit_8 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (j >= (n - i ))) (PreH2 : (j < n)) (PreH3 : (0 <= j)) (PreH4 : (j <= n)) (PreH5 : (0 < n)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (rotate <> 0)) (PreH9 : ((n + 1 ) < INT_MAX)) (PreH10 : (valid_string a_l )) (PreH11 : (valid_string b_l )) (PreH12 : ((string_length (a_l)) < INT_MAX)) (PreH13 : (n = (string_length (b_l)))) (PreH14 : (rotation_scan_state_154 a_l b_l i )) (PreH15 : (rotation_prefix_154 b_l i j rotate_l )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.full rotate j rotate_l )
  **  (CharArray.undef_seg rotate j (n + 1 ) )
|--
  “ ((j - (n - i ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - (n - i ) )) ”
.

Definition cycpattern_check_safety_wit_9 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (j >= (n - i ))) (PreH2 : (j < n)) (PreH3 : (0 <= j)) (PreH4 : (j <= n)) (PreH5 : (0 < n)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (rotate <> 0)) (PreH9 : ((n + 1 ) < INT_MAX)) (PreH10 : (valid_string a_l )) (PreH11 : (valid_string b_l )) (PreH12 : ((string_length (a_l)) < INT_MAX)) (PreH13 : (n = (string_length (b_l)))) (PreH14 : (rotation_scan_state_154 a_l b_l i )) (PreH15 : (rotation_prefix_154 b_l i j rotate_l )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.full rotate j rotate_l )
  **  (CharArray.undef_seg rotate j (n + 1 ) )
|--
  “ ((n - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - i )) ”
.

Definition cycpattern_check_safety_wit_10 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (j < (n - i ))) (PreH2 : (j < n)) (PreH3 : (0 <= j)) (PreH4 : (j <= n)) (PreH5 : (0 < n)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (rotate <> 0)) (PreH9 : ((n + 1 ) < INT_MAX)) (PreH10 : (valid_string a_l )) (PreH11 : (valid_string b_l )) (PreH12 : ((string_length (a_l)) < INT_MAX)) (PreH13 : (n = (string_length (b_l)))) (PreH14 : (rotation_scan_state_154 a_l b_l i )) (PreH15 : (rotation_prefix_154 b_l i j rotate_l )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.full rotate j rotate_l )
  **  (CharArray.undef_seg rotate j (n + 1 ) )
|--
  “ ((i + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + j )) ”
.

Definition cycpattern_check_safety_wit_11 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l: (@list Z)) (ch: Z) (idx: Z) (i: Z) (j: Z) (n: Z) (rotate: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (ch = (Znth (idx) (b_l) (0)))) (PreH4 : (idx = ((i + j ) % ( n ) ))) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (0 <= idx)) (PreH8 : (idx < n)) (PreH9 : (0 <= j)) (PreH10 : (j < n)) (PreH11 : (0 < n)) (PreH12 : (0 <= i)) (PreH13 : (i < n)) (PreH14 : (rotate <> 0)) (PreH15 : ((n + 1 ) < INT_MAX)) (PreH16 : (valid_string a_l )) (PreH17 : (valid_string b_l )) (PreH18 : ((string_length (a_l)) < INT_MAX)) (PreH19 : (n = (string_length (b_l)))) (PreH20 : (rotation_scan_state_154 a_l b_l i )) (PreH21 : (rotation_prefix_154 b_l i j rotate_l )) ,
  (CharArray.full rotate (j + 1 ) (app (rotate_l) ((cons (ch) ((@nil Z))))) )
  **  (CharArray.undef_seg rotate (j + 1 ) (n + 1 ) )
  **  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition cycpattern_check_safety_wit_12 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (j >= n)) (PreH2 : (0 <= j)) (PreH3 : (j <= n)) (PreH4 : (0 < n)) (PreH5 : (0 <= i)) (PreH6 : (i < n)) (PreH7 : (rotate <> 0)) (PreH8 : ((n + 1 ) < INT_MAX)) (PreH9 : (valid_string a_l )) (PreH10 : (valid_string b_l )) (PreH11 : ((string_length (a_l)) < INT_MAX)) (PreH12 : (n = (string_length (b_l)))) (PreH13 : (rotation_scan_state_154 a_l b_l i )) (PreH14 : (rotation_prefix_154 b_l i j rotate_l )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.full rotate j rotate_l )
  **  (CharArray.undef_seg rotate j (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cycpattern_check_safety_wit_13 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (strstr_result a_l (rotate_at_154 (b_l) (i)) retval a0 )) (PreH2 : (0 <= ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ))) (PreH3 : (0 <= ((string_length (b_l)) + 1 ))) (PreH4 : (0 <= ((string_length (a_l)) + 1 ))) (PreH5 : (rotate <> 0)) (PreH6 : ((n + 1 ) < INT_MAX)) (PreH7 : (valid_string a_l )) (PreH8 : (valid_string b_l )) (PreH9 : ((string_length (a_l)) < INT_MAX)) (PreH10 : (n = (string_length (b_l)))) (PreH11 : (rotation_scan_state_154 a_l b_l i )) (PreH12 : (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) )) (PreH13 : (valid_string (rotate_at_154 (b_l) (i)) )) ,
  (store_string a0 a_l )
  **  (store_string rotate (rotate_at_154 (b_l) (i)) )
  **  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  ((( &( "hit" ) )) # Ptr  |-> retval)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cycpattern_check_safety_wit_14 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (hit: Z) (rotate: Z) (n: Z) (i: Z) (PreH1 : (hit <> 0)) (PreH2 : (rotate <> 0)) (PreH3 : ((n + 1 ) < INT_MAX)) (PreH4 : (valid_string a_l )) (PreH5 : (valid_string b_l )) (PreH6 : ((string_length (a_l)) < INT_MAX)) (PreH7 : (n = (string_length (b_l)))) (PreH8 : (rotation_success_154 a_l b_l i (rotate_at_154 (b_l) (i)) )) ,
  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n + 1 )) ”
.

Definition cycpattern_check_safety_wit_15 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (hit: Z) (rotate: Z) (n: Z) (i: Z) (PreH1 : (hit <> 0)) (PreH2 : (rotate <> 0)) (PreH3 : ((n + 1 ) < INT_MAX)) (PreH4 : (valid_string a_l )) (PreH5 : (valid_string b_l )) (PreH6 : ((string_length (a_l)) < INT_MAX)) (PreH7 : (n = (string_length (b_l)))) (PreH8 : (rotation_success_154 a_l b_l i (rotate_at_154 (b_l) (i)) )) ,
  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cycpattern_check_safety_wit_16 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (hit: Z) (rotate: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (hit <> 0)) (PreH4 : (rotate <> 0)) (PreH5 : ((n + 1 ) < INT_MAX)) (PreH6 : (valid_string a_l )) (PreH7 : (valid_string b_l )) (PreH8 : ((string_length (a_l)) < INT_MAX)) (PreH9 : (n = (string_length (b_l)))) (PreH10 : (rotation_success_154 a_l b_l i (rotate_at_154 (b_l) (i)) )) ,
  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cycpattern_check_safety_wit_17 := 
(
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (hit: Z) (rotate: Z) (n: Z) (i: Z) (PreH1 : (hit = 0)) (PreH2 : (rotate <> 0)) (PreH3 : ((n + 1 ) < INT_MAX)) (PreH4 : (valid_string a_l )) (PreH5 : (valid_string b_l )) (PreH6 : ((string_length (a_l)) < INT_MAX)) (PreH7 : (n = (string_length (b_l)))) (PreH8 : (rotation_scan_state_154 a_l b_l (i + 1 ) )) ,
  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (hit: Z) (rotate: Z) (n: Z) (i: Z) (PreH1 : (hit = 0)) (PreH2 : (rotate <> 0)) (PreH3 : ((n + 1 ) < INT_MAX)) (PreH4 : (valid_string a_l )) (PreH5 : (valid_string b_l )) (PreH6 : ((string_length (a_l)) < INT_MAX)) (PreH7 : (n = (string_length (b_l)))) (PreH8 : (rotation_scan_state_154 a_l b_l (i + 1 ) )) ,
  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition cycpattern_check_safety_wit_17_split_goal_1 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (hit: Z) (rotate: Z) (n: Z) (i: Z) (PreH1 : (hit = 0)) (PreH2 : (rotate <> 0)) (PreH3 : ((n + 1 ) < INT_MAX)) (PreH4 : (valid_string a_l )) (PreH5 : (valid_string b_l )) (PreH6 : ((string_length (a_l)) < INT_MAX)) (PreH7 : (n = (string_length (b_l)))) (PreH8 : (rotation_scan_state_154 a_l b_l (i + 1 ) )) ,
  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition cycpattern_check_safety_wit_17_split_goal_2 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (hit: Z) (rotate: Z) (n: Z) (i: Z) (PreH1 : (hit = 0)) (PreH2 : (rotate <> 0)) (PreH3 : ((n + 1 ) < INT_MAX)) (PreH4 : (valid_string a_l )) (PreH5 : (valid_string b_l )) (PreH6 : ((string_length (a_l)) < INT_MAX)) (PreH7 : (n = (string_length (b_l)))) (PreH8 : (rotation_scan_state_154 a_l b_l (i + 1 ) )) ,
  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition cycpattern_check_safety_wit_18 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (rotate <> 0)) (PreH5 : ((n + 1 ) < INT_MAX)) (PreH6 : (valid_string a_l )) (PreH7 : (valid_string b_l )) (PreH8 : ((string_length (a_l)) < INT_MAX)) (PreH9 : (n = (string_length (b_l)))) (PreH10 : (rotation_scan_state_154 a_l b_l i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n + 1 )) ”
.

Definition cycpattern_check_safety_wit_19 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (rotate <> 0)) (PreH5 : ((n + 1 ) < INT_MAX)) (PreH6 : (valid_string a_l )) (PreH7 : (valid_string b_l )) (PreH8 : ((string_length (a_l)) < INT_MAX)) (PreH9 : (n = (string_length (b_l)))) (PreH10 : (rotation_scan_state_154 a_l b_l i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cycpattern_check_safety_wit_20 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (rotate <> 0)) (PreH7 : ((n + 1 ) < INT_MAX)) (PreH8 : (valid_string a_l )) (PreH9 : (valid_string b_l )) (PreH10 : ((string_length (a_l)) < INT_MAX)) (PreH11 : (n = (string_length (b_l)))) (PreH12 : (rotation_scan_state_154 a_l b_l i )) ,
  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cycpattern_check_entail_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (b_l)))) (PreH4 : (0 <= ((string_length (b_l)) + 1 ))) (PreH5 : (0 <= ((string_length (a_l)) + 1 ))) (PreH6 : (a_pre = a0)) (PreH7 : (b_pre = b0)) (PreH8 : (problem_154_pre_z a_l b_l )) (PreH9 : (valid_string a_l )) (PreH10 : (valid_string b_l )) (PreH11 : ((string_length (a_l)) < INT_MAX)) (PreH12 : (((string_length (b_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full b_pre ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (retval = (string_length (b_l))) ” 
  &&  “ (rotation_scan_state_154 a_l b_l 0 ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
) \/
(
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (b_l)))) (PreH4 : (0 <= ((string_length (b_l)) + 1 ))) (PreH5 : (0 <= ((string_length (a_l)) + 1 ))) (PreH6 : (a_pre = a0)) (PreH7 : (b_pre = b0)) (PreH8 : (problem_154_pre_z a_l b_l )) (PreH9 : (valid_string a_l )) (PreH10 : (valid_string b_l )) (PreH11 : ((string_length (a_l)) < INT_MAX)) (PreH12 : (((string_length (b_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full b_pre ((string_length (b_l)) + 1 ) (c_string (b_l)) )
|--
  “ (rotation_scan_state_154 a_l b_l 0 ) ” 
  &&  “ (0 <= retval) ”
  &&  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
).

Definition cycpattern_check_entail_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (b_l)))) (PreH4 : (0 <= ((string_length (b_l)) + 1 ))) (PreH5 : (0 <= ((string_length (a_l)) + 1 ))) (PreH6 : (a_pre = a0)) (PreH7 : (b_pre = b0)) (PreH8 : (problem_154_pre_z a_l b_l )) (PreH9 : (valid_string a_l )) (PreH10 : (valid_string b_l )) (PreH11 : ((string_length (a_l)) < INT_MAX)) (PreH12 : (((string_length (b_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full b_pre ((string_length (b_l)) + 1 ) (c_string (b_l)) )
|--
  “ (rotation_scan_state_154 a_l b_l 0 ) ”
.

Definition cycpattern_check_entail_wit_1_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (b_l)))) (PreH4 : (0 <= ((string_length (b_l)) + 1 ))) (PreH5 : (0 <= ((string_length (a_l)) + 1 ))) (PreH6 : (a_pre = a0)) (PreH7 : (b_pre = b0)) (PreH8 : (problem_154_pre_z a_l b_l )) (PreH9 : (valid_string a_l )) (PreH10 : (valid_string b_l )) (PreH11 : ((string_length (a_l)) < INT_MAX)) (PreH12 : (((string_length (b_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full b_pre ((string_length (b_l)) + 1 ) (c_string (b_l)) )
|--
  “ (0 <= retval) ”
.

Definition cycpattern_check_entail_wit_1_split_goal_spatial := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (b_l)))) (PreH4 : (0 <= ((string_length (b_l)) + 1 ))) (PreH5 : (0 <= ((string_length (a_l)) + 1 ))) (PreH6 : (a_pre = a0)) (PreH7 : (b_pre = b0)) (PreH8 : (problem_154_pre_z a_l b_l )) (PreH9 : (valid_string a_l )) (PreH10 : (valid_string b_l )) (PreH11 : ((string_length (a_l)) < INT_MAX)) (PreH12 : (((string_length (b_l)) + 1 ) < INT_MAX)) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full b_pre ((string_length (b_l)) + 1 ) (c_string (b_l)) )
|--
  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
.

Definition cycpattern_check_entail_wit_2 := 
(
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (rotate <> 0)) (PreH5 : ((n + 1 ) < INT_MAX)) (PreH6 : (valid_string a_l )) (PreH7 : (valid_string b_l )) (PreH8 : ((string_length (a_l)) < INT_MAX)) (PreH9 : (n = (string_length (b_l)))) (PreH10 : (rotation_scan_state_154 a_l b_l i )) ,
  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
|--
  EX (rotate_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (0 < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (rotate <> 0) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (n = (string_length (b_l))) ” 
  &&  “ (rotation_scan_state_154 a_l b_l i ) ” 
  &&  “ (rotation_prefix_154 b_l i 0 rotate_l ) ”
  &&  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.full rotate 0 rotate_l )
  **  (CharArray.undef_seg rotate 0 (n + 1 ) )
) \/
(
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (rotate <> 0)) (PreH7 : ((n + 1 ) < INT_MAX)) (PreH8 : (valid_string a_l )) (PreH9 : (valid_string b_l )) (PreH10 : ((string_length (a_l)) < INT_MAX)) (PreH11 : (n = (string_length (b_l)))) (PreH12 : (rotation_scan_state_154 a_l b_l i )) ,
  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ (rotation_prefix_154 b_l i 0 (@nil Z) ) ”
  &&  (CharArray.undef_full rotate (n + 1 ) )
).

Definition cycpattern_check_entail_wit_2_split_goal_1 := 
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (rotate <> 0)) (PreH7 : ((n + 1 ) < INT_MAX)) (PreH8 : (valid_string a_l )) (PreH9 : (valid_string b_l )) (PreH10 : ((string_length (a_l)) < INT_MAX)) (PreH11 : (n = (string_length (b_l)))) (PreH12 : (rotation_scan_state_154 a_l b_l i )) ,
  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ (rotation_prefix_154 b_l i 0 (@nil Z) ) ”
.

Definition cycpattern_check_entail_wit_2_split_goal_spatial := 
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (rotate <> 0)) (PreH7 : ((n + 1 ) < INT_MAX)) (PreH8 : (valid_string a_l )) (PreH9 : (valid_string b_l )) (PreH10 : ((string_length (a_l)) < INT_MAX)) (PreH11 : (n = (string_length (b_l)))) (PreH12 : (rotation_scan_state_154 a_l b_l i )) ,
  (CharArray.undef_full rotate (n + 1 ) )
|--
  (CharArray.undef_full rotate (n + 1 ) )
.

Definition cycpattern_check_entail_wit_3_1 := 
(
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l_2: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (j < (n - i ))) (PreH2 : (j < n)) (PreH3 : (0 <= j)) (PreH4 : (j <= n)) (PreH5 : (0 < n)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (rotate <> 0)) (PreH9 : ((n + 1 ) < INT_MAX)) (PreH10 : (valid_string a_l )) (PreH11 : (valid_string b_l )) (PreH12 : ((string_length (a_l)) < INT_MAX)) (PreH13 : (n = (string_length (b_l)))) (PreH14 : (rotation_scan_state_154 a_l b_l i )) (PreH15 : (rotation_prefix_154 b_l i j rotate_l_2 )) ,
  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.full rotate j rotate_l_2 )
  **  (CharArray.undef_seg rotate j (n + 1 ) )
|--
  EX (rotate_l: (@list Z)) ,
  “ ((i + j ) = ((i + j ) % ( n ) )) ” 
  &&  “ (0 <= (i + j )) ” 
  &&  “ ((i + j ) < n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n) ” 
  &&  “ (0 < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (rotate <> 0) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (n = (string_length (b_l))) ” 
  &&  “ (rotation_scan_state_154 a_l b_l i ) ” 
  &&  “ (rotation_prefix_154 b_l i j rotate_l ) ”
  &&  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.full rotate j rotate_l )
  **  (CharArray.undef_seg rotate j (n + 1 ) )
) \/
(
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l_2: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (j < (n - i ))) (PreH4 : (j < n)) (PreH5 : (0 <= j)) (PreH6 : (j <= n)) (PreH7 : (0 < n)) (PreH8 : (0 <= i)) (PreH9 : (i < n)) (PreH10 : (rotate <> 0)) (PreH11 : ((n + 1 ) < INT_MAX)) (PreH12 : (valid_string a_l )) (PreH13 : (valid_string b_l )) (PreH14 : ((string_length (a_l)) < INT_MAX)) (PreH15 : (n = (string_length (b_l)))) (PreH16 : (rotation_scan_state_154 a_l b_l i )) (PreH17 : (rotation_prefix_154 b_l i j rotate_l_2 )) ,
  TT && emp 
|--
  “ ((i + j ) = ((i + j ) % ( n ) )) ”
  &&  emp
).

Definition cycpattern_check_entail_wit_3_1_split_goal_1 := 
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l_2: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (j < (n - i ))) (PreH4 : (j < n)) (PreH5 : (0 <= j)) (PreH6 : (j <= n)) (PreH7 : (0 < n)) (PreH8 : (0 <= i)) (PreH9 : (i < n)) (PreH10 : (rotate <> 0)) (PreH11 : ((n + 1 ) < INT_MAX)) (PreH12 : (valid_string a_l )) (PreH13 : (valid_string b_l )) (PreH14 : ((string_length (a_l)) < INT_MAX)) (PreH15 : (n = (string_length (b_l)))) (PreH16 : (rotation_scan_state_154 a_l b_l i )) (PreH17 : (rotation_prefix_154 b_l i j rotate_l_2 )) ,
  TT && emp 
|--
  “ ((i + j ) = ((i + j ) % ( n ) )) ”
.

Definition cycpattern_check_entail_wit_3_2 := 
(
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l_2: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (j >= (n - i ))) (PreH2 : (j < n)) (PreH3 : (0 <= j)) (PreH4 : (j <= n)) (PreH5 : (0 < n)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (rotate <> 0)) (PreH9 : ((n + 1 ) < INT_MAX)) (PreH10 : (valid_string a_l )) (PreH11 : (valid_string b_l )) (PreH12 : ((string_length (a_l)) < INT_MAX)) (PreH13 : (n = (string_length (b_l)))) (PreH14 : (rotation_scan_state_154 a_l b_l i )) (PreH15 : (rotation_prefix_154 b_l i j rotate_l_2 )) ,
  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.full rotate j rotate_l_2 )
  **  (CharArray.undef_seg rotate j (n + 1 ) )
|--
  EX (rotate_l: (@list Z)) ,
  “ ((j - (n - i ) ) = ((i + j ) % ( n ) )) ” 
  &&  “ (0 <= (j - (n - i ) )) ” 
  &&  “ ((j - (n - i ) ) < n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n) ” 
  &&  “ (0 < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (rotate <> 0) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (n = (string_length (b_l))) ” 
  &&  “ (rotation_scan_state_154 a_l b_l i ) ” 
  &&  “ (rotation_prefix_154 b_l i j rotate_l ) ”
  &&  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.full rotate j rotate_l )
  **  (CharArray.undef_seg rotate j (n + 1 ) )
) \/
(
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l_2: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (j >= (n - i ))) (PreH4 : (j < n)) (PreH5 : (0 <= j)) (PreH6 : (j <= n)) (PreH7 : (0 < n)) (PreH8 : (0 <= i)) (PreH9 : (i < n)) (PreH10 : (rotate <> 0)) (PreH11 : ((n + 1 ) < INT_MAX)) (PreH12 : (valid_string a_l )) (PreH13 : (valid_string b_l )) (PreH14 : ((string_length (a_l)) < INT_MAX)) (PreH15 : (n = (string_length (b_l)))) (PreH16 : (rotation_scan_state_154 a_l b_l i )) (PreH17 : (rotation_prefix_154 b_l i j rotate_l_2 )) ,
  TT && emp 
|--
  “ ((j - (n - i ) ) = ((i + j ) % ( n ) )) ”
  &&  emp
).

Definition cycpattern_check_entail_wit_3_2_split_goal_1 := 
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l_2: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (j >= (n - i ))) (PreH4 : (j < n)) (PreH5 : (0 <= j)) (PreH6 : (j <= n)) (PreH7 : (0 < n)) (PreH8 : (0 <= i)) (PreH9 : (i < n)) (PreH10 : (rotate <> 0)) (PreH11 : ((n + 1 ) < INT_MAX)) (PreH12 : (valid_string a_l )) (PreH13 : (valid_string b_l )) (PreH14 : ((string_length (a_l)) < INT_MAX)) (PreH15 : (n = (string_length (b_l)))) (PreH16 : (rotation_scan_state_154 a_l b_l i )) (PreH17 : (rotation_prefix_154 b_l i j rotate_l_2 )) ,
  TT && emp 
|--
  “ ((j - (n - i ) ) = ((i + j ) % ( n ) )) ”
.

Definition cycpattern_check_entail_wit_4 := 
(
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l_2: (@list Z)) (idx: Z) (i: Z) (j: Z) (n: Z) (rotate: Z) (PreH1 : (idx = ((i + j ) % ( n ) ))) (PreH2 : (0 <= idx)) (PreH3 : (idx < n)) (PreH4 : (0 <= j)) (PreH5 : (j < n)) (PreH6 : (0 < n)) (PreH7 : (0 <= i)) (PreH8 : (i < n)) (PreH9 : (rotate <> 0)) (PreH10 : ((n + 1 ) < INT_MAX)) (PreH11 : (valid_string a_l )) (PreH12 : (valid_string b_l )) (PreH13 : ((string_length (a_l)) < INT_MAX)) (PreH14 : (n = (string_length (b_l)))) (PreH15 : (rotation_scan_state_154 a_l b_l i )) (PreH16 : (rotation_prefix_154 b_l i j rotate_l_2 )) ,
  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.full rotate j rotate_l_2 )
  **  (CharArray.undef_seg rotate j (n + 1 ) )
|--
  EX (rotate_l: (@list Z)) ,
  “ ((Znth idx (c_string (b_l)) 0) = (Znth (idx) (b_l) (0))) ” 
  &&  “ (idx = ((i + j ) % ( n ) )) ” 
  &&  “ (0 <= (Znth idx (c_string (b_l)) 0)) ” 
  &&  “ ((Znth idx (c_string (b_l)) 0) <= 127) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n) ” 
  &&  “ (0 < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (rotate <> 0) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (n = (string_length (b_l))) ” 
  &&  “ (rotation_scan_state_154 a_l b_l i ) ” 
  &&  “ (rotation_prefix_154 b_l i j rotate_l ) ”
  &&  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.full rotate j rotate_l )
  **  (CharArray.undef_seg rotate j (n + 1 ) )
) \/
(
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l_2: (@list Z)) (idx: Z) (i: Z) (j: Z) (n: Z) (rotate: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (idx = ((i + j ) % ( n ) ))) (PreH4 : (0 <= idx)) (PreH5 : (idx < n)) (PreH6 : (0 <= j)) (PreH7 : (j < n)) (PreH8 : (0 < n)) (PreH9 : (0 <= i)) (PreH10 : (i < n)) (PreH11 : (rotate <> 0)) (PreH12 : ((n + 1 ) < INT_MAX)) (PreH13 : (valid_string a_l )) (PreH14 : (valid_string b_l )) (PreH15 : ((string_length (a_l)) < INT_MAX)) (PreH16 : (n = (string_length (b_l)))) (PreH17 : (rotation_scan_state_154 a_l b_l i )) (PreH18 : (rotation_prefix_154 b_l i j rotate_l_2 )) ,
  TT && emp 
|--
  “ ((Znth idx (c_string (b_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth idx (c_string (b_l)) 0)) ” 
  &&  “ ((Znth idx (c_string (b_l)) 0) = (Znth (idx) (b_l) (0))) ”
  &&  emp
).

Definition cycpattern_check_entail_wit_4_split_goal_1 := 
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l_2: (@list Z)) (idx: Z) (i: Z) (j: Z) (n: Z) (rotate: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (idx = ((i + j ) % ( n ) ))) (PreH4 : (0 <= idx)) (PreH5 : (idx < n)) (PreH6 : (0 <= j)) (PreH7 : (j < n)) (PreH8 : (0 < n)) (PreH9 : (0 <= i)) (PreH10 : (i < n)) (PreH11 : (rotate <> 0)) (PreH12 : ((n + 1 ) < INT_MAX)) (PreH13 : (valid_string a_l )) (PreH14 : (valid_string b_l )) (PreH15 : ((string_length (a_l)) < INT_MAX)) (PreH16 : (n = (string_length (b_l)))) (PreH17 : (rotation_scan_state_154 a_l b_l i )) (PreH18 : (rotation_prefix_154 b_l i j rotate_l_2 )) ,
  TT && emp 
|--
  “ ((Znth idx (c_string (b_l)) 0) <= 127) ”
.

Definition cycpattern_check_entail_wit_4_split_goal_2 := 
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l_2: (@list Z)) (idx: Z) (i: Z) (j: Z) (n: Z) (rotate: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (idx = ((i + j ) % ( n ) ))) (PreH4 : (0 <= idx)) (PreH5 : (idx < n)) (PreH6 : (0 <= j)) (PreH7 : (j < n)) (PreH8 : (0 < n)) (PreH9 : (0 <= i)) (PreH10 : (i < n)) (PreH11 : (rotate <> 0)) (PreH12 : ((n + 1 ) < INT_MAX)) (PreH13 : (valid_string a_l )) (PreH14 : (valid_string b_l )) (PreH15 : ((string_length (a_l)) < INT_MAX)) (PreH16 : (n = (string_length (b_l)))) (PreH17 : (rotation_scan_state_154 a_l b_l i )) (PreH18 : (rotation_prefix_154 b_l i j rotate_l_2 )) ,
  TT && emp 
|--
  “ (0 <= (Znth idx (c_string (b_l)) 0)) ”
.

Definition cycpattern_check_entail_wit_4_split_goal_3 := 
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l_2: (@list Z)) (idx: Z) (i: Z) (j: Z) (n: Z) (rotate: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (idx = ((i + j ) % ( n ) ))) (PreH4 : (0 <= idx)) (PreH5 : (idx < n)) (PreH6 : (0 <= j)) (PreH7 : (j < n)) (PreH8 : (0 < n)) (PreH9 : (0 <= i)) (PreH10 : (i < n)) (PreH11 : (rotate <> 0)) (PreH12 : ((n + 1 ) < INT_MAX)) (PreH13 : (valid_string a_l )) (PreH14 : (valid_string b_l )) (PreH15 : ((string_length (a_l)) < INT_MAX)) (PreH16 : (n = (string_length (b_l)))) (PreH17 : (rotation_scan_state_154 a_l b_l i )) (PreH18 : (rotation_prefix_154 b_l i j rotate_l_2 )) ,
  TT && emp 
|--
  “ ((Znth idx (c_string (b_l)) 0) = (Znth (idx) (b_l) (0))) ”
.

Definition cycpattern_check_entail_wit_5 := 
(
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l_2: (@list Z)) (ch: Z) (idx: Z) (i: Z) (j: Z) (n: Z) (rotate: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (ch = (Znth (idx) (b_l) (0)))) (PreH4 : (idx = ((i + j ) % ( n ) ))) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (0 <= idx)) (PreH8 : (idx < n)) (PreH9 : (0 <= j)) (PreH10 : (j < n)) (PreH11 : (0 < n)) (PreH12 : (0 <= i)) (PreH13 : (i < n)) (PreH14 : (rotate <> 0)) (PreH15 : ((n + 1 ) < INT_MAX)) (PreH16 : (valid_string a_l )) (PreH17 : (valid_string b_l )) (PreH18 : ((string_length (a_l)) < INT_MAX)) (PreH19 : (n = (string_length (b_l)))) (PreH20 : (rotation_scan_state_154 a_l b_l i )) (PreH21 : (rotation_prefix_154 b_l i j rotate_l_2 )) ,
  (CharArray.full rotate (j + 1 ) (app (rotate_l_2) ((cons (ch) ((@nil Z))))) )
  **  (CharArray.undef_seg rotate (j + 1 ) (n + 1 ) )
  **  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
|--
  EX (rotate_l: (@list Z)) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n) ” 
  &&  “ (0 < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (rotate <> 0) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (n = (string_length (b_l))) ” 
  &&  “ (rotation_scan_state_154 a_l b_l i ) ” 
  &&  “ (rotation_prefix_154 b_l i (j + 1 ) rotate_l ) ”
  &&  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.full rotate (j + 1 ) rotate_l )
  **  (CharArray.undef_seg rotate (j + 1 ) (n + 1 ) )
) \/
(
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l_2: (@list Z)) (ch: Z) (idx: Z) (i: Z) (j: Z) (n: Z) (rotate: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (ch = (Znth (idx) (b_l) (0)))) (PreH4 : (idx = ((i + j ) % ( n ) ))) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (0 <= idx)) (PreH8 : (idx < n)) (PreH9 : (0 <= j)) (PreH10 : (j < n)) (PreH11 : (0 < n)) (PreH12 : (0 <= i)) (PreH13 : (i < n)) (PreH14 : (rotate <> 0)) (PreH15 : ((n + 1 ) < INT_MAX)) (PreH16 : (valid_string a_l )) (PreH17 : (valid_string b_l )) (PreH18 : ((string_length (a_l)) < INT_MAX)) (PreH19 : (n = (string_length (b_l)))) (PreH20 : (rotation_scan_state_154 a_l b_l i )) (PreH21 : (rotation_prefix_154 b_l i j rotate_l_2 )) ,
  TT && emp 
|--
  “ (rotation_prefix_154 b_l i (j + 1 ) (app (rotate_l_2) ((cons (ch) ((@nil Z))))) ) ”
  &&  emp
).

Definition cycpattern_check_entail_wit_5_split_goal_1 := 
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l_2: (@list Z)) (ch: Z) (idx: Z) (i: Z) (j: Z) (n: Z) (rotate: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (ch = (Znth (idx) (b_l) (0)))) (PreH4 : (idx = ((i + j ) % ( n ) ))) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (0 <= idx)) (PreH8 : (idx < n)) (PreH9 : (0 <= j)) (PreH10 : (j < n)) (PreH11 : (0 < n)) (PreH12 : (0 <= i)) (PreH13 : (i < n)) (PreH14 : (rotate <> 0)) (PreH15 : ((n + 1 ) < INT_MAX)) (PreH16 : (valid_string a_l )) (PreH17 : (valid_string b_l )) (PreH18 : ((string_length (a_l)) < INT_MAX)) (PreH19 : (n = (string_length (b_l)))) (PreH20 : (rotation_scan_state_154 a_l b_l i )) (PreH21 : (rotation_prefix_154 b_l i j rotate_l_2 )) ,
  TT && emp 
|--
  “ (rotation_prefix_154 b_l i (j + 1 ) (app (rotate_l_2) ((cons (ch) ((@nil Z))))) ) ”
.

Definition cycpattern_check_entail_wit_6 := 
(
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (j >= n)) (PreH4 : (0 <= j)) (PreH5 : (j <= n)) (PreH6 : (0 < n)) (PreH7 : (0 <= i)) (PreH8 : (i < n)) (PreH9 : (rotate <> 0)) (PreH10 : ((n + 1 ) < INT_MAX)) (PreH11 : (valid_string a_l )) (PreH12 : (valid_string b_l )) (PreH13 : ((string_length (a_l)) < INT_MAX)) (PreH14 : (n = (string_length (b_l)))) (PreH15 : (rotation_scan_state_154 a_l b_l i )) (PreH16 : (rotation_prefix_154 b_l i j rotate_l )) ,
  (CharArray.full rotate (j + 1 ) (app (rotate_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg rotate (n + 1 ) (n + 1 ) )
  **  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
|--
  “ (rotate <> 0) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (n = (string_length (b_l))) ” 
  &&  “ (rotation_scan_state_154 a_l b_l i ) ” 
  &&  “ (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) ) ” 
  &&  “ (valid_string (rotate_at_154 (b_l) (i)) ) ”
  &&  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (store_string rotate (rotate_at_154 (b_l) (i)) )
) \/
(
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (0 <= (j + 1 ))) (PreH2 : (0 <= ((string_length (b_l)) + 1 ))) (PreH3 : (0 <= ((string_length (a_l)) + 1 ))) (PreH4 : (j >= n)) (PreH5 : (0 <= j)) (PreH6 : (j <= n)) (PreH7 : (0 < n)) (PreH8 : (0 <= i)) (PreH9 : (i < n)) (PreH10 : (rotate <> 0)) (PreH11 : ((n + 1 ) < INT_MAX)) (PreH12 : (valid_string a_l )) (PreH13 : (valid_string b_l )) (PreH14 : ((string_length (a_l)) < INT_MAX)) (PreH15 : (n = (string_length (b_l)))) (PreH16 : (rotation_scan_state_154 a_l b_l i )) (PreH17 : (rotation_prefix_154 b_l i j rotate_l )) ,
  (CharArray.full rotate (j + 1 ) (app (rotate_l) ((cons (0) ((@nil Z))))) )
|--
  “ (valid_string (rotate_at_154 (b_l) (i)) ) ” 
  &&  “ (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) ) ”
  &&  (CharArray.full rotate ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ) (c_string ((rotate_at_154 (b_l) (i)))) )
).

Definition cycpattern_check_entail_wit_6_split_goal_1 := 
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (0 <= (j + 1 ))) (PreH2 : (0 <= ((string_length (b_l)) + 1 ))) (PreH3 : (0 <= ((string_length (a_l)) + 1 ))) (PreH4 : (j >= n)) (PreH5 : (0 <= j)) (PreH6 : (j <= n)) (PreH7 : (0 < n)) (PreH8 : (0 <= i)) (PreH9 : (i < n)) (PreH10 : (rotate <> 0)) (PreH11 : ((n + 1 ) < INT_MAX)) (PreH12 : (valid_string a_l )) (PreH13 : (valid_string b_l )) (PreH14 : ((string_length (a_l)) < INT_MAX)) (PreH15 : (n = (string_length (b_l)))) (PreH16 : (rotation_scan_state_154 a_l b_l i )) (PreH17 : (rotation_prefix_154 b_l i j rotate_l )) ,
  (CharArray.full rotate (j + 1 ) (app (rotate_l) ((cons (0) ((@nil Z))))) )
|--
  “ (valid_string (rotate_at_154 (b_l) (i)) ) ”
.

Definition cycpattern_check_entail_wit_6_split_goal_2 := 
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (0 <= (j + 1 ))) (PreH2 : (0 <= ((string_length (b_l)) + 1 ))) (PreH3 : (0 <= ((string_length (a_l)) + 1 ))) (PreH4 : (j >= n)) (PreH5 : (0 <= j)) (PreH6 : (j <= n)) (PreH7 : (0 < n)) (PreH8 : (0 <= i)) (PreH9 : (i < n)) (PreH10 : (rotate <> 0)) (PreH11 : ((n + 1 ) < INT_MAX)) (PreH12 : (valid_string a_l )) (PreH13 : (valid_string b_l )) (PreH14 : ((string_length (a_l)) < INT_MAX)) (PreH15 : (n = (string_length (b_l)))) (PreH16 : (rotation_scan_state_154 a_l b_l i )) (PreH17 : (rotation_prefix_154 b_l i j rotate_l )) ,
  (CharArray.full rotate (j + 1 ) (app (rotate_l) ((cons (0) ((@nil Z))))) )
|--
  “ (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) ) ”
.

Definition cycpattern_check_entail_wit_6_split_goal_spatial := 
forall (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (0 <= (j + 1 ))) (PreH2 : (0 <= ((string_length (b_l)) + 1 ))) (PreH3 : (0 <= ((string_length (a_l)) + 1 ))) (PreH4 : (j >= n)) (PreH5 : (0 <= j)) (PreH6 : (j <= n)) (PreH7 : (0 < n)) (PreH8 : (0 <= i)) (PreH9 : (i < n)) (PreH10 : (rotate <> 0)) (PreH11 : ((n + 1 ) < INT_MAX)) (PreH12 : (valid_string a_l )) (PreH13 : (valid_string b_l )) (PreH14 : ((string_length (a_l)) < INT_MAX)) (PreH15 : (n = (string_length (b_l)))) (PreH16 : (rotation_scan_state_154 a_l b_l i )) (PreH17 : (rotation_prefix_154 b_l i j rotate_l )) ,
  (CharArray.full rotate (j + 1 ) (app (rotate_l) ((cons (0) ((@nil Z))))) )
|--
  (CharArray.full rotate ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ) (c_string ((rotate_at_154 (b_l) (i)))) )
.

Definition cycpattern_check_entail_wit_7 := 
(
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strstr_result a_l (rotate_at_154 (b_l) (i)) retval a0 )) (PreH3 : (0 <= ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ))) (PreH4 : (0 <= ((string_length (b_l)) + 1 ))) (PreH5 : (0 <= ((string_length (a_l)) + 1 ))) (PreH6 : (rotate <> 0)) (PreH7 : ((n + 1 ) < INT_MAX)) (PreH8 : (valid_string a_l )) (PreH9 : (valid_string b_l )) (PreH10 : ((string_length (a_l)) < INT_MAX)) (PreH11 : (n = (string_length (b_l)))) (PreH12 : (rotation_scan_state_154 a_l b_l i )) (PreH13 : (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) )) (PreH14 : (valid_string (rotate_at_154 (b_l) (i)) )) ,
  (store_string a0 a_l )
  **  (store_string rotate (rotate_at_154 (b_l) (i)) )
  **  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
|--
  “ (retval <> 0) ” 
  &&  “ (rotate <> 0) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (n = (string_length (b_l))) ” 
  &&  “ (rotation_success_154 a_l b_l i (rotate_at_154 (b_l) (i)) ) ”
  &&  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
) \/
(
forall (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strstr_result a_l (rotate_at_154 (b_l) (i)) retval a0 )) (PreH3 : (0 <= ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ))) (PreH4 : (0 <= ((string_length (b_l)) + 1 ))) (PreH5 : (0 <= ((string_length (a_l)) + 1 ))) (PreH6 : (rotate <> 0)) (PreH7 : ((n + 1 ) < INT_MAX)) (PreH8 : (valid_string a_l )) (PreH9 : (valid_string b_l )) (PreH10 : ((string_length (a_l)) < INT_MAX)) (PreH11 : (n = (string_length (b_l)))) (PreH12 : (rotation_scan_state_154 a_l b_l i )) (PreH13 : (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) )) (PreH14 : (valid_string (rotate_at_154 (b_l) (i)) )) ,
  (CharArray.full rotate ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ) (c_string ((rotate_at_154 (b_l) (i)))) )
|--
  “ (rotation_success_154 a_l b_l i (rotate_at_154 (b_l) (i)) ) ”
  &&  (CharArray.undef_full rotate (n + 1 ) )
).

Definition cycpattern_check_entail_wit_7_split_goal_1 := 
forall (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strstr_result a_l (rotate_at_154 (b_l) (i)) retval a0 )) (PreH3 : (0 <= ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ))) (PreH4 : (0 <= ((string_length (b_l)) + 1 ))) (PreH5 : (0 <= ((string_length (a_l)) + 1 ))) (PreH6 : (rotate <> 0)) (PreH7 : ((n + 1 ) < INT_MAX)) (PreH8 : (valid_string a_l )) (PreH9 : (valid_string b_l )) (PreH10 : ((string_length (a_l)) < INT_MAX)) (PreH11 : (n = (string_length (b_l)))) (PreH12 : (rotation_scan_state_154 a_l b_l i )) (PreH13 : (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) )) (PreH14 : (valid_string (rotate_at_154 (b_l) (i)) )) ,
  (CharArray.full rotate ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ) (c_string ((rotate_at_154 (b_l) (i)))) )
|--
  “ (rotation_success_154 a_l b_l i (rotate_at_154 (b_l) (i)) ) ”
.

Definition cycpattern_check_entail_wit_7_split_goal_spatial := 
forall (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strstr_result a_l (rotate_at_154 (b_l) (i)) retval a0 )) (PreH3 : (0 <= ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ))) (PreH4 : (0 <= ((string_length (b_l)) + 1 ))) (PreH5 : (0 <= ((string_length (a_l)) + 1 ))) (PreH6 : (rotate <> 0)) (PreH7 : ((n + 1 ) < INT_MAX)) (PreH8 : (valid_string a_l )) (PreH9 : (valid_string b_l )) (PreH10 : ((string_length (a_l)) < INT_MAX)) (PreH11 : (n = (string_length (b_l)))) (PreH12 : (rotation_scan_state_154 a_l b_l i )) (PreH13 : (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) )) (PreH14 : (valid_string (rotate_at_154 (b_l) (i)) )) ,
  (CharArray.full rotate ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ) (c_string ((rotate_at_154 (b_l) (i)))) )
|--
  (CharArray.undef_full rotate (n + 1 ) )
.

Definition cycpattern_check_entail_wit_8 := 
(
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strstr_result a_l (rotate_at_154 (b_l) (i)) retval a0 )) (PreH3 : (0 <= ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ))) (PreH4 : (0 <= ((string_length (b_l)) + 1 ))) (PreH5 : (0 <= ((string_length (a_l)) + 1 ))) (PreH6 : (rotate <> 0)) (PreH7 : ((n + 1 ) < INT_MAX)) (PreH8 : (valid_string a_l )) (PreH9 : (valid_string b_l )) (PreH10 : ((string_length (a_l)) < INT_MAX)) (PreH11 : (n = (string_length (b_l)))) (PreH12 : (rotation_scan_state_154 a_l b_l i )) (PreH13 : (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) )) (PreH14 : (valid_string (rotate_at_154 (b_l) (i)) )) ,
  (store_string a0 a_l )
  **  (store_string rotate (rotate_at_154 (b_l) (i)) )
  **  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
|--
  “ (retval = 0) ” 
  &&  “ (rotate <> 0) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (n = (string_length (b_l))) ” 
  &&  “ (rotation_scan_state_154 a_l b_l (i + 1 ) ) ”
  &&  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
) \/
(
forall (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strstr_result a_l (rotate_at_154 (b_l) (i)) retval a0 )) (PreH3 : (0 <= ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ))) (PreH4 : (0 <= ((string_length (b_l)) + 1 ))) (PreH5 : (0 <= ((string_length (a_l)) + 1 ))) (PreH6 : (rotate <> 0)) (PreH7 : ((n + 1 ) < INT_MAX)) (PreH8 : (valid_string a_l )) (PreH9 : (valid_string b_l )) (PreH10 : ((string_length (a_l)) < INT_MAX)) (PreH11 : (n = (string_length (b_l)))) (PreH12 : (rotation_scan_state_154 a_l b_l i )) (PreH13 : (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) )) (PreH14 : (valid_string (rotate_at_154 (b_l) (i)) )) ,
  (CharArray.full rotate ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ) (c_string ((rotate_at_154 (b_l) (i)))) )
|--
  “ (rotation_scan_state_154 a_l b_l (i + 1 ) ) ”
  &&  (CharArray.undef_full rotate (n + 1 ) )
).

Definition cycpattern_check_entail_wit_8_split_goal_1 := 
forall (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strstr_result a_l (rotate_at_154 (b_l) (i)) retval a0 )) (PreH3 : (0 <= ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ))) (PreH4 : (0 <= ((string_length (b_l)) + 1 ))) (PreH5 : (0 <= ((string_length (a_l)) + 1 ))) (PreH6 : (rotate <> 0)) (PreH7 : ((n + 1 ) < INT_MAX)) (PreH8 : (valid_string a_l )) (PreH9 : (valid_string b_l )) (PreH10 : ((string_length (a_l)) < INT_MAX)) (PreH11 : (n = (string_length (b_l)))) (PreH12 : (rotation_scan_state_154 a_l b_l i )) (PreH13 : (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) )) (PreH14 : (valid_string (rotate_at_154 (b_l) (i)) )) ,
  (CharArray.full rotate ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ) (c_string ((rotate_at_154 (b_l) (i)))) )
|--
  “ (rotation_scan_state_154 a_l b_l (i + 1 ) ) ”
.

Definition cycpattern_check_entail_wit_8_split_goal_spatial := 
forall (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strstr_result a_l (rotate_at_154 (b_l) (i)) retval a0 )) (PreH3 : (0 <= ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ))) (PreH4 : (0 <= ((string_length (b_l)) + 1 ))) (PreH5 : (0 <= ((string_length (a_l)) + 1 ))) (PreH6 : (rotate <> 0)) (PreH7 : ((n + 1 ) < INT_MAX)) (PreH8 : (valid_string a_l )) (PreH9 : (valid_string b_l )) (PreH10 : ((string_length (a_l)) < INT_MAX)) (PreH11 : (n = (string_length (b_l)))) (PreH12 : (rotation_scan_state_154 a_l b_l i )) (PreH13 : (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) )) (PreH14 : (valid_string (rotate_at_154 (b_l) (i)) )) ,
  (CharArray.full rotate ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ) (c_string ((rotate_at_154 (b_l) (i)))) )
|--
  (CharArray.undef_full rotate (n + 1 ) )
.

Definition cycpattern_check_entail_wit_9 := 
(
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (hit: Z) (rotate: Z) (n: Z) (i: Z) (PreH1 : (hit = 0)) (PreH2 : (rotate <> 0)) (PreH3 : ((n + 1 ) < INT_MAX)) (PreH4 : (valid_string a_l )) (PreH5 : (valid_string b_l )) (PreH6 : ((string_length (a_l)) < INT_MAX)) (PreH7 : (n = (string_length (b_l)))) (PreH8 : (rotation_scan_state_154 a_l b_l (i + 1 ) )) ,
  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (rotate <> 0) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (n = (string_length (b_l))) ” 
  &&  “ (rotation_scan_state_154 a_l b_l (i + 1 ) ) ”
  &&  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
) \/
(
forall (b_l: (@list Z)) (a_l: (@list Z)) (hit: Z) (rotate: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (hit = 0)) (PreH4 : (rotate <> 0)) (PreH5 : ((n + 1 ) < INT_MAX)) (PreH6 : (valid_string a_l )) (PreH7 : (valid_string b_l )) (PreH8 : ((string_length (a_l)) < INT_MAX)) (PreH9 : (n = (string_length (b_l)))) (PreH10 : (rotation_scan_state_154 a_l b_l (i + 1 ) )) ,
  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= (i + 1 )) ”
  &&  (CharArray.undef_full rotate (n + 1 ) )
).

Definition cycpattern_check_entail_wit_9_split_goal_1 := 
forall (b_l: (@list Z)) (a_l: (@list Z)) (hit: Z) (rotate: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (hit = 0)) (PreH4 : (rotate <> 0)) (PreH5 : ((n + 1 ) < INT_MAX)) (PreH6 : (valid_string a_l )) (PreH7 : (valid_string b_l )) (PreH8 : ((string_length (a_l)) < INT_MAX)) (PreH9 : (n = (string_length (b_l)))) (PreH10 : (rotation_scan_state_154 a_l b_l (i + 1 ) )) ,
  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ ((i + 1 ) <= n) ”
.

Definition cycpattern_check_entail_wit_9_split_goal_2 := 
forall (b_l: (@list Z)) (a_l: (@list Z)) (hit: Z) (rotate: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (hit = 0)) (PreH4 : (rotate <> 0)) (PreH5 : ((n + 1 ) < INT_MAX)) (PreH6 : (valid_string a_l )) (PreH7 : (valid_string b_l )) (PreH8 : ((string_length (a_l)) < INT_MAX)) (PreH9 : (n = (string_length (b_l)))) (PreH10 : (rotation_scan_state_154 a_l b_l (i + 1 ) )) ,
  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ (0 <= (i + 1 )) ”
.

Definition cycpattern_check_entail_wit_9_split_goal_spatial := 
forall (b_l: (@list Z)) (a_l: (@list Z)) (hit: Z) (rotate: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (hit = 0)) (PreH4 : (rotate <> 0)) (PreH5 : ((n + 1 ) < INT_MAX)) (PreH6 : (valid_string a_l )) (PreH7 : (valid_string b_l )) (PreH8 : ((string_length (a_l)) < INT_MAX)) (PreH9 : (n = (string_length (b_l)))) (PreH10 : (rotation_scan_state_154 a_l b_l (i + 1 ) )) ,
  (CharArray.undef_full rotate (n + 1 ) )
|--
  (CharArray.undef_full rotate (n + 1 ) )
.

Definition cycpattern_check_return_wit_1 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (rotate <> 0)) (PreH7 : ((n + 1 ) < INT_MAX)) (PreH8 : (valid_string a_l )) (PreH9 : (valid_string b_l )) (PreH10 : ((string_length (a_l)) < INT_MAX)) (PreH11 : (n = (string_length (b_l)))) (PreH12 : (rotation_scan_state_154 a_l b_l i )) ,
  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
|--
  (“ (0 = 0) ” 
  &&  “ (problem_154_spec_z a_l b_l 0 ) ”
  &&  (store_string a0 a_l )
  **  (store_string b0 b_l ))
  ||
  (“ (0 = 1) ” 
  &&  “ (problem_154_spec_z a_l b_l 0 ) ”
  &&  (store_string a0 a_l )
  **  (store_string b0 b_l ))
.

Definition cycpattern_check_return_wit_2 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (hit: Z) (rotate: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (b_l)) + 1 ))) (PreH2 : (0 <= ((string_length (a_l)) + 1 ))) (PreH3 : (hit <> 0)) (PreH4 : (rotate <> 0)) (PreH5 : ((n + 1 ) < INT_MAX)) (PreH6 : (valid_string a_l )) (PreH7 : (valid_string b_l )) (PreH8 : ((string_length (a_l)) < INT_MAX)) (PreH9 : (n = (string_length (b_l)))) (PreH10 : (rotation_success_154 a_l b_l i (rotate_at_154 (b_l) (i)) )) ,
  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
|--
  (“ (1 = 0) ” 
  &&  “ (problem_154_spec_z a_l b_l 1 ) ”
  &&  (store_string a0 a_l )
  **  (store_string b0 b_l ))
  ||
  (“ (1 = 1) ” 
  &&  “ (problem_154_spec_z a_l b_l 1 ) ”
  &&  (store_string a0 a_l )
  **  (store_string b0 b_l ))
.

Definition cycpattern_check_partial_solve_wit_1_pure := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (problem_154_pre_z a_l b_l )) (PreH4 : (valid_string a_l )) (PreH5 : (valid_string b_l )) (PreH6 : ((string_length (a_l)) < INT_MAX)) (PreH7 : (((string_length (b_l)) + 1 ) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
|--
  “ (valid_string b_l ) ” 
  &&  “ ((string_length (b_l)) < INT_MAX) ”
.

Definition cycpattern_check_partial_solve_wit_1_aux := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (problem_154_pre_z a_l b_l )) (PreH4 : (valid_string a_l )) (PreH5 : (valid_string b_l )) (PreH6 : ((string_length (a_l)) < INT_MAX)) (PreH7 : (((string_length (b_l)) + 1 ) < INT_MAX)) ,
  (store_string a0 a_l )
  **  (store_string b0 b_l )
|--
  “ (valid_string b_l ) ” 
  &&  “ ((string_length (b_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (b_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (a_l)) + 1 )) ” 
  &&  “ (a_pre = a0) ” 
  &&  “ (b_pre = b0) ” 
  &&  “ (problem_154_pre_z a_l b_l ) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (((string_length (b_l)) + 1 ) < INT_MAX) ”
  &&  (store_string b_pre b_l )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
.

Definition cycpattern_check_partial_solve_wit_1 := cycpattern_check_partial_solve_wit_1_pure -> cycpattern_check_partial_solve_wit_1_aux.

Definition cycpattern_check_partial_solve_wit_2_pure := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (b_l)))) (PreH2 : (0 <= ((string_length (b_l)) + 1 ))) (PreH3 : (0 <= ((string_length (a_l)) + 1 ))) (PreH4 : (a_pre = a0)) (PreH5 : (b_pre = b0)) (PreH6 : (problem_154_pre_z a_l b_l )) (PreH7 : (valid_string a_l )) (PreH8 : (valid_string b_l )) (PreH9 : ((string_length (a_l)) < INT_MAX)) (PreH10 : (((string_length (b_l)) + 1 ) < INT_MAX)) ,
  ((( &( "rotate" ) )) # Ptr  |->_)
  **  (store_string b_pre b_l )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) < INT_MAX) ”
.

Definition cycpattern_check_partial_solve_wit_2_aux := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (b_l)))) (PreH2 : (0 <= ((string_length (b_l)) + 1 ))) (PreH3 : (0 <= ((string_length (a_l)) + 1 ))) (PreH4 : (a_pre = a0)) (PreH5 : (b_pre = b0)) (PreH6 : (problem_154_pre_z a_l b_l )) (PreH7 : (valid_string a_l )) (PreH8 : (valid_string b_l )) (PreH9 : ((string_length (a_l)) < INT_MAX)) (PreH10 : (((string_length (b_l)) + 1 ) < INT_MAX)) ,
  (store_string b_pre b_l )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
|--
  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ (retval = (string_length (b_l))) ” 
  &&  “ (0 <= ((string_length (b_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (a_l)) + 1 )) ” 
  &&  “ (a_pre = a0) ” 
  &&  “ (b_pre = b0) ” 
  &&  “ (problem_154_pre_z a_l b_l ) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (((string_length (b_l)) + 1 ) < INT_MAX) ”
  &&  (CharArray.full b_pre ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
.

Definition cycpattern_check_partial_solve_wit_2 := cycpattern_check_partial_solve_wit_2_pure -> cycpattern_check_partial_solve_wit_2_aux.

Definition cycpattern_check_partial_solve_wit_3 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l: (@list Z)) (ch: Z) (idx: Z) (i: Z) (j: Z) (n: Z) (rotate: Z) (PreH1 : (ch = (Znth (idx) (b_l) (0)))) (PreH2 : (idx = ((i + j ) % ( n ) ))) (PreH3 : (0 <= ch)) (PreH4 : (ch <= 127)) (PreH5 : (0 <= idx)) (PreH6 : (idx < n)) (PreH7 : (0 <= j)) (PreH8 : (j < n)) (PreH9 : (0 < n)) (PreH10 : (0 <= i)) (PreH11 : (i < n)) (PreH12 : (rotate <> 0)) (PreH13 : ((n + 1 ) < INT_MAX)) (PreH14 : (valid_string a_l )) (PreH15 : (valid_string b_l )) (PreH16 : ((string_length (a_l)) < INT_MAX)) (PreH17 : (n = (string_length (b_l)))) (PreH18 : (rotation_scan_state_154 a_l b_l i )) (PreH19 : (rotation_prefix_154 b_l i j rotate_l )) ,
  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.full rotate j rotate_l )
  **  (CharArray.undef_seg rotate j (n + 1 ) )
|--
  “ (0 <= ((string_length (b_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (a_l)) + 1 )) ” 
  &&  “ (ch = (Znth (idx) (b_l) (0))) ” 
  &&  “ (idx = ((i + j ) % ( n ) )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n) ” 
  &&  “ (0 < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (rotate <> 0) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (n = (string_length (b_l))) ” 
  &&  “ (rotation_scan_state_154 a_l b_l i ) ” 
  &&  “ (rotation_prefix_154 b_l i j rotate_l ) ”
  &&  (((rotate + (j * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
  **  (CharArray.undef_missing_i rotate j j (n + 1 ) )
  **  (CharArray.full rotate j rotate_l )
.

Definition cycpattern_check_partial_solve_wit_4 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate_l: (@list Z)) (rotate: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (j >= n)) (PreH2 : (0 <= j)) (PreH3 : (j <= n)) (PreH4 : (0 < n)) (PreH5 : (0 <= i)) (PreH6 : (i < n)) (PreH7 : (rotate <> 0)) (PreH8 : ((n + 1 ) < INT_MAX)) (PreH9 : (valid_string a_l )) (PreH10 : (valid_string b_l )) (PreH11 : ((string_length (a_l)) < INT_MAX)) (PreH12 : (n = (string_length (b_l)))) (PreH13 : (rotation_scan_state_154 a_l b_l i )) (PreH14 : (rotation_prefix_154 b_l i j rotate_l )) ,
  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.full rotate j rotate_l )
  **  (CharArray.undef_seg rotate j (n + 1 ) )
|--
  “ (0 <= ((string_length (b_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (a_l)) + 1 )) ” 
  &&  “ (j >= n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= n) ” 
  &&  “ (0 < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (rotate <> 0) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (n = (string_length (b_l))) ” 
  &&  “ (rotation_scan_state_154 a_l b_l i ) ” 
  &&  “ (rotation_prefix_154 b_l i j rotate_l ) ”
  &&  (((rotate + (n * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
  **  (CharArray.undef_missing_i rotate n j (n + 1 ) )
  **  (CharArray.full rotate j rotate_l )
.

Definition cycpattern_check_partial_solve_wit_5_pure := 
(
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (PreH1 : (rotate <> 0)) (PreH2 : ((n + 1 ) < INT_MAX)) (PreH3 : (valid_string a_l )) (PreH4 : (valid_string b_l )) (PreH5 : ((string_length (a_l)) < INT_MAX)) (PreH6 : (n = (string_length (b_l)))) (PreH7 : (rotation_scan_state_154 a_l b_l i )) (PreH8 : (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) )) (PreH9 : (valid_string (rotate_at_154 (b_l) (i)) )) ,
  ((( &( "hit" ) )) # Ptr  |->_)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (store_string rotate (rotate_at_154 (b_l) (i)) )
|--
  “ (valid_string a_l ) ” 
  &&  “ (valid_string (rotate_at_154 (b_l) (i)) ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ ((string_length ((rotate_at_154 (b_l) (i)))) < INT_MAX) ”
) \/
(
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (n <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (n >= INT_MIN)) (PreH5 : (0 <= ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ))) (PreH6 : (0 <= ((string_length (b_l)) + 1 ))) (PreH7 : (0 <= ((string_length (a_l)) + 1 ))) (PreH8 : (rotate <> 0)) (PreH9 : ((n + 1 ) < INT_MAX)) (PreH10 : (valid_string a_l )) (PreH11 : (valid_string b_l )) (PreH12 : ((string_length (a_l)) < INT_MAX)) (PreH13 : (n = (string_length (b_l)))) (PreH14 : (rotation_scan_state_154 a_l b_l i )) (PreH15 : (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) )) (PreH16 : (valid_string (rotate_at_154 (b_l) (i)) )) ,
  (CharArray.full rotate ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ) (c_string ((rotate_at_154 (b_l) (i)))) )
  **  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
  **  ((( &( "hit" ) )) # Ptr  |->_)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((string_length ((rotate_at_154 (b_l) (i)))) < INT_MAX) ”
).

Definition cycpattern_check_partial_solve_wit_5_pure_split_goal_1 := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (n <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (n >= INT_MIN)) (PreH5 : (0 <= ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ))) (PreH6 : (0 <= ((string_length (b_l)) + 1 ))) (PreH7 : (0 <= ((string_length (a_l)) + 1 ))) (PreH8 : (rotate <> 0)) (PreH9 : ((n + 1 ) < INT_MAX)) (PreH10 : (valid_string a_l )) (PreH11 : (valid_string b_l )) (PreH12 : ((string_length (a_l)) < INT_MAX)) (PreH13 : (n = (string_length (b_l)))) (PreH14 : (rotation_scan_state_154 a_l b_l i )) (PreH15 : (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) )) (PreH16 : (valid_string (rotate_at_154 (b_l) (i)) )) ,
  (CharArray.full rotate ((string_length ((rotate_at_154 (b_l) (i)))) + 1 ) (c_string ((rotate_at_154 (b_l) (i)))) )
  **  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
  **  ((( &( "hit" ) )) # Ptr  |->_)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((string_length ((rotate_at_154 (b_l) (i)))) < INT_MAX) ”
.

Definition cycpattern_check_partial_solve_wit_5_aux := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (PreH1 : (rotate <> 0)) (PreH2 : ((n + 1 ) < INT_MAX)) (PreH3 : (valid_string a_l )) (PreH4 : (valid_string b_l )) (PreH5 : ((string_length (a_l)) < INT_MAX)) (PreH6 : (n = (string_length (b_l)))) (PreH7 : (rotation_scan_state_154 a_l b_l i )) (PreH8 : (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) )) (PreH9 : (valid_string (rotate_at_154 (b_l) (i)) )) ,
  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (store_string rotate (rotate_at_154 (b_l) (i)) )
|--
  “ (valid_string a_l ) ” 
  &&  “ (valid_string (rotate_at_154 (b_l) (i)) ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ ((string_length ((rotate_at_154 (b_l) (i)))) < INT_MAX) ” 
  &&  “ (0 <= ((string_length ((rotate_at_154 (b_l) (i)))) + 1 )) ” 
  &&  “ (0 <= ((string_length (b_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (a_l)) + 1 )) ” 
  &&  “ (rotate <> 0) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (n = (string_length (b_l))) ” 
  &&  “ (rotation_scan_state_154 a_l b_l i ) ” 
  &&  “ (rotation_prefix_154 b_l i n (rotate_at_154 (b_l) (i)) ) ” 
  &&  “ (valid_string (rotate_at_154 (b_l) (i)) ) ”
  &&  (store_string a0 a_l )
  **  (store_string rotate (rotate_at_154 (b_l) (i)) )
  **  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
.

Definition cycpattern_check_partial_solve_wit_5 := cycpattern_check_partial_solve_wit_5_pure -> cycpattern_check_partial_solve_wit_5_aux.

Definition cycpattern_check_partial_solve_wit_6_pure := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (hit: Z) (rotate: Z) (n: Z) (i: Z) (PreH1 : (hit <> 0)) (PreH2 : (rotate <> 0)) (PreH3 : ((n + 1 ) < INT_MAX)) (PreH4 : (valid_string a_l )) (PreH5 : (valid_string b_l )) (PreH6 : ((string_length (a_l)) < INT_MAX)) (PreH7 : (n = (string_length (b_l)))) (PreH8 : (rotation_success_154 a_l b_l i (rotate_at_154 (b_l) (i)) )) ,
  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ (rotate <> 0) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ ((n + 1 ) < INT_MAX) ”
.

Definition cycpattern_check_partial_solve_wit_6_aux := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (hit: Z) (rotate: Z) (n: Z) (i: Z) (PreH1 : (hit <> 0)) (PreH2 : (rotate <> 0)) (PreH3 : ((n + 1 ) < INT_MAX)) (PreH4 : (valid_string a_l )) (PreH5 : (valid_string b_l )) (PreH6 : ((string_length (a_l)) < INT_MAX)) (PreH7 : (n = (string_length (b_l)))) (PreH8 : (rotation_success_154 a_l b_l i (rotate_at_154 (b_l) (i)) )) ,
  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ (rotate <> 0) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (b_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (a_l)) + 1 )) ” 
  &&  “ (hit <> 0) ” 
  &&  “ (rotate <> 0) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (n = (string_length (b_l))) ” 
  &&  “ (rotation_success_154 a_l b_l i (rotate_at_154 (b_l) (i)) ) ”
  &&  (CharArray.undef_full rotate (n + 1 ) )
  **  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
.

Definition cycpattern_check_partial_solve_wit_6 := cycpattern_check_partial_solve_wit_6_pure -> cycpattern_check_partial_solve_wit_6_aux.

Definition cycpattern_check_partial_solve_wit_7_pure := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (rotate <> 0)) (PreH5 : ((n + 1 ) < INT_MAX)) (PreH6 : (valid_string a_l )) (PreH7 : (valid_string b_l )) (PreH8 : ((string_length (a_l)) < INT_MAX)) (PreH9 : (n = (string_length (b_l)))) (PreH10 : (rotation_scan_state_154 a_l b_l i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "rotate" ) )) # Ptr  |-> rotate)
  **  ((( &( "a" ) )) # Ptr  |-> a0)
  **  ((( &( "b" ) )) # Ptr  |-> b0)
  **  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ (rotate <> 0) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ ((n + 1 ) < INT_MAX) ”
.

Definition cycpattern_check_partial_solve_wit_7_aux := 
forall (b0: Z) (a0: Z) (b_l: (@list Z)) (a_l: (@list Z)) (rotate: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (rotate <> 0)) (PreH5 : ((n + 1 ) < INT_MAX)) (PreH6 : (valid_string a_l )) (PreH7 : (valid_string b_l )) (PreH8 : ((string_length (a_l)) < INT_MAX)) (PreH9 : (n = (string_length (b_l)))) (PreH10 : (rotation_scan_state_154 a_l b_l i )) ,
  (store_string a0 a_l )
  **  (store_string b0 b_l )
  **  (CharArray.undef_full rotate (n + 1 ) )
|--
  “ (rotate <> 0) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (b_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (a_l)) + 1 )) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (rotate <> 0) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (valid_string a_l ) ” 
  &&  “ (valid_string b_l ) ” 
  &&  “ ((string_length (a_l)) < INT_MAX) ” 
  &&  “ (n = (string_length (b_l))) ” 
  &&  “ (rotation_scan_state_154 a_l b_l i ) ”
  &&  (CharArray.undef_full rotate (n + 1 ) )
  **  (CharArray.full b0 ((string_length (b_l)) + 1 ) (c_string (b_l)) )
  **  (CharArray.full a0 ((string_length (a_l)) + 1 ) (c_string (a_l)) )
.

Definition cycpattern_check_partial_solve_wit_7 := cycpattern_check_partial_solve_wit_7_pure -> cycpattern_check_partial_solve_wit_7_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_cycpattern_check_safety_wit_1 : cycpattern_check_safety_wit_1.
Axiom proof_of_cycpattern_check_safety_wit_2 : cycpattern_check_safety_wit_2.
Axiom proof_of_cycpattern_check_safety_wit_3 : cycpattern_check_safety_wit_3.
Axiom proof_of_cycpattern_check_safety_wit_4 : cycpattern_check_safety_wit_4.
Axiom proof_of_cycpattern_check_safety_wit_5 : cycpattern_check_safety_wit_5.
Axiom proof_of_cycpattern_check_safety_wit_6 : cycpattern_check_safety_wit_6.
Axiom proof_of_cycpattern_check_safety_wit_7 : cycpattern_check_safety_wit_7.
Axiom proof_of_cycpattern_check_safety_wit_8 : cycpattern_check_safety_wit_8.
Axiom proof_of_cycpattern_check_safety_wit_9 : cycpattern_check_safety_wit_9.
Axiom proof_of_cycpattern_check_safety_wit_10 : cycpattern_check_safety_wit_10.
Axiom proof_of_cycpattern_check_safety_wit_11 : cycpattern_check_safety_wit_11.
Axiom proof_of_cycpattern_check_safety_wit_12 : cycpattern_check_safety_wit_12.
Axiom proof_of_cycpattern_check_safety_wit_13 : cycpattern_check_safety_wit_13.
Axiom proof_of_cycpattern_check_safety_wit_14 : cycpattern_check_safety_wit_14.
Axiom proof_of_cycpattern_check_safety_wit_15 : cycpattern_check_safety_wit_15.
Axiom proof_of_cycpattern_check_safety_wit_16 : cycpattern_check_safety_wit_16.
Axiom proof_of_cycpattern_check_safety_wit_17 : cycpattern_check_safety_wit_17.
Axiom proof_of_cycpattern_check_safety_wit_18 : cycpattern_check_safety_wit_18.
Axiom proof_of_cycpattern_check_safety_wit_19 : cycpattern_check_safety_wit_19.
Axiom proof_of_cycpattern_check_safety_wit_20 : cycpattern_check_safety_wit_20.
Axiom proof_of_cycpattern_check_entail_wit_1 : cycpattern_check_entail_wit_1.
Axiom proof_of_cycpattern_check_entail_wit_2 : cycpattern_check_entail_wit_2.
Axiom proof_of_cycpattern_check_entail_wit_3_1 : cycpattern_check_entail_wit_3_1.
Axiom proof_of_cycpattern_check_entail_wit_3_2 : cycpattern_check_entail_wit_3_2.
Axiom proof_of_cycpattern_check_entail_wit_4 : cycpattern_check_entail_wit_4.
Axiom proof_of_cycpattern_check_entail_wit_5 : cycpattern_check_entail_wit_5.
Axiom proof_of_cycpattern_check_entail_wit_6 : cycpattern_check_entail_wit_6.
Axiom proof_of_cycpattern_check_entail_wit_7 : cycpattern_check_entail_wit_7.
Axiom proof_of_cycpattern_check_entail_wit_8 : cycpattern_check_entail_wit_8.
Axiom proof_of_cycpattern_check_entail_wit_9 : cycpattern_check_entail_wit_9.
Axiom proof_of_cycpattern_check_return_wit_1 : cycpattern_check_return_wit_1.
Axiom proof_of_cycpattern_check_return_wit_2 : cycpattern_check_return_wit_2.
Axiom proof_of_cycpattern_check_partial_solve_wit_1_pure : cycpattern_check_partial_solve_wit_1_pure.
Axiom proof_of_cycpattern_check_partial_solve_wit_1 : cycpattern_check_partial_solve_wit_1.
Axiom proof_of_cycpattern_check_partial_solve_wit_2_pure : cycpattern_check_partial_solve_wit_2_pure.
Axiom proof_of_cycpattern_check_partial_solve_wit_2 : cycpattern_check_partial_solve_wit_2.
Axiom proof_of_cycpattern_check_partial_solve_wit_3 : cycpattern_check_partial_solve_wit_3.
Axiom proof_of_cycpattern_check_partial_solve_wit_4 : cycpattern_check_partial_solve_wit_4.
Axiom proof_of_cycpattern_check_partial_solve_wit_5_pure : cycpattern_check_partial_solve_wit_5_pure.
Axiom proof_of_cycpattern_check_partial_solve_wit_5 : cycpattern_check_partial_solve_wit_5.
Axiom proof_of_cycpattern_check_partial_solve_wit_6_pure : cycpattern_check_partial_solve_wit_6_pure.
Axiom proof_of_cycpattern_check_partial_solve_wit_6 : cycpattern_check_partial_solve_wit_6.
Axiom proof_of_cycpattern_check_partial_solve_wit_7_pure : cycpattern_check_partial_solve_wit_7_pure.
Axiom proof_of_cycpattern_check_partial_solve_wit_7 : cycpattern_check_partial_solve_wit_7.

End VC_Correct.
