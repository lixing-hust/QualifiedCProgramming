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
Require Import coins_144.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function simplify -----*)

Definition simplify_safety_wit_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (ln)))) (PreH2 : (retval = (string_length (lx)))) (PreH3 : (0 <= ((string_length (ln)) + 1 ))) (PreH4 : (0 <= ((string_length (lx)) + 1 ))) (PreH5 : (valid_string lx )) (PreH6 : (valid_string ln )) (PreH7 : ((string_length (lx)) < INT_MAX)) (PreH8 : ((string_length (ln)) < INT_MAX)) (PreH9 : (problem_144_pre_z lx ln )) (PreH10 : (fraction_parts_z_144 lx sx ax bx )) (PreH11 : (fraction_parts_z_144 ln sy cn dn )) (PreH12 : (1 <= ax)) (PreH13 : (ax <= 46340)) (PreH14 : (1 <= bx)) (PreH15 : (bx <= 46340)) (PreH16 : (1 <= cn)) (PreH17 : (cn <= 46340)) (PreH18 : (1 <= dn)) (PreH19 : (dn <= 46340)) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_string n_pre ln )
  **  (CharArray.full x_pre ((string_length (lx)) + 1 ) (c_string (lx)) )
  **  ((( &( "len_n" ) )) # Int  |-> retval_2)
  **  ((( &( "len_x" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition simplify_safety_wit_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (ln)))) (PreH2 : (retval = (string_length (lx)))) (PreH3 : (0 <= ((string_length (ln)) + 1 ))) (PreH4 : (0 <= ((string_length (lx)) + 1 ))) (PreH5 : (valid_string lx )) (PreH6 : (valid_string ln )) (PreH7 : ((string_length (lx)) < INT_MAX)) (PreH8 : ((string_length (ln)) < INT_MAX)) (PreH9 : (problem_144_pre_z lx ln )) (PreH10 : (fraction_parts_z_144 lx sx ax bx )) (PreH11 : (fraction_parts_z_144 ln sy cn dn )) (PreH12 : (1 <= ax)) (PreH13 : (ax <= 46340)) (PreH14 : (1 <= bx)) (PreH15 : (bx <= 46340)) (PreH16 : (1 <= cn)) (PreH17 : (cn <= 46340)) (PreH18 : (1 <= dn)) (PreH19 : (dn <= 46340)) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_string n_pre ln )
  **  (CharArray.full x_pre ((string_length (lx)) + 1 ) (c_string (lx)) )
  **  ((( &( "len_n" ) )) # Int  |-> retval_2)
  **  ((( &( "len_x" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition simplify_safety_wit_3 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (ln)))) (PreH2 : (retval = (string_length (lx)))) (PreH3 : (0 <= ((string_length (ln)) + 1 ))) (PreH4 : (0 <= ((string_length (lx)) + 1 ))) (PreH5 : (valid_string lx )) (PreH6 : (valid_string ln )) (PreH7 : ((string_length (lx)) < INT_MAX)) (PreH8 : ((string_length (ln)) < INT_MAX)) (PreH9 : (problem_144_pre_z lx ln )) (PreH10 : (fraction_parts_z_144 lx sx ax bx )) (PreH11 : (fraction_parts_z_144 ln sy cn dn )) (PreH12 : (1 <= ax)) (PreH13 : (ax <= 46340)) (PreH14 : (1 <= bx)) (PreH15 : (bx <= 46340)) (PreH16 : (1 <= cn)) (PreH17 : (cn <= 46340)) (PreH18 : (1 <= dn)) (PreH19 : (dn <= 46340)) ,
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_string n_pre ln )
  **  (CharArray.full x_pre ((string_length (lx)) + 1 ) (c_string (lx)) )
  **  ((( &( "len_n" ) )) # Int  |-> retval_2)
  **  ((( &( "len_x" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition simplify_safety_wit_4 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (ln)))) (PreH2 : (retval = (string_length (lx)))) (PreH3 : (0 <= ((string_length (ln)) + 1 ))) (PreH4 : (0 <= ((string_length (lx)) + 1 ))) (PreH5 : (valid_string lx )) (PreH6 : (valid_string ln )) (PreH7 : ((string_length (lx)) < INT_MAX)) (PreH8 : ((string_length (ln)) < INT_MAX)) (PreH9 : (problem_144_pre_z lx ln )) (PreH10 : (fraction_parts_z_144 lx sx ax bx )) (PreH11 : (fraction_parts_z_144 ln sy cn dn )) (PreH12 : (1 <= ax)) (PreH13 : (ax <= 46340)) (PreH14 : (1 <= bx)) (PreH15 : (bx <= 46340)) (PreH16 : (1 <= cn)) (PreH17 : (cn <= 46340)) (PreH18 : (1 <= dn)) (PreH19 : (dn <= 46340)) ,
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_string n_pre ln )
  **  (CharArray.full x_pre ((string_length (lx)) + 1 ) (c_string (lx)) )
  **  ((( &( "len_n" ) )) # Int  |-> retval_2)
  **  ((( &( "len_x" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition simplify_safety_wit_5 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (ln)))) (PreH2 : (retval = (string_length (lx)))) (PreH3 : (0 <= ((string_length (ln)) + 1 ))) (PreH4 : (0 <= ((string_length (lx)) + 1 ))) (PreH5 : (valid_string lx )) (PreH6 : (valid_string ln )) (PreH7 : ((string_length (lx)) < INT_MAX)) (PreH8 : ((string_length (ln)) < INT_MAX)) (PreH9 : (problem_144_pre_z lx ln )) (PreH10 : (fraction_parts_z_144 lx sx ax bx )) (PreH11 : (fraction_parts_z_144 ln sy cn dn )) (PreH12 : (1 <= ax)) (PreH13 : (ax <= 46340)) (PreH14 : (1 <= bx)) (PreH15 : (bx <= 46340)) (PreH16 : (1 <= cn)) (PreH17 : (cn <= 46340)) (PreH18 : (1 <= dn)) (PreH19 : (dn <= 46340)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_string n_pre ln )
  **  (CharArray.full x_pre ((string_length (lx)) + 1 ) (c_string (lx)) )
  **  ((( &( "len_n" ) )) # Int  |-> retval_2)
  **  ((( &( "len_x" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition simplify_safety_wit_6 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (ln)))) (PreH2 : (retval = (string_length (lx)))) (PreH3 : (0 <= ((string_length (ln)) + 1 ))) (PreH4 : (0 <= ((string_length (lx)) + 1 ))) (PreH5 : (valid_string lx )) (PreH6 : (valid_string ln )) (PreH7 : ((string_length (lx)) < INT_MAX)) (PreH8 : ((string_length (ln)) < INT_MAX)) (PreH9 : (problem_144_pre_z lx ln )) (PreH10 : (fraction_parts_z_144 lx sx ax bx )) (PreH11 : (fraction_parts_z_144 ln sy cn dn )) (PreH12 : (1 <= ax)) (PreH13 : (ax <= 46340)) (PreH14 : (1 <= bx)) (PreH15 : (bx <= 46340)) (PreH16 : (1 <= cn)) (PreH17 : (cn <= 46340)) (PreH18 : (1 <= dn)) (PreH19 : (dn <= 46340)) ,
  ((( &( "seen_x" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_string n_pre ln )
  **  (CharArray.full x_pre ((string_length (lx)) + 1 ) (c_string (lx)) )
  **  ((( &( "len_n" ) )) # Int  |-> retval_2)
  **  ((( &( "len_x" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition simplify_safety_wit_7 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (ln)))) (PreH2 : (retval = (string_length (lx)))) (PreH3 : (0 <= ((string_length (ln)) + 1 ))) (PreH4 : (0 <= ((string_length (lx)) + 1 ))) (PreH5 : (valid_string lx )) (PreH6 : (valid_string ln )) (PreH7 : ((string_length (lx)) < INT_MAX)) (PreH8 : ((string_length (ln)) < INT_MAX)) (PreH9 : (problem_144_pre_z lx ln )) (PreH10 : (fraction_parts_z_144 lx sx ax bx )) (PreH11 : (fraction_parts_z_144 ln sy cn dn )) (PreH12 : (1 <= ax)) (PreH13 : (ax <= 46340)) (PreH14 : (1 <= bx)) (PreH15 : (bx <= 46340)) (PreH16 : (1 <= cn)) (PreH17 : (cn <= 46340)) (PreH18 : (1 <= dn)) (PreH19 : (dn <= 46340)) ,
  ((( &( "seen_n" ) )) # Int  |->_)
  **  ((( &( "seen_x" ) )) # Int  |-> 0)
  **  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_string n_pre ln )
  **  (CharArray.full x_pre ((string_length (lx)) + 1 ) (c_string (lx)) )
  **  ((( &( "len_n" ) )) # Int  |-> retval_2)
  **  ((( &( "len_x" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition simplify_safety_wit_8 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (ln)))) (PreH2 : (retval = (string_length (lx)))) (PreH3 : (0 <= ((string_length (ln)) + 1 ))) (PreH4 : (0 <= ((string_length (lx)) + 1 ))) (PreH5 : (valid_string lx )) (PreH6 : (valid_string ln )) (PreH7 : ((string_length (lx)) < INT_MAX)) (PreH8 : ((string_length (ln)) < INT_MAX)) (PreH9 : (problem_144_pre_z lx ln )) (PreH10 : (fraction_parts_z_144 lx sx ax bx )) (PreH11 : (fraction_parts_z_144 ln sy cn dn )) (PreH12 : (1 <= ax)) (PreH13 : (ax <= 46340)) (PreH14 : (1 <= bx)) (PreH15 : (bx <= 46340)) (PreH16 : (1 <= cn)) (PreH17 : (cn <= 46340)) (PreH18 : (1 <= dn)) (PreH19 : (dn <= 46340)) ,
  ((( &( "seen_n" ) )) # Int  |-> 0)
  **  ((( &( "seen_x" ) )) # Int  |-> 0)
  **  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_string n_pre ln )
  **  (CharArray.full x_pre ((string_length (lx)) + 1 ) (c_string (lx)) )
  **  ((( &( "len_n" ) )) # Int  |-> retval_2)
  **  ((( &( "len_x" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition simplify_safety_wit_9 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (i < len_x)) (PreH2 : (len_x = (string_length (lx)))) (PreH3 : (len_n = (string_length (ln)))) (PreH4 : (0 <= i)) (PreH5 : (i <= len_x)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= a)) (PreH9 : (a <= ax)) (PreH10 : (0 <= b)) (PreH11 : (b <= bx)) (PreH12 : (seen_x = 1)) (PreH13 : (c = 0)) (PreH14 : (d = 0)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (47 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 47) ”
.

Definition simplify_safety_wit_10 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (i < len_x)) (PreH2 : (len_x = (string_length (lx)))) (PreH3 : (len_n = (string_length (ln)))) (PreH4 : (0 <= i)) (PreH5 : (i <= len_x)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= a)) (PreH9 : (a <= ax)) (PreH10 : (0 <= b)) (PreH11 : (b <= bx)) (PreH12 : (seen_x = 0)) (PreH13 : (c = 0)) (PreH14 : (d = 0)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (47 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 47) ”
.

Definition simplify_safety_wit_11 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : ((Znth i (c_string (lx)) 0) = 47)) (PreH2 : (i < len_x)) (PreH3 : (len_x = (string_length (lx)))) (PreH4 : (len_n = (string_length (ln)))) (PreH5 : (0 <= i)) (PreH6 : (i <= len_x)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= a)) (PreH10 : (a <= ax)) (PreH11 : (0 <= b)) (PreH12 : (b <= bx)) (PreH13 : (seen_x = 1)) (PreH14 : (c = 0)) (PreH15 : (d = 0)) (PreH16 : (seen_n = 0)) (PreH17 : (valid_string lx )) (PreH18 : (valid_string ln )) (PreH19 : ((string_length (lx)) < INT_MAX)) (PreH20 : ((string_length (ln)) < INT_MAX)) (PreH21 : (problem_144_pre_z lx ln )) (PreH22 : (fraction_parts_z_144 lx sx ax bx )) (PreH23 : (fraction_parts_z_144 ln sy cn dn )) (PreH24 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH25 : (1 <= ax)) (PreH26 : (ax <= 46340)) (PreH27 : (1 <= bx)) (PreH28 : (bx <= 46340)) (PreH29 : (1 <= cn)) (PreH30 : (cn <= 46340)) (PreH31 : (1 <= dn)) (PreH32 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition simplify_safety_wit_12 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : ((Znth i (c_string (lx)) 0) = 47)) (PreH2 : (i < len_x)) (PreH3 : (len_x = (string_length (lx)))) (PreH4 : (len_n = (string_length (ln)))) (PreH5 : (0 <= i)) (PreH6 : (i <= len_x)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= a)) (PreH10 : (a <= ax)) (PreH11 : (0 <= b)) (PreH12 : (b <= bx)) (PreH13 : (seen_x = 0)) (PreH14 : (c = 0)) (PreH15 : (d = 0)) (PreH16 : (seen_n = 0)) (PreH17 : (valid_string lx )) (PreH18 : (valid_string ln )) (PreH19 : ((string_length (lx)) < INT_MAX)) (PreH20 : ((string_length (ln)) < INT_MAX)) (PreH21 : (problem_144_pre_z lx ln )) (PreH22 : (fraction_parts_z_144 lx sx ax bx )) (PreH23 : (fraction_parts_z_144 ln sy cn dn )) (PreH24 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH25 : (1 <= ax)) (PreH26 : (ax <= 46340)) (PreH27 : (1 <= bx)) (PreH28 : (bx <= 46340)) (PreH29 : (1 <= cn)) (PreH30 : (cn <= 46340)) (PreH31 : (1 <= dn)) (PreH32 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition simplify_safety_wit_13 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH2 : (i < len_x)) (PreH3 : (len_x = (string_length (lx)))) (PreH4 : (len_n = (string_length (ln)))) (PreH5 : (0 <= i)) (PreH6 : (i <= len_x)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= a)) (PreH10 : (a <= ax)) (PreH11 : (0 <= b)) (PreH12 : (b <= bx)) (PreH13 : (seen_x = 1)) (PreH14 : (c = 0)) (PreH15 : (d = 0)) (PreH16 : (seen_n = 0)) (PreH17 : (valid_string lx )) (PreH18 : (valid_string ln )) (PreH19 : ((string_length (lx)) < INT_MAX)) (PreH20 : ((string_length (ln)) < INT_MAX)) (PreH21 : (problem_144_pre_z lx ln )) (PreH22 : (fraction_parts_z_144 lx sx ax bx )) (PreH23 : (fraction_parts_z_144 ln sy cn dn )) (PreH24 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH25 : (1 <= ax)) (PreH26 : (ax <= 46340)) (PreH27 : (1 <= bx)) (PreH28 : (bx <= 46340)) (PreH29 : (1 <= cn)) (PreH30 : (cn <= 46340)) (PreH31 : (1 <= dn)) (PreH32 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition simplify_safety_wit_14 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH2 : (i < len_x)) (PreH3 : (len_x = (string_length (lx)))) (PreH4 : (len_n = (string_length (ln)))) (PreH5 : (0 <= i)) (PreH6 : (i <= len_x)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= a)) (PreH10 : (a <= ax)) (PreH11 : (0 <= b)) (PreH12 : (b <= bx)) (PreH13 : (seen_x = 0)) (PreH14 : (c = 0)) (PreH15 : (d = 0)) (PreH16 : (seen_n = 0)) (PreH17 : (valid_string lx )) (PreH18 : (valid_string ln )) (PreH19 : ((string_length (lx)) < INT_MAX)) (PreH20 : ((string_length (ln)) < INT_MAX)) (PreH21 : (problem_144_pre_z lx ln )) (PreH22 : (fraction_parts_z_144 lx sx ax bx )) (PreH23 : (fraction_parts_z_144 ln sy cn dn )) (PreH24 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH25 : (1 <= ax)) (PreH26 : (ax <= 46340)) (PreH27 : (1 <= bx)) (PreH28 : (bx <= 46340)) (PreH29 : (1 <= cn)) (PreH30 : (cn <= 46340)) (PreH31 : (1 <= dn)) (PreH32 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition simplify_safety_wit_15 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x = 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ False ”
.

Definition simplify_safety_wit_16 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x <> 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ False ”
.

Definition simplify_safety_wit_17 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x = 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((a * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) )) ”
) \/
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x = 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((a * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) )) ”
).

Definition simplify_safety_wit_17_split_goal_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x = 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((a * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) ) <= INT_MAX) ”
.

Definition simplify_safety_wit_17_split_goal_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x = 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((INT_MIN) <= ((a * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) )) ”
.

Definition simplify_safety_wit_18 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x = 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((Znth i (c_string (lx)) 0) - 48 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (lx)) 0) - 48 )) ”
) \/
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x = 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((Znth i (c_string (lx)) 0) - 48 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (lx)) 0) - 48 )) ”
).

Definition simplify_safety_wit_18_split_goal_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x = 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((Znth i (c_string (lx)) 0) - 48 ) <= INT_MAX) ”
.

Definition simplify_safety_wit_18_split_goal_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x = 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((INT_MIN) <= ((Znth i (c_string (lx)) 0) - 48 )) ”
.

Definition simplify_safety_wit_19 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x = 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((a * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a * 10 )) ”
.

Definition simplify_safety_wit_20 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x = 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition simplify_safety_wit_21 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x = 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition simplify_safety_wit_22 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x <> 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((b * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) )) ”
) \/
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x <> 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((b * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) )) ”
).

Definition simplify_safety_wit_22_split_goal_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x <> 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((b * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) ) <= INT_MAX) ”
.

Definition simplify_safety_wit_22_split_goal_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x <> 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((INT_MIN) <= ((b * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) )) ”
.

Definition simplify_safety_wit_23 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x <> 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((Znth i (c_string (lx)) 0) - 48 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (lx)) 0) - 48 )) ”
) \/
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x <> 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((Znth i (c_string (lx)) 0) - 48 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (lx)) 0) - 48 )) ”
).

Definition simplify_safety_wit_23_split_goal_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x <> 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((Znth i (c_string (lx)) 0) - 48 ) <= INT_MAX) ”
.

Definition simplify_safety_wit_23_split_goal_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x <> 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((INT_MIN) <= ((Znth i (c_string (lx)) 0) - 48 )) ”
.

Definition simplify_safety_wit_24 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x <> 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((b * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b * 10 )) ”
.

Definition simplify_safety_wit_25 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x <> 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition simplify_safety_wit_26 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x <> 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (lx)) 0))
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition simplify_safety_wit_27 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (a: Z) (b: Z) (seen_x: Z) (c: Z) (d: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (0 <= i)) (PreH4 : (i < len_x)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (0 <= a)) (PreH8 : (a <= ax)) (PreH9 : (0 <= b)) (PreH10 : (b <= bx)) (PreH11 : (seen_x = 1)) (PreH12 : (c = 0)) (PreH13 : (d = 0)) (PreH14 : (seen_n = 0)) (PreH15 : (valid_string lx )) (PreH16 : (valid_string ln )) (PreH17 : ((string_length (lx)) < INT_MAX)) (PreH18 : ((string_length (ln)) < INT_MAX)) (PreH19 : (problem_144_pre_z lx ln )) (PreH20 : (fraction_parts_z_144 lx sx ax bx )) (PreH21 : (fraction_parts_z_144 ln sy cn dn )) (PreH22 : (fraction_scan_state_144 lx sx ax (i + 1 ) seen_x a b )) (PreH23 : (1 <= ax)) (PreH24 : (ax <= 46340)) (PreH25 : (1 <= bx)) (PreH26 : (bx <= 46340)) (PreH27 : (1 <= cn)) (PreH28 : (cn <= 46340)) (PreH29 : (1 <= dn)) (PreH30 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition simplify_safety_wit_28 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (a: Z) (b: Z) (seen_x: Z) (c: Z) (d: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (0 <= i)) (PreH4 : (i < len_x)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (0 <= a)) (PreH8 : (a <= ax)) (PreH9 : (0 <= b)) (PreH10 : (b <= bx)) (PreH11 : (seen_x = 0)) (PreH12 : (c = 0)) (PreH13 : (d = 0)) (PreH14 : (seen_n = 0)) (PreH15 : (valid_string lx )) (PreH16 : (valid_string ln )) (PreH17 : ((string_length (lx)) < INT_MAX)) (PreH18 : ((string_length (ln)) < INT_MAX)) (PreH19 : (problem_144_pre_z lx ln )) (PreH20 : (fraction_parts_z_144 lx sx ax bx )) (PreH21 : (fraction_parts_z_144 ln sy cn dn )) (PreH22 : (fraction_scan_state_144 lx sx ax (i + 1 ) seen_x a b )) (PreH23 : (1 <= ax)) (PreH24 : (ax <= 46340)) (PreH25 : (1 <= bx)) (PreH26 : (bx <= 46340)) (PreH27 : (1 <= cn)) (PreH28 : (cn <= 46340)) (PreH29 : (1 <= dn)) (PreH30 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition simplify_safety_wit_29 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (c: Z) (d: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (i = len_x)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (seen_x = 1)) (PreH7 : (c = 0)) (PreH8 : (d = 0)) (PreH9 : (seen_n = 0)) (PreH10 : (valid_string lx )) (PreH11 : (valid_string ln )) (PreH12 : ((string_length (lx)) < INT_MAX)) (PreH13 : ((string_length (ln)) < INT_MAX)) (PreH14 : (problem_144_pre_z lx ln )) (PreH15 : (fraction_parts_z_144 lx sx ax bx )) (PreH16 : (fraction_parts_z_144 ln sy cn dn )) (PreH17 : (1 <= ax)) (PreH18 : (ax <= 46340)) (PreH19 : (1 <= bx)) (PreH20 : (bx <= 46340)) (PreH21 : (1 <= cn)) (PreH22 : (cn <= 46340)) (PreH23 : (1 <= dn)) (PreH24 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition simplify_safety_wit_30 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (i < len_n)) (PreH2 : (len_x = (string_length (lx)))) (PreH3 : (len_n = (string_length (ln)))) (PreH4 : (0 <= i)) (PreH5 : (i <= len_n)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (seen_x = 1)) (PreH9 : (0 <= c)) (PreH10 : (c <= cn)) (PreH11 : (0 <= d)) (PreH12 : (d <= dn)) (PreH13 : (seen_n = 0)) (PreH14 : (valid_string lx )) (PreH15 : (valid_string ln )) (PreH16 : ((string_length (lx)) < INT_MAX)) (PreH17 : ((string_length (ln)) < INT_MAX)) (PreH18 : (problem_144_pre_z lx ln )) (PreH19 : (fraction_parts_z_144 lx sx ax bx )) (PreH20 : (fraction_parts_z_144 ln sy cn dn )) (PreH21 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH22 : (1 <= ax)) (PreH23 : (ax <= 46340)) (PreH24 : (1 <= bx)) (PreH25 : (bx <= 46340)) (PreH26 : (1 <= cn)) (PreH27 : (cn <= 46340)) (PreH28 : (1 <= dn)) (PreH29 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (47 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 47) ”
.

Definition simplify_safety_wit_31 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (i < len_n)) (PreH2 : (len_x = (string_length (lx)))) (PreH3 : (len_n = (string_length (ln)))) (PreH4 : (0 <= i)) (PreH5 : (i <= len_n)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (seen_x = 1)) (PreH9 : (0 <= c)) (PreH10 : (c <= cn)) (PreH11 : (0 <= d)) (PreH12 : (d <= dn)) (PreH13 : (seen_n = 1)) (PreH14 : (valid_string lx )) (PreH15 : (valid_string ln )) (PreH16 : ((string_length (lx)) < INT_MAX)) (PreH17 : ((string_length (ln)) < INT_MAX)) (PreH18 : (problem_144_pre_z lx ln )) (PreH19 : (fraction_parts_z_144 lx sx ax bx )) (PreH20 : (fraction_parts_z_144 ln sy cn dn )) (PreH21 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH22 : (1 <= ax)) (PreH23 : (ax <= 46340)) (PreH24 : (1 <= bx)) (PreH25 : (bx <= 46340)) (PreH26 : (1 <= cn)) (PreH27 : (cn <= 46340)) (PreH28 : (1 <= dn)) (PreH29 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (47 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 47) ”
.

Definition simplify_safety_wit_32 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : ((Znth i (c_string (ln)) 0) = 47)) (PreH2 : (i < len_n)) (PreH3 : (len_x = (string_length (lx)))) (PreH4 : (len_n = (string_length (ln)))) (PreH5 : (0 <= i)) (PreH6 : (i <= len_n)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (seen_x = 1)) (PreH10 : (0 <= c)) (PreH11 : (c <= cn)) (PreH12 : (0 <= d)) (PreH13 : (d <= dn)) (PreH14 : (seen_n = 0)) (PreH15 : (valid_string lx )) (PreH16 : (valid_string ln )) (PreH17 : ((string_length (lx)) < INT_MAX)) (PreH18 : ((string_length (ln)) < INT_MAX)) (PreH19 : (problem_144_pre_z lx ln )) (PreH20 : (fraction_parts_z_144 lx sx ax bx )) (PreH21 : (fraction_parts_z_144 ln sy cn dn )) (PreH22 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH23 : (1 <= ax)) (PreH24 : (ax <= 46340)) (PreH25 : (1 <= bx)) (PreH26 : (bx <= 46340)) (PreH27 : (1 <= cn)) (PreH28 : (cn <= 46340)) (PreH29 : (1 <= dn)) (PreH30 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition simplify_safety_wit_33 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : ((Znth i (c_string (ln)) 0) = 47)) (PreH2 : (i < len_n)) (PreH3 : (len_x = (string_length (lx)))) (PreH4 : (len_n = (string_length (ln)))) (PreH5 : (0 <= i)) (PreH6 : (i <= len_n)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (seen_x = 1)) (PreH10 : (0 <= c)) (PreH11 : (c <= cn)) (PreH12 : (0 <= d)) (PreH13 : (d <= dn)) (PreH14 : (seen_n = 1)) (PreH15 : (valid_string lx )) (PreH16 : (valid_string ln )) (PreH17 : ((string_length (lx)) < INT_MAX)) (PreH18 : ((string_length (ln)) < INT_MAX)) (PreH19 : (problem_144_pre_z lx ln )) (PreH20 : (fraction_parts_z_144 lx sx ax bx )) (PreH21 : (fraction_parts_z_144 ln sy cn dn )) (PreH22 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH23 : (1 <= ax)) (PreH24 : (ax <= 46340)) (PreH25 : (1 <= bx)) (PreH26 : (bx <= 46340)) (PreH27 : (1 <= cn)) (PreH28 : (cn <= 46340)) (PreH29 : (1 <= dn)) (PreH30 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition simplify_safety_wit_34 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH2 : (i < len_n)) (PreH3 : (len_x = (string_length (lx)))) (PreH4 : (len_n = (string_length (ln)))) (PreH5 : (0 <= i)) (PreH6 : (i <= len_n)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (seen_x = 1)) (PreH10 : (0 <= c)) (PreH11 : (c <= cn)) (PreH12 : (0 <= d)) (PreH13 : (d <= dn)) (PreH14 : (seen_n = 0)) (PreH15 : (valid_string lx )) (PreH16 : (valid_string ln )) (PreH17 : ((string_length (lx)) < INT_MAX)) (PreH18 : ((string_length (ln)) < INT_MAX)) (PreH19 : (problem_144_pre_z lx ln )) (PreH20 : (fraction_parts_z_144 lx sx ax bx )) (PreH21 : (fraction_parts_z_144 ln sy cn dn )) (PreH22 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH23 : (1 <= ax)) (PreH24 : (ax <= 46340)) (PreH25 : (1 <= bx)) (PreH26 : (bx <= 46340)) (PreH27 : (1 <= cn)) (PreH28 : (cn <= 46340)) (PreH29 : (1 <= dn)) (PreH30 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition simplify_safety_wit_35 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH2 : (i < len_n)) (PreH3 : (len_x = (string_length (lx)))) (PreH4 : (len_n = (string_length (ln)))) (PreH5 : (0 <= i)) (PreH6 : (i <= len_n)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (seen_x = 1)) (PreH10 : (0 <= c)) (PreH11 : (c <= cn)) (PreH12 : (0 <= d)) (PreH13 : (d <= dn)) (PreH14 : (seen_n = 1)) (PreH15 : (valid_string lx )) (PreH16 : (valid_string ln )) (PreH17 : ((string_length (lx)) < INT_MAX)) (PreH18 : ((string_length (ln)) < INT_MAX)) (PreH19 : (problem_144_pre_z lx ln )) (PreH20 : (fraction_parts_z_144 lx sx ax bx )) (PreH21 : (fraction_parts_z_144 ln sy cn dn )) (PreH22 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH23 : (1 <= ax)) (PreH24 : (ax <= 46340)) (PreH25 : (1 <= bx)) (PreH26 : (bx <= 46340)) (PreH27 : (1 <= cn)) (PreH28 : (cn <= 46340)) (PreH29 : (1 <= dn)) (PreH30 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition simplify_safety_wit_36 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n <> 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ False ”
.

Definition simplify_safety_wit_37 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n = 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ False ”
.

Definition simplify_safety_wit_38 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n = 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((c * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((c * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) )) ”
) \/
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n = 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((c * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((c * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) )) ”
).

Definition simplify_safety_wit_38_split_goal_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n = 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((c * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) ) <= INT_MAX) ”
.

Definition simplify_safety_wit_38_split_goal_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n = 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((INT_MIN) <= ((c * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) )) ”
.

Definition simplify_safety_wit_39 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n = 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((Znth i (c_string (ln)) 0) - 48 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (ln)) 0) - 48 )) ”
) \/
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n = 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((Znth i (c_string (ln)) 0) - 48 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (ln)) 0) - 48 )) ”
).

Definition simplify_safety_wit_39_split_goal_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n = 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((Znth i (c_string (ln)) 0) - 48 ) <= INT_MAX) ”
.

Definition simplify_safety_wit_39_split_goal_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n = 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((INT_MIN) <= ((Znth i (c_string (ln)) 0) - 48 )) ”
.

Definition simplify_safety_wit_40 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n = 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((c * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c * 10 )) ”
.

Definition simplify_safety_wit_41 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n = 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition simplify_safety_wit_42 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n = 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition simplify_safety_wit_43 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n <> 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((d * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((d * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) )) ”
) \/
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n <> 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((d * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((d * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) )) ”
).

Definition simplify_safety_wit_43_split_goal_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n <> 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((d * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) ) <= INT_MAX) ”
.

Definition simplify_safety_wit_43_split_goal_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n <> 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((INT_MIN) <= ((d * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) )) ”
.

Definition simplify_safety_wit_44 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n <> 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((Znth i (c_string (ln)) 0) - 48 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (ln)) 0) - 48 )) ”
) \/
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n <> 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((Znth i (c_string (ln)) 0) - 48 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (ln)) 0) - 48 )) ”
).

Definition simplify_safety_wit_44_split_goal_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n <> 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((Znth i (c_string (ln)) 0) - 48 ) <= INT_MAX) ”
.

Definition simplify_safety_wit_44_split_goal_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n <> 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((INT_MIN) <= ((Znth i (c_string (ln)) 0) - 48 )) ”
.

Definition simplify_safety_wit_45 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n <> 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((d * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d * 10 )) ”
.

Definition simplify_safety_wit_46 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n <> 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition simplify_safety_wit_47 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n <> 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (ln)) 0))
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition simplify_safety_wit_48 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (c: Z) (d: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (0 <= i)) (PreH4 : (i < len_n)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (seen_x = 1)) (PreH8 : (0 <= c)) (PreH9 : (c <= cn)) (PreH10 : (0 <= d)) (PreH11 : (d <= dn)) (PreH12 : (seen_n = 0)) (PreH13 : (valid_string lx )) (PreH14 : (valid_string ln )) (PreH15 : ((string_length (lx)) < INT_MAX)) (PreH16 : ((string_length (ln)) < INT_MAX)) (PreH17 : (problem_144_pre_z lx ln )) (PreH18 : (fraction_parts_z_144 lx sx ax bx )) (PreH19 : (fraction_parts_z_144 ln sy cn dn )) (PreH20 : (fraction_scan_state_144 ln sy cn (i + 1 ) seen_n c d )) (PreH21 : (1 <= ax)) (PreH22 : (ax <= 46340)) (PreH23 : (1 <= bx)) (PreH24 : (bx <= 46340)) (PreH25 : (1 <= cn)) (PreH26 : (cn <= 46340)) (PreH27 : (1 <= dn)) (PreH28 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition simplify_safety_wit_49 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (c: Z) (d: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (0 <= i)) (PreH4 : (i < len_n)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (seen_x = 1)) (PreH8 : (0 <= c)) (PreH9 : (c <= cn)) (PreH10 : (0 <= d)) (PreH11 : (d <= dn)) (PreH12 : (seen_n = 1)) (PreH13 : (valid_string lx )) (PreH14 : (valid_string ln )) (PreH15 : ((string_length (lx)) < INT_MAX)) (PreH16 : ((string_length (ln)) < INT_MAX)) (PreH17 : (problem_144_pre_z lx ln )) (PreH18 : (fraction_parts_z_144 lx sx ax bx )) (PreH19 : (fraction_parts_z_144 ln sy cn dn )) (PreH20 : (fraction_scan_state_144 ln sy cn (i + 1 ) seen_n c d )) (PreH21 : (1 <= ax)) (PreH22 : (ax <= 46340)) (PreH23 : (1 <= bx)) (PreH24 : (bx <= 46340)) (PreH25 : (1 <= cn)) (PreH26 : (cn <= 46340)) (PreH27 : (1 <= dn)) (PreH28 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition simplify_safety_wit_50 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (i = len_n)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (seen_x = 1)) (PreH7 : (seen_n = 1)) (PreH8 : (valid_string lx )) (PreH9 : (valid_string ln )) (PreH10 : ((string_length (lx)) < INT_MAX)) (PreH11 : ((string_length (ln)) < INT_MAX)) (PreH12 : (problem_144_pre_z lx ln )) (PreH13 : (fraction_parts_z_144 lx sx ax bx )) (PreH14 : (fraction_parts_z_144 ln sy cn dn )) (PreH15 : (1 <= ax)) (PreH16 : (ax <= 46340)) (PreH17 : (1 <= bx)) (PreH18 : (bx <= 46340)) (PreH19 : (1 <= cn)) (PreH20 : (cn <= 46340)) (PreH21 : (1 <= dn)) (PreH22 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((ax * cn ) <> (INT_MIN)) \/ ((bx * dn ) <> (-1))) ” 
  &&  “ ((bx * dn ) <> 0) ”
) \/
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (i = len_n)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (seen_x = 1)) (PreH7 : (seen_n = 1)) (PreH8 : (valid_string lx )) (PreH9 : (valid_string ln )) (PreH10 : ((string_length (lx)) < INT_MAX)) (PreH11 : ((string_length (ln)) < INT_MAX)) (PreH12 : (problem_144_pre_z lx ln )) (PreH13 : (fraction_parts_z_144 lx sx ax bx )) (PreH14 : (fraction_parts_z_144 ln sy cn dn )) (PreH15 : (1 <= ax)) (PreH16 : (ax <= 46340)) (PreH17 : (1 <= bx)) (PreH18 : (bx <= 46340)) (PreH19 : (1 <= cn)) (PreH20 : (cn <= 46340)) (PreH21 : (1 <= dn)) (PreH22 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((ax * cn ) <> (INT_MIN)) \/ ((bx * dn ) <> (-1))) ” 
  &&  “ ((bx * dn ) <> 0) ”
).

Definition simplify_safety_wit_50_split_goal_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (i = len_n)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (seen_x = 1)) (PreH7 : (seen_n = 1)) (PreH8 : (valid_string lx )) (PreH9 : (valid_string ln )) (PreH10 : ((string_length (lx)) < INT_MAX)) (PreH11 : ((string_length (ln)) < INT_MAX)) (PreH12 : (problem_144_pre_z lx ln )) (PreH13 : (fraction_parts_z_144 lx sx ax bx )) (PreH14 : (fraction_parts_z_144 ln sy cn dn )) (PreH15 : (1 <= ax)) (PreH16 : (ax <= 46340)) (PreH17 : (1 <= bx)) (PreH18 : (bx <= 46340)) (PreH19 : (1 <= cn)) (PreH20 : (cn <= 46340)) (PreH21 : (1 <= dn)) (PreH22 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (((ax * cn ) <> (INT_MIN)) \/ ((bx * dn ) <> (-1))) ”
.

Definition simplify_safety_wit_50_split_goal_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (i = len_n)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (seen_x = 1)) (PreH7 : (seen_n = 1)) (PreH8 : (valid_string lx )) (PreH9 : (valid_string ln )) (PreH10 : ((string_length (lx)) < INT_MAX)) (PreH11 : ((string_length (ln)) < INT_MAX)) (PreH12 : (problem_144_pre_z lx ln )) (PreH13 : (fraction_parts_z_144 lx sx ax bx )) (PreH14 : (fraction_parts_z_144 ln sy cn dn )) (PreH15 : (1 <= ax)) (PreH16 : (ax <= 46340)) (PreH17 : (1 <= bx)) (PreH18 : (bx <= 46340)) (PreH19 : (1 <= cn)) (PreH20 : (cn <= 46340)) (PreH21 : (1 <= dn)) (PreH22 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((bx * dn ) <> 0) ”
.

Definition simplify_safety_wit_51 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (i = len_n)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (seen_x = 1)) (PreH7 : (seen_n = 1)) (PreH8 : (valid_string lx )) (PreH9 : (valid_string ln )) (PreH10 : ((string_length (lx)) < INT_MAX)) (PreH11 : ((string_length (ln)) < INT_MAX)) (PreH12 : (problem_144_pre_z lx ln )) (PreH13 : (fraction_parts_z_144 lx sx ax bx )) (PreH14 : (fraction_parts_z_144 ln sy cn dn )) (PreH15 : (1 <= ax)) (PreH16 : (ax <= 46340)) (PreH17 : (1 <= bx)) (PreH18 : (bx <= 46340)) (PreH19 : (1 <= cn)) (PreH20 : (cn <= 46340)) (PreH21 : (1 <= dn)) (PreH22 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((bx * dn ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bx * dn )) ”
) \/
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (i = len_n)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (seen_x = 1)) (PreH7 : (seen_n = 1)) (PreH8 : (valid_string lx )) (PreH9 : (valid_string ln )) (PreH10 : ((string_length (lx)) < INT_MAX)) (PreH11 : ((string_length (ln)) < INT_MAX)) (PreH12 : (problem_144_pre_z lx ln )) (PreH13 : (fraction_parts_z_144 lx sx ax bx )) (PreH14 : (fraction_parts_z_144 ln sy cn dn )) (PreH15 : (1 <= ax)) (PreH16 : (ax <= 46340)) (PreH17 : (1 <= bx)) (PreH18 : (bx <= 46340)) (PreH19 : (1 <= cn)) (PreH20 : (cn <= 46340)) (PreH21 : (1 <= dn)) (PreH22 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((bx * dn ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bx * dn )) ”
).

Definition simplify_safety_wit_51_split_goal_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (i = len_n)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (seen_x = 1)) (PreH7 : (seen_n = 1)) (PreH8 : (valid_string lx )) (PreH9 : (valid_string ln )) (PreH10 : ((string_length (lx)) < INT_MAX)) (PreH11 : ((string_length (ln)) < INT_MAX)) (PreH12 : (problem_144_pre_z lx ln )) (PreH13 : (fraction_parts_z_144 lx sx ax bx )) (PreH14 : (fraction_parts_z_144 ln sy cn dn )) (PreH15 : (1 <= ax)) (PreH16 : (ax <= 46340)) (PreH17 : (1 <= bx)) (PreH18 : (bx <= 46340)) (PreH19 : (1 <= cn)) (PreH20 : (cn <= 46340)) (PreH21 : (1 <= dn)) (PreH22 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((bx * dn ) <= INT_MAX) ”
.

Definition simplify_safety_wit_51_split_goal_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (i = len_n)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (seen_x = 1)) (PreH7 : (seen_n = 1)) (PreH8 : (valid_string lx )) (PreH9 : (valid_string ln )) (PreH10 : ((string_length (lx)) < INT_MAX)) (PreH11 : ((string_length (ln)) < INT_MAX)) (PreH12 : (problem_144_pre_z lx ln )) (PreH13 : (fraction_parts_z_144 lx sx ax bx )) (PreH14 : (fraction_parts_z_144 ln sy cn dn )) (PreH15 : (1 <= ax)) (PreH16 : (ax <= 46340)) (PreH17 : (1 <= bx)) (PreH18 : (bx <= 46340)) (PreH19 : (1 <= cn)) (PreH20 : (cn <= 46340)) (PreH21 : (1 <= dn)) (PreH22 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((INT_MIN) <= (bx * dn )) ”
.

Definition simplify_safety_wit_52 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (i = len_n)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (seen_x = 1)) (PreH7 : (seen_n = 1)) (PreH8 : (valid_string lx )) (PreH9 : (valid_string ln )) (PreH10 : ((string_length (lx)) < INT_MAX)) (PreH11 : ((string_length (ln)) < INT_MAX)) (PreH12 : (problem_144_pre_z lx ln )) (PreH13 : (fraction_parts_z_144 lx sx ax bx )) (PreH14 : (fraction_parts_z_144 ln sy cn dn )) (PreH15 : (1 <= ax)) (PreH16 : (ax <= 46340)) (PreH17 : (1 <= bx)) (PreH18 : (bx <= 46340)) (PreH19 : (1 <= cn)) (PreH20 : (cn <= 46340)) (PreH21 : (1 <= dn)) (PreH22 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((ax * cn ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ax * cn )) ”
) \/
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (i = len_n)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (seen_x = 1)) (PreH7 : (seen_n = 1)) (PreH8 : (valid_string lx )) (PreH9 : (valid_string ln )) (PreH10 : ((string_length (lx)) < INT_MAX)) (PreH11 : ((string_length (ln)) < INT_MAX)) (PreH12 : (problem_144_pre_z lx ln )) (PreH13 : (fraction_parts_z_144 lx sx ax bx )) (PreH14 : (fraction_parts_z_144 ln sy cn dn )) (PreH15 : (1 <= ax)) (PreH16 : (ax <= 46340)) (PreH17 : (1 <= bx)) (PreH18 : (bx <= 46340)) (PreH19 : (1 <= cn)) (PreH20 : (cn <= 46340)) (PreH21 : (1 <= dn)) (PreH22 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((ax * cn ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ax * cn )) ”
).

Definition simplify_safety_wit_52_split_goal_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (i = len_n)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (seen_x = 1)) (PreH7 : (seen_n = 1)) (PreH8 : (valid_string lx )) (PreH9 : (valid_string ln )) (PreH10 : ((string_length (lx)) < INT_MAX)) (PreH11 : ((string_length (ln)) < INT_MAX)) (PreH12 : (problem_144_pre_z lx ln )) (PreH13 : (fraction_parts_z_144 lx sx ax bx )) (PreH14 : (fraction_parts_z_144 ln sy cn dn )) (PreH15 : (1 <= ax)) (PreH16 : (ax <= 46340)) (PreH17 : (1 <= bx)) (PreH18 : (bx <= 46340)) (PreH19 : (1 <= cn)) (PreH20 : (cn <= 46340)) (PreH21 : (1 <= dn)) (PreH22 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((ax * cn ) <= INT_MAX) ”
.

Definition simplify_safety_wit_52_split_goal_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (i = len_n)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (seen_x = 1)) (PreH7 : (seen_n = 1)) (PreH8 : (valid_string lx )) (PreH9 : (valid_string ln )) (PreH10 : ((string_length (lx)) < INT_MAX)) (PreH11 : ((string_length (ln)) < INT_MAX)) (PreH12 : (problem_144_pre_z lx ln )) (PreH13 : (fraction_parts_z_144 lx sx ax bx )) (PreH14 : (fraction_parts_z_144 ln sy cn dn )) (PreH15 : (1 <= ax)) (PreH16 : (ax <= 46340)) (PreH17 : (1 <= bx)) (PreH18 : (bx <= 46340)) (PreH19 : (1 <= cn)) (PreH20 : (cn <= 46340)) (PreH21 : (1 <= dn)) (PreH22 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ ((INT_MIN) <= (ax * cn )) ”
.

Definition simplify_safety_wit_53 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (i = len_n)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (seen_x = 1)) (PreH7 : (seen_n = 1)) (PreH8 : (valid_string lx )) (PreH9 : (valid_string ln )) (PreH10 : ((string_length (lx)) < INT_MAX)) (PreH11 : ((string_length (ln)) < INT_MAX)) (PreH12 : (problem_144_pre_z lx ln )) (PreH13 : (fraction_parts_z_144 lx sx ax bx )) (PreH14 : (fraction_parts_z_144 ln sy cn dn )) (PreH15 : (1 <= ax)) (PreH16 : (ax <= 46340)) (PreH17 : (1 <= bx)) (PreH18 : (bx <= 46340)) (PreH19 : (1 <= cn)) (PreH20 : (cn <= 46340)) (PreH21 : (1 <= dn)) (PreH22 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition simplify_safety_wit_54 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (((ax * cn ) % ( (bx * dn ) ) ) = 0)) (PreH2 : (len_x = (string_length (lx)))) (PreH3 : (len_n = (string_length (ln)))) (PreH4 : (i = len_n)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (seen_x = 1)) (PreH8 : (seen_n = 1)) (PreH9 : (valid_string lx )) (PreH10 : (valid_string ln )) (PreH11 : ((string_length (lx)) < INT_MAX)) (PreH12 : ((string_length (ln)) < INT_MAX)) (PreH13 : (problem_144_pre_z lx ln )) (PreH14 : (fraction_parts_z_144 lx sx ax bx )) (PreH15 : (fraction_parts_z_144 ln sy cn dn )) (PreH16 : (1 <= ax)) (PreH17 : (ax <= 46340)) (PreH18 : (1 <= bx)) (PreH19 : (bx <= 46340)) (PreH20 : (1 <= cn)) (PreH21 : (cn <= 46340)) (PreH22 : (1 <= dn)) (PreH23 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition simplify_safety_wit_55 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (((ax * cn ) % ( (bx * dn ) ) ) <> 0)) (PreH2 : (len_x = (string_length (lx)))) (PreH3 : (len_n = (string_length (ln)))) (PreH4 : (i = len_n)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (seen_x = 1)) (PreH8 : (seen_n = 1)) (PreH9 : (valid_string lx )) (PreH10 : (valid_string ln )) (PreH11 : ((string_length (lx)) < INT_MAX)) (PreH12 : ((string_length (ln)) < INT_MAX)) (PreH13 : (problem_144_pre_z lx ln )) (PreH14 : (fraction_parts_z_144 lx sx ax bx )) (PreH15 : (fraction_parts_z_144 ln sy cn dn )) (PreH16 : (1 <= ax)) (PreH17 : (ax <= 46340)) (PreH18 : (1 <= bx)) (PreH19 : (bx <= 46340)) (PreH20 : (1 <= cn)) (PreH21 : (cn <= 46340)) (PreH22 : (1 <= dn)) (PreH23 : (dn <= 46340)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "len_x" ) )) # Int  |-> len_x)
  **  ((( &( "len_n" ) )) # Int  |-> len_n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  ((( &( "seen_x" ) )) # Int  |-> seen_x)
  **  ((( &( "seen_n" ) )) # Int  |-> seen_n)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition simplify_entail_wit_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (ln)))) (PreH2 : (retval = (string_length (lx)))) (PreH3 : (0 <= ((string_length (ln)) + 1 ))) (PreH4 : (0 <= ((string_length (lx)) + 1 ))) (PreH5 : (valid_string lx )) (PreH6 : (valid_string ln )) (PreH7 : ((string_length (lx)) < INT_MAX)) (PreH8 : ((string_length (ln)) < INT_MAX)) (PreH9 : (problem_144_pre_z lx ln )) (PreH10 : (fraction_parts_z_144 lx sx ax bx )) (PreH11 : (fraction_parts_z_144 ln sy cn dn )) (PreH12 : (1 <= ax)) (PreH13 : (ax <= 46340)) (PreH14 : (1 <= bx)) (PreH15 : (bx <= 46340)) (PreH16 : (1 <= cn)) (PreH17 : (cn <= 46340)) (PreH18 : (1 <= dn)) (PreH19 : (dn <= 46340)) ,
  (store_string n_pre ln )
  **  (CharArray.full x_pre ((string_length (lx)) + 1 ) (c_string (lx)) )
|--
  (“ (retval = (string_length (lx))) ” 
  &&  “ (retval_2 = (string_length (ln))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ax) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= bx) ” 
  &&  “ (0 = 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 lx sx ax 0 0 0 0 ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
  ||
  (“ (retval = (string_length (lx))) ” 
  &&  “ (retval_2 = (string_length (ln))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ax) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= bx) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 lx sx ax 0 0 0 0 ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
.

Definition simplify_entail_wit_2_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x <> 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_x) ” 
  &&  “ (0 <= (Znth i (c_string (lx)) 0)) ” 
  &&  “ ((Znth i (c_string (lx)) 0) <= 127) ” 
  &&  “ (0 <= a) ” 
  &&  “ (a <= ax) ” 
  &&  “ (0 <= ((b * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) )) ” 
  &&  “ (((b * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) ) <= bx) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (c = 0) ” 
  &&  “ (d = 0) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 lx sx ax (i + 1 ) seen_x a ((b * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) ) ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
  ||
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_x) ” 
  &&  “ (0 <= (Znth i (c_string (lx)) 0)) ” 
  &&  “ ((Znth i (c_string (lx)) 0) <= 127) ” 
  &&  “ (0 <= a) ” 
  &&  “ (a <= ax) ” 
  &&  “ (0 <= ((b * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) )) ” 
  &&  “ (((b * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) ) <= bx) ” 
  &&  “ (seen_x = 0) ” 
  &&  “ (c = 0) ” 
  &&  “ (d = 0) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 lx sx ax (i + 1 ) seen_x a ((b * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) ) ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
.

Definition simplify_entail_wit_2_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_x = 0)) (PreH2 : ((Znth i (c_string (lx)) 0) <> 47)) (PreH3 : (i < len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_x) ” 
  &&  “ (0 <= (Znth i (c_string (lx)) 0)) ” 
  &&  “ ((Znth i (c_string (lx)) 0) <= 127) ” 
  &&  “ (0 <= ((a * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) )) ” 
  &&  “ (((a * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) ) <= ax) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= bx) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (c = 0) ” 
  &&  “ (d = 0) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 lx sx ax (i + 1 ) seen_x ((a * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) ) b ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
  ||
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_x) ” 
  &&  “ (0 <= (Znth i (c_string (lx)) 0)) ” 
  &&  “ ((Znth i (c_string (lx)) 0) <= 127) ” 
  &&  “ (0 <= ((a * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) )) ” 
  &&  “ (((a * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) ) <= ax) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= bx) ” 
  &&  “ (seen_x = 0) ” 
  &&  “ (c = 0) ” 
  &&  “ (d = 0) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 lx sx ax (i + 1 ) seen_x ((a * 10 ) + ((Znth i (c_string (lx)) 0) - 48 ) ) b ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
.

Definition simplify_entail_wit_2_3 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : ((Znth i (c_string (lx)) 0) = 47)) (PreH2 : (i < len_x)) (PreH3 : (len_x = (string_length (lx)))) (PreH4 : (len_n = (string_length (ln)))) (PreH5 : (0 <= i)) (PreH6 : (i <= len_x)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= a)) (PreH10 : (a <= ax)) (PreH11 : (0 <= b)) (PreH12 : (b <= bx)) (PreH13 : (seen_x = 0)) (PreH14 : (c = 0)) (PreH15 : (d = 0)) (PreH16 : (seen_n = 0)) (PreH17 : (valid_string lx )) (PreH18 : (valid_string ln )) (PreH19 : ((string_length (lx)) < INT_MAX)) (PreH20 : ((string_length (ln)) < INT_MAX)) (PreH21 : (problem_144_pre_z lx ln )) (PreH22 : (fraction_parts_z_144 lx sx ax bx )) (PreH23 : (fraction_parts_z_144 ln sy cn dn )) (PreH24 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH25 : (1 <= ax)) (PreH26 : (ax <= 46340)) (PreH27 : (1 <= bx)) (PreH28 : (bx <= 46340)) (PreH29 : (1 <= cn)) (PreH30 : (cn <= 46340)) (PreH31 : (1 <= dn)) (PreH32 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_x) ” 
  &&  “ (0 <= (Znth i (c_string (lx)) 0)) ” 
  &&  “ ((Znth i (c_string (lx)) 0) <= 127) ” 
  &&  “ (0 <= a) ” 
  &&  “ (a <= ax) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= bx) ” 
  &&  “ (1 = 1) ” 
  &&  “ (c = 0) ” 
  &&  “ (d = 0) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 lx sx ax (i + 1 ) 1 a b ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
  ||
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_x) ” 
  &&  “ (0 <= (Znth i (c_string (lx)) 0)) ” 
  &&  “ ((Znth i (c_string (lx)) 0) <= 127) ” 
  &&  “ (0 <= a) ” 
  &&  “ (a <= ax) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= bx) ” 
  &&  “ (1 = 0) ” 
  &&  “ (c = 0) ” 
  &&  “ (d = 0) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 lx sx ax (i + 1 ) 1 a b ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
.

Definition simplify_entail_wit_2_4 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : ((Znth i (c_string (lx)) 0) = 47)) (PreH2 : (i < len_x)) (PreH3 : (len_x = (string_length (lx)))) (PreH4 : (len_n = (string_length (ln)))) (PreH5 : (0 <= i)) (PreH6 : (i <= len_x)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= a)) (PreH10 : (a <= ax)) (PreH11 : (0 <= b)) (PreH12 : (b <= bx)) (PreH13 : (seen_x = 1)) (PreH14 : (c = 0)) (PreH15 : (d = 0)) (PreH16 : (seen_n = 0)) (PreH17 : (valid_string lx )) (PreH18 : (valid_string ln )) (PreH19 : ((string_length (lx)) < INT_MAX)) (PreH20 : ((string_length (ln)) < INT_MAX)) (PreH21 : (problem_144_pre_z lx ln )) (PreH22 : (fraction_parts_z_144 lx sx ax bx )) (PreH23 : (fraction_parts_z_144 ln sy cn dn )) (PreH24 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH25 : (1 <= ax)) (PreH26 : (ax <= 46340)) (PreH27 : (1 <= bx)) (PreH28 : (bx <= 46340)) (PreH29 : (1 <= cn)) (PreH30 : (cn <= 46340)) (PreH31 : (1 <= dn)) (PreH32 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_x) ” 
  &&  “ (0 <= (Znth i (c_string (lx)) 0)) ” 
  &&  “ ((Znth i (c_string (lx)) 0) <= 127) ” 
  &&  “ (0 <= a) ” 
  &&  “ (a <= ax) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= bx) ” 
  &&  “ (1 = 1) ” 
  &&  “ (c = 0) ” 
  &&  “ (d = 0) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 lx sx ax (i + 1 ) 1 a b ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
  ||
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_x) ” 
  &&  “ (0 <= (Znth i (c_string (lx)) 0)) ” 
  &&  “ ((Znth i (c_string (lx)) 0) <= 127) ” 
  &&  “ (0 <= a) ” 
  &&  “ (a <= ax) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= bx) ” 
  &&  “ (1 = 0) ” 
  &&  “ (c = 0) ” 
  &&  “ (d = 0) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 lx sx ax (i + 1 ) 1 a b ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
.

Definition simplify_entail_wit_3_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (a: Z) (b: Z) (seen_x: Z) (c: Z) (d: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (0 <= i)) (PreH4 : (i < len_x)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (0 <= a)) (PreH8 : (a <= ax)) (PreH9 : (0 <= b)) (PreH10 : (b <= bx)) (PreH11 : (seen_x = 1)) (PreH12 : (c = 0)) (PreH13 : (d = 0)) (PreH14 : (seen_n = 0)) (PreH15 : (valid_string lx )) (PreH16 : (valid_string ln )) (PreH17 : ((string_length (lx)) < INT_MAX)) (PreH18 : ((string_length (ln)) < INT_MAX)) (PreH19 : (problem_144_pre_z lx ln )) (PreH20 : (fraction_parts_z_144 lx sx ax bx )) (PreH21 : (fraction_parts_z_144 ln sy cn dn )) (PreH22 : (fraction_scan_state_144 lx sx ax (i + 1 ) seen_x a b )) (PreH23 : (1 <= ax)) (PreH24 : (ax <= 46340)) (PreH25 : (1 <= bx)) (PreH26 : (bx <= 46340)) (PreH27 : (1 <= cn)) (PreH28 : (cn <= 46340)) (PreH29 : (1 <= dn)) (PreH30 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len_x) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= a) ” 
  &&  “ (a <= ax) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= bx) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (c = 0) ” 
  &&  “ (d = 0) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 lx sx ax (i + 1 ) seen_x a b ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
  ||
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len_x) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= a) ” 
  &&  “ (a <= ax) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= bx) ” 
  &&  “ (seen_x = 0) ” 
  &&  “ (c = 0) ” 
  &&  “ (d = 0) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 lx sx ax (i + 1 ) seen_x a b ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
.

Definition simplify_entail_wit_3_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (a: Z) (b: Z) (seen_x: Z) (c: Z) (d: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (0 <= i)) (PreH4 : (i < len_x)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (0 <= a)) (PreH8 : (a <= ax)) (PreH9 : (0 <= b)) (PreH10 : (b <= bx)) (PreH11 : (seen_x = 0)) (PreH12 : (c = 0)) (PreH13 : (d = 0)) (PreH14 : (seen_n = 0)) (PreH15 : (valid_string lx )) (PreH16 : (valid_string ln )) (PreH17 : ((string_length (lx)) < INT_MAX)) (PreH18 : ((string_length (ln)) < INT_MAX)) (PreH19 : (problem_144_pre_z lx ln )) (PreH20 : (fraction_parts_z_144 lx sx ax bx )) (PreH21 : (fraction_parts_z_144 ln sy cn dn )) (PreH22 : (fraction_scan_state_144 lx sx ax (i + 1 ) seen_x a b )) (PreH23 : (1 <= ax)) (PreH24 : (ax <= 46340)) (PreH25 : (1 <= bx)) (PreH26 : (bx <= 46340)) (PreH27 : (1 <= cn)) (PreH28 : (cn <= 46340)) (PreH29 : (1 <= dn)) (PreH30 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len_x) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= a) ” 
  &&  “ (a <= ax) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= bx) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (c = 0) ” 
  &&  “ (d = 0) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 lx sx ax (i + 1 ) seen_x a b ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
  ||
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len_x) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= a) ” 
  &&  “ (a <= ax) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= bx) ” 
  &&  “ (seen_x = 0) ” 
  &&  “ (c = 0) ” 
  &&  “ (d = 0) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 lx sx ax (i + 1 ) seen_x a b ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
.

Definition simplify_entail_wit_4_1 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (i >= len_x)) (PreH2 : (len_x = (string_length (lx)))) (PreH3 : (len_n = (string_length (ln)))) (PreH4 : (0 <= i)) (PreH5 : (i <= len_x)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= a)) (PreH9 : (a <= ax)) (PreH10 : (0 <= b)) (PreH11 : (b <= bx)) (PreH12 : (seen_x = 0)) (PreH13 : (c = 0)) (PreH14 : (d = 0)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (i = len_x) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (c = 0) ” 
  &&  “ (d = 0) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
) \/
(
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (b = bx) ” 
  &&  “ (a = ax) ” 
  &&  “ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (i = len_x) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (c = 0) ” 
  &&  “ (d = 0) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  emp
).

Definition simplify_entail_wit_4_1_split_goal_1 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (b = bx) ”
.

Definition simplify_entail_wit_4_1_split_goal_2 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (a = ax) ”
.

Definition simplify_entail_wit_4_1_split_goal_3 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (len_x = (string_length (lx))) ”
.

Definition simplify_entail_wit_4_1_split_goal_4 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (len_n = (string_length (ln))) ”
.

Definition simplify_entail_wit_4_1_split_goal_5 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (i = len_x) ”
.

Definition simplify_entail_wit_4_1_split_goal_6 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (0 <= ch) ”
.

Definition simplify_entail_wit_4_1_split_goal_7 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (ch <= 127) ”
.

Definition simplify_entail_wit_4_1_split_goal_8 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (seen_x = 1) ”
.

Definition simplify_entail_wit_4_1_split_goal_9 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (c = 0) ”
.

Definition simplify_entail_wit_4_1_split_goal_10 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (d = 0) ”
.

Definition simplify_entail_wit_4_1_split_goal_11 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (seen_n = 0) ”
.

Definition simplify_entail_wit_4_1_split_goal_12 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (valid_string lx ) ”
.

Definition simplify_entail_wit_4_1_split_goal_13 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (valid_string ln ) ”
.

Definition simplify_entail_wit_4_1_split_goal_14 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ ((string_length (lx)) < INT_MAX) ”
.

Definition simplify_entail_wit_4_1_split_goal_15 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ ((string_length (ln)) < INT_MAX) ”
.

Definition simplify_entail_wit_4_1_split_goal_16 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (problem_144_pre_z lx ln ) ”
.

Definition simplify_entail_wit_4_1_split_goal_17 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (fraction_parts_z_144 lx sx ax bx ) ”
.

Definition simplify_entail_wit_4_1_split_goal_18 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (fraction_parts_z_144 ln sy cn dn ) ”
.

Definition simplify_entail_wit_4_1_split_goal_19 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (1 <= ax) ”
.

Definition simplify_entail_wit_4_1_split_goal_20 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (ax <= 46340) ”
.

Definition simplify_entail_wit_4_1_split_goal_21 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (1 <= bx) ”
.

Definition simplify_entail_wit_4_1_split_goal_22 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (bx <= 46340) ”
.

Definition simplify_entail_wit_4_1_split_goal_23 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (1 <= cn) ”
.

Definition simplify_entail_wit_4_1_split_goal_24 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (cn <= 46340) ”
.

Definition simplify_entail_wit_4_1_split_goal_25 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (1 <= dn) ”
.

Definition simplify_entail_wit_4_1_split_goal_26 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 0)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (dn <= 46340) ”
.

Definition simplify_entail_wit_4_2 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (i >= len_x)) (PreH2 : (len_x = (string_length (lx)))) (PreH3 : (len_n = (string_length (ln)))) (PreH4 : (0 <= i)) (PreH5 : (i <= len_x)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= a)) (PreH9 : (a <= ax)) (PreH10 : (0 <= b)) (PreH11 : (b <= bx)) (PreH12 : (seen_x = 1)) (PreH13 : (c = 0)) (PreH14 : (d = 0)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (i = len_x) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (c = 0) ” 
  &&  “ (d = 0) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
) \/
(
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (a = ax) ” 
  &&  “ (b = bx) ”
  &&  emp
).

Definition simplify_entail_wit_4_2_split_goal_1 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (a = ax) ”
.

Definition simplify_entail_wit_4_2_split_goal_2 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (b: Z) (a: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_x)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_x)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= a)) (PreH11 : (a <= ax)) (PreH12 : (0 <= b)) (PreH13 : (b <= bx)) (PreH14 : (seen_x = 1)) (PreH15 : (c = 0)) (PreH16 : (d = 0)) (PreH17 : (seen_n = 0)) (PreH18 : (valid_string lx )) (PreH19 : (valid_string ln )) (PreH20 : ((string_length (lx)) < INT_MAX)) (PreH21 : ((string_length (ln)) < INT_MAX)) (PreH22 : (problem_144_pre_z lx ln )) (PreH23 : (fraction_parts_z_144 lx sx ax bx )) (PreH24 : (fraction_parts_z_144 ln sy cn dn )) (PreH25 : (fraction_scan_state_144 lx sx ax i seen_x a b )) (PreH26 : (1 <= ax)) (PreH27 : (ax <= 46340)) (PreH28 : (1 <= bx)) (PreH29 : (bx <= 46340)) (PreH30 : (1 <= cn)) (PreH31 : (cn <= 46340)) (PreH32 : (1 <= dn)) (PreH33 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (b = bx) ”
.

Definition simplify_entail_wit_5 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (c: Z) (d: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (i = len_x)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (seen_x = 1)) (PreH7 : (c = 0)) (PreH8 : (d = 0)) (PreH9 : (seen_n = 0)) (PreH10 : (valid_string lx )) (PreH11 : (valid_string ln )) (PreH12 : ((string_length (lx)) < INT_MAX)) (PreH13 : ((string_length (ln)) < INT_MAX)) (PreH14 : (problem_144_pre_z lx ln )) (PreH15 : (fraction_parts_z_144 lx sx ax bx )) (PreH16 : (fraction_parts_z_144 ln sy cn dn )) (PreH17 : (1 <= ax)) (PreH18 : (ax <= 46340)) (PreH19 : (1 <= bx)) (PreH20 : (bx <= 46340)) (PreH21 : (1 <= cn)) (PreH22 : (cn <= 46340)) (PreH23 : (1 <= dn)) (PreH24 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= len_n) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= cn) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= dn) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 ln sy cn 0 seen_n c d ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
  ||
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= len_n) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= cn) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= dn) ” 
  &&  “ (seen_n = 1) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 ln sy cn 0 seen_n c d ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
.

Definition simplify_entail_wit_6_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n <> 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_n) ” 
  &&  “ (0 <= (Znth i (c_string (ln)) 0)) ” 
  &&  “ ((Znth i (c_string (ln)) 0) <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= cn) ” 
  &&  “ (0 <= ((d * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) )) ” 
  &&  “ (((d * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) ) <= dn) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 ln sy cn (i + 1 ) seen_n c ((d * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) ) ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
  ||
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_n) ” 
  &&  “ (0 <= (Znth i (c_string (ln)) 0)) ” 
  &&  “ ((Znth i (c_string (ln)) 0) <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= cn) ” 
  &&  “ (0 <= ((d * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) )) ” 
  &&  “ (((d * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) ) <= dn) ” 
  &&  “ (seen_n = 1) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 ln sy cn (i + 1 ) seen_n c ((d * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) ) ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
.

Definition simplify_entail_wit_6_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (seen_n = 0)) (PreH2 : ((Znth i (c_string (ln)) 0) <> 47)) (PreH3 : (i < len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_n) ” 
  &&  “ (0 <= (Znth i (c_string (ln)) 0)) ” 
  &&  “ ((Znth i (c_string (ln)) 0) <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (0 <= ((c * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) )) ” 
  &&  “ (((c * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) ) <= cn) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= dn) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 ln sy cn (i + 1 ) seen_n ((c * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) ) d ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
  ||
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_n) ” 
  &&  “ (0 <= (Znth i (c_string (ln)) 0)) ” 
  &&  “ ((Znth i (c_string (ln)) 0) <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (0 <= ((c * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) )) ” 
  &&  “ (((c * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) ) <= cn) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= dn) ” 
  &&  “ (seen_n = 1) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 ln sy cn (i + 1 ) seen_n ((c * 10 ) + ((Znth i (c_string (ln)) 0) - 48 ) ) d ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
.

Definition simplify_entail_wit_6_3 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : ((Znth i (c_string (ln)) 0) = 47)) (PreH2 : (i < len_n)) (PreH3 : (len_x = (string_length (lx)))) (PreH4 : (len_n = (string_length (ln)))) (PreH5 : (0 <= i)) (PreH6 : (i <= len_n)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (seen_x = 1)) (PreH10 : (0 <= c)) (PreH11 : (c <= cn)) (PreH12 : (0 <= d)) (PreH13 : (d <= dn)) (PreH14 : (seen_n = 1)) (PreH15 : (valid_string lx )) (PreH16 : (valid_string ln )) (PreH17 : ((string_length (lx)) < INT_MAX)) (PreH18 : ((string_length (ln)) < INT_MAX)) (PreH19 : (problem_144_pre_z lx ln )) (PreH20 : (fraction_parts_z_144 lx sx ax bx )) (PreH21 : (fraction_parts_z_144 ln sy cn dn )) (PreH22 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH23 : (1 <= ax)) (PreH24 : (ax <= 46340)) (PreH25 : (1 <= bx)) (PreH26 : (bx <= 46340)) (PreH27 : (1 <= cn)) (PreH28 : (cn <= 46340)) (PreH29 : (1 <= dn)) (PreH30 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_n) ” 
  &&  “ (0 <= (Znth i (c_string (ln)) 0)) ” 
  &&  “ ((Znth i (c_string (ln)) 0) <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= cn) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= dn) ” 
  &&  “ (1 = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 ln sy cn (i + 1 ) 1 c d ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
  ||
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_n) ” 
  &&  “ (0 <= (Znth i (c_string (ln)) 0)) ” 
  &&  “ ((Znth i (c_string (ln)) 0) <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= cn) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= dn) ” 
  &&  “ (1 = 1) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 ln sy cn (i + 1 ) 1 c d ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
.

Definition simplify_entail_wit_6_4 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : ((Znth i (c_string (ln)) 0) = 47)) (PreH2 : (i < len_n)) (PreH3 : (len_x = (string_length (lx)))) (PreH4 : (len_n = (string_length (ln)))) (PreH5 : (0 <= i)) (PreH6 : (i <= len_n)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (seen_x = 1)) (PreH10 : (0 <= c)) (PreH11 : (c <= cn)) (PreH12 : (0 <= d)) (PreH13 : (d <= dn)) (PreH14 : (seen_n = 0)) (PreH15 : (valid_string lx )) (PreH16 : (valid_string ln )) (PreH17 : ((string_length (lx)) < INT_MAX)) (PreH18 : ((string_length (ln)) < INT_MAX)) (PreH19 : (problem_144_pre_z lx ln )) (PreH20 : (fraction_parts_z_144 lx sx ax bx )) (PreH21 : (fraction_parts_z_144 ln sy cn dn )) (PreH22 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH23 : (1 <= ax)) (PreH24 : (ax <= 46340)) (PreH25 : (1 <= bx)) (PreH26 : (bx <= 46340)) (PreH27 : (1 <= cn)) (PreH28 : (cn <= 46340)) (PreH29 : (1 <= dn)) (PreH30 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_n) ” 
  &&  “ (0 <= (Znth i (c_string (ln)) 0)) ” 
  &&  “ ((Znth i (c_string (ln)) 0) <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= cn) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= dn) ” 
  &&  “ (1 = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 ln sy cn (i + 1 ) 1 c d ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
  ||
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len_n) ” 
  &&  “ (0 <= (Znth i (c_string (ln)) 0)) ” 
  &&  “ ((Znth i (c_string (ln)) 0) <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= cn) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= dn) ” 
  &&  “ (1 = 1) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 ln sy cn (i + 1 ) 1 c d ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
.

Definition simplify_entail_wit_7_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (c: Z) (d: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (0 <= i)) (PreH4 : (i < len_n)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (seen_x = 1)) (PreH8 : (0 <= c)) (PreH9 : (c <= cn)) (PreH10 : (0 <= d)) (PreH11 : (d <= dn)) (PreH12 : (seen_n = 0)) (PreH13 : (valid_string lx )) (PreH14 : (valid_string ln )) (PreH15 : ((string_length (lx)) < INT_MAX)) (PreH16 : ((string_length (ln)) < INT_MAX)) (PreH17 : (problem_144_pre_z lx ln )) (PreH18 : (fraction_parts_z_144 lx sx ax bx )) (PreH19 : (fraction_parts_z_144 ln sy cn dn )) (PreH20 : (fraction_scan_state_144 ln sy cn (i + 1 ) seen_n c d )) (PreH21 : (1 <= ax)) (PreH22 : (ax <= 46340)) (PreH23 : (1 <= bx)) (PreH24 : (bx <= 46340)) (PreH25 : (1 <= cn)) (PreH26 : (cn <= 46340)) (PreH27 : (1 <= dn)) (PreH28 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len_n) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= cn) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= dn) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 ln sy cn (i + 1 ) seen_n c d ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
  ||
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len_n) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= cn) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= dn) ” 
  &&  “ (seen_n = 1) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 ln sy cn (i + 1 ) seen_n c d ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
.

Definition simplify_entail_wit_7_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (c: Z) (d: Z) (seen_n: Z) (PreH1 : (len_x = (string_length (lx)))) (PreH2 : (len_n = (string_length (ln)))) (PreH3 : (0 <= i)) (PreH4 : (i < len_n)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (seen_x = 1)) (PreH8 : (0 <= c)) (PreH9 : (c <= cn)) (PreH10 : (0 <= d)) (PreH11 : (d <= dn)) (PreH12 : (seen_n = 1)) (PreH13 : (valid_string lx )) (PreH14 : (valid_string ln )) (PreH15 : ((string_length (lx)) < INT_MAX)) (PreH16 : ((string_length (ln)) < INT_MAX)) (PreH17 : (problem_144_pre_z lx ln )) (PreH18 : (fraction_parts_z_144 lx sx ax bx )) (PreH19 : (fraction_parts_z_144 ln sy cn dn )) (PreH20 : (fraction_scan_state_144 ln sy cn (i + 1 ) seen_n c d )) (PreH21 : (1 <= ax)) (PreH22 : (ax <= 46340)) (PreH23 : (1 <= bx)) (PreH24 : (bx <= 46340)) (PreH25 : (1 <= cn)) (PreH26 : (cn <= 46340)) (PreH27 : (1 <= dn)) (PreH28 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len_n) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= cn) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= dn) ” 
  &&  “ (seen_n = 0) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 ln sy cn (i + 1 ) seen_n c d ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
  ||
  (“ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len_n) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= cn) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= dn) ” 
  &&  “ (seen_n = 1) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (fraction_scan_state_144 ln sy cn (i + 1 ) seen_n c d ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln ))
.

Definition simplify_entail_wit_8_1 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (i >= len_n)) (PreH2 : (len_x = (string_length (lx)))) (PreH3 : (len_n = (string_length (ln)))) (PreH4 : (0 <= i)) (PreH5 : (i <= len_n)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (seen_x = 1)) (PreH9 : (0 <= c)) (PreH10 : (c <= cn)) (PreH11 : (0 <= d)) (PreH12 : (d <= dn)) (PreH13 : (seen_n = 1)) (PreH14 : (valid_string lx )) (PreH15 : (valid_string ln )) (PreH16 : ((string_length (lx)) < INT_MAX)) (PreH17 : ((string_length (ln)) < INT_MAX)) (PreH18 : (problem_144_pre_z lx ln )) (PreH19 : (fraction_parts_z_144 lx sx ax bx )) (PreH20 : (fraction_parts_z_144 ln sy cn dn )) (PreH21 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH22 : (1 <= ax)) (PreH23 : (ax <= 46340)) (PreH24 : (1 <= bx)) (PreH25 : (bx <= 46340)) (PreH26 : (1 <= cn)) (PreH27 : (cn <= 46340)) (PreH28 : (1 <= dn)) (PreH29 : (dn <= 46340)) ,
  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (i = len_n) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (seen_n = 1) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
) \/
(
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (c = cn) ” 
  &&  “ (d = dn) ”
  &&  emp
).

Definition simplify_entail_wit_8_1_split_goal_1 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (c = cn) ”
.

Definition simplify_entail_wit_8_1_split_goal_2 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 1)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (d = dn) ”
.

Definition simplify_entail_wit_8_2 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (i >= len_n)) (PreH2 : (len_x = (string_length (lx)))) (PreH3 : (len_n = (string_length (ln)))) (PreH4 : (0 <= i)) (PreH5 : (i <= len_n)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (seen_x = 1)) (PreH9 : (0 <= c)) (PreH10 : (c <= cn)) (PreH11 : (0 <= d)) (PreH12 : (d <= dn)) (PreH13 : (seen_n = 0)) (PreH14 : (valid_string lx )) (PreH15 : (valid_string ln )) (PreH16 : ((string_length (lx)) < INT_MAX)) (PreH17 : ((string_length (ln)) < INT_MAX)) (PreH18 : (problem_144_pre_z lx ln )) (PreH19 : (fraction_parts_z_144 lx sx ax bx )) (PreH20 : (fraction_parts_z_144 ln sy cn dn )) (PreH21 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH22 : (1 <= ax)) (PreH23 : (ax <= 46340)) (PreH24 : (1 <= bx)) (PreH25 : (bx <= 46340)) (PreH26 : (1 <= cn)) (PreH27 : (cn <= 46340)) (PreH28 : (1 <= dn)) (PreH29 : (dn <= 46340)) ,
  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (i = len_n) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (seen_n = 1) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> dn)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
) \/
(
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (d = dn) ” 
  &&  “ (c = cn) ” 
  &&  “ (len_x = (string_length (lx))) ” 
  &&  “ (len_n = (string_length (ln))) ” 
  &&  “ (i = len_n) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (seen_x = 1) ” 
  &&  “ (seen_n = 1) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  emp
).

Definition simplify_entail_wit_8_2_split_goal_1 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (d = dn) ”
.

Definition simplify_entail_wit_8_2_split_goal_2 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (c = cn) ”
.

Definition simplify_entail_wit_8_2_split_goal_3 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (len_x = (string_length (lx))) ”
.

Definition simplify_entail_wit_8_2_split_goal_4 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (len_n = (string_length (ln))) ”
.

Definition simplify_entail_wit_8_2_split_goal_5 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (i = len_n) ”
.

Definition simplify_entail_wit_8_2_split_goal_6 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (0 <= ch) ”
.

Definition simplify_entail_wit_8_2_split_goal_7 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (ch <= 127) ”
.

Definition simplify_entail_wit_8_2_split_goal_8 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (seen_x = 1) ”
.

Definition simplify_entail_wit_8_2_split_goal_9 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (seen_n = 1) ”
.

Definition simplify_entail_wit_8_2_split_goal_10 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (valid_string lx ) ”
.

Definition simplify_entail_wit_8_2_split_goal_11 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (valid_string ln ) ”
.

Definition simplify_entail_wit_8_2_split_goal_12 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ ((string_length (lx)) < INT_MAX) ”
.

Definition simplify_entail_wit_8_2_split_goal_13 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ ((string_length (ln)) < INT_MAX) ”
.

Definition simplify_entail_wit_8_2_split_goal_14 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (problem_144_pre_z lx ln ) ”
.

Definition simplify_entail_wit_8_2_split_goal_15 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (fraction_parts_z_144 lx sx ax bx ) ”
.

Definition simplify_entail_wit_8_2_split_goal_16 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (fraction_parts_z_144 ln sy cn dn ) ”
.

Definition simplify_entail_wit_8_2_split_goal_17 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (1 <= ax) ”
.

Definition simplify_entail_wit_8_2_split_goal_18 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (ax <= 46340) ”
.

Definition simplify_entail_wit_8_2_split_goal_19 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (1 <= bx) ”
.

Definition simplify_entail_wit_8_2_split_goal_20 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (bx <= 46340) ”
.

Definition simplify_entail_wit_8_2_split_goal_21 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (1 <= cn) ”
.

Definition simplify_entail_wit_8_2_split_goal_22 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (cn <= 46340) ”
.

Definition simplify_entail_wit_8_2_split_goal_23 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (1 <= dn) ”
.

Definition simplify_entail_wit_8_2_split_goal_24 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (seen_n: Z) (d: Z) (c: Z) (seen_x: Z) (ch: Z) (i: Z) (len_n: Z) (len_x: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (i >= len_n)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (0 <= i)) (PreH7 : (i <= len_n)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (seen_x = 1)) (PreH11 : (0 <= c)) (PreH12 : (c <= cn)) (PreH13 : (0 <= d)) (PreH14 : (d <= dn)) (PreH15 : (seen_n = 0)) (PreH16 : (valid_string lx )) (PreH17 : (valid_string ln )) (PreH18 : ((string_length (lx)) < INT_MAX)) (PreH19 : ((string_length (ln)) < INT_MAX)) (PreH20 : (problem_144_pre_z lx ln )) (PreH21 : (fraction_parts_z_144 lx sx ax bx )) (PreH22 : (fraction_parts_z_144 ln sy cn dn )) (PreH23 : (fraction_scan_state_144 ln sy cn i seen_n c d )) (PreH24 : (1 <= ax)) (PreH25 : (ax <= 46340)) (PreH26 : (1 <= bx)) (PreH27 : (bx <= 46340)) (PreH28 : (1 <= cn)) (PreH29 : (cn <= 46340)) (PreH30 : (1 <= dn)) (PreH31 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (dn <= 46340) ”
.

Definition simplify_return_wit_1 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (((ax * cn ) % ( (bx * dn ) ) ) <> 0)) (PreH2 : (len_x = (string_length (lx)))) (PreH3 : (len_n = (string_length (ln)))) (PreH4 : (i = len_n)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (seen_x = 1)) (PreH8 : (seen_n = 1)) (PreH9 : (valid_string lx )) (PreH10 : (valid_string ln )) (PreH11 : ((string_length (lx)) < INT_MAX)) (PreH12 : ((string_length (ln)) < INT_MAX)) (PreH13 : (problem_144_pre_z lx ln )) (PreH14 : (fraction_parts_z_144 lx sx ax bx )) (PreH15 : (fraction_parts_z_144 ln sy cn dn )) (PreH16 : (1 <= ax)) (PreH17 : (ax <= 46340)) (PreH18 : (1 <= bx)) (PreH19 : (bx <= 46340)) (PreH20 : (1 <= cn)) (PreH21 : (cn <= 46340)) (PreH22 : (1 <= dn)) (PreH23 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (problem_144_spec_z lx ln 0 ) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln )
) \/
(
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (((ax * cn ) % ( (bx * dn ) ) ) <> 0)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (i = len_n)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (seen_x = 1)) (PreH10 : (seen_n = 1)) (PreH11 : (valid_string lx )) (PreH12 : (valid_string ln )) (PreH13 : ((string_length (lx)) < INT_MAX)) (PreH14 : ((string_length (ln)) < INT_MAX)) (PreH15 : (problem_144_pre_z lx ln )) (PreH16 : (fraction_parts_z_144 lx sx ax bx )) (PreH17 : (fraction_parts_z_144 ln sy cn dn )) (PreH18 : (1 <= ax)) (PreH19 : (ax <= 46340)) (PreH20 : (1 <= bx)) (PreH21 : (bx <= 46340)) (PreH22 : (1 <= cn)) (PreH23 : (cn <= 46340)) (PreH24 : (1 <= dn)) (PreH25 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (problem_144_spec_z lx ln 0 ) ”
  &&  emp
).

Definition simplify_return_wit_1_split_goal_1 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (((ax * cn ) % ( (bx * dn ) ) ) <> 0)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (i = len_n)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (seen_x = 1)) (PreH10 : (seen_n = 1)) (PreH11 : (valid_string lx )) (PreH12 : (valid_string ln )) (PreH13 : ((string_length (lx)) < INT_MAX)) (PreH14 : ((string_length (ln)) < INT_MAX)) (PreH15 : (problem_144_pre_z lx ln )) (PreH16 : (fraction_parts_z_144 lx sx ax bx )) (PreH17 : (fraction_parts_z_144 ln sy cn dn )) (PreH18 : (1 <= ax)) (PreH19 : (ax <= 46340)) (PreH20 : (1 <= bx)) (PreH21 : (bx <= 46340)) (PreH22 : (1 <= cn)) (PreH23 : (cn <= 46340)) (PreH24 : (1 <= dn)) (PreH25 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (problem_144_spec_z lx ln 0 ) ”
.

Definition simplify_return_wit_2 := 
(
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (((ax * cn ) % ( (bx * dn ) ) ) = 0)) (PreH2 : (len_x = (string_length (lx)))) (PreH3 : (len_n = (string_length (ln)))) (PreH4 : (i = len_n)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (seen_x = 1)) (PreH8 : (seen_n = 1)) (PreH9 : (valid_string lx )) (PreH10 : (valid_string ln )) (PreH11 : ((string_length (lx)) < INT_MAX)) (PreH12 : ((string_length (ln)) < INT_MAX)) (PreH13 : (problem_144_pre_z lx ln )) (PreH14 : (fraction_parts_z_144 lx sx ax bx )) (PreH15 : (fraction_parts_z_144 ln sy cn dn )) (PreH16 : (1 <= ax)) (PreH17 : (ax <= 46340)) (PreH18 : (1 <= bx)) (PreH19 : (bx <= 46340)) (PreH20 : (1 <= cn)) (PreH21 : (cn <= 46340)) (PreH22 : (1 <= dn)) (PreH23 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (problem_144_spec_z lx ln 1 ) ”
  &&  (store_string x_pre lx )
  **  (store_string n_pre ln )
) \/
(
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (((ax * cn ) % ( (bx * dn ) ) ) = 0)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (i = len_n)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (seen_x = 1)) (PreH10 : (seen_n = 1)) (PreH11 : (valid_string lx )) (PreH12 : (valid_string ln )) (PreH13 : ((string_length (lx)) < INT_MAX)) (PreH14 : ((string_length (ln)) < INT_MAX)) (PreH15 : (problem_144_pre_z lx ln )) (PreH16 : (fraction_parts_z_144 lx sx ax bx )) (PreH17 : (fraction_parts_z_144 ln sy cn dn )) (PreH18 : (1 <= ax)) (PreH19 : (ax <= 46340)) (PreH20 : (1 <= bx)) (PreH21 : (bx <= 46340)) (PreH22 : (1 <= cn)) (PreH23 : (cn <= 46340)) (PreH24 : (1 <= dn)) (PreH25 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (problem_144_spec_z lx ln 1 ) ”
  &&  emp
).

Definition simplify_return_wit_2_split_goal_1 := 
forall (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (len_x: Z) (len_n: Z) (i: Z) (ch: Z) (seen_x: Z) (seen_n: Z) (PreH1 : (0 <= ((string_length (ln)) + 1 ))) (PreH2 : (0 <= ((string_length (lx)) + 1 ))) (PreH3 : (((ax * cn ) % ( (bx * dn ) ) ) = 0)) (PreH4 : (len_x = (string_length (lx)))) (PreH5 : (len_n = (string_length (ln)))) (PreH6 : (i = len_n)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (seen_x = 1)) (PreH10 : (seen_n = 1)) (PreH11 : (valid_string lx )) (PreH12 : (valid_string ln )) (PreH13 : ((string_length (lx)) < INT_MAX)) (PreH14 : ((string_length (ln)) < INT_MAX)) (PreH15 : (problem_144_pre_z lx ln )) (PreH16 : (fraction_parts_z_144 lx sx ax bx )) (PreH17 : (fraction_parts_z_144 ln sy cn dn )) (PreH18 : (1 <= ax)) (PreH19 : (ax <= 46340)) (PreH20 : (1 <= bx)) (PreH21 : (bx <= 46340)) (PreH22 : (1 <= cn)) (PreH23 : (cn <= 46340)) (PreH24 : (1 <= dn)) (PreH25 : (dn <= 46340)) ,
  TT && emp 
|--
  “ (problem_144_spec_z lx ln 1 ) ”
.

Definition simplify_partial_solve_wit_1_pure := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (PreH1 : (valid_string lx )) (PreH2 : (valid_string ln )) (PreH3 : ((string_length (lx)) < INT_MAX)) (PreH4 : ((string_length (ln)) < INT_MAX)) (PreH5 : (problem_144_pre_z lx ln )) (PreH6 : (fraction_parts_z_144 lx sx ax bx )) (PreH7 : (fraction_parts_z_144 ln sy cn dn )) (PreH8 : (1 <= ax)) (PreH9 : (ax <= 46340)) (PreH10 : (1 <= bx)) (PreH11 : (bx <= 46340)) (PreH12 : (1 <= cn)) (PreH13 : (cn <= 46340)) (PreH14 : (1 <= dn)) (PreH15 : (dn <= 46340)) ,
  ((( &( "len_x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (valid_string lx ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ”
.

Definition simplify_partial_solve_wit_1_aux := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (PreH1 : (valid_string lx )) (PreH2 : (valid_string ln )) (PreH3 : ((string_length (lx)) < INT_MAX)) (PreH4 : ((string_length (ln)) < INT_MAX)) (PreH5 : (problem_144_pre_z lx ln )) (PreH6 : (fraction_parts_z_144 lx sx ax bx )) (PreH7 : (fraction_parts_z_144 ln sy cn dn )) (PreH8 : (1 <= ax)) (PreH9 : (ax <= 46340)) (PreH10 : (1 <= bx)) (PreH11 : (bx <= 46340)) (PreH12 : (1 <= cn)) (PreH13 : (cn <= 46340)) (PreH14 : (1 <= dn)) (PreH15 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (store_string n_pre ln )
|--
  “ (valid_string lx ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (ln)) + 1 )) ” 
  &&  “ (0 <= ((string_length (lx)) + 1 )) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string x_pre lx )
  **  (CharArray.full n_pre ((string_length (ln)) + 1 ) (c_string (ln)) )
.

Definition simplify_partial_solve_wit_1 := simplify_partial_solve_wit_1_pure -> simplify_partial_solve_wit_1_aux.

Definition simplify_partial_solve_wit_2_pure := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (lx)))) (PreH2 : (0 <= ((string_length (ln)) + 1 ))) (PreH3 : (0 <= ((string_length (lx)) + 1 ))) (PreH4 : (valid_string lx )) (PreH5 : (valid_string ln )) (PreH6 : ((string_length (lx)) < INT_MAX)) (PreH7 : ((string_length (ln)) < INT_MAX)) (PreH8 : (problem_144_pre_z lx ln )) (PreH9 : (fraction_parts_z_144 lx sx ax bx )) (PreH10 : (fraction_parts_z_144 ln sy cn dn )) (PreH11 : (1 <= ax)) (PreH12 : (ax <= 46340)) (PreH13 : (1 <= bx)) (PreH14 : (bx <= 46340)) (PreH15 : (1 <= cn)) (PreH16 : (cn <= 46340)) (PreH17 : (1 <= dn)) (PreH18 : (dn <= 46340)) ,
  ((( &( "len_n" ) )) # Int  |->_)
  **  (store_string x_pre lx )
  **  (CharArray.full n_pre ((string_length (ln)) + 1 ) (c_string (ln)) )
  **  ((( &( "len_x" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (valid_string ln ) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ”
.

Definition simplify_partial_solve_wit_2_aux := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sy: Z) (sx: Z) (ln: (@list Z)) (lx: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (lx)))) (PreH2 : (0 <= ((string_length (ln)) + 1 ))) (PreH3 : (0 <= ((string_length (lx)) + 1 ))) (PreH4 : (valid_string lx )) (PreH5 : (valid_string ln )) (PreH6 : ((string_length (lx)) < INT_MAX)) (PreH7 : ((string_length (ln)) < INT_MAX)) (PreH8 : (problem_144_pre_z lx ln )) (PreH9 : (fraction_parts_z_144 lx sx ax bx )) (PreH10 : (fraction_parts_z_144 ln sy cn dn )) (PreH11 : (1 <= ax)) (PreH12 : (ax <= 46340)) (PreH13 : (1 <= bx)) (PreH14 : (bx <= 46340)) (PreH15 : (1 <= cn)) (PreH16 : (cn <= 46340)) (PreH17 : (1 <= dn)) (PreH18 : (dn <= 46340)) ,
  (store_string x_pre lx )
  **  (CharArray.full n_pre ((string_length (ln)) + 1 ) (c_string (ln)) )
|--
  “ (valid_string ln ) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (retval = (string_length (lx))) ” 
  &&  “ (0 <= ((string_length (ln)) + 1 )) ” 
  &&  “ (0 <= ((string_length (lx)) + 1 )) ” 
  &&  “ (valid_string lx ) ” 
  &&  “ (valid_string ln ) ” 
  &&  “ ((string_length (lx)) < INT_MAX) ” 
  &&  “ ((string_length (ln)) < INT_MAX) ” 
  &&  “ (problem_144_pre_z lx ln ) ” 
  &&  “ (fraction_parts_z_144 lx sx ax bx ) ” 
  &&  “ (fraction_parts_z_144 ln sy cn dn ) ” 
  &&  “ (1 <= ax) ” 
  &&  “ (ax <= 46340) ” 
  &&  “ (1 <= bx) ” 
  &&  “ (bx <= 46340) ” 
  &&  “ (1 <= cn) ” 
  &&  “ (cn <= 46340) ” 
  &&  “ (1 <= dn) ” 
  &&  “ (dn <= 46340) ”
  &&  (store_string n_pre ln )
  **  (CharArray.full x_pre ((string_length (lx)) + 1 ) (c_string (lx)) )
.

Definition simplify_partial_solve_wit_2 := simplify_partial_solve_wit_2_pure -> simplify_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_simplify_safety_wit_1 : simplify_safety_wit_1.
Axiom proof_of_simplify_safety_wit_2 : simplify_safety_wit_2.
Axiom proof_of_simplify_safety_wit_3 : simplify_safety_wit_3.
Axiom proof_of_simplify_safety_wit_4 : simplify_safety_wit_4.
Axiom proof_of_simplify_safety_wit_5 : simplify_safety_wit_5.
Axiom proof_of_simplify_safety_wit_6 : simplify_safety_wit_6.
Axiom proof_of_simplify_safety_wit_7 : simplify_safety_wit_7.
Axiom proof_of_simplify_safety_wit_8 : simplify_safety_wit_8.
Axiom proof_of_simplify_safety_wit_9 : simplify_safety_wit_9.
Axiom proof_of_simplify_safety_wit_10 : simplify_safety_wit_10.
Axiom proof_of_simplify_safety_wit_11 : simplify_safety_wit_11.
Axiom proof_of_simplify_safety_wit_12 : simplify_safety_wit_12.
Axiom proof_of_simplify_safety_wit_13 : simplify_safety_wit_13.
Axiom proof_of_simplify_safety_wit_14 : simplify_safety_wit_14.
Axiom proof_of_simplify_safety_wit_15 : simplify_safety_wit_15.
Axiom proof_of_simplify_safety_wit_16 : simplify_safety_wit_16.
Axiom proof_of_simplify_safety_wit_17 : simplify_safety_wit_17.
Axiom proof_of_simplify_safety_wit_18 : simplify_safety_wit_18.
Axiom proof_of_simplify_safety_wit_19 : simplify_safety_wit_19.
Axiom proof_of_simplify_safety_wit_20 : simplify_safety_wit_20.
Axiom proof_of_simplify_safety_wit_21 : simplify_safety_wit_21.
Axiom proof_of_simplify_safety_wit_22 : simplify_safety_wit_22.
Axiom proof_of_simplify_safety_wit_23 : simplify_safety_wit_23.
Axiom proof_of_simplify_safety_wit_24 : simplify_safety_wit_24.
Axiom proof_of_simplify_safety_wit_25 : simplify_safety_wit_25.
Axiom proof_of_simplify_safety_wit_26 : simplify_safety_wit_26.
Axiom proof_of_simplify_safety_wit_27 : simplify_safety_wit_27.
Axiom proof_of_simplify_safety_wit_28 : simplify_safety_wit_28.
Axiom proof_of_simplify_safety_wit_29 : simplify_safety_wit_29.
Axiom proof_of_simplify_safety_wit_30 : simplify_safety_wit_30.
Axiom proof_of_simplify_safety_wit_31 : simplify_safety_wit_31.
Axiom proof_of_simplify_safety_wit_32 : simplify_safety_wit_32.
Axiom proof_of_simplify_safety_wit_33 : simplify_safety_wit_33.
Axiom proof_of_simplify_safety_wit_34 : simplify_safety_wit_34.
Axiom proof_of_simplify_safety_wit_35 : simplify_safety_wit_35.
Axiom proof_of_simplify_safety_wit_36 : simplify_safety_wit_36.
Axiom proof_of_simplify_safety_wit_37 : simplify_safety_wit_37.
Axiom proof_of_simplify_safety_wit_38 : simplify_safety_wit_38.
Axiom proof_of_simplify_safety_wit_39 : simplify_safety_wit_39.
Axiom proof_of_simplify_safety_wit_40 : simplify_safety_wit_40.
Axiom proof_of_simplify_safety_wit_41 : simplify_safety_wit_41.
Axiom proof_of_simplify_safety_wit_42 : simplify_safety_wit_42.
Axiom proof_of_simplify_safety_wit_43 : simplify_safety_wit_43.
Axiom proof_of_simplify_safety_wit_44 : simplify_safety_wit_44.
Axiom proof_of_simplify_safety_wit_45 : simplify_safety_wit_45.
Axiom proof_of_simplify_safety_wit_46 : simplify_safety_wit_46.
Axiom proof_of_simplify_safety_wit_47 : simplify_safety_wit_47.
Axiom proof_of_simplify_safety_wit_48 : simplify_safety_wit_48.
Axiom proof_of_simplify_safety_wit_49 : simplify_safety_wit_49.
Axiom proof_of_simplify_safety_wit_50 : simplify_safety_wit_50.
Axiom proof_of_simplify_safety_wit_51 : simplify_safety_wit_51.
Axiom proof_of_simplify_safety_wit_52 : simplify_safety_wit_52.
Axiom proof_of_simplify_safety_wit_53 : simplify_safety_wit_53.
Axiom proof_of_simplify_safety_wit_54 : simplify_safety_wit_54.
Axiom proof_of_simplify_safety_wit_55 : simplify_safety_wit_55.
Axiom proof_of_simplify_entail_wit_1 : simplify_entail_wit_1.
Axiom proof_of_simplify_entail_wit_2_1 : simplify_entail_wit_2_1.
Axiom proof_of_simplify_entail_wit_2_2 : simplify_entail_wit_2_2.
Axiom proof_of_simplify_entail_wit_2_3 : simplify_entail_wit_2_3.
Axiom proof_of_simplify_entail_wit_2_4 : simplify_entail_wit_2_4.
Axiom proof_of_simplify_entail_wit_3_1 : simplify_entail_wit_3_1.
Axiom proof_of_simplify_entail_wit_3_2 : simplify_entail_wit_3_2.
Axiom proof_of_simplify_entail_wit_4_1 : simplify_entail_wit_4_1.
Axiom proof_of_simplify_entail_wit_4_2 : simplify_entail_wit_4_2.
Axiom proof_of_simplify_entail_wit_5 : simplify_entail_wit_5.
Axiom proof_of_simplify_entail_wit_6_1 : simplify_entail_wit_6_1.
Axiom proof_of_simplify_entail_wit_6_2 : simplify_entail_wit_6_2.
Axiom proof_of_simplify_entail_wit_6_3 : simplify_entail_wit_6_3.
Axiom proof_of_simplify_entail_wit_6_4 : simplify_entail_wit_6_4.
Axiom proof_of_simplify_entail_wit_7_1 : simplify_entail_wit_7_1.
Axiom proof_of_simplify_entail_wit_7_2 : simplify_entail_wit_7_2.
Axiom proof_of_simplify_entail_wit_8_1 : simplify_entail_wit_8_1.
Axiom proof_of_simplify_entail_wit_8_2 : simplify_entail_wit_8_2.
Axiom proof_of_simplify_return_wit_1 : simplify_return_wit_1.
Axiom proof_of_simplify_return_wit_2 : simplify_return_wit_2.
Axiom proof_of_simplify_partial_solve_wit_1_pure : simplify_partial_solve_wit_1_pure.
Axiom proof_of_simplify_partial_solve_wit_1 : simplify_partial_solve_wit_1.
Axiom proof_of_simplify_partial_solve_wit_2_pure : simplify_partial_solve_wit_2_pure.
Axiom proof_of_simplify_partial_solve_wit_2 : simplify_partial_solve_wit_2.

End VC_Correct.
