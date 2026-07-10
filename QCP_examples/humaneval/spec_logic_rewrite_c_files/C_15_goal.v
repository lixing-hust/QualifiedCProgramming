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
Require Import coins_15.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function decimal_len -----*)

Definition decimal_len_safety_wit_1 := 
forall (value_pre: Z) (PreH1 : (0 <= value_pre)) (PreH2 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decimal_len_safety_wit_2 := 
forall (value_pre: Z) (PreH1 : (value_pre = 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition decimal_len_safety_wit_3 := 
forall (value_pre: Z) (PreH1 : (value_pre <> 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) ,
  ((( &( "digits" ) )) # Int  |->_)
  **  ((( &( "tmp" ) )) # Int  |-> value_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decimal_len_safety_wit_4 := 
forall (value_pre: Z) (digits: Z) (tmp: Z) (PreH1 : (0 < value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (0 <= tmp)) (PreH4 : (0 <= digits)) (PreH5 : (digits < INT_MAX)) (PreH6 : (decimal_count_state_z value_pre tmp digits )) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "digits" ) )) # Int  |-> digits)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition decimal_len_safety_wit_5 := 
forall (value_pre: Z) (digits: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (0 <= tmp)) (PreH5 : (0 <= digits)) (PreH6 : (digits < INT_MAX)) (PreH7 : (decimal_count_state_z value_pre tmp digits )) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "digits" ) )) # Int  |-> digits)
|--
  “ ((digits + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digits + 1 )) ”
.

Definition decimal_len_safety_wit_6 := 
forall (value_pre: Z) (digits: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (0 <= tmp)) (PreH5 : (0 <= digits)) (PreH6 : (digits < INT_MAX)) (PreH7 : (decimal_count_state_z value_pre tmp digits )) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "digits" ) )) # Int  |-> digits)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition decimal_len_safety_wit_7 := 
forall (value_pre: Z) (digits: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (0 <= tmp)) (PreH5 : (0 <= digits)) (PreH6 : (digits < INT_MAX)) (PreH7 : (decimal_count_state_z value_pre tmp digits )) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "digits" ) )) # Int  |-> (digits + 1 ))
|--
  “ ((tmp <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition decimal_len_safety_wit_8 := 
forall (value_pre: Z) (digits: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (0 <= tmp)) (PreH5 : (0 <= digits)) (PreH6 : (digits < INT_MAX)) (PreH7 : (decimal_count_state_z value_pre tmp digits )) ,
  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "digits" ) )) # Int  |-> (digits + 1 ))
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition decimal_len_entail_wit_1 := 
(
forall (value_pre: Z) (PreH1 : (value_pre <> 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) ,
  TT && emp 
|--
  “ (0 < value_pre) ” 
  &&  “ (value_pre < INT_MAX) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (decimal_count_state_z value_pre value_pre 0 ) ”
  &&  emp
) \/
(
forall (value_pre: Z) (PreH1 : (value_pre <> 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) ,
  TT && emp 
|--
  “ (decimal_count_state_z value_pre value_pre 0 ) ”
  &&  emp
).

Definition decimal_len_entail_wit_1_split_goal_1 := 
forall (value_pre: Z) (PreH1 : (value_pre <> 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) ,
  TT && emp 
|--
  “ (decimal_count_state_z value_pre value_pre 0 ) ”
.

Definition decimal_len_entail_wit_2 := 
(
forall (value_pre: Z) (digits: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (0 <= tmp)) (PreH5 : (0 <= digits)) (PreH6 : (digits < INT_MAX)) (PreH7 : (decimal_count_state_z value_pre tmp digits )) ,
  TT && emp 
|--
  “ (0 < value_pre) ” 
  &&  “ (value_pre < INT_MAX) ” 
  &&  “ (0 <= (tmp ÷ 10 )) ” 
  &&  “ (0 <= (digits + 1 )) ” 
  &&  “ ((digits + 1 ) < INT_MAX) ” 
  &&  “ (decimal_count_state_z value_pre (tmp ÷ 10 ) (digits + 1 ) ) ”
  &&  emp
) \/
(
forall (value_pre: Z) (digits: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (0 <= tmp)) (PreH5 : (0 <= digits)) (PreH6 : (digits < INT_MAX)) (PreH7 : (decimal_count_state_z value_pre tmp digits )) ,
  TT && emp 
|--
  “ (decimal_count_state_z value_pre (tmp ÷ 10 ) (digits + 1 ) ) ” 
  &&  “ ((digits + 1 ) < INT_MAX) ” 
  &&  “ (0 <= (tmp ÷ 10 )) ”
  &&  emp
).

Definition decimal_len_entail_wit_2_split_goal_1 := 
forall (value_pre: Z) (digits: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (0 <= tmp)) (PreH5 : (0 <= digits)) (PreH6 : (digits < INT_MAX)) (PreH7 : (decimal_count_state_z value_pre tmp digits )) ,
  TT && emp 
|--
  “ (decimal_count_state_z value_pre (tmp ÷ 10 ) (digits + 1 ) ) ”
.

Definition decimal_len_entail_wit_2_split_goal_2 := 
forall (value_pre: Z) (digits: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (0 <= tmp)) (PreH5 : (0 <= digits)) (PreH6 : (digits < INT_MAX)) (PreH7 : (decimal_count_state_z value_pre tmp digits )) ,
  TT && emp 
|--
  “ ((digits + 1 ) < INT_MAX) ”
.

Definition decimal_len_entail_wit_2_split_goal_3 := 
forall (value_pre: Z) (digits: Z) (tmp: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (0 <= tmp)) (PreH5 : (0 <= digits)) (PreH6 : (digits < INT_MAX)) (PreH7 : (decimal_count_state_z value_pre tmp digits )) ,
  TT && emp 
|--
  “ (0 <= (tmp ÷ 10 )) ”
.

Definition decimal_len_return_wit_1 := 
(
forall (value_pre: Z) (digits: Z) (tmp: Z) (PreH1 : (tmp <= 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (0 <= tmp)) (PreH5 : (0 <= digits)) (PreH6 : (digits < INT_MAX)) (PreH7 : (decimal_count_state_z value_pre tmp digits )) ,
  TT && emp 
|--
  “ (digits = (Zlength ((decimal_digits_z (value_pre))))) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits < INT_MAX) ”
  &&  emp
) \/
(
forall (value_pre: Z) (digits: Z) (tmp: Z) (PreH1 : (tmp <= 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (0 <= tmp)) (PreH5 : (0 <= digits)) (PreH6 : (digits < INT_MAX)) (PreH7 : (decimal_count_state_z value_pre tmp digits )) ,
  TT && emp 
|--
  “ (1 <= digits) ” 
  &&  “ (digits = (Zlength ((decimal_digits_z (value_pre))))) ”
  &&  emp
).

Definition decimal_len_return_wit_1_split_goal_1 := 
forall (value_pre: Z) (digits: Z) (tmp: Z) (PreH1 : (tmp <= 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (0 <= tmp)) (PreH5 : (0 <= digits)) (PreH6 : (digits < INT_MAX)) (PreH7 : (decimal_count_state_z value_pre tmp digits )) ,
  TT && emp 
|--
  “ (1 <= digits) ”
.

Definition decimal_len_return_wit_1_split_goal_2 := 
forall (value_pre: Z) (digits: Z) (tmp: Z) (PreH1 : (tmp <= 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (0 <= tmp)) (PreH5 : (0 <= digits)) (PreH6 : (digits < INT_MAX)) (PreH7 : (decimal_count_state_z value_pre tmp digits )) ,
  TT && emp 
|--
  “ (digits = (Zlength ((decimal_digits_z (value_pre))))) ”
.

Definition decimal_len_return_wit_2 := 
(
forall (value_pre: Z) (PreH1 : (value_pre = 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (Zlength ((decimal_digits_z (value_pre))))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 < INT_MAX) ”
  &&  emp
) \/
(
forall (value_pre: Z) (PreH1 : (value_pre = 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (Zlength ((decimal_digits_z (value_pre))))) ”
  &&  emp
).

Definition decimal_len_return_wit_2_split_goal_1 := 
forall (value_pre: Z) (PreH1 : (value_pre = 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (Zlength ((decimal_digits_z (value_pre))))) ”
.

(*----- Function write_decimal -----*)

Definition write_decimal_safety_wit_1 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (0 <= value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH4 : (1 <= digits_pre)) (PreH5 : (digits_pre < INT_MAX)) ,
  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  (CharArray.undef_full buf_pre digits_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition write_decimal_safety_wit_2 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (value_pre = 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) ,
  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  (CharArray.undef_full buf_pre digits_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition write_decimal_safety_wit_3 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (value_pre = 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) ,
  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  (CharArray.undef_full buf_pre digits_pre )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition write_decimal_safety_wit_4 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (value_pre <> 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "tmp" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  (CharArray.undef_full buf_pre digits_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition write_decimal_safety_wit_5 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (i: Z) (fill: Z) (tmp: Z) (PreH1 : (i < digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (tmp = value_pre)) (PreH8 : (fill = digits_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= digits_pre)) ,
  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full buf_pre i (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg buf_pre i digits_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition write_decimal_safety_wit_6 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (i: Z) (fill: Z) (tmp: Z) (PreH1 : (i < digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (tmp = value_pre)) (PreH8 : (fill = digits_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= digits_pre)) ,
  (CharArray.full buf_pre (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf_pre (i + 1 ) digits_pre )
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition write_decimal_safety_wit_7 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (i: Z) (fill: Z) (tmp: Z) (PreH1 : (i < digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (tmp = value_pre)) (PreH8 : (fill = digits_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= digits_pre)) ,
  (CharArray.full buf_pre (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf_pre (i + 1 ) digits_pre )
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition write_decimal_safety_wit_8 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (PreH1 : (0 < value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH4 : (1 <= digits_pre)) (PreH5 : (digits_pre < INT_MAX)) (PreH6 : (i = digits_pre)) (PreH7 : (0 <= tmp)) (PreH8 : (0 <= fill)) (PreH9 : (fill <= digits_pre)) (PreH10 : ((Zlength (out_l)) = digits_pre)) (PreH11 : (decimal_fill_full_state_z value_pre tmp fill out_l )) ,
  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full buf_pre digits_pre out_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition write_decimal_safety_wit_9 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill <= digits_pre)) (PreH11 : ((Zlength (out_l)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp fill out_l )) ,
  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full buf_pre digits_pre out_l )
|--
  “ ((fill - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (fill - 1 )) ”
.

Definition write_decimal_safety_wit_10 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill <= digits_pre)) (PreH11 : ((Zlength (out_l)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp fill out_l )) ,
  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full buf_pre digits_pre out_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition write_decimal_safety_wit_11 := 
(
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l: (@list Z)) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 < value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH4 : (1 <= digits_pre)) (PreH5 : (digits_pre < INT_MAX)) (PreH6 : (i = digits_pre)) (PreH7 : (0 < tmp)) (PreH8 : (0 <= fill)) (PreH9 : (fill < digits_pre)) (PreH10 : ((Zlength (out_l)) = digits_pre)) (PreH11 : (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l )) ,
  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full buf_pre digits_pre out_l )
|--
  “ ((48 + (tmp % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (48 + (tmp % ( 10 ) ) )) ”
) \/
(
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l: (@list Z)) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 < value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH4 : (1 <= digits_pre)) (PreH5 : (digits_pre < INT_MAX)) (PreH6 : (i = digits_pre)) (PreH7 : (0 < tmp)) (PreH8 : (0 <= fill)) (PreH9 : (fill < digits_pre)) (PreH10 : ((Zlength (out_l)) = digits_pre)) (PreH11 : (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l )) ,
  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full buf_pre digits_pre out_l )
|--
  “ ((48 + (tmp % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (48 + (tmp % ( 10 ) ) )) ”
).

Definition write_decimal_safety_wit_11_split_goal_1 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l: (@list Z)) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 < value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH4 : (1 <= digits_pre)) (PreH5 : (digits_pre < INT_MAX)) (PreH6 : (i = digits_pre)) (PreH7 : (0 < tmp)) (PreH8 : (0 <= fill)) (PreH9 : (fill < digits_pre)) (PreH10 : ((Zlength (out_l)) = digits_pre)) (PreH11 : (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l )) ,
  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full buf_pre digits_pre out_l )
|--
  “ ((48 + (tmp % ( 10 ) ) ) <= INT_MAX) ”
.

Definition write_decimal_safety_wit_11_split_goal_2 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l: (@list Z)) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 < value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH4 : (1 <= digits_pre)) (PreH5 : (digits_pre < INT_MAX)) (PreH6 : (i = digits_pre)) (PreH7 : (0 < tmp)) (PreH8 : (0 <= fill)) (PreH9 : (fill < digits_pre)) (PreH10 : ((Zlength (out_l)) = digits_pre)) (PreH11 : (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l )) ,
  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full buf_pre digits_pre out_l )
|--
  “ ((INT_MIN) <= (48 + (tmp % ( 10 ) ) )) ”
.

Definition write_decimal_safety_wit_12 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l: (@list Z)) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 < value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH4 : (1 <= digits_pre)) (PreH5 : (digits_pre < INT_MAX)) (PreH6 : (i = digits_pre)) (PreH7 : (0 < tmp)) (PreH8 : (0 <= fill)) (PreH9 : (fill < digits_pre)) (PreH10 : ((Zlength (out_l)) = digits_pre)) (PreH11 : (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l )) ,
  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full buf_pre digits_pre out_l )
|--
  “ ((tmp <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition write_decimal_safety_wit_13 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l: (@list Z)) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 < value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH4 : (1 <= digits_pre)) (PreH5 : (digits_pre < INT_MAX)) (PreH6 : (i = digits_pre)) (PreH7 : (0 < tmp)) (PreH8 : (0 <= fill)) (PreH9 : (fill < digits_pre)) (PreH10 : ((Zlength (out_l)) = digits_pre)) (PreH11 : (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l )) ,
  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full buf_pre digits_pre out_l )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition write_decimal_safety_wit_14 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l: (@list Z)) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 < value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH4 : (1 <= digits_pre)) (PreH5 : (digits_pre < INT_MAX)) (PreH6 : (i = digits_pre)) (PreH7 : (0 < tmp)) (PreH8 : (0 <= fill)) (PreH9 : (fill < digits_pre)) (PreH10 : ((Zlength (out_l)) = digits_pre)) (PreH11 : (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l )) ,
  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  (CharArray.full buf_pre digits_pre out_l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition write_decimal_safety_wit_15 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l: (@list Z)) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 <= digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 < tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill < digits_pre)) (PreH11 : ((Zlength (out_l)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l )) ,
  (CharArray.full buf_pre digits_pre (replace_Znth (fill) ((signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8))) (out_l)) )
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
|--
  “ ((tmp <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition write_decimal_safety_wit_16 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l: (@list Z)) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 <= digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 < tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill < digits_pre)) (PreH11 : ((Zlength (out_l)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l )) ,
  (CharArray.full buf_pre digits_pre (replace_Znth (fill) ((signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8))) (out_l)) )
  **  ((( &( "buf" ) )) # Ptr  |-> buf_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # Int  |-> tmp)
  **  ((( &( "fill" ) )) # Int  |-> fill)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition write_decimal_entail_wit_1 := 
(
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (value_pre <> 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) ,
  (CharArray.undef_full buf_pre digits_pre )
|--
  “ (0 < value_pre) ” 
  &&  “ (value_pre < INT_MAX) ” 
  &&  “ (digits_pre = (Zlength ((decimal_digits_z (value_pre))))) ” 
  &&  “ (1 <= digits_pre) ” 
  &&  “ (digits_pre < INT_MAX) ” 
  &&  “ (value_pre = value_pre) ” 
  &&  “ (digits_pre = digits_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= digits_pre) ”
  &&  (CharArray.full buf_pre 0 (repeat_Z (0) (0)) )
  **  (CharArray.undef_seg buf_pre 0 digits_pre )
) \/
(
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (value_pre <> 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) ,
  (CharArray.undef_full buf_pre digits_pre )
|--
  “ ((repeat_Z (0) (0)) = (@nil Z)) ”
  &&  (CharArray.undef_full buf_pre digits_pre )
).

Definition write_decimal_entail_wit_1_split_goal_1 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (value_pre <> 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) ,
  (CharArray.undef_full buf_pre digits_pre )
|--
  “ ((repeat_Z (0) (0)) = (@nil Z)) ”
.

Definition write_decimal_entail_wit_1_split_goal_spatial := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (value_pre <> 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) ,
  (CharArray.undef_full buf_pre digits_pre )
|--
  (CharArray.undef_full buf_pre digits_pre )
.

Definition write_decimal_entail_wit_2 := 
(
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (i: Z) (fill: Z) (tmp: Z) (PreH1 : (i < digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (tmp = value_pre)) (PreH8 : (fill = digits_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= digits_pre)) ,
  (CharArray.full buf_pre (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg buf_pre (i + 1 ) digits_pre )
|--
  “ (0 < value_pre) ” 
  &&  “ (value_pre < INT_MAX) ” 
  &&  “ (digits_pre = (Zlength ((decimal_digits_z (value_pre))))) ” 
  &&  “ (1 <= digits_pre) ” 
  &&  “ (digits_pre < INT_MAX) ” 
  &&  “ (tmp = value_pre) ” 
  &&  “ (fill = digits_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= digits_pre) ”
  &&  (CharArray.full buf_pre (i + 1 ) (repeat_Z (0) ((i + 1 ))) )
  **  (CharArray.undef_seg buf_pre (i + 1 ) digits_pre )
) \/
(
forall (digits_pre: Z) (value_pre: Z) (i: Z) (fill: Z) (tmp: Z) (PreH1 : (i < digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (tmp = value_pre)) (PreH8 : (fill = digits_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= digits_pre)) ,
  TT && emp 
|--
  “ ((app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) = (repeat_Z (0) ((i + 1 )))) ”
  &&  emp
).

Definition write_decimal_entail_wit_2_split_goal_1 := 
forall (digits_pre: Z) (value_pre: Z) (i: Z) (fill: Z) (tmp: Z) (PreH1 : (i < digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (tmp = value_pre)) (PreH8 : (fill = digits_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= digits_pre)) ,
  TT && emp 
|--
  “ ((app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) = (repeat_Z (0) ((i + 1 )))) ”
.

Definition write_decimal_entail_wit_3 := 
(
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (i: Z) (fill: Z) (tmp: Z) (PreH1 : (i >= digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (tmp = value_pre)) (PreH8 : (fill = digits_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= digits_pre)) ,
  (CharArray.full buf_pre i (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg buf_pre i digits_pre )
|--
  EX (out_l: (@list Z)) ,
  “ (0 < value_pre) ” 
  &&  “ (value_pre < INT_MAX) ” 
  &&  “ (digits_pre = (Zlength ((decimal_digits_z (value_pre))))) ” 
  &&  “ (1 <= digits_pre) ” 
  &&  “ (digits_pre < INT_MAX) ” 
  &&  “ (tmp = value_pre) ” 
  &&  “ (fill = digits_pre) ” 
  &&  “ (i = digits_pre) ” 
  &&  “ ((Zlength (out_l)) = digits_pre) ” 
  &&  “ (decimal_fill_full_state_z value_pre tmp fill out_l ) ”
  &&  (CharArray.full buf_pre digits_pre out_l )
) \/
(
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (i: Z) (fill: Z) (tmp: Z) (PreH1 : (i >= digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (tmp = value_pre)) (PreH8 : (fill = digits_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= digits_pre)) ,
  (CharArray.full buf_pre i (repeat_Z (0) (i)) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 < value_pre) ” 
  &&  “ (value_pre < INT_MAX) ” 
  &&  “ (digits_pre = (Zlength ((decimal_digits_z (value_pre))))) ” 
  &&  “ (1 <= digits_pre) ” 
  &&  “ (digits_pre < INT_MAX) ” 
  &&  “ (tmp = value_pre) ” 
  &&  “ (fill = digits_pre) ” 
  &&  “ (i = digits_pre) ” 
  &&  “ ((Zlength (out_l)) = digits_pre) ” 
  &&  “ (decimal_fill_full_state_z value_pre tmp fill out_l ) ”
  &&  (CharArray.full buf_pre digits_pre out_l )
).

Definition write_decimal_entail_wit_4 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l_2: (@list Z)) (tmp: Z) (fill: Z) (i: Z) (PreH1 : (0 < value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH4 : (1 <= digits_pre)) (PreH5 : (digits_pre < INT_MAX)) (PreH6 : (tmp = value_pre)) (PreH7 : (fill = digits_pre)) (PreH8 : (i = digits_pre)) (PreH9 : ((Zlength (out_l_2)) = digits_pre)) (PreH10 : (decimal_fill_full_state_z value_pre tmp fill out_l_2 )) ,
  (CharArray.full buf_pre digits_pre out_l_2 )
|--
  EX (out_l: (@list Z)) ,
  “ (0 < value_pre) ” 
  &&  “ (value_pre < INT_MAX) ” 
  &&  “ (digits_pre = (Zlength ((decimal_digits_z (value_pre))))) ” 
  &&  “ (1 <= digits_pre) ” 
  &&  “ (digits_pre < INT_MAX) ” 
  &&  “ (i = digits_pre) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits_pre) ” 
  &&  “ ((Zlength (out_l)) = digits_pre) ” 
  &&  “ (decimal_fill_full_state_z value_pre tmp fill out_l ) ”
  &&  (CharArray.full buf_pre digits_pre out_l )
.

Definition write_decimal_entail_wit_5 := 
(
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l_2: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill <= digits_pre)) (PreH11 : ((Zlength (out_l_2)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp fill out_l_2 )) ,
  (CharArray.full buf_pre digits_pre out_l_2 )
|--
  EX (out_l: (@list Z)) ,
  “ (0 < value_pre) ” 
  &&  “ (value_pre < INT_MAX) ” 
  &&  “ (digits_pre = (Zlength ((decimal_digits_z (value_pre))))) ” 
  &&  “ (1 <= digits_pre) ” 
  &&  “ (digits_pre < INT_MAX) ” 
  &&  “ (i = digits_pre) ” 
  &&  “ (0 < tmp) ” 
  &&  “ (0 <= (fill - 1 )) ” 
  &&  “ ((fill - 1 ) < digits_pre) ” 
  &&  “ ((Zlength (out_l)) = digits_pre) ” 
  &&  “ (decimal_fill_full_state_z value_pre tmp ((fill - 1 ) + 1 ) out_l ) ”
  &&  (CharArray.full buf_pre digits_pre out_l )
) \/
(
forall (digits_pre: Z) (value_pre: Z) (out_l_2: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill <= digits_pre)) (PreH11 : ((Zlength (out_l_2)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp fill out_l_2 )) ,
  TT && emp 
|--
  “ (decimal_fill_full_state_z value_pre tmp ((fill - 1 ) + 1 ) out_l_2 ) ” 
  &&  “ (0 <= (fill - 1 )) ”
  &&  emp
).

Definition write_decimal_entail_wit_5_split_goal_1 := 
forall (digits_pre: Z) (value_pre: Z) (out_l_2: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill <= digits_pre)) (PreH11 : ((Zlength (out_l_2)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp fill out_l_2 )) ,
  TT && emp 
|--
  “ (decimal_fill_full_state_z value_pre tmp ((fill - 1 ) + 1 ) out_l_2 ) ”
.

Definition write_decimal_entail_wit_5_split_goal_2 := 
forall (digits_pre: Z) (value_pre: Z) (out_l_2: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (PreH1 : (tmp > 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill <= digits_pre)) (PreH11 : ((Zlength (out_l_2)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp fill out_l_2 )) ,
  TT && emp 
|--
  “ (0 <= (fill - 1 )) ”
.

Definition write_decimal_entail_wit_6 := 
(
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l_2: (@list Z)) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 <= digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 < tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill < digits_pre)) (PreH11 : ((Zlength (out_l_2)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l_2 )) ,
  (CharArray.full buf_pre digits_pre (replace_Znth (fill) ((signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8))) (out_l_2)) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 < value_pre) ” 
  &&  “ (value_pre < INT_MAX) ” 
  &&  “ (digits_pre = (Zlength ((decimal_digits_z (value_pre))))) ” 
  &&  “ (1 <= digits_pre) ” 
  &&  “ (digits_pre < INT_MAX) ” 
  &&  “ (i = digits_pre) ” 
  &&  “ (0 <= (tmp ÷ 10 )) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits_pre) ” 
  &&  “ ((Zlength (out_l)) = digits_pre) ” 
  &&  “ (decimal_fill_full_state_z value_pre (tmp ÷ 10 ) fill out_l ) ”
  &&  (CharArray.full buf_pre digits_pre out_l )
) \/
(
forall (digits_pre: Z) (value_pre: Z) (out_l_2: (@list Z)) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 <= digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 < tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill < digits_pre)) (PreH11 : ((Zlength (out_l_2)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l_2 )) ,
  TT && emp 
|--
  “ (decimal_fill_full_state_z value_pre (tmp ÷ 10 ) fill (replace_Znth (fill) ((signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8))) (out_l_2)) ) ” 
  &&  “ ((Zlength ((replace_Znth (fill) ((signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8))) (out_l_2)))) = digits_pre) ” 
  &&  “ (0 <= (tmp ÷ 10 )) ”
  &&  emp
).

Definition write_decimal_entail_wit_6_split_goal_1 := 
forall (digits_pre: Z) (value_pre: Z) (out_l_2: (@list Z)) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 <= digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 < tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill < digits_pre)) (PreH11 : ((Zlength (out_l_2)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l_2 )) ,
  TT && emp 
|--
  “ (decimal_fill_full_state_z value_pre (tmp ÷ 10 ) fill (replace_Znth (fill) ((signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8))) (out_l_2)) ) ”
.

Definition write_decimal_entail_wit_6_split_goal_2 := 
forall (digits_pre: Z) (value_pre: Z) (out_l_2: (@list Z)) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 <= digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 < tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill < digits_pre)) (PreH11 : ((Zlength (out_l_2)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l_2 )) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth (fill) ((signed_last_nbits ((48 + (tmp % ( 10 ) ) )) (8))) (out_l_2)))) = digits_pre) ”
.

Definition write_decimal_entail_wit_6_split_goal_3 := 
forall (digits_pre: Z) (value_pre: Z) (out_l_2: (@list Z)) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 <= digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 < tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill < digits_pre)) (PreH11 : ((Zlength (out_l_2)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l_2 )) ,
  TT && emp 
|--
  “ (0 <= (tmp ÷ 10 )) ”
.

Definition write_decimal_return_wit_1 := 
(
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (value_pre = 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) ,
  (CharArray.undef_seg buf_pre (0 + 1 ) digits_pre )
  **  (((buf_pre + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  (CharArray.full buf_pre digits_pre (decimal_digits_z (value_pre)) )
) \/
(
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (value_pre = 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) ,
  (CharArray.undef_seg buf_pre (0 + 1 ) digits_pre )
  **  (((buf_pre + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  (CharArray.full buf_pre digits_pre (decimal_digits_z (value_pre)) )
).

Definition write_decimal_return_wit_1_split_goal_spatial := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (value_pre = 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) ,
  (CharArray.undef_seg buf_pre (0 + 1 ) digits_pre )
  **  (((buf_pre + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  (CharArray.full buf_pre digits_pre (decimal_digits_z (value_pre)) )
.

Definition write_decimal_return_wit_2 := 
(
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (PreH1 : (tmp <= 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill <= digits_pre)) (PreH11 : ((Zlength (out_l)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp fill out_l )) ,
  (CharArray.full buf_pre digits_pre out_l )
|--
  (CharArray.full buf_pre digits_pre (decimal_digits_z (value_pre)) )
) \/
(
forall (digits_pre: Z) (value_pre: Z) (out_l: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (PreH1 : (tmp <= 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill <= digits_pre)) (PreH11 : ((Zlength (out_l)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp fill out_l )) ,
  TT && emp 
|--
  “ (out_l = (decimal_digits_z (value_pre))) ”
  &&  emp
).

Definition write_decimal_return_wit_2_split_goal_1 := 
forall (digits_pre: Z) (value_pre: Z) (out_l: (@list Z)) (fill: Z) (tmp: Z) (i: Z) (PreH1 : (tmp <= 0)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (i = digits_pre)) (PreH8 : (0 <= tmp)) (PreH9 : (0 <= fill)) (PreH10 : (fill <= digits_pre)) (PreH11 : ((Zlength (out_l)) = digits_pre)) (PreH12 : (decimal_fill_full_state_z value_pre tmp fill out_l )) ,
  TT && emp 
|--
  “ (out_l = (decimal_digits_z (value_pre))) ”
.

Definition write_decimal_partial_solve_wit_1 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (PreH1 : (value_pre = 0)) (PreH2 : (0 <= value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) ,
  (CharArray.undef_full buf_pre digits_pre )
|--
  “ (value_pre = 0) ” 
  &&  “ (0 <= value_pre) ” 
  &&  “ (value_pre < INT_MAX) ” 
  &&  “ (digits_pre = (Zlength ((decimal_digits_z (value_pre))))) ” 
  &&  “ (1 <= digits_pre) ” 
  &&  “ (digits_pre < INT_MAX) ”
  &&  (((buf_pre + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i buf_pre 0 0 digits_pre )
.

Definition write_decimal_partial_solve_wit_2 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (i: Z) (fill: Z) (tmp: Z) (PreH1 : (i < digits_pre)) (PreH2 : (0 < value_pre)) (PreH3 : (value_pre < INT_MAX)) (PreH4 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH5 : (1 <= digits_pre)) (PreH6 : (digits_pre < INT_MAX)) (PreH7 : (tmp = value_pre)) (PreH8 : (fill = digits_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= digits_pre)) ,
  (CharArray.full buf_pre i (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg buf_pre i digits_pre )
|--
  “ (i < digits_pre) ” 
  &&  “ (0 < value_pre) ” 
  &&  “ (value_pre < INT_MAX) ” 
  &&  “ (digits_pre = (Zlength ((decimal_digits_z (value_pre))))) ” 
  &&  “ (1 <= digits_pre) ” 
  &&  “ (digits_pre < INT_MAX) ” 
  &&  “ (tmp = value_pre) ” 
  &&  “ (fill = digits_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= digits_pre) ”
  &&  (((buf_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i buf_pre i i digits_pre )
  **  (CharArray.full buf_pre i (repeat_Z (0) (i)) )
.

Definition write_decimal_partial_solve_wit_3 := 
forall (digits_pre: Z) (value_pre: Z) (buf_pre: Z) (out_l: (@list Z)) (i: Z) (tmp: Z) (fill: Z) (PreH1 : (0 < value_pre)) (PreH2 : (value_pre < INT_MAX)) (PreH3 : (digits_pre = (Zlength ((decimal_digits_z (value_pre)))))) (PreH4 : (1 <= digits_pre)) (PreH5 : (digits_pre < INT_MAX)) (PreH6 : (i = digits_pre)) (PreH7 : (0 < tmp)) (PreH8 : (0 <= fill)) (PreH9 : (fill < digits_pre)) (PreH10 : ((Zlength (out_l)) = digits_pre)) (PreH11 : (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l )) ,
  (CharArray.full buf_pre digits_pre out_l )
|--
  “ (0 <= digits_pre) ” 
  &&  “ (0 < value_pre) ” 
  &&  “ (value_pre < INT_MAX) ” 
  &&  “ (digits_pre = (Zlength ((decimal_digits_z (value_pre))))) ” 
  &&  “ (1 <= digits_pre) ” 
  &&  “ (digits_pre < INT_MAX) ” 
  &&  “ (i = digits_pre) ” 
  &&  “ (0 < tmp) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill < digits_pre) ” 
  &&  “ ((Zlength (out_l)) = digits_pre) ” 
  &&  “ (decimal_fill_full_state_z value_pre tmp (fill + 1 ) out_l ) ”
  &&  (((buf_pre + (fill * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i buf_pre fill 0 digits_pre out_l )
.

(*----- Function string_sequence -----*)

Definition string_sequence_safety_wit_1 := 
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) ,
  ((( &( "total" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition string_sequence_safety_wit_2 := 
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "total" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition string_sequence_safety_wit_3 := 
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "total" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition string_sequence_safety_wit_4 := 
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "total" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition string_sequence_safety_wit_5 := 
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "total" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition string_sequence_safety_wit_6 := 
(
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_z (i)))))) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH8 : (problem_15_pre_z n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH12 : (total <= (sequence_len_z (n_pre)))) (PreH13 : (k = 0)) (PreH14 : (len >= 0)) (PreH15 : (out = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (((total + 1 ) + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((total + 1 ) + retval )) ”
) \/
(
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_z (i)))))) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH8 : (problem_15_pre_z n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH12 : (total <= (sequence_len_z (n_pre)))) (PreH13 : (k = 0)) (PreH14 : (len >= 0)) (PreH15 : (out = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (((total + 1 ) + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((total + 1 ) + retval )) ”
).

Definition string_sequence_safety_wit_6_split_goal_1 := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_z (i)))))) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH8 : (problem_15_pre_z n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH12 : (total <= (sequence_len_z (n_pre)))) (PreH13 : (k = 0)) (PreH14 : (len >= 0)) (PreH15 : (out = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (((total + 1 ) + retval ) <= INT_MAX) ”
.

Definition string_sequence_safety_wit_6_split_goal_2 := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_z (i)))))) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH8 : (problem_15_pre_z n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH12 : (total <= (sequence_len_z (n_pre)))) (PreH13 : (k = 0)) (PreH14 : (len >= 0)) (PreH15 : (out = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((INT_MIN) <= ((total + 1 ) + retval )) ”
.

Definition string_sequence_safety_wit_7 := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_z (i)))))) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH8 : (problem_15_pre_z n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH12 : (total <= (sequence_len_z (n_pre)))) (PreH13 : (k = 0)) (PreH14 : (len >= 0)) (PreH15 : (out = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((total + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total + 1 )) ”
.

Definition string_sequence_safety_wit_8 := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_z (i)))))) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH8 : (problem_15_pre_z n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH12 : (total <= (sequence_len_z (n_pre)))) (PreH13 : (k = 0)) (PreH14 : (len >= 0)) (PreH15 : (out = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition string_sequence_safety_wit_9 := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_z (i)))))) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH8 : (problem_15_pre_z n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH12 : (total <= (sequence_len_z (n_pre)))) (PreH13 : (k = 0)) (PreH14 : (len >= 0)) (PreH15 : (out = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> ((total + 1 ) + retval ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition string_sequence_safety_wit_10 := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_z (i)))))) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH8 : (problem_15_pre_z n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH12 : (total <= (sequence_len_z (n_pre)))) (PreH13 : (k = 0)) (PreH14 : (len >= 0)) (PreH15 : (out = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> ((total + 1 ) + retval ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition string_sequence_safety_wit_11 := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH9 : (total <= (sequence_len_z (n_pre)))) (PreH10 : (k = 0)) (PreH11 : (len >= 0)) (PreH12 : (out = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((total + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total + 1 )) ”
.

Definition string_sequence_safety_wit_12 := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH9 : (total <= (sequence_len_z (n_pre)))) (PreH10 : (k = 0)) (PreH11 : (len >= 0)) (PreH12 : (out = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition string_sequence_safety_wit_13 := 
forall (n_pre: Z) (i: Z) (total: Z) (k: Z) (len: Z) (out: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (i = (n_pre + 1 ))) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (0 <= total)) (PreH8 : (k = 0)) (PreH9 : (len >= 0)) (PreH10 : (out <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (total + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition string_sequence_safety_wit_14 := 
forall (n_pre: Z) (i: Z) (total: Z) (k: Z) (len: Z) (out: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (i = (n_pre + 1 ))) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (0 <= total)) (PreH8 : (k = 0)) (PreH9 : (len >= 0)) (PreH10 : (out <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_full out (total + 1 ) )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition string_sequence_safety_wit_15 := 
forall (n_pre: Z) (i: Z) (total: Z) (k: Z) (len: Z) (out: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (i = (n_pre + 1 ))) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (0 <= total)) (PreH8 : (k = 0)) (PreH9 : (len >= 0)) (PreH10 : (out <> 0)) ,
  (CharArray.undef_seg out (0 + 1 ) (total + 1 ) )
  **  (((out + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition string_sequence_safety_wit_16 := 
forall (n_pre: Z) (i: Z) (total: Z) (k: Z) (len: Z) (out: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (i = (n_pre + 1 ))) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (0 <= total)) (PreH8 : (k = 0)) (PreH9 : (len >= 0)) (PreH10 : (out <> 0)) ,
  (CharArray.undef_seg out (0 + 1 ) (total + 1 ) )
  **  (((out + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> 1)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition string_sequence_safety_wit_17 := 
forall (n_pre: Z) (out: Z) (len: Z) (out_l: (@list Z)) (k: Z) (i: Z) (total: Z) (PreH1 : (i <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= k)) (PreH10 : (k <= total)) (PreH11 : (k = (Zlength (out_l)))) (PreH12 : (out_l = (string_sequence_prefix_z (i)))) (PreH13 : (len >= 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (total + 1 ) )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition string_sequence_safety_wit_18 := 
forall (n_pre: Z) (out: Z) (len: Z) (out_l: (@list Z)) (k: Z) (i: Z) (total: Z) (PreH1 : (i <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= k)) (PreH10 : (k <= total)) (PreH11 : (k = (Zlength (out_l)))) (PreH12 : (out_l = (string_sequence_prefix_z (i)))) (PreH13 : (len >= 0)) ,
  (CharArray.full out (k + 1 ) (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (total + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition string_sequence_safety_wit_19 := 
forall (n_pre: Z) (out: Z) (len: Z) (out_l: (@list Z)) (k: Z) (i: Z) (total: Z) (PreH1 : (i <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= k)) (PreH10 : (k <= total)) (PreH11 : (k = (Zlength (out_l)))) (PreH12 : (out_l = (string_sequence_prefix_z (i)))) (PreH13 : (len >= 0)) ,
  (CharArray.full out (k + 1 ) (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (total + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition string_sequence_safety_wit_20 := 
(
forall (n_pre: Z) (out_l: (@list Z)) (total: Z) (i: Z) (len: Z) (k: Z) (out: Z) (PreH1 : (0 <= k)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (len = (Zlength ((decimal_digits_z (i)))))) (PreH10 : (1 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (k = ((Zlength (out_l)) + 1 ))) (PreH13 : (out_l = (string_sequence_prefix_z (i)))) ,
  (CharArray.full (out + (k * sizeof(CHAR) ) ) len (decimal_digits_z (i)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + len ) (total + 1 ) )
|--
  “ ((k + len ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + len )) ”
) \/
(
forall (n_pre: Z) (out_l: (@list Z)) (total: Z) (i: Z) (len: Z) (k: Z) (out: Z) (PreH1 : (0 <= k)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (len = (Zlength ((decimal_digits_z (i)))))) (PreH10 : (1 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (k = ((Zlength (out_l)) + 1 ))) (PreH13 : (out_l = (string_sequence_prefix_z (i)))) ,
  (CharArray.full (out + (k * sizeof(CHAR) ) ) len (decimal_digits_z (i)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + len ) (total + 1 ) )
|--
  “ ((k + len ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + len )) ”
).

Definition string_sequence_safety_wit_20_split_goal_1 := 
forall (n_pre: Z) (out_l: (@list Z)) (total: Z) (i: Z) (len: Z) (k: Z) (out: Z) (PreH1 : (0 <= k)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (len = (Zlength ((decimal_digits_z (i)))))) (PreH10 : (1 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (k = ((Zlength (out_l)) + 1 ))) (PreH13 : (out_l = (string_sequence_prefix_z (i)))) ,
  (CharArray.full (out + (k * sizeof(CHAR) ) ) len (decimal_digits_z (i)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + len ) (total + 1 ) )
|--
  “ ((k + len ) <= INT_MAX) ”
.

Definition string_sequence_safety_wit_20_split_goal_2 := 
forall (n_pre: Z) (out_l: (@list Z)) (total: Z) (i: Z) (len: Z) (k: Z) (out: Z) (PreH1 : (0 <= k)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (len = (Zlength ((decimal_digits_z (i)))))) (PreH10 : (1 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (k = ((Zlength (out_l)) + 1 ))) (PreH13 : (out_l = (string_sequence_prefix_z (i)))) ,
  (CharArray.full (out + (k * sizeof(CHAR) ) ) len (decimal_digits_z (i)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + len ) (total + 1 ) )
|--
  “ ((INT_MIN) <= (k + len )) ”
.

Definition string_sequence_safety_wit_21 := 
forall (n_pre: Z) (out_l: (@list Z)) (total: Z) (i: Z) (len: Z) (k: Z) (out: Z) (PreH1 : (0 <= k)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (len = (Zlength ((decimal_digits_z (i)))))) (PreH10 : (1 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (k = ((Zlength (out_l)) + 1 ))) (PreH13 : (out_l = (string_sequence_prefix_z (i)))) ,
  (CharArray.full (out + (k * sizeof(CHAR) ) ) len (decimal_digits_z (i)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> (k + len ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + len ) (total + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition string_sequence_safety_wit_22 := 
forall (n_pre: Z) (out_l: (@list Z)) (total: Z) (i: Z) (len: Z) (k: Z) (out: Z) (PreH1 : (0 <= k)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (len = (Zlength ((decimal_digits_z (i)))))) (PreH10 : (1 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (k = ((Zlength (out_l)) + 1 ))) (PreH13 : (out_l = (string_sequence_prefix_z (i)))) ,
  (CharArray.full (out + (k * sizeof(CHAR) ) ) len (decimal_digits_z (i)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> (k + len ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + len ) (total + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition string_sequence_safety_wit_23 := 
forall (n_pre: Z) (out: Z) (len: Z) (out_l: (@list Z)) (k: Z) (i: Z) (total: Z) (PreH1 : (i > n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= k)) (PreH10 : (k <= total)) (PreH11 : (k = (Zlength (out_l)))) (PreH12 : (out_l = (string_sequence_prefix_z (i)))) (PreH13 : (len >= 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (total + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition string_sequence_entail_wit_1 := 
(
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) ,
  TT && emp 
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (((sequence_len_z (n_pre)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre_z n_pre ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (1 = (Zlength ((string_sequence_prefix_z (1))))) ” 
  &&  “ (1 <= (sequence_len_z (n_pre))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (0 = 0) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) ,
  TT && emp 
|--
  “ (1 <= (sequence_len_z (n_pre))) ” 
  &&  “ (1 = (Zlength ((string_sequence_prefix_z (1))))) ”
  &&  emp
).

Definition string_sequence_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) ,
  TT && emp 
|--
  “ (1 <= (sequence_len_z (n_pre))) ”
.

Definition string_sequence_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) ,
  TT && emp 
|--
  “ (1 = (Zlength ((string_sequence_prefix_z (1))))) ”
.

Definition string_sequence_entail_wit_2 := 
(
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_z (i)))))) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH8 : (problem_15_pre_z n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH12 : (total <= (sequence_len_z (n_pre)))) (PreH13 : (k = 0)) (PreH14 : (len >= 0)) (PreH15 : (out = 0)) ,
  TT && emp 
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (((sequence_len_z (n_pre)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre_z n_pre ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (((total + 1 ) + retval ) = (Zlength ((string_sequence_prefix_z ((i + 1 )))))) ” 
  &&  “ (((total + 1 ) + retval ) <= (sequence_len_z (n_pre))) ” 
  &&  “ (k = 0) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (out = 0) ”
  &&  emp
) \/
(
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_z (i)))))) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH8 : (problem_15_pre_z n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH12 : (total <= (sequence_len_z (n_pre)))) (PreH13 : (k = 0)) (PreH14 : (len >= 0)) (PreH15 : (out = 0)) ,
  TT && emp 
|--
  “ (((total + 1 ) + retval ) <= (sequence_len_z (n_pre))) ” 
  &&  “ (((total + 1 ) + retval ) = (Zlength ((string_sequence_prefix_z ((i + 1 )))))) ”
  &&  emp
).

Definition string_sequence_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_z (i)))))) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH8 : (problem_15_pre_z n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH12 : (total <= (sequence_len_z (n_pre)))) (PreH13 : (k = 0)) (PreH14 : (len >= 0)) (PreH15 : (out = 0)) ,
  TT && emp 
|--
  “ (((total + 1 ) + retval ) <= (sequence_len_z (n_pre))) ”
.

Definition string_sequence_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_z (i)))))) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH8 : (problem_15_pre_z n_pre )) (PreH9 : (1 <= i)) (PreH10 : (i <= (n_pre + 1 ))) (PreH11 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH12 : (total <= (sequence_len_z (n_pre)))) (PreH13 : (k = 0)) (PreH14 : (len >= 0)) (PreH15 : (out = 0)) ,
  TT && emp 
|--
  “ (((total + 1 ) + retval ) = (Zlength ((string_sequence_prefix_z ((i + 1 )))))) ”
.

Definition string_sequence_entail_wit_3 := 
(
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i > n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH6 : (problem_15_pre_z n_pre )) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH10 : (total <= (sequence_len_z (n_pre)))) (PreH11 : (k = 0)) (PreH12 : (len >= 0)) (PreH13 : (out = 0)) ,
  (CharArray.undef_full retval (total + 1 ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (((sequence_len_z (n_pre)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre_z n_pre ) ” 
  &&  “ (i = (n_pre + 1 )) ” 
  &&  “ (total = (sequence_len_z (n_pre))) ” 
  &&  “ (0 <= total) ” 
  &&  “ (k = 0) ” 
  &&  “ (len >= 0) ” 
  &&  “ (retval <> 0) ”
  &&  (CharArray.undef_full retval (total + 1 ) )
) \/
(
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i > n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH6 : (problem_15_pre_z n_pre )) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH10 : (total <= (sequence_len_z (n_pre)))) (PreH11 : (k = 0)) (PreH12 : (len >= 0)) (PreH13 : (out = 0)) ,
  (CharArray.undef_full retval (total + 1 ) )
|--
  “ (0 <= total) ” 
  &&  “ (total = (sequence_len_z (n_pre))) ”
  &&  (CharArray.undef_full retval (total + 1 ) )
).

Definition string_sequence_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i > n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH6 : (problem_15_pre_z n_pre )) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH10 : (total <= (sequence_len_z (n_pre)))) (PreH11 : (k = 0)) (PreH12 : (len >= 0)) (PreH13 : (out = 0)) ,
  (CharArray.undef_full retval (total + 1 ) )
|--
  “ (0 <= total) ”
.

Definition string_sequence_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i > n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH6 : (problem_15_pre_z n_pre )) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH10 : (total <= (sequence_len_z (n_pre)))) (PreH11 : (k = 0)) (PreH12 : (len >= 0)) (PreH13 : (out = 0)) ,
  (CharArray.undef_full retval (total + 1 ) )
|--
  “ (total = (sequence_len_z (n_pre))) ”
.

Definition string_sequence_entail_wit_3_split_goal_spatial := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i > n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH6 : (problem_15_pre_z n_pre )) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH10 : (total <= (sequence_len_z (n_pre)))) (PreH11 : (k = 0)) (PreH12 : (len >= 0)) (PreH13 : (out = 0)) ,
  (CharArray.undef_full retval (total + 1 ) )
|--
  (CharArray.undef_full retval (total + 1 ) )
.

Definition string_sequence_entail_wit_4 := 
(
forall (n_pre: Z) (i: Z) (total: Z) (k: Z) (len: Z) (out: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (i = (n_pre + 1 ))) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (0 <= total)) (PreH8 : (k = 0)) (PreH9 : (len >= 0)) (PreH10 : (out <> 0)) ,
  (CharArray.undef_seg out (0 + 1 ) (total + 1 ) )
  **  (((out + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (((sequence_len_z (n_pre)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre_z n_pre ) ” 
  &&  “ (total = (sequence_len_z (n_pre))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= total) ” 
  &&  “ (1 = (Zlength (out_l))) ” 
  &&  “ (out_l = (string_sequence_prefix_z (1))) ” 
  &&  “ (len >= 0) ”
  &&  (CharArray.full out 1 out_l )
  **  (CharArray.undef_seg out 1 (total + 1 ) )
) \/
(
forall (n_pre: Z) (i: Z) (total: Z) (k: Z) (len: Z) (out: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (i = (n_pre + 1 ))) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (0 <= total)) (PreH8 : (k = 0)) (PreH9 : (len >= 0)) (PreH10 : (out <> 0)) ,
  (((out + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  “ (1 = (Zlength ((string_sequence_prefix_z (1))))) ” 
  &&  “ (1 <= total) ”
  &&  (CharArray.full out 1 (string_sequence_prefix_z (1)) )
).

Definition string_sequence_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (i: Z) (total: Z) (k: Z) (len: Z) (out: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (i = (n_pre + 1 ))) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (0 <= total)) (PreH8 : (k = 0)) (PreH9 : (len >= 0)) (PreH10 : (out <> 0)) ,
  (((out + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  “ (1 = (Zlength ((string_sequence_prefix_z (1))))) ”
.

Definition string_sequence_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (i: Z) (total: Z) (k: Z) (len: Z) (out: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (i = (n_pre + 1 ))) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (0 <= total)) (PreH8 : (k = 0)) (PreH9 : (len >= 0)) (PreH10 : (out <> 0)) ,
  (((out + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  “ (1 <= total) ”
.

Definition string_sequence_entail_wit_4_split_goal_spatial := 
forall (n_pre: Z) (i: Z) (total: Z) (k: Z) (len: Z) (out: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (i = (n_pre + 1 ))) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (0 <= total)) (PreH8 : (k = 0)) (PreH9 : (len >= 0)) (PreH10 : (out <> 0)) ,
  (((out + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  (CharArray.full out 1 (string_sequence_prefix_z (1)) )
.

Definition string_sequence_entail_wit_5 := 
(
forall (n_pre: Z) (out: Z) (len: Z) (out_l_2: (@list Z)) (k: Z) (i: Z) (total: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_z (i)))))) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (0 <= (k + 1 ))) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH9 : (problem_15_pre_z n_pre )) (PreH10 : (total = (sequence_len_z (n_pre)))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= k)) (PreH14 : (k <= total)) (PreH15 : (k = (Zlength (out_l_2)))) (PreH16 : (out_l_2 = (string_sequence_prefix_z (i)))) (PreH17 : (len >= 0)) ,
  (CharArray.full out (k + 1 ) (app (out_l_2) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (total + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (((sequence_len_z (n_pre)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre_z n_pre ) ” 
  &&  “ (total = (sequence_len_z (n_pre))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (retval = (Zlength ((decimal_digits_z (i))))) ” 
  &&  “ (1 <= retval) ” 
  &&  “ (retval < INT_MAX) ” 
  &&  “ ((k + 1 ) = ((Zlength (out_l)) + 1 )) ” 
  &&  “ (out_l = (string_sequence_prefix_z (i))) ”
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_full (out + ((k + 1 ) * sizeof(CHAR) ) ) retval )
  **  (CharArray.undef_seg out ((k + 1 ) + retval ) (total + 1 ) )
) \/
(
forall (n_pre: Z) (out: Z) (len: Z) (out_l_2: (@list Z)) (k: Z) (i: Z) (total: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_z (i)))))) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (0 <= (k + 1 ))) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH9 : (problem_15_pre_z n_pre )) (PreH10 : (total = (sequence_len_z (n_pre)))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= k)) (PreH14 : (k <= total)) (PreH15 : (k = (Zlength (out_l_2)))) (PreH16 : (out_l_2 = (string_sequence_prefix_z (i)))) (PreH17 : (len >= 0)) ,
  (CharArray.undef_seg out (k + 1 ) (total + 1 ) )
|--
  (CharArray.undef_full (out + ((k + 1 ) * sizeof(CHAR) ) ) retval )
  **  (CharArray.undef_seg out ((k + 1 ) + retval ) (total + 1 ) )
).

Definition string_sequence_entail_wit_5_split_goal_spatial := 
forall (n_pre: Z) (out: Z) (len: Z) (out_l_2: (@list Z)) (k: Z) (i: Z) (total: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_z (i)))))) (PreH2 : (1 <= retval)) (PreH3 : (retval < INT_MAX)) (PreH4 : (0 <= (k + 1 ))) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH9 : (problem_15_pre_z n_pre )) (PreH10 : (total = (sequence_len_z (n_pre)))) (PreH11 : (1 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= k)) (PreH14 : (k <= total)) (PreH15 : (k = (Zlength (out_l_2)))) (PreH16 : (out_l_2 = (string_sequence_prefix_z (i)))) (PreH17 : (len >= 0)) ,
  (CharArray.undef_seg out (k + 1 ) (total + 1 ) )
|--
  (CharArray.undef_full (out + ((k + 1 ) * sizeof(CHAR) ) ) retval )
  **  (CharArray.undef_seg out ((k + 1 ) + retval ) (total + 1 ) )
.

Definition string_sequence_entail_wit_6 := 
(
forall (n_pre: Z) (out_l_2: (@list Z)) (total: Z) (i: Z) (len: Z) (k: Z) (out: Z) (PreH1 : (0 <= k)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (len = (Zlength ((decimal_digits_z (i)))))) (PreH10 : (1 <= len)) (PreH11 : (len < INT_MAX)) (PreH12 : (k = ((Zlength (out_l_2)) + 1 ))) (PreH13 : (out_l_2 = (string_sequence_prefix_z (i)))) ,
  (CharArray.full (out + (k * sizeof(CHAR) ) ) len (decimal_digits_z (i)) )
  **  (CharArray.full out k (app (out_l_2) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + len ) (total + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (((sequence_len_z (n_pre)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre_z n_pre ) ” 
  &&  “ (total = (sequence_len_z (n_pre))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((k + len ) = (Zlength (out_l))) ” 
  &&  “ (out_l = (string_sequence_prefix_z ((i + 1 )))) ” 
  &&  “ (len >= 0) ”
  &&  (CharArray.full out (k + len ) out_l )
  **  (CharArray.undef_seg out (k + len ) (total + 1 ) )
) \/
(
forall (n_pre: Z) (out_l_2: (@list Z)) (total: Z) (i: Z) (len: Z) (k: Z) (out: Z) (PreH1 : (0 <= len)) (PreH2 : (0 <= k)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH6 : (problem_15_pre_z n_pre )) (PreH7 : (total = (sequence_len_z (n_pre)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (len = (Zlength ((decimal_digits_z (i)))))) (PreH11 : (1 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (k = ((Zlength (out_l_2)) + 1 ))) (PreH14 : (out_l_2 = (string_sequence_prefix_z (i)))) ,
  (CharArray.full (out + (k * sizeof(CHAR) ) ) len (decimal_digits_z (i)) )
  **  (CharArray.full out k (app (out_l_2) ((cons (32) ((@nil Z))))) )
|--
  “ ((k + len ) = (Zlength ((string_sequence_prefix_z ((i + 1 )))))) ”
  &&  (CharArray.full out (k + len ) (string_sequence_prefix_z ((i + 1 ))) )
).

Definition string_sequence_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (out_l_2: (@list Z)) (total: Z) (i: Z) (len: Z) (k: Z) (out: Z) (PreH1 : (0 <= len)) (PreH2 : (0 <= k)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH6 : (problem_15_pre_z n_pre )) (PreH7 : (total = (sequence_len_z (n_pre)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (len = (Zlength ((decimal_digits_z (i)))))) (PreH11 : (1 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (k = ((Zlength (out_l_2)) + 1 ))) (PreH14 : (out_l_2 = (string_sequence_prefix_z (i)))) ,
  (CharArray.full (out + (k * sizeof(CHAR) ) ) len (decimal_digits_z (i)) )
  **  (CharArray.full out k (app (out_l_2) ((cons (32) ((@nil Z))))) )
|--
  “ ((k + len ) = (Zlength ((string_sequence_prefix_z ((i + 1 )))))) ”
.

Definition string_sequence_entail_wit_6_split_goal_spatial := 
forall (n_pre: Z) (out_l_2: (@list Z)) (total: Z) (i: Z) (len: Z) (k: Z) (out: Z) (PreH1 : (0 <= len)) (PreH2 : (0 <= k)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH6 : (problem_15_pre_z n_pre )) (PreH7 : (total = (sequence_len_z (n_pre)))) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (len = (Zlength ((decimal_digits_z (i)))))) (PreH11 : (1 <= len)) (PreH12 : (len < INT_MAX)) (PreH13 : (k = ((Zlength (out_l_2)) + 1 ))) (PreH14 : (out_l_2 = (string_sequence_prefix_z (i)))) ,
  (CharArray.full (out + (k * sizeof(CHAR) ) ) len (decimal_digits_z (i)) )
  **  (CharArray.full out k (app (out_l_2) ((cons (32) ((@nil Z))))) )
|--
  (CharArray.full out (k + len ) (string_sequence_prefix_z ((i + 1 ))) )
.

Definition string_sequence_entail_wit_7 := 
(
forall (n_pre: Z) (out_l_2: (@list Z)) (total: Z) (i: Z) (k: Z) (len: Z) (out: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (total = (sequence_len_z (n_pre)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : (k = (Zlength (out_l_2)))) (PreH9 : (out_l_2 = (string_sequence_prefix_z (i)))) (PreH10 : (len >= 0)) ,
  (CharArray.full out k out_l_2 )
  **  (CharArray.undef_seg out k (total + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (((sequence_len_z (n_pre)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre_z n_pre ) ” 
  &&  “ (total = (sequence_len_z (n_pre))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= total) ” 
  &&  “ (k = (Zlength (out_l))) ” 
  &&  “ (out_l = (string_sequence_prefix_z (i))) ” 
  &&  “ (len >= 0) ”
  &&  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (total + 1 ) )
) \/
(
forall (n_pre: Z) (out_l_2: (@list Z)) (total: Z) (i: Z) (k: Z) (len: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (total = (sequence_len_z (n_pre)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : (k = (Zlength (out_l_2)))) (PreH9 : (out_l_2 = (string_sequence_prefix_z (i)))) (PreH10 : (len >= 0)) ,
  TT && emp 
|--
  “ (k <= total) ” 
  &&  “ (0 <= k) ”
  &&  emp
).

Definition string_sequence_entail_wit_7_split_goal_1 := 
forall (n_pre: Z) (out_l_2: (@list Z)) (total: Z) (i: Z) (k: Z) (len: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (total = (sequence_len_z (n_pre)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : (k = (Zlength (out_l_2)))) (PreH9 : (out_l_2 = (string_sequence_prefix_z (i)))) (PreH10 : (len >= 0)) ,
  TT && emp 
|--
  “ (k <= total) ”
.

Definition string_sequence_entail_wit_7_split_goal_2 := 
forall (n_pre: Z) (out_l_2: (@list Z)) (total: Z) (i: Z) (k: Z) (len: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (total = (sequence_len_z (n_pre)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : (k = (Zlength (out_l_2)))) (PreH9 : (out_l_2 = (string_sequence_prefix_z (i)))) (PreH10 : (len >= 0)) ,
  TT && emp 
|--
  “ (0 <= k) ”
.

Definition string_sequence_return_wit_1 := 
(
forall (n_pre: Z) (out: Z) (len_2: Z) (out_l_2: (@list Z)) (k: Z) (i: Z) (total: Z) (PreH1 : (i > n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= k)) (PreH10 : (k <= total)) (PreH11 : (k = (Zlength (out_l_2)))) (PreH12 : (out_l_2 = (string_sequence_prefix_z (i)))) (PreH13 : (len_2 >= 0)) ,
  (CharArray.full out (k + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (total + 1 ) )
|--
  EX (out_l: (@list Z))  (len: Z) ,
  “ (len = (Zlength (out_l))) ” 
  &&  “ (len = (sequence_len_z (n_pre))) ” 
  &&  “ (problem_15_spec_z n_pre out_l ) ”
  &&  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (out: Z) (len_2: Z) (out_l_2: (@list Z)) (k: Z) (i: Z) (total: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (i > n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH6 : (problem_15_pre_z n_pre )) (PreH7 : (total = (sequence_len_z (n_pre)))) (PreH8 : (1 <= i)) (PreH9 : (i <= (n_pre + 1 ))) (PreH10 : (0 <= k)) (PreH11 : (k <= total)) (PreH12 : (k = (Zlength (out_l_2)))) (PreH13 : (out_l_2 = (string_sequence_prefix_z (i)))) (PreH14 : (len_2 >= 0)) ,
  (CharArray.full out (k + 1 ) (app (out_l_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (total + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (out_l)) = (sequence_len_z (n_pre))) ” 
  &&  “ (problem_15_spec_z n_pre out_l ) ”
  &&  (CharArray.full out ((Zlength (out_l)) + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
).

Definition string_sequence_partial_solve_wit_1_pure := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH9 : (total <= (sequence_len_z (n_pre)))) (PreH10 : (k = 0)) (PreH11 : (len >= 0)) (PreH12 : (out = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (0 <= i) ” 
  &&  “ (i < INT_MAX) ”
.

Definition string_sequence_partial_solve_wit_1_aux := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH9 : (total <= (sequence_len_z (n_pre)))) (PreH10 : (k = 0)) (PreH11 : (len >= 0)) (PreH12 : (out = 0)) ,
  TT && emp 
|--
  “ (0 <= i) ” 
  &&  “ (i < INT_MAX) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (((sequence_len_z (n_pre)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre_z n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (total = (Zlength ((string_sequence_prefix_z (i))))) ” 
  &&  “ (total <= (sequence_len_z (n_pre))) ” 
  &&  “ (k = 0) ” 
  &&  “ (len >= 0) ” 
  &&  “ (out = 0) ”
  &&  emp
.

Definition string_sequence_partial_solve_wit_1 := string_sequence_partial_solve_wit_1_pure -> string_sequence_partial_solve_wit_1_aux.

Definition string_sequence_partial_solve_wit_2_pure := 
(
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH9 : (total <= (sequence_len_z (n_pre)))) (PreH10 : (k = 0)) (PreH11 : (len >= 0)) (PreH12 : (out = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((total + 1 ) > 0) ”
) \/
(
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (PreH1 : (len <= INT_MAX)) (PreH2 : (k <= INT_MAX)) (PreH3 : (total <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (len >= INT_MIN)) (PreH7 : (k >= INT_MIN)) (PreH8 : (total >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i > n_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH15 : (problem_15_pre_z n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= (n_pre + 1 ))) (PreH18 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH19 : (total <= (sequence_len_z (n_pre)))) (PreH20 : (k = 0)) (PreH21 : (len >= 0)) (PreH22 : (out = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((total + 1 ) > 0) ”
).

Definition string_sequence_partial_solve_wit_2_pure_split_goal_1 := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (PreH1 : (len <= INT_MAX)) (PreH2 : (k <= INT_MAX)) (PreH3 : (total <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (len >= INT_MIN)) (PreH7 : (k >= INT_MIN)) (PreH8 : (total >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i > n_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre < INT_MAX)) (PreH14 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH15 : (problem_15_pre_z n_pre )) (PreH16 : (1 <= i)) (PreH17 : (i <= (n_pre + 1 ))) (PreH18 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH19 : (total <= (sequence_len_z (n_pre)))) (PreH20 : (k = 0)) (PreH21 : (len >= 0)) (PreH22 : (out = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((total + 1 ) > 0) ”
.

Definition string_sequence_partial_solve_wit_2_aux := 
forall (n_pre: Z) (out: Z) (len: Z) (k: Z) (total: Z) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : (total = (Zlength ((string_sequence_prefix_z (i)))))) (PreH9 : (total <= (sequence_len_z (n_pre)))) (PreH10 : (k = 0)) (PreH11 : (len >= 0)) (PreH12 : (out = 0)) ,
  TT && emp 
|--
  “ ((total + 1 ) > 0) ” 
  &&  “ (i > n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (((sequence_len_z (n_pre)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre_z n_pre ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (total = (Zlength ((string_sequence_prefix_z (i))))) ” 
  &&  “ (total <= (sequence_len_z (n_pre))) ” 
  &&  “ (k = 0) ” 
  &&  “ (len >= 0) ” 
  &&  “ (out = 0) ”
  &&  emp
.

Definition string_sequence_partial_solve_wit_2 := string_sequence_partial_solve_wit_2_pure -> string_sequence_partial_solve_wit_2_aux.

Definition string_sequence_partial_solve_wit_3 := 
forall (n_pre: Z) (i: Z) (total: Z) (k: Z) (len: Z) (out: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (i = (n_pre + 1 ))) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (0 <= total)) (PreH8 : (k = 0)) (PreH9 : (len >= 0)) (PreH10 : (out <> 0)) ,
  (CharArray.undef_full out (total + 1 ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (((sequence_len_z (n_pre)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre_z n_pre ) ” 
  &&  “ (i = (n_pre + 1 )) ” 
  &&  “ (total = (sequence_len_z (n_pre))) ” 
  &&  “ (0 <= total) ” 
  &&  “ (k = 0) ” 
  &&  “ (len >= 0) ” 
  &&  “ (out <> 0) ”
  &&  (((out + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out 0 0 (total + 1 ) )
.

Definition string_sequence_partial_solve_wit_4 := 
forall (n_pre: Z) (out: Z) (len: Z) (out_l: (@list Z)) (k: Z) (i: Z) (total: Z) (PreH1 : (i <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= k)) (PreH10 : (k <= total)) (PreH11 : (k = (Zlength (out_l)))) (PreH12 : (out_l = (string_sequence_prefix_z (i)))) (PreH13 : (len >= 0)) ,
  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (total + 1 ) )
|--
  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (((sequence_len_z (n_pre)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre_z n_pre ) ” 
  &&  “ (total = (sequence_len_z (n_pre))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= total) ” 
  &&  “ (k = (Zlength (out_l))) ” 
  &&  “ (out_l = (string_sequence_prefix_z (i))) ” 
  &&  “ (len >= 0) ”
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k (total + 1 ) )
  **  (CharArray.full out k out_l )
.

Definition string_sequence_partial_solve_wit_5_pure := 
forall (n_pre: Z) (out: Z) (len: Z) (out_l: (@list Z)) (k: Z) (i: Z) (total: Z) (PreH1 : (i <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= k)) (PreH10 : (k <= total)) (PreH11 : (k = (Zlength (out_l)))) (PreH12 : (out_l = (string_sequence_prefix_z (i)))) (PreH13 : (len >= 0)) ,
  (CharArray.full out (k + 1 ) (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (total + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (0 <= i) ” 
  &&  “ (i < INT_MAX) ”
.

Definition string_sequence_partial_solve_wit_5_aux := 
forall (n_pre: Z) (out: Z) (len: Z) (out_l: (@list Z)) (k: Z) (i: Z) (total: Z) (PreH1 : (i <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= k)) (PreH10 : (k <= total)) (PreH11 : (k = (Zlength (out_l)))) (PreH12 : (out_l = (string_sequence_prefix_z (i)))) (PreH13 : (len >= 0)) ,
  (CharArray.full out (k + 1 ) (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (total + 1 ) )
|--
  “ (0 <= i) ” 
  &&  “ (i < INT_MAX) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (((sequence_len_z (n_pre)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre_z n_pre ) ” 
  &&  “ (total = (sequence_len_z (n_pre))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= total) ” 
  &&  “ (k = (Zlength (out_l))) ” 
  &&  “ (out_l = (string_sequence_prefix_z (i))) ” 
  &&  “ (len >= 0) ”
  &&  (CharArray.full out (k + 1 ) (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + 1 ) (total + 1 ) )
.

Definition string_sequence_partial_solve_wit_5 := string_sequence_partial_solve_wit_5_pure -> string_sequence_partial_solve_wit_5_aux.

Definition string_sequence_partial_solve_wit_6_pure := 
forall (n_pre: Z) (out_l: (@list Z)) (total: Z) (i: Z) (len: Z) (k: Z) (out: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (total = (sequence_len_z (n_pre)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (len = (Zlength ((decimal_digits_z (i)))))) (PreH9 : (1 <= len)) (PreH10 : (len < INT_MAX)) (PreH11 : (k = ((Zlength (out_l)) + 1 ))) (PreH12 : (out_l = (string_sequence_prefix_z (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_full (out + (k * sizeof(CHAR) ) ) len )
  **  (CharArray.undef_seg out (k + len ) (total + 1 ) )
|--
  “ (0 <= i) ” 
  &&  “ (i < INT_MAX) ” 
  &&  “ (len = (Zlength ((decimal_digits_z (i))))) ” 
  &&  “ (1 <= len) ” 
  &&  “ (len < INT_MAX) ”
.

Definition string_sequence_partial_solve_wit_6_aux := 
forall (n_pre: Z) (out_l: (@list Z)) (total: Z) (i: Z) (len: Z) (k: Z) (out: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH4 : (problem_15_pre_z n_pre )) (PreH5 : (total = (sequence_len_z (n_pre)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (len = (Zlength ((decimal_digits_z (i)))))) (PreH9 : (1 <= len)) (PreH10 : (len < INT_MAX)) (PreH11 : (k = ((Zlength (out_l)) + 1 ))) (PreH12 : (out_l = (string_sequence_prefix_z (i)))) ,
  (CharArray.full out k (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_full (out + (k * sizeof(CHAR) ) ) len )
  **  (CharArray.undef_seg out (k + len ) (total + 1 ) )
|--
  “ (0 <= i) ” 
  &&  “ (i < INT_MAX) ” 
  &&  “ (len = (Zlength ((decimal_digits_z (i))))) ” 
  &&  “ (1 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (((sequence_len_z (n_pre)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre_z n_pre ) ” 
  &&  “ (total = (sequence_len_z (n_pre))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (len = (Zlength ((decimal_digits_z (i))))) ” 
  &&  “ (1 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (k = ((Zlength (out_l)) + 1 )) ” 
  &&  “ (out_l = (string_sequence_prefix_z (i))) ”
  &&  (CharArray.undef_full (out + (k * sizeof(CHAR) ) ) len )
  **  (CharArray.full out k (app (out_l) ((cons (32) ((@nil Z))))) )
  **  (CharArray.undef_seg out (k + len ) (total + 1 ) )
.

Definition string_sequence_partial_solve_wit_6 := string_sequence_partial_solve_wit_6_pure -> string_sequence_partial_solve_wit_6_aux.

Definition string_sequence_partial_solve_wit_7 := 
forall (n_pre: Z) (out: Z) (len: Z) (out_l: (@list Z)) (k: Z) (i: Z) (total: Z) (PreH1 : (i > n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (((sequence_len_z (n_pre)) + 1 ) < INT_MAX)) (PreH5 : (problem_15_pre_z n_pre )) (PreH6 : (total = (sequence_len_z (n_pre)))) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= k)) (PreH10 : (k <= total)) (PreH11 : (k = (Zlength (out_l)))) (PreH12 : (out_l = (string_sequence_prefix_z (i)))) (PreH13 : (len >= 0)) ,
  (CharArray.full out k out_l )
  **  (CharArray.undef_seg out k (total + 1 ) )
|--
  “ (i > n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (((sequence_len_z (n_pre)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre_z n_pre ) ” 
  &&  “ (total = (sequence_len_z (n_pre))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= total) ” 
  &&  “ (k = (Zlength (out_l))) ” 
  &&  “ (out_l = (string_sequence_prefix_z (i))) ” 
  &&  “ (len >= 0) ”
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k (total + 1 ) )
  **  (CharArray.full out k out_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_decimal_len_safety_wit_1 : decimal_len_safety_wit_1.
Axiom proof_of_decimal_len_safety_wit_2 : decimal_len_safety_wit_2.
Axiom proof_of_decimal_len_safety_wit_3 : decimal_len_safety_wit_3.
Axiom proof_of_decimal_len_safety_wit_4 : decimal_len_safety_wit_4.
Axiom proof_of_decimal_len_safety_wit_5 : decimal_len_safety_wit_5.
Axiom proof_of_decimal_len_safety_wit_6 : decimal_len_safety_wit_6.
Axiom proof_of_decimal_len_safety_wit_7 : decimal_len_safety_wit_7.
Axiom proof_of_decimal_len_safety_wit_8 : decimal_len_safety_wit_8.
Axiom proof_of_decimal_len_entail_wit_1 : decimal_len_entail_wit_1.
Axiom proof_of_decimal_len_entail_wit_2 : decimal_len_entail_wit_2.
Axiom proof_of_decimal_len_return_wit_1 : decimal_len_return_wit_1.
Axiom proof_of_decimal_len_return_wit_2 : decimal_len_return_wit_2.
Axiom proof_of_write_decimal_safety_wit_1 : write_decimal_safety_wit_1.
Axiom proof_of_write_decimal_safety_wit_2 : write_decimal_safety_wit_2.
Axiom proof_of_write_decimal_safety_wit_3 : write_decimal_safety_wit_3.
Axiom proof_of_write_decimal_safety_wit_4 : write_decimal_safety_wit_4.
Axiom proof_of_write_decimal_safety_wit_5 : write_decimal_safety_wit_5.
Axiom proof_of_write_decimal_safety_wit_6 : write_decimal_safety_wit_6.
Axiom proof_of_write_decimal_safety_wit_7 : write_decimal_safety_wit_7.
Axiom proof_of_write_decimal_safety_wit_8 : write_decimal_safety_wit_8.
Axiom proof_of_write_decimal_safety_wit_9 : write_decimal_safety_wit_9.
Axiom proof_of_write_decimal_safety_wit_10 : write_decimal_safety_wit_10.
Axiom proof_of_write_decimal_safety_wit_11 : write_decimal_safety_wit_11.
Axiom proof_of_write_decimal_safety_wit_12 : write_decimal_safety_wit_12.
Axiom proof_of_write_decimal_safety_wit_13 : write_decimal_safety_wit_13.
Axiom proof_of_write_decimal_safety_wit_14 : write_decimal_safety_wit_14.
Axiom proof_of_write_decimal_safety_wit_15 : write_decimal_safety_wit_15.
Axiom proof_of_write_decimal_safety_wit_16 : write_decimal_safety_wit_16.
Axiom proof_of_write_decimal_entail_wit_1 : write_decimal_entail_wit_1.
Axiom proof_of_write_decimal_entail_wit_2 : write_decimal_entail_wit_2.
Axiom proof_of_write_decimal_entail_wit_3 : write_decimal_entail_wit_3.
Axiom proof_of_write_decimal_entail_wit_4 : write_decimal_entail_wit_4.
Axiom proof_of_write_decimal_entail_wit_5 : write_decimal_entail_wit_5.
Axiom proof_of_write_decimal_entail_wit_6 : write_decimal_entail_wit_6.
Axiom proof_of_write_decimal_return_wit_1 : write_decimal_return_wit_1.
Axiom proof_of_write_decimal_return_wit_2 : write_decimal_return_wit_2.
Axiom proof_of_write_decimal_partial_solve_wit_1 : write_decimal_partial_solve_wit_1.
Axiom proof_of_write_decimal_partial_solve_wit_2 : write_decimal_partial_solve_wit_2.
Axiom proof_of_write_decimal_partial_solve_wit_3 : write_decimal_partial_solve_wit_3.
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
Axiom proof_of_string_sequence_entail_wit_1 : string_sequence_entail_wit_1.
Axiom proof_of_string_sequence_entail_wit_2 : string_sequence_entail_wit_2.
Axiom proof_of_string_sequence_entail_wit_3 : string_sequence_entail_wit_3.
Axiom proof_of_string_sequence_entail_wit_4 : string_sequence_entail_wit_4.
Axiom proof_of_string_sequence_entail_wit_5 : string_sequence_entail_wit_5.
Axiom proof_of_string_sequence_entail_wit_6 : string_sequence_entail_wit_6.
Axiom proof_of_string_sequence_entail_wit_7 : string_sequence_entail_wit_7.
Axiom proof_of_string_sequence_return_wit_1 : string_sequence_return_wit_1.
Axiom proof_of_string_sequence_partial_solve_wit_1_pure : string_sequence_partial_solve_wit_1_pure.
Axiom proof_of_string_sequence_partial_solve_wit_1 : string_sequence_partial_solve_wit_1.
Axiom proof_of_string_sequence_partial_solve_wit_2_pure : string_sequence_partial_solve_wit_2_pure.
Axiom proof_of_string_sequence_partial_solve_wit_2 : string_sequence_partial_solve_wit_2.
Axiom proof_of_string_sequence_partial_solve_wit_3 : string_sequence_partial_solve_wit_3.
Axiom proof_of_string_sequence_partial_solve_wit_4 : string_sequence_partial_solve_wit_4.
Axiom proof_of_string_sequence_partial_solve_wit_5_pure : string_sequence_partial_solve_wit_5_pure.
Axiom proof_of_string_sequence_partial_solve_wit_5 : string_sequence_partial_solve_wit_5.
Axiom proof_of_string_sequence_partial_solve_wit_6_pure : string_sequence_partial_solve_wit_6_pure.
Axiom proof_of_string_sequence_partial_solve_wit_6 : string_sequence_partial_solve_wit_6.
Axiom proof_of_string_sequence_partial_solve_wit_7 : string_sequence_partial_solve_wit_7.

End VC_Correct.
