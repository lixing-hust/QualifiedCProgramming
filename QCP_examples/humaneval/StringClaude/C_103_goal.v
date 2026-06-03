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
Require Import coins_103.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function rounded_avg -----*)

Definition rounded_avg_safety_wit_1 := 
forall (m_pre: Z) (n_pre: Z) ,
  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  ((( &( "out_neg" ) )) # Ptr  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition rounded_avg_safety_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  (CharArray.undef_full retval 3 )
  **  ((( &( "out_neg" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition rounded_avg_safety_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  (CharArray.undef_full retval 3 )
  **  ((( &( "out_neg" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (45 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 45) |]
.

Definition rounded_avg_safety_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) 3 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
  **  ((( &( "out_neg" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition rounded_avg_safety_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) 3 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
  **  ((( &( "out_neg" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (49 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 49) |]
.

Definition rounded_avg_safety_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  (CharArray.undef_seg retval (1 + 1 ) 3 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 49)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
  **  ((( &( "out_neg" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition rounded_avg_safety_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  (CharArray.undef_seg retval (1 + 1 ) 3 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 49)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
  **  ((( &( "out_neg" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition rounded_avg_safety_wit_8 := 
forall (m_pre: Z) (n_pre: Z) ,
  [| (n_pre <= m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (((n_pre + m_pre ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition rounded_avg_safety_wit_9 := 
forall (m_pre: Z) (n_pre: Z) ,
  [| (n_pre <= m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((n_pre + m_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre + m_pre )) |]
.

Definition rounded_avg_safety_wit_10 := 
forall (m_pre: Z) (n_pre: Z) ,
  [| (n_pre <= m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition rounded_avg_safety_wit_11 := 
forall (m_pre: Z) (n_pre: Z) ,
  [| (n_pre <= m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  ((( &( "digits" ) )) # Int  |->_)
  **  ((( &( "orig" ) )) # Int  |-> ((n_pre + m_pre ) ÷ 2 ))
  **  ((( &( "num" ) )) # Int  |-> ((n_pre + m_pre ) ÷ 2 ))
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition rounded_avg_safety_wit_12 := 
forall (m_pre: Z) (n_pre: Z) ,
  [| (n_pre <= m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  ((( &( "total" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |-> ((n_pre + m_pre ) ÷ 2 ))
  **  ((( &( "digits" ) )) # Int  |-> 0)
  **  ((( &( "orig" ) )) # Int  |-> ((n_pre + m_pre ) ÷ 2 ))
  **  ((( &( "num" ) )) # Int  |-> ((n_pre + m_pre ) ÷ 2 ))
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition rounded_avg_safety_wit_13 := 
forall (m_pre: Z) (n_pre: Z) ,
  [| (n_pre <= m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "total" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> ((n_pre + m_pre ) ÷ 2 ))
  **  ((( &( "digits" ) )) # Int  |-> 0)
  **  ((( &( "orig" ) )) # Int  |-> ((n_pre + m_pre ) ÷ 2 ))
  **  ((( &( "num" ) )) # Int  |-> ((n_pre + m_pre ) ÷ 2 ))
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition rounded_avg_safety_wit_14 := 
forall (m_pre: Z) (n_pre: Z) ,
  [| (n_pre <= m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "total" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> ((n_pre + m_pre ) ÷ 2 ))
  **  ((( &( "digits" ) )) # Int  |-> 0)
  **  ((( &( "orig" ) )) # Int  |-> ((n_pre + m_pre ) ÷ 2 ))
  **  ((( &( "num" ) )) # Int  |-> ((n_pre + m_pre ) ÷ 2 ))
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition rounded_avg_safety_wit_15 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (total: Z) (digits: Z) (t: Z) (orig: Z) (num: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t digits ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition rounded_avg_safety_wit_16 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (total: Z) (digits: Z) (t: Z) (orig: Z) (num: Z) ,
  [| (t > 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t digits ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((digits + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (digits + 1 )) |]
.

Definition rounded_avg_safety_wit_17 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (total: Z) (digits: Z) (t: Z) (orig: Z) (num: Z) ,
  [| (t > 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t digits ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition rounded_avg_safety_wit_18 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (total: Z) (digits: Z) (t: Z) (orig: Z) (num: Z) ,
  [| (t > 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t digits ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> (digits + 1 ))
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((t <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition rounded_avg_safety_wit_19 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (total: Z) (digits: Z) (t: Z) (orig: Z) (num: Z) ,
  [| (t > 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t digits ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> (digits + 1 ))
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition rounded_avg_safety_wit_20 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (total: Z) (digits: Z) (t: Z) (orig: Z) (num: Z) ,
  [| (t <= 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t digits ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "total" ) )) # Int  |-> digits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((digits + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (digits + 1 )) |]
.

Definition rounded_avg_safety_wit_21 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (total: Z) (digits: Z) (t: Z) (orig: Z) (num: Z) ,
  [| (t <= 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t digits ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "total" ) )) # Int  |-> digits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition rounded_avg_safety_wit_22 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (total: Z) (digits: Z) (t: Z) (orig: Z) (num: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (t <= 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t digits ) |]
  &&  (CharArray.undef_full retval (digits + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "total" ) )) # Int  |-> digits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition rounded_avg_safety_wit_23 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (digits: Z) (total: Z) (t: Z) (orig: Z) (num: Z) ,
  [| (i <= total) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (digits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (total + 1 )) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg out i (total + 1 ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition rounded_avg_safety_wit_24 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (digits: Z) (total: Z) (t: Z) (orig: Z) (num: Z) ,
  [| (i <= total) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (digits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (total + 1 )) |]
  &&  (CharArray.full out (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (total + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition rounded_avg_safety_wit_25 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (out_l: (@list Z)) (num: Z) (digits: Z) (total: Z) (i: Z) (t: Z) (orig: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num digits out_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition rounded_avg_safety_wit_26 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (out_l: (@list Z)) (num: Z) (digits: Z) (total: Z) (i: Z) (t: Z) (orig: Z) ,
  [| (num > 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num digits out_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| ((digits - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (digits - 1 )) |]
.

Definition rounded_avg_safety_wit_27 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (out_l: (@list Z)) (num: Z) (digits: Z) (total: Z) (i: Z) (t: Z) (orig: Z) ,
  [| (num > 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num digits out_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition rounded_avg_safety_wit_28 := 
forall (m_pre: Z) (n_pre: Z) (out_l: (@list Z)) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (digits: Z) (out: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (digits + 1 ) out_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| ((48 + (num % ( 2 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (48 + (num % ( 2 ) ) )) |]
.

Definition rounded_avg_safety_wit_29 := 
forall (m_pre: Z) (n_pre: Z) (out_l: (@list Z)) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (digits: Z) (out: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (digits + 1 ) out_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| ((num <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition rounded_avg_safety_wit_30 := 
forall (m_pre: Z) (n_pre: Z) (out_l: (@list Z)) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (digits: Z) (out: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (digits + 1 ) out_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition rounded_avg_safety_wit_31 := 
forall (m_pre: Z) (n_pre: Z) (out_l: (@list Z)) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (digits: Z) (out: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (digits + 1 ) out_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition rounded_avg_safety_wit_32 := 
forall (m_pre: Z) (n_pre: Z) (out_l: (@list Z)) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (digits: Z) (out: Z) ,
  [| (0 <= (total + 1 )) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (digits + 1 ) out_l ) |]
  &&  (CharArray.full out (total + 1 ) (replace_Znth (digits) ((signed_last_nbits ((48 + (num % ( 2 ) ) )) (8))) ((app (out_l) ((cons (0) (nil)))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((num <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition rounded_avg_safety_wit_33 := 
forall (m_pre: Z) (n_pre: Z) (out_l: (@list Z)) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (digits: Z) (out: Z) ,
  [| (0 <= (total + 1 )) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (digits + 1 ) out_l ) |]
  &&  (CharArray.full out (total + 1 ) (replace_Znth (digits) ((signed_last_nbits ((48 + (num % ( 2 ) ) )) (8))) ((app (out_l) ((cons (0) (nil)))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition rounded_avg_entail_wit_1 := 
forall (m_pre: Z) (n_pre: Z) ,
  [| (n_pre <= m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  emp
|--
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (((n_pre + m_pre ) ÷ 2 ) = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (((n_pre + m_pre ) ÷ 2 ) = ((n_pre + m_pre ) ÷ 2 )) |] 
  &&  [| (0 < ((n_pre + m_pre ) ÷ 2 )) |] 
  &&  [| (((n_pre + m_pre ) ÷ 2 ) < INT_MAX) |] 
  &&  [| (0 <= ((n_pre + m_pre ) ÷ 2 )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 < INT_MAX) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (binary_count_state_z ((n_pre + m_pre ) ÷ 2 ) ((n_pre + m_pre ) ÷ 2 ) 0 ) |]
  &&  emp
.

Definition rounded_avg_entail_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (total: Z) (digits: Z) (t: Z) (orig: Z) (num: Z) ,
  [| (t > 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t digits ) |]
  &&  emp
|--
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (0 <= (t ÷ 2 )) |] 
  &&  [| (0 <= (digits + 1 )) |] 
  &&  [| ((digits + 1 ) < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num (t ÷ 2 ) (digits + 1 ) ) |]
  &&  emp
.

Definition rounded_avg_entail_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (total: Z) (digits: Z) (t: Z) (orig: Z) (num: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (t <= 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t digits ) |]
  &&  (CharArray.undef_full retval (digits + 1 ) )
|--
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (digits = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (digits = digits) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (digits + 1 )) |]
  &&  (CharArray.full retval 0 (repeat_Z (0) (0)) )
  **  (CharArray.undef_seg retval 0 (digits + 1 ) )
.

Definition rounded_avg_entail_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (digits: Z) (total: Z) (t: Z) (orig: Z) (num: Z) ,
  [| (i <= total) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (digits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (total + 1 )) |]
  &&  (CharArray.full out (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (total + 1 ) )
|--
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (digits = total) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (total + 1 )) |]
  &&  (CharArray.full out (i + 1 ) (repeat_Z (0) ((i + 1 ))) )
  **  (CharArray.undef_seg out (i + 1 ) (total + 1 ) )
.

Definition rounded_avg_entail_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (digits: Z) (total: Z) (t: Z) (orig: Z) (num: Z) ,
  [| (i > total) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (digits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (total + 1 )) |]
  &&  (CharArray.full out i (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg out i (total + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (digits = total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z num num digits out_l ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition rounded_avg_entail_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (out_l_2: (@list Z)) (num: Z) (orig: Z) (t: Z) (i: Z) (total: Z) (digits: Z) (out: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (digits = total) |] 
  &&  [| ((Zlength (out_l_2)) = total) |] 
  &&  [| (binary_fill_full_state_z num num digits out_l_2 ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num digits out_l ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition rounded_avg_entail_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (out_l_2: (@list Z)) (num: Z) (digits: Z) (total: Z) (i: Z) (t: Z) (orig: Z) ,
  [| (num > 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l_2)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num digits out_l_2 ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= (digits - 1 )) |] 
  &&  [| ((digits - 1 ) < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num ((digits - 1 ) + 1 ) out_l ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition rounded_avg_entail_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (out_l_2: (@list Z)) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (digits: Z) (out: Z) ,
  [| (0 <= (total + 1 )) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < total) |] 
  &&  [| ((Zlength (out_l_2)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (digits + 1 ) out_l_2 ) |]
  &&  (CharArray.full out (total + 1 ) (replace_Znth (digits) ((signed_last_nbits ((48 + (num % ( 2 ) ) )) (8))) ((app (out_l_2) ((cons (0) (nil)))))) )
|--
  EX (out_l: (@list Z)) ,
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits <= total) |] 
  &&  [| (0 <= (num ÷ 2 )) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig (num ÷ 2 ) digits out_l ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition rounded_avg_return_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (out_l_2: (@list Z)) (num: Z) (digits: Z) (total: Z) (i: Z) (t: Z) (orig: Z) ,
  [| (num <= 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits <= total) |] 
  &&  [| (0 <= num) |] 
  &&  [| ((Zlength (out_l_2)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num digits out_l_2 ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z))  (len: Z) ,
  [| (1 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (out_l)) = len) |] 
  &&  [| (problem_103_spec_z n_pre m_pre out_l ) |]
  &&  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition rounded_avg_return_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  (CharArray.undef_seg retval (2 + 1 ) 3 )
  **  (((retval + (2 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 49)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
|--
  EX (out_l: (@list Z))  (len: Z) ,
  [| (1 <= len) |] 
  &&  [| (len < INT_MAX) |] 
  &&  [| ((Zlength (out_l)) = len) |] 
  &&  [| (problem_103_spec_z n_pre m_pre out_l ) |]
  &&  (CharArray.full retval (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition rounded_avg_partial_solve_wit_1_pure := 
forall (m_pre: Z) (n_pre: Z) ,
  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  ((( &( "out_neg" ) )) # Ptr  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (3 > 0) |]
.

Definition rounded_avg_partial_solve_wit_1_aux := 
forall (m_pre: Z) (n_pre: Z) ,
  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  emp
|--
  [| (3 > 0) |] 
  &&  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  emp
.

Definition rounded_avg_partial_solve_wit_1 := rounded_avg_partial_solve_wit_1_pure -> rounded_avg_partial_solve_wit_1_aux.

Definition rounded_avg_partial_solve_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  (CharArray.undef_full retval 3 )
|--
  [| (retval <> 0) |] 
  &&  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 3 )
.

Definition rounded_avg_partial_solve_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) 3 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
|--
  [| (retval <> 0) |] 
  &&  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  (((retval + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 (0 + 1 ) 3 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
.

Definition rounded_avg_partial_solve_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  (CharArray.undef_seg retval (1 + 1 ) 3 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 49)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
|--
  [| (retval <> 0) |] 
  &&  [| (n_pre > m_pre) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (m_pre < INT_MAX) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (problem_103_pre_z n_pre m_pre ) |]
  &&  (((retval + (2 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 2 (1 + 1 ) 3 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 49)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 45)
.

Definition rounded_avg_partial_solve_wit_5_pure := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (total: Z) (digits: Z) (t: Z) (orig: Z) (num: Z) ,
  [| (t <= 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t digits ) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "orig" ) )) # Int  |-> orig)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "total" ) )) # Int  |-> digits)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  [| ((digits + 1 ) > 0) |]
.

Definition rounded_avg_partial_solve_wit_5_aux := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (total: Z) (digits: Z) (t: Z) (orig: Z) (num: Z) ,
  [| (t <= 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t digits ) |]
  &&  emp
|--
  [| ((digits + 1 ) > 0) |] 
  &&  [| (t <= 0) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (0 <= t) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < INT_MAX) |] 
  &&  [| (total = 0) |] 
  &&  [| (i = 0) |] 
  &&  [| (out = 0) |] 
  &&  [| (binary_count_state_z num t digits ) |]
  &&  emp
.

Definition rounded_avg_partial_solve_wit_5 := rounded_avg_partial_solve_wit_5_pure -> rounded_avg_partial_solve_wit_5_aux.

Definition rounded_avg_partial_solve_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (out: Z) (i: Z) (digits: Z) (total: Z) (t: Z) (orig: Z) (num: Z) ,
  [| (i <= total) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (digits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (total + 1 )) |]
  &&  (CharArray.full out i (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg out i (total + 1 ) )
|--
  [| (i <= total) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (num = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (orig = num) |] 
  &&  [| (0 < num) |] 
  &&  [| (num < INT_MAX) |] 
  &&  [| (t = 0) |] 
  &&  [| (total = (Zlength ((binary_digits_z (num))))) |] 
  &&  [| (digits = total) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= (total + 1 )) |]
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (total + 1 ) )
  **  (CharArray.full out i (repeat_Z (0) (i)) )
.

Definition rounded_avg_partial_solve_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (out_l: (@list Z)) (orig: Z) (num: Z) (t: Z) (i: Z) (total: Z) (digits: Z) (out: Z) ,
  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (digits + 1 ) out_l ) |]
  &&  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  [| (0 <= (total + 1 )) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (0 < m_pre) |] 
  &&  [| (n_pre <= m_pre) |] 
  &&  [| ((n_pre + m_pre ) < INT_MAX) |] 
  &&  [| (orig = (avg_103 (n_pre) (m_pre))) |] 
  &&  [| (0 < orig) |] 
  &&  [| (orig < INT_MAX) |] 
  &&  [| (0 < num) |] 
  &&  [| (t = 0) |] 
  &&  [| (i = (total + 1 )) |] 
  &&  [| (total = (Zlength ((binary_digits_z (orig))))) |] 
  &&  [| (0 <= digits) |] 
  &&  [| (digits < total) |] 
  &&  [| ((Zlength (out_l)) = total) |] 
  &&  [| (binary_fill_full_state_z orig num (digits + 1 ) out_l ) |]
  &&  (((out + (digits * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i out digits 0 (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

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
Axiom proof_of_rounded_avg_safety_wit_11 : rounded_avg_safety_wit_11.
Axiom proof_of_rounded_avg_safety_wit_12 : rounded_avg_safety_wit_12.
Axiom proof_of_rounded_avg_safety_wit_13 : rounded_avg_safety_wit_13.
Axiom proof_of_rounded_avg_safety_wit_14 : rounded_avg_safety_wit_14.
Axiom proof_of_rounded_avg_safety_wit_15 : rounded_avg_safety_wit_15.
Axiom proof_of_rounded_avg_safety_wit_16 : rounded_avg_safety_wit_16.
Axiom proof_of_rounded_avg_safety_wit_17 : rounded_avg_safety_wit_17.
Axiom proof_of_rounded_avg_safety_wit_18 : rounded_avg_safety_wit_18.
Axiom proof_of_rounded_avg_safety_wit_19 : rounded_avg_safety_wit_19.
Axiom proof_of_rounded_avg_safety_wit_20 : rounded_avg_safety_wit_20.
Axiom proof_of_rounded_avg_safety_wit_21 : rounded_avg_safety_wit_21.
Axiom proof_of_rounded_avg_safety_wit_22 : rounded_avg_safety_wit_22.
Axiom proof_of_rounded_avg_safety_wit_23 : rounded_avg_safety_wit_23.
Axiom proof_of_rounded_avg_safety_wit_24 : rounded_avg_safety_wit_24.
Axiom proof_of_rounded_avg_safety_wit_25 : rounded_avg_safety_wit_25.
Axiom proof_of_rounded_avg_safety_wit_26 : rounded_avg_safety_wit_26.
Axiom proof_of_rounded_avg_safety_wit_27 : rounded_avg_safety_wit_27.
Axiom proof_of_rounded_avg_safety_wit_28 : rounded_avg_safety_wit_28.
Axiom proof_of_rounded_avg_safety_wit_29 : rounded_avg_safety_wit_29.
Axiom proof_of_rounded_avg_safety_wit_30 : rounded_avg_safety_wit_30.
Axiom proof_of_rounded_avg_safety_wit_31 : rounded_avg_safety_wit_31.
Axiom proof_of_rounded_avg_safety_wit_32 : rounded_avg_safety_wit_32.
Axiom proof_of_rounded_avg_safety_wit_33 : rounded_avg_safety_wit_33.
Axiom proof_of_rounded_avg_entail_wit_1 : rounded_avg_entail_wit_1.
Axiom proof_of_rounded_avg_entail_wit_2 : rounded_avg_entail_wit_2.
Axiom proof_of_rounded_avg_entail_wit_3 : rounded_avg_entail_wit_3.
Axiom proof_of_rounded_avg_entail_wit_4 : rounded_avg_entail_wit_4.
Axiom proof_of_rounded_avg_entail_wit_5 : rounded_avg_entail_wit_5.
Axiom proof_of_rounded_avg_entail_wit_6 : rounded_avg_entail_wit_6.
Axiom proof_of_rounded_avg_entail_wit_7 : rounded_avg_entail_wit_7.
Axiom proof_of_rounded_avg_entail_wit_8 : rounded_avg_entail_wit_8.
Axiom proof_of_rounded_avg_return_wit_1 : rounded_avg_return_wit_1.
Axiom proof_of_rounded_avg_return_wit_2 : rounded_avg_return_wit_2.
Axiom proof_of_rounded_avg_partial_solve_wit_1_pure : rounded_avg_partial_solve_wit_1_pure.
Axiom proof_of_rounded_avg_partial_solve_wit_1 : rounded_avg_partial_solve_wit_1.
Axiom proof_of_rounded_avg_partial_solve_wit_2 : rounded_avg_partial_solve_wit_2.
Axiom proof_of_rounded_avg_partial_solve_wit_3 : rounded_avg_partial_solve_wit_3.
Axiom proof_of_rounded_avg_partial_solve_wit_4 : rounded_avg_partial_solve_wit_4.
Axiom proof_of_rounded_avg_partial_solve_wit_5_pure : rounded_avg_partial_solve_wit_5_pure.
Axiom proof_of_rounded_avg_partial_solve_wit_5 : rounded_avg_partial_solve_wit_5.
Axiom proof_of_rounded_avg_partial_solve_wit_6 : rounded_avg_partial_solve_wit_6.
Axiom proof_of_rounded_avg_partial_solve_wit_7 : rounded_avg_partial_solve_wit_7.

End VC_Correct.
