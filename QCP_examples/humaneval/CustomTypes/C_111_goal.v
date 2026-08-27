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
Require Import coins_111.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function histogram -----*)

Definition histogram_safety_wit_1 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < INT_MAX)) (PreH3 : ((Zlength (input_l)) = n)) (PreH4 : (valid_string input_l )) (PreH5 : (ascii_range_z input_l )) (PreH6 : (problem_111_pre_z input_l )) ,
  ((( &( "init" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "count" ) ) 256 )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_2 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (PreH1 : (0 <= init)) (PreH2 : (init <= 256)) (PreH3 : (0 <= n)) (PreH4 : (n < INT_MAX)) (PreH5 : ((Zlength (input_l)) = n)) (PreH6 : (valid_string input_l )) (PreH7 : (ascii_range_z input_l )) (PreH8 : (problem_111_pre_z input_l )) ,
  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
  **  (IntArray.undef_seg ( &( "count" ) ) init 256 )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition histogram_safety_wit_3 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (PreH1 : (init < 256)) (PreH2 : (0 <= init)) (PreH3 : (init <= 256)) (PreH4 : (0 <= n)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (valid_string input_l )) (PreH8 : (ascii_range_z input_l )) (PreH9 : (problem_111_pre_z input_l )) ,
  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
  **  (IntArray.undef_seg ( &( "count" ) ) init 256 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_4 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (init < 256)) (PreH3 : (0 <= init)) (PreH4 : (init <= 256)) (PreH5 : (0 <= n)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (valid_string input_l )) (PreH9 : (ascii_range_z input_l )) (PreH10 : (problem_111_pre_z input_l )) ,
  (IntArray.seg ( &( "count" ) ) 0 (init + 1 ) (app ((zeros (init))) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "count" ) ) (init + 1 ) 256 )
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
|--
  “ ((init + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (init + 1 )) ”
.

Definition histogram_safety_wit_5 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (init < 256)) (PreH3 : (0 <= init)) (PreH4 : (init <= 256)) (PreH5 : (0 <= n)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (valid_string input_l )) (PreH9 : (ascii_range_z input_l )) (PreH10 : (problem_111_pre_z input_l )) ,
  (IntArray.seg ( &( "count" ) ) 0 (init + 1 ) (app ((zeros (init))) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "count" ) ) (init + 1 ) 256 )
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition histogram_safety_wit_6 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (init >= 256)) (PreH4 : (0 <= init)) (PreH5 : (init <= 256)) (PreH6 : (0 <= n)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (valid_string input_l )) (PreH10 : (ascii_range_z input_l )) (PreH11 : (problem_111_pre_z input_l )) ,
  ((( &( "max" ) )) # Int  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_7 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (init >= 256)) (PreH4 : (0 <= init)) (PreH5 : (init <= 256)) (PreH6 : (0 <= n)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (valid_string input_l )) (PreH10 : (ascii_range_z input_l )) (PreH11 : (problem_111_pre_z input_l )) ,
  ((( &( "max" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition histogram_safety_wit_8 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (init >= 256)) (PreH5 : (0 <= init)) (PreH6 : (init <= 256)) (PreH7 : (0 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : ((Zlength (input_l)) = n)) (PreH10 : (valid_string input_l )) (PreH11 : (ascii_range_z input_l )) (PreH12 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full retval_2 256 )
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition histogram_safety_wit_9 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= (n + 1 ))) (PreH5 : (init >= 256)) (PreH6 : (0 <= init)) (PreH7 : (init <= 256)) (PreH8 : (0 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : ((Zlength (input_l)) = n)) (PreH11 : (valid_string input_l )) (PreH12 : (ascii_range_z input_l )) (PreH13 : (problem_111_pre_z input_l )) ,
  (IntArray.undef_full retval_3 256 )
  **  (CharArray.undef_full retval_2 256 )
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_10 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= (n + 1 ))) (PreH5 : (init >= 256)) (PreH6 : (0 <= init)) (PreH7 : (init <= 256)) (PreH8 : (0 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : ((Zlength (input_l)) = n)) (PreH11 : (valid_string input_l )) (PreH12 : (ascii_range_z input_l )) (PreH13 : (problem_111_pre_z input_l )) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "values" ) )) # Ptr  |-> retval_3)
  **  ((( &( "keys" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_3 256 )
  **  (CharArray.undef_full retval_2 256 )
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_11 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= (n + 1 ))) (PreH5 : (init >= 256)) (PreH6 : (0 <= init)) (PreH7 : (init <= 256)) (PreH8 : (0 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : ((Zlength (input_l)) = n)) (PreH11 : (valid_string input_l )) (PreH12 : (ascii_range_z input_l )) (PreH13 : (problem_111_pre_z input_l )) ,
  ((( &( "next_count" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "values" ) )) # Ptr  |-> retval_3)
  **  ((( &( "keys" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_3 256 )
  **  (CharArray.undef_full retval_2 256 )
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_12 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= (n + 1 ))) (PreH5 : (init >= 256)) (PreH6 : (0 <= init)) (PreH7 : (init <= 256)) (PreH8 : (0 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : ((Zlength (input_l)) = n)) (PreH11 : (valid_string input_l )) (PreH12 : (ascii_range_z input_l )) (PreH13 : (problem_111_pre_z input_l )) ,
  ((( &( "next_count" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "values" ) )) # Ptr  |-> retval_3)
  **  ((( &( "keys" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_3 256 )
  **  (CharArray.undef_full retval_2 256 )
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_13 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (max: Z) (i: Z) (next_count: Z) (ch: Z) (init: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : (out <> 0)) (PreH2 : (keys <> 0)) (PreH3 : (values <> 0)) (PreH4 : (n < INT_MAX)) (PreH5 : ((Zlength (input_l)) = n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= max)) (PreH9 : (max <= i)) (PreH10 : ((Zlength (count_l)) = 256)) (PreH11 : (histogram_scan_state_111 input_l i count_l max )) (PreH12 : (histogram_counts_bounded_111 count_l i )) (PreH13 : (valid_string input_l )) (PreH14 : (ascii_range_z input_l )) (PreH15 : (problem_111_pre_z input_l )) ,
  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_14 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (max: Z) (i: Z) (next_count: Z) (ch: Z) (init: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= max)) (PreH10 : (max <= i)) (PreH11 : ((Zlength (count_l)) = 256)) (PreH12 : (histogram_scan_state_111 input_l i count_l max )) (PreH13 : (histogram_counts_bounded_111 count_l i )) (PreH14 : (valid_string input_l )) (PreH15 : (ascii_range_z input_l )) (PreH16 : (problem_111_pre_z input_l )) ,
  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition histogram_safety_wit_15 := 
(
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (max: Z) (next_count: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < n)) (PreH7 : (0 <= ch)) (PreH8 : (ch < 256)) (PreH9 : (ch <> 32)) (PreH10 : (ch = (Znth (i) (input_l) (0)))) (PreH11 : (n < INT_MAX)) (PreH12 : ((Zlength (input_l)) = n)) (PreH13 : (0 <= max)) (PreH14 : (max <= i)) (PreH15 : ((Zlength (count_l)) = 256)) (PreH16 : (histogram_scan_state_111 input_l i count_l max )) (PreH17 : (histogram_counts_bounded_111 count_l i )) (PreH18 : (valid_string input_l )) (PreH19 : (ascii_range_z input_l )) (PreH20 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (((Znth ch count_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ch count_l 0) + 1 )) ”
) \/
(
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (max: Z) (next_count: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < n)) (PreH7 : (0 <= ch)) (PreH8 : (ch < 256)) (PreH9 : (ch <> 32)) (PreH10 : (ch = (Znth (i) (input_l) (0)))) (PreH11 : (n < INT_MAX)) (PreH12 : ((Zlength (input_l)) = n)) (PreH13 : (0 <= max)) (PreH14 : (max <= i)) (PreH15 : ((Zlength (count_l)) = 256)) (PreH16 : (histogram_scan_state_111 input_l i count_l max )) (PreH17 : (histogram_counts_bounded_111 count_l i )) (PreH18 : (valid_string input_l )) (PreH19 : (ascii_range_z input_l )) (PreH20 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (((Znth ch count_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ch count_l 0) + 1 )) ”
).

Definition histogram_safety_wit_15_split_goal_1 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (max: Z) (next_count: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < n)) (PreH7 : (0 <= ch)) (PreH8 : (ch < 256)) (PreH9 : (ch <> 32)) (PreH10 : (ch = (Znth (i) (input_l) (0)))) (PreH11 : (n < INT_MAX)) (PreH12 : ((Zlength (input_l)) = n)) (PreH13 : (0 <= max)) (PreH14 : (max <= i)) (PreH15 : ((Zlength (count_l)) = 256)) (PreH16 : (histogram_scan_state_111 input_l i count_l max )) (PreH17 : (histogram_counts_bounded_111 count_l i )) (PreH18 : (valid_string input_l )) (PreH19 : (ascii_range_z input_l )) (PreH20 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (((Znth ch count_l 0) + 1 ) <= INT_MAX) ”
.

Definition histogram_safety_wit_15_split_goal_2 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (max: Z) (next_count: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < n)) (PreH7 : (0 <= ch)) (PreH8 : (ch < 256)) (PreH9 : (ch <> 32)) (PreH10 : (ch = (Znth (i) (input_l) (0)))) (PreH11 : (n < INT_MAX)) (PreH12 : ((Zlength (input_l)) = n)) (PreH13 : (0 <= max)) (PreH14 : (max <= i)) (PreH15 : ((Zlength (count_l)) = 256)) (PreH16 : (histogram_scan_state_111 input_l i count_l max )) (PreH17 : (histogram_counts_bounded_111 count_l i )) (PreH18 : (valid_string input_l )) (PreH19 : (ascii_range_z input_l )) (PreH20 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((INT_MIN) <= ((Znth ch count_l 0) + 1 )) ”
.

Definition histogram_safety_wit_16 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (max: Z) (next_count: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < n)) (PreH7 : (0 <= ch)) (PreH8 : (ch < 256)) (PreH9 : (ch <> 32)) (PreH10 : (ch = (Znth (i) (input_l) (0)))) (PreH11 : (n < INT_MAX)) (PreH12 : ((Zlength (input_l)) = n)) (PreH13 : (0 <= max)) (PreH14 : (max <= i)) (PreH15 : ((Zlength (count_l)) = 256)) (PreH16 : (histogram_scan_state_111 input_l i count_l max )) (PreH17 : (histogram_counts_bounded_111 count_l i )) (PreH18 : (valid_string input_l )) (PreH19 : (ascii_range_z input_l )) (PreH20 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition histogram_safety_wit_17 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l 0) + 1 ) > max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l max )) (PreH18 : (histogram_counts_bounded_111 count_l i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 (replace_Znth (ch) (((Znth ch count_l 0) + 1 )) (count_l)) )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "max" ) )) # Int  |-> ((Znth ch count_l 0) + 1 ))
  **  ((( &( "next_count" ) )) # Int  |-> ((Znth ch count_l 0) + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition histogram_safety_wit_18 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l 0) + 1 ) > max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l max )) (PreH18 : (histogram_counts_bounded_111 count_l i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 (replace_Znth (ch) (((Znth ch count_l 0) + 1 )) (count_l)) )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "max" ) )) # Int  |-> ((Znth ch count_l 0) + 1 ))
  **  ((( &( "next_count" ) )) # Int  |-> ((Znth ch count_l 0) + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition histogram_safety_wit_19 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l 0) + 1 ) <= max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l max )) (PreH18 : (histogram_counts_bounded_111 count_l i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 (replace_Znth (ch) (((Znth ch count_l 0) + 1 )) (count_l)) )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "next_count" ) )) # Int  |-> ((Znth ch count_l 0) + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition histogram_safety_wit_20 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l 0) + 1 ) <= max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l max )) (PreH18 : (histogram_counts_bounded_111 count_l i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 (replace_Znth (ch) (((Znth ch count_l 0) + 1 )) (count_l)) )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "next_count" ) )) # Int  |-> ((Znth ch count_l 0) + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition histogram_safety_wit_21 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (max: Z) (i: Z) (next_count: Z) (ch: Z) (init: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l max )) (PreH14 : (histogram_counts_bounded_111 count_l i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition histogram_safety_wit_22 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (max: Z) (i: Z) (next_count: Z) (ch: Z) (init: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l max )) (PreH14 : (histogram_counts_bounded_111 count_l i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition histogram_safety_wit_23 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (max: Z) (i: Z) (next_count: Z) (ch: Z) (init: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= max)) (PreH10 : (max <= i)) (PreH11 : ((Zlength (count_l)) = 256)) (PreH12 : (histogram_scan_state_111 input_l i count_l max )) (PreH13 : (histogram_counts_bounded_111 count_l i )) (PreH14 : (valid_string input_l )) (PreH15 : (ascii_range_z input_l )) (PreH16 : (problem_111_pre_z input_l )) ,
  ((( &( "selected_count" ) )) # Int  |->_)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_24 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (max: Z) (i: Z) (next_count: Z) (ch: Z) (init: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= max)) (PreH10 : (max <= i)) (PreH11 : ((Zlength (count_l)) = 256)) (PreH12 : (histogram_scan_state_111 input_l i count_l max )) (PreH13 : (histogram_counts_bounded_111 count_l i )) (PreH14 : (valid_string input_l )) (PreH15 : (ascii_range_z input_l )) (PreH16 : (problem_111_pre_z input_l )) ,
  ((( &( "output_size" ) )) # Int  |->_)
  **  ((( &( "selected_count" ) )) # Int  |-> 0)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_25 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (max: Z) (i: Z) (next_count: Z) (ch: Z) (init: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= max)) (PreH10 : (max <= i)) (PreH11 : ((Zlength (count_l)) = 256)) (PreH12 : (histogram_scan_state_111 input_l i count_l max )) (PreH13 : (histogram_counts_bounded_111 count_l i )) (PreH14 : (valid_string input_l )) (PreH15 : (ascii_range_z input_l )) (PreH16 : (problem_111_pre_z input_l )) ,
  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "selected_count" ) )) # Int  |-> 0)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_26 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (max: Z) (count_l: (@list Z)) (values_l: (@list Z)) (keys_l: (@list Z)) (scan: Z) (output_size: Z) (selected_count: Z) (next_count: Z) (ch: Z) (i: Z) (init: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : (out <> 0)) (PreH2 : (keys <> 0)) (PreH3 : (values <> 0)) (PreH4 : (n < INT_MAX)) (PreH5 : ((Zlength (input_l)) = n)) (PreH6 : (0 <= scan)) (PreH7 : (scan <= 256)) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= scan)) (PreH10 : (output_size = (Zlength (keys_l)))) (PreH11 : (output_size = (Zlength (values_l)))) (PreH12 : ((Zlength (count_l)) = 256)) (PreH13 : (histogram_scan_state_111 input_l n count_l max )) (PreH14 : (histogram_counts_bounded_111 count_l n )) (PreH15 : (histogram_output_state_111 count_l max scan keys_l values_l )) (PreH16 : (valid_string input_l )) (PreH17 : (ascii_range_z input_l )) (PreH18 : (problem_111_pre_z input_l )) ,
  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "selected_count" ) )) # Int  |-> selected_count)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.seg keys 0 output_size keys_l )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l )
  **  (IntArray.undef_seg values output_size 256 )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition histogram_safety_wit_27 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (keys_l: (@list Z)) (values_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (next_count: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : ((Znth scan count_l 0) = max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= scan)) (PreH9 : (scan < 256)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= scan)) (PreH12 : (output_size = (Zlength (keys_l)))) (PreH13 : (output_size = (Zlength (values_l)))) (PreH14 : ((Zlength (count_l)) = 256)) (PreH15 : (histogram_scan_state_111 input_l n count_l max )) (PreH16 : (histogram_counts_bounded_111 count_l n )) (PreH17 : (histogram_output_state_111 count_l max scan keys_l values_l )) (PreH18 : (valid_string input_l )) (PreH19 : (ascii_range_z input_l )) (PreH20 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "selected_count" ) )) # Int  |-> (Znth scan count_l 0))
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg keys 0 output_size keys_l )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l )
  **  (IntArray.undef_seg values output_size 256 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_28 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (keys_l: (@list Z)) (values_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (next_count: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth scan count_l 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l)))) (PreH14 : (output_size = (Zlength (values_l)))) (PreH15 : ((Zlength (count_l)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l max )) (PreH17 : (histogram_counts_bounded_111 count_l n )) (PreH18 : (histogram_output_state_111 count_l max scan keys_l values_l )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (IntArray.seg values 0 (output_size + 1 ) (app (values_l) ((cons ((Znth scan count_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg values (output_size + 1 ) 256 )
  **  (CharArray.seg keys 0 (output_size + 1 ) (app (keys_l) ((cons (scan) ((@nil Z))))) )
  **  (CharArray.undef_seg keys (output_size + 1 ) 256 )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "selected_count" ) )) # Int  |-> (Znth scan count_l 0))
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
|--
  “ ((output_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (output_size + 1 )) ”
.

Definition histogram_safety_wit_29 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (keys_l: (@list Z)) (values_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (next_count: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth scan count_l 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l)))) (PreH14 : (output_size = (Zlength (values_l)))) (PreH15 : ((Zlength (count_l)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l max )) (PreH17 : (histogram_counts_bounded_111 count_l n )) (PreH18 : (histogram_output_state_111 count_l max scan keys_l values_l )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (IntArray.seg values 0 (output_size + 1 ) (app (values_l) ((cons ((Znth scan count_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg values (output_size + 1 ) 256 )
  **  (CharArray.seg keys 0 (output_size + 1 ) (app (keys_l) ((cons (scan) ((@nil Z))))) )
  **  (CharArray.undef_seg keys (output_size + 1 ) 256 )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "selected_count" ) )) # Int  |-> (Znth scan count_l 0))
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition histogram_safety_wit_30 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (keys_l: (@list Z)) (values_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (next_count: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth scan count_l 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l)))) (PreH14 : (output_size = (Zlength (values_l)))) (PreH15 : ((Zlength (count_l)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l max )) (PreH17 : (histogram_counts_bounded_111 count_l n )) (PreH18 : (histogram_output_state_111 count_l max scan keys_l values_l )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (IntArray.seg values 0 (output_size + 1 ) (app (values_l) ((cons ((Znth scan count_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg values (output_size + 1 ) 256 )
  **  (CharArray.seg keys 0 (output_size + 1 ) (app (keys_l) ((cons (scan) ((@nil Z))))) )
  **  (CharArray.undef_seg keys (output_size + 1 ) 256 )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "selected_count" ) )) # Int  |-> (Znth scan count_l 0))
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
|--
  “ ((scan + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (scan + 1 )) ”
.

Definition histogram_safety_wit_31 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (keys_l: (@list Z)) (values_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (next_count: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth scan count_l 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l)))) (PreH14 : (output_size = (Zlength (values_l)))) (PreH15 : ((Zlength (count_l)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l max )) (PreH17 : (histogram_counts_bounded_111 count_l n )) (PreH18 : (histogram_output_state_111 count_l max scan keys_l values_l )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (IntArray.seg values 0 (output_size + 1 ) (app (values_l) ((cons ((Znth scan count_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg values (output_size + 1 ) 256 )
  **  (CharArray.seg keys 0 (output_size + 1 ) (app (keys_l) ((cons (scan) ((@nil Z))))) )
  **  (CharArray.undef_seg keys (output_size + 1 ) 256 )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "selected_count" ) )) # Int  |-> (Znth scan count_l 0))
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition histogram_safety_wit_32 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (keys_l: (@list Z)) (values_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (next_count: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : ((Znth scan count_l 0) <> max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= scan)) (PreH9 : (scan < 256)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= scan)) (PreH12 : (output_size = (Zlength (keys_l)))) (PreH13 : (output_size = (Zlength (values_l)))) (PreH14 : ((Zlength (count_l)) = 256)) (PreH15 : (histogram_scan_state_111 input_l n count_l max )) (PreH16 : (histogram_counts_bounded_111 count_l n )) (PreH17 : (histogram_output_state_111 count_l max scan keys_l values_l )) (PreH18 : (valid_string input_l )) (PreH19 : (ascii_range_z input_l )) (PreH20 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "selected_count" ) )) # Int  |-> (Znth scan count_l 0))
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg keys 0 output_size keys_l )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l )
  **  (IntArray.undef_seg values output_size 256 )
|--
  “ ((scan + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (scan + 1 )) ”
.

Definition histogram_safety_wit_33 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (keys_l: (@list Z)) (values_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (next_count: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : ((Znth scan count_l 0) <> max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= scan)) (PreH9 : (scan < 256)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= scan)) (PreH12 : (output_size = (Zlength (keys_l)))) (PreH13 : (output_size = (Zlength (values_l)))) (PreH14 : ((Zlength (count_l)) = 256)) (PreH15 : (histogram_scan_state_111 input_l n count_l max )) (PreH16 : (histogram_counts_bounded_111 count_l n )) (PreH17 : (histogram_output_state_111 count_l max scan keys_l values_l )) (PreH18 : (valid_string input_l )) (PreH19 : (ascii_range_z input_l )) (PreH20 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "selected_count" ) )) # Int  |-> (Znth scan count_l 0))
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg keys 0 output_size keys_l )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l )
  **  (IntArray.undef_seg values output_size 256 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition histogram_safety_wit_34 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (keys_l: (@list Z)) (values_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (next_count: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max <= 0)) (PreH2 : ((Znth scan count_l 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l)))) (PreH14 : (output_size = (Zlength (values_l)))) (PreH15 : ((Zlength (count_l)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l max )) (PreH17 : (histogram_counts_bounded_111 count_l n )) (PreH18 : (histogram_output_state_111 count_l max scan keys_l values_l )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "selected_count" ) )) # Int  |-> (Znth scan count_l 0))
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg keys 0 output_size keys_l )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l )
  **  (IntArray.undef_seg values output_size 256 )
|--
  “ ((scan + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (scan + 1 )) ”
.

Definition histogram_safety_wit_35 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (keys_l: (@list Z)) (values_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (init: Z) (i: Z) (ch: Z) (next_count: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max <= 0)) (PreH2 : ((Znth scan count_l 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l)))) (PreH14 : (output_size = (Zlength (values_l)))) (PreH15 : ((Zlength (count_l)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l max )) (PreH17 : (histogram_counts_bounded_111 count_l n )) (PreH18 : (histogram_output_state_111 count_l max scan keys_l values_l )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "next_count" ) )) # Int  |-> next_count)
  **  ((( &( "selected_count" ) )) # Int  |-> (Znth scan count_l 0))
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg keys 0 output_size keys_l )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l )
  **  (IntArray.undef_seg values output_size 256 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition histogram_entail_wit_1 := 
(
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < INT_MAX)) (PreH3 : ((Zlength (input_l)) = n)) (PreH4 : (valid_string input_l )) (PreH5 : (ascii_range_z input_l )) (PreH6 : (problem_111_pre_z input_l )) ,
  (IntArray.undef_full ( &( "count" ) ) 256 )
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 256) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 0 (zeros (0)) )
  **  (IntArray.undef_seg ( &( "count" ) ) 0 256 )
) \/
(
forall (n: Z) (input_l: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < INT_MAX)) (PreH3 : ((Zlength (input_l)) = n)) (PreH4 : (valid_string input_l )) (PreH5 : (ascii_range_z input_l )) (PreH6 : (problem_111_pre_z input_l )) ,
  TT && emp 
|--
  “ ((zeros (0)) = (@nil Z)) ”
  &&  emp
).

Definition histogram_entail_wit_1_split_goal_1 := 
forall (n: Z) (input_l: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n < INT_MAX)) (PreH3 : ((Zlength (input_l)) = n)) (PreH4 : (valid_string input_l )) (PreH5 : (ascii_range_z input_l )) (PreH6 : (problem_111_pre_z input_l )) ,
  ((zeros (0)) = (@nil Z))
.

Definition histogram_entail_wit_2 := 
(
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (init < 256)) (PreH3 : (0 <= init)) (PreH4 : (init <= 256)) (PreH5 : (0 <= n)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (valid_string input_l )) (PreH9 : (ascii_range_z input_l )) (PreH10 : (problem_111_pre_z input_l )) ,
  (IntArray.seg ( &( "count" ) ) 0 (init + 1 ) (app ((zeros (init))) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "count" ) ) (init + 1 ) 256 )
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= (init + 1 )) ” 
  &&  “ ((init + 1 ) <= 256) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 (init + 1 ) (zeros ((init + 1 ))) )
  **  (IntArray.undef_seg ( &( "count" ) ) (init + 1 ) 256 )
) \/
(
forall (n: Z) (input_l: (@list Z)) (init: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (init < 256)) (PreH3 : (0 <= init)) (PreH4 : (init <= 256)) (PreH5 : (0 <= n)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (valid_string input_l )) (PreH9 : (ascii_range_z input_l )) (PreH10 : (problem_111_pre_z input_l )) ,
  TT && emp 
|--
  “ ((app ((zeros (init))) ((cons (0) ((@nil Z))))) = (zeros ((init + 1 )))) ”
  &&  emp
).

Definition histogram_entail_wit_2_split_goal_1 := 
forall (n: Z) (input_l: (@list Z)) (init: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (init < 256)) (PreH3 : (0 <= init)) (PreH4 : (init <= 256)) (PreH5 : (0 <= n)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (valid_string input_l )) (PreH9 : (ascii_range_z input_l )) (PreH10 : (problem_111_pre_z input_l )) ,
  ((app ((zeros (init))) ((cons (0) ((@nil Z))))) = (zeros ((init + 1 ))))
.

Definition histogram_entail_wit_3 := 
(
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= (n + 1 ))) (PreH5 : (init >= 256)) (PreH6 : (0 <= init)) (PreH7 : (init <= 256)) (PreH8 : (0 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : ((Zlength (input_l)) = n)) (PreH11 : (valid_string input_l )) (PreH12 : (ascii_range_z input_l )) (PreH13 : (problem_111_pre_z input_l )) ,
  (IntArray.undef_full retval_3 256 )
  **  (CharArray.undef_full retval_2 256 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
|--
  EX (count_l: (@list Z)) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l 0 count_l 0 ) ” 
  &&  “ (histogram_counts_bounded_111 count_l 0 ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full retval_2 256 )
  **  (IntArray.undef_full retval_3 256 )
) \/
(
forall (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= (n + 1 ))) (PreH5 : (init >= 256)) (PreH6 : (0 <= init)) (PreH7 : (init <= 256)) (PreH8 : (0 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : ((Zlength (input_l)) = n)) (PreH11 : (valid_string input_l )) (PreH12 : (ascii_range_z input_l )) (PreH13 : (problem_111_pre_z input_l )) ,
  (IntArray.undef_full retval_3 256 )
  **  (CharArray.undef_full retval_2 256 )
|--
  “ (histogram_counts_bounded_111 (zeros (init)) 0 ) ” 
  &&  “ (histogram_scan_state_111 input_l 0 (zeros (init)) 0 ) ” 
  &&  “ ((Zlength ((zeros (init)))) = 256) ”
  &&  (CharArray.undef_full retval_2 256 )
  **  (IntArray.undef_full retval_3 256 )
).

Definition histogram_entail_wit_3_split_goal_1 := 
forall (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= (n + 1 ))) (PreH5 : (init >= 256)) (PreH6 : (0 <= init)) (PreH7 : (init <= 256)) (PreH8 : (0 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : ((Zlength (input_l)) = n)) (PreH11 : (valid_string input_l )) (PreH12 : (ascii_range_z input_l )) (PreH13 : (problem_111_pre_z input_l )) ,
  (IntArray.undef_full retval_3 256 )
  **  (CharArray.undef_full retval_2 256 )
|--
  “ (histogram_counts_bounded_111 (zeros (init)) 0 ) ”
.

Definition histogram_entail_wit_3_split_goal_2 := 
forall (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= (n + 1 ))) (PreH5 : (init >= 256)) (PreH6 : (0 <= init)) (PreH7 : (init <= 256)) (PreH8 : (0 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : ((Zlength (input_l)) = n)) (PreH11 : (valid_string input_l )) (PreH12 : (ascii_range_z input_l )) (PreH13 : (problem_111_pre_z input_l )) ,
  (IntArray.undef_full retval_3 256 )
  **  (CharArray.undef_full retval_2 256 )
|--
  “ (histogram_scan_state_111 input_l 0 (zeros (init)) 0 ) ”
.

Definition histogram_entail_wit_3_split_goal_3 := 
forall (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= (n + 1 ))) (PreH5 : (init >= 256)) (PreH6 : (0 <= init)) (PreH7 : (init <= 256)) (PreH8 : (0 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : ((Zlength (input_l)) = n)) (PreH11 : (valid_string input_l )) (PreH12 : (ascii_range_z input_l )) (PreH13 : (problem_111_pre_z input_l )) ,
  (IntArray.undef_full retval_3 256 )
  **  (CharArray.undef_full retval_2 256 )
|--
  “ ((Zlength ((zeros (init)))) = 256) ”
.

Definition histogram_entail_wit_3_split_goal_spatial := 
forall (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= (n + 1 ))) (PreH5 : (init >= 256)) (PreH6 : (0 <= init)) (PreH7 : (init <= 256)) (PreH8 : (0 <= n)) (PreH9 : (n < INT_MAX)) (PreH10 : ((Zlength (input_l)) = n)) (PreH11 : (valid_string input_l )) (PreH12 : (ascii_range_z input_l )) (PreH13 : (problem_111_pre_z input_l )) ,
  (IntArray.undef_full retval_3 256 )
  **  (CharArray.undef_full retval_2 256 )
|--
  (CharArray.undef_full retval_2 256 )
  **  (IntArray.undef_full retval_3 256 )
.

Definition histogram_entail_wit_4 := 
(
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l_2)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH14 : (histogram_counts_bounded_111 count_l_2 i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full ( &( "count" ) ) 256 count_l_2 )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  EX (count_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0)) (8))) ” 
  &&  “ ((unsigned_last_nbits ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0)) (8)) < 256) ” 
  &&  “ ((unsigned_last_nbits ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0)) (8)) <> 32) ” 
  &&  “ ((unsigned_last_nbits ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0)) (8)) = (Znth (i) (input_l) (0))) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= max) ” 
  &&  “ (max <= i) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l i count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l i ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
) \/
(
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l_2)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH14 : (histogram_counts_bounded_111 count_l_2 i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((unsigned_last_nbits ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0)) (8)) = (Znth (i) (input_l) (0))) ” 
  &&  “ ((unsigned_last_nbits ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0)) (8)) <> 32) ” 
  &&  “ ((unsigned_last_nbits ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0)) (8)) < 256) ” 
  &&  “ (0 <= (unsigned_last_nbits ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0)) (8))) ” 
  &&  “ (i < n) ”
  &&  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
).

Definition histogram_entail_wit_4_split_goal_1 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l_2)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH14 : (histogram_counts_bounded_111 count_l_2 i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((unsigned_last_nbits ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0)) (8)) = (Znth (i) (input_l) (0))) ”
.

Definition histogram_entail_wit_4_split_goal_2 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l_2)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH14 : (histogram_counts_bounded_111 count_l_2 i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((unsigned_last_nbits ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0)) (8)) <> 32) ”
.

Definition histogram_entail_wit_4_split_goal_3 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l_2)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH14 : (histogram_counts_bounded_111 count_l_2 i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((unsigned_last_nbits ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0)) (8)) < 256) ”
.

Definition histogram_entail_wit_4_split_goal_4 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l_2)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH14 : (histogram_counts_bounded_111 count_l_2 i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= (unsigned_last_nbits ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0)) (8))) ”
.

Definition histogram_entail_wit_4_split_goal_5 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l_2)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH14 : (histogram_counts_bounded_111 count_l_2 i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (i < n) ”
.

Definition histogram_entail_wit_4_split_goal_spatial := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l_2)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH14 : (histogram_counts_bounded_111 count_l_2 i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_entail_wit_5_1 := 
(
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l_2 0) + 1 ) > max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l_2)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH18 : (histogram_counts_bounded_111 count_l_2 i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 (replace_Znth (ch) (((Znth ch count_l_2 0) + 1 )) (count_l_2)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  EX (count_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= ((Znth ch count_l_2 0) + 1 )) ” 
  &&  “ (((Znth ch count_l_2 0) + 1 ) <= (i + 1 )) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l (i + 1 ) count_l ((Znth ch count_l_2 0) + 1 ) ) ” 
  &&  “ (histogram_counts_bounded_111 count_l (i + 1 ) ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
) \/
(
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l_2 0) + 1 ) > max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l_2)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH18 : (histogram_counts_bounded_111 count_l_2 i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (histogram_counts_bounded_111 (replace_Znth (ch) (((Znth ch count_l_2 0) + 1 )) (count_l_2)) (i + 1 ) ) ” 
  &&  “ (histogram_scan_state_111 input_l (i + 1 ) (replace_Znth (ch) (((Znth ch count_l_2 0) + 1 )) (count_l_2)) ((Znth ch count_l_2 0) + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (ch) (((Znth ch count_l_2 0) + 1 )) (count_l_2)))) = 256) ” 
  &&  “ (((Znth ch count_l_2 0) + 1 ) <= (i + 1 )) ”
  &&  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
).

Definition histogram_entail_wit_5_1_split_goal_1 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l_2 0) + 1 ) > max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l_2)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH18 : (histogram_counts_bounded_111 count_l_2 i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (histogram_counts_bounded_111 (replace_Znth (ch) (((Znth ch count_l_2 0) + 1 )) (count_l_2)) (i + 1 ) ) ”
.

Definition histogram_entail_wit_5_1_split_goal_2 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l_2 0) + 1 ) > max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l_2)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH18 : (histogram_counts_bounded_111 count_l_2 i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (histogram_scan_state_111 input_l (i + 1 ) (replace_Znth (ch) (((Znth ch count_l_2 0) + 1 )) (count_l_2)) ((Znth ch count_l_2 0) + 1 ) ) ”
.

Definition histogram_entail_wit_5_1_split_goal_3 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l_2 0) + 1 ) > max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l_2)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH18 : (histogram_counts_bounded_111 count_l_2 i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((Zlength ((replace_Znth (ch) (((Znth ch count_l_2 0) + 1 )) (count_l_2)))) = 256) ”
.

Definition histogram_entail_wit_5_1_split_goal_4 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l_2 0) + 1 ) > max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l_2)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH18 : (histogram_counts_bounded_111 count_l_2 i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (((Znth ch count_l_2 0) + 1 ) <= (i + 1 )) ”
.

Definition histogram_entail_wit_5_1_split_goal_spatial := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l_2 0) + 1 ) > max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l_2)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH18 : (histogram_counts_bounded_111 count_l_2 i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_entail_wit_5_2 := 
(
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l_2 0) + 1 ) <= max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l_2)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH18 : (histogram_counts_bounded_111 count_l_2 i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 (replace_Znth (ch) (((Znth ch count_l_2 0) + 1 )) (count_l_2)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  EX (count_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= max) ” 
  &&  “ (max <= (i + 1 )) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l (i + 1 ) count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l (i + 1 ) ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
) \/
(
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l_2 0) + 1 ) <= max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l_2)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH18 : (histogram_counts_bounded_111 count_l_2 i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (histogram_counts_bounded_111 (replace_Znth (ch) (((Znth ch count_l_2 0) + 1 )) (count_l_2)) (i + 1 ) ) ” 
  &&  “ (histogram_scan_state_111 input_l (i + 1 ) (replace_Znth (ch) (((Znth ch count_l_2 0) + 1 )) (count_l_2)) max ) ” 
  &&  “ ((Zlength ((replace_Znth (ch) (((Znth ch count_l_2 0) + 1 )) (count_l_2)))) = 256) ”
  &&  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
).

Definition histogram_entail_wit_5_2_split_goal_1 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l_2 0) + 1 ) <= max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l_2)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH18 : (histogram_counts_bounded_111 count_l_2 i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (histogram_counts_bounded_111 (replace_Znth (ch) (((Znth ch count_l_2 0) + 1 )) (count_l_2)) (i + 1 ) ) ”
.

Definition histogram_entail_wit_5_2_split_goal_2 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l_2 0) + 1 ) <= max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l_2)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH18 : (histogram_counts_bounded_111 count_l_2 i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (histogram_scan_state_111 input_l (i + 1 ) (replace_Znth (ch) (((Znth ch count_l_2 0) + 1 )) (count_l_2)) max ) ”
.

Definition histogram_entail_wit_5_2_split_goal_3 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l_2 0) + 1 ) <= max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l_2)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH18 : (histogram_counts_bounded_111 count_l_2 i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((Zlength ((replace_Znth (ch) (((Znth ch count_l_2 0) + 1 )) (count_l_2)))) = 256) ”
.

Definition histogram_entail_wit_5_2_split_goal_spatial := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (((Znth ch count_l_2 0) + 1 ) <= max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < n)) (PreH8 : (0 <= ch)) (PreH9 : (ch < 256)) (PreH10 : (ch <> 32)) (PreH11 : (ch = (Znth (i) (input_l) (0)))) (PreH12 : (n < INT_MAX)) (PreH13 : ((Zlength (input_l)) = n)) (PreH14 : (0 <= max)) (PreH15 : (max <= i)) (PreH16 : ((Zlength (count_l_2)) = 256)) (PreH17 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH18 : (histogram_counts_bounded_111 count_l_2 i )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_entail_wit_5_3 := 
(
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l_2)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH14 : (histogram_counts_bounded_111 count_l_2 i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full ( &( "count" ) ) 256 count_l_2 )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  EX (count_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= max) ” 
  &&  “ (max <= (i + 1 )) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l (i + 1 ) count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l (i + 1 ) ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
) \/
(
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l_2)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH14 : (histogram_counts_bounded_111 count_l_2 i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (histogram_counts_bounded_111 count_l_2 (i + 1 ) ) ” 
  &&  “ (histogram_scan_state_111 input_l (i + 1 ) count_l_2 max ) ” 
  &&  “ ((i + 1 ) <= n) ”
  &&  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
).

Definition histogram_entail_wit_5_3_split_goal_1 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l_2)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH14 : (histogram_counts_bounded_111 count_l_2 i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (histogram_counts_bounded_111 count_l_2 (i + 1 ) ) ”
.

Definition histogram_entail_wit_5_3_split_goal_2 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l_2)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH14 : (histogram_counts_bounded_111 count_l_2 i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (histogram_scan_state_111 input_l (i + 1 ) count_l_2 max ) ”
.

Definition histogram_entail_wit_5_3_split_goal_3 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l_2)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH14 : (histogram_counts_bounded_111 count_l_2 i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((i + 1 ) <= n) ”
.

Definition histogram_entail_wit_5_3_split_goal_spatial := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l_2)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH14 : (histogram_counts_bounded_111 count_l_2 i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_entail_wit_6 := 
(
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= max)) (PreH10 : (max <= i)) (PreH11 : ((Zlength (count_l_2)) = 256)) (PreH12 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH13 : (histogram_counts_bounded_111 count_l_2 i )) (PreH14 : (valid_string input_l )) (PreH15 : (ascii_range_z input_l )) (PreH16 : (problem_111_pre_z input_l )) ,
  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full ( &( "count" ) ) 256 count_l_2 )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  EX (count_l: (@list Z))  (values_l: (@list Z))  (keys_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 256) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (keys_l))) ” 
  &&  “ (0 = (Zlength (values_l))) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l n count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l n ) ” 
  &&  “ (histogram_output_state_111 count_l max 0 keys_l values_l ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.seg keys 0 0 keys_l )
  **  (CharArray.undef_seg keys 0 256 )
  **  (IntArray.seg values 0 0 values_l )
  **  (IntArray.undef_seg values 0 256 )
) \/
(
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= max)) (PreH10 : (max <= i)) (PreH11 : ((Zlength (count_l_2)) = 256)) (PreH12 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH13 : (histogram_counts_bounded_111 count_l_2 i )) (PreH14 : (valid_string input_l )) (PreH15 : (ascii_range_z input_l )) (PreH16 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
|--
  “ (histogram_output_state_111 count_l_2 max 0 (@nil Z) (@nil Z) ) ” 
  &&  “ (histogram_counts_bounded_111 count_l_2 n ) ” 
  &&  “ (histogram_scan_state_111 input_l n count_l_2 max ) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  (CharArray.undef_full keys 256 )
).

Definition histogram_entail_wit_6_split_goal_1 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= max)) (PreH10 : (max <= i)) (PreH11 : ((Zlength (count_l_2)) = 256)) (PreH12 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH13 : (histogram_counts_bounded_111 count_l_2 i )) (PreH14 : (valid_string input_l )) (PreH15 : (ascii_range_z input_l )) (PreH16 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
|--
  “ (histogram_output_state_111 count_l_2 max 0 (@nil Z) (@nil Z) ) ”
.

Definition histogram_entail_wit_6_split_goal_2 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= max)) (PreH10 : (max <= i)) (PreH11 : ((Zlength (count_l_2)) = 256)) (PreH12 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH13 : (histogram_counts_bounded_111 count_l_2 i )) (PreH14 : (valid_string input_l )) (PreH15 : (ascii_range_z input_l )) (PreH16 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
|--
  “ (histogram_counts_bounded_111 count_l_2 n ) ”
.

Definition histogram_entail_wit_6_split_goal_3 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= max)) (PreH10 : (max <= i)) (PreH11 : ((Zlength (count_l_2)) = 256)) (PreH12 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH13 : (histogram_counts_bounded_111 count_l_2 i )) (PreH14 : (valid_string input_l )) (PreH15 : (ascii_range_z input_l )) (PreH16 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
|--
  “ (histogram_scan_state_111 input_l n count_l_2 max ) ”
.

Definition histogram_entail_wit_6_split_goal_4 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= max)) (PreH10 : (max <= i)) (PreH11 : ((Zlength (count_l_2)) = 256)) (PreH12 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH13 : (histogram_counts_bounded_111 count_l_2 i )) (PreH14 : (valid_string input_l )) (PreH15 : (ascii_range_z input_l )) (PreH16 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition histogram_entail_wit_6_split_goal_5 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= max)) (PreH10 : (max <= i)) (PreH11 : ((Zlength (count_l_2)) = 256)) (PreH12 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH13 : (histogram_counts_bounded_111 count_l_2 i )) (PreH14 : (valid_string input_l )) (PreH15 : (ascii_range_z input_l )) (PreH16 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition histogram_entail_wit_6_split_goal_spatial := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= max)) (PreH10 : (max <= i)) (PreH11 : ((Zlength (count_l_2)) = 256)) (PreH12 : (histogram_scan_state_111 input_l i count_l_2 max )) (PreH13 : (histogram_counts_bounded_111 count_l_2 i )) (PreH14 : (valid_string input_l )) (PreH15 : (ascii_range_z input_l )) (PreH16 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full keys 256 )
|--
  (CharArray.undef_full keys 256 )
.

Definition histogram_entail_wit_7 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (max: Z) (count_l_2: (@list Z)) (values_l_2: (@list Z)) (keys_l_2: (@list Z)) (scan: Z) (output_size: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : (scan < 256)) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= scan)) (PreH8 : (scan <= 256)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= scan)) (PreH11 : (output_size = (Zlength (keys_l_2)))) (PreH12 : (output_size = (Zlength (values_l_2)))) (PreH13 : ((Zlength (count_l_2)) = 256)) (PreH14 : (histogram_scan_state_111 input_l n count_l_2 max )) (PreH15 : (histogram_counts_bounded_111 count_l_2 n )) (PreH16 : (histogram_output_state_111 count_l_2 max scan keys_l_2 values_l_2 )) (PreH17 : (valid_string input_l )) (PreH18 : (ascii_range_z input_l )) (PreH19 : (problem_111_pre_z input_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "count" ) ) 256 count_l_2 )
  **  (CharArray.seg keys 0 output_size keys_l_2 )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l_2 )
  **  (IntArray.undef_seg values output_size 256 )
|--
  EX (count_l: (@list Z))  (values_l: (@list Z))  (keys_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= scan) ” 
  &&  “ (scan < 256) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= scan) ” 
  &&  “ (output_size = (Zlength (keys_l))) ” 
  &&  “ (output_size = (Zlength (values_l))) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l n count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l n ) ” 
  &&  “ (histogram_output_state_111 count_l max scan keys_l values_l ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.seg keys 0 output_size keys_l )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l )
  **  (IntArray.undef_seg values output_size 256 )
.

Definition histogram_entail_wit_8_1 := 
(
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (keys_l_2: (@list Z)) (values_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth scan count_l_2 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l_2)))) (PreH14 : (output_size = (Zlength (values_l_2)))) (PreH15 : ((Zlength (count_l_2)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l_2 max )) (PreH17 : (histogram_counts_bounded_111 count_l_2 n )) (PreH18 : (histogram_output_state_111 count_l_2 max scan keys_l_2 values_l_2 )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (IntArray.seg values 0 (output_size + 1 ) (app (values_l_2) ((cons ((Znth scan count_l_2 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg values (output_size + 1 ) 256 )
  **  (CharArray.seg keys 0 (output_size + 1 ) (app (keys_l_2) ((cons (scan) ((@nil Z))))) )
  **  (CharArray.undef_seg keys (output_size + 1 ) 256 )
  **  (IntArray.full ( &( "count" ) ) 256 count_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
|--
  EX (count_l: (@list Z))  (values_l: (@list Z))  (keys_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= (scan + 1 )) ” 
  &&  “ ((scan + 1 ) <= 256) ” 
  &&  “ (0 <= (output_size + 1 )) ” 
  &&  “ ((output_size + 1 ) <= (scan + 1 )) ” 
  &&  “ ((output_size + 1 ) = (Zlength (keys_l))) ” 
  &&  “ ((output_size + 1 ) = (Zlength (values_l))) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l n count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l n ) ” 
  &&  “ (histogram_output_state_111 count_l max (scan + 1 ) keys_l values_l ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.seg keys 0 (output_size + 1 ) keys_l )
  **  (CharArray.undef_seg keys (output_size + 1 ) 256 )
  **  (IntArray.seg values 0 (output_size + 1 ) values_l )
  **  (IntArray.undef_seg values (output_size + 1 ) 256 )
) \/
(
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (keys_l_2: (@list Z)) (values_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth scan count_l_2 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l_2)))) (PreH14 : (output_size = (Zlength (values_l_2)))) (PreH15 : ((Zlength (count_l_2)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l_2 max )) (PreH17 : (histogram_counts_bounded_111 count_l_2 n )) (PreH18 : (histogram_output_state_111 count_l_2 max scan keys_l_2 values_l_2 )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  TT && emp 
|--
  “ (histogram_output_state_111 count_l_2 max (scan + 1 ) (app (keys_l_2) ((cons (scan) ((@nil Z))))) (app (values_l_2) ((cons ((Znth scan count_l_2 0)) ((@nil Z))))) ) ” 
  &&  “ ((output_size + 1 ) = (Zlength ((app (values_l_2) ((cons ((Znth scan count_l_2 0)) ((@nil Z)))))))) ” 
  &&  “ ((output_size + 1 ) = (Zlength ((app (keys_l_2) ((cons (scan) ((@nil Z)))))))) ”
  &&  emp
).

Definition histogram_entail_wit_8_1_split_goal_1 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (keys_l_2: (@list Z)) (values_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth scan count_l_2 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l_2)))) (PreH14 : (output_size = (Zlength (values_l_2)))) (PreH15 : ((Zlength (count_l_2)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l_2 max )) (PreH17 : (histogram_counts_bounded_111 count_l_2 n )) (PreH18 : (histogram_output_state_111 count_l_2 max scan keys_l_2 values_l_2 )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (histogram_output_state_111 count_l_2 max (scan + 1 ) (app (keys_l_2) ((cons (scan) ((@nil Z))))) (app (values_l_2) ((cons ((Znth scan count_l_2 0)) ((@nil Z))))) )
.

Definition histogram_entail_wit_8_1_split_goal_2 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (keys_l_2: (@list Z)) (values_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth scan count_l_2 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l_2)))) (PreH14 : (output_size = (Zlength (values_l_2)))) (PreH15 : ((Zlength (count_l_2)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l_2 max )) (PreH17 : (histogram_counts_bounded_111 count_l_2 n )) (PreH18 : (histogram_output_state_111 count_l_2 max scan keys_l_2 values_l_2 )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  ((output_size + 1 ) = (Zlength ((app (values_l_2) ((cons ((Znth scan count_l_2 0)) ((@nil Z))))))))
.

Definition histogram_entail_wit_8_1_split_goal_3 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (keys_l_2: (@list Z)) (values_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth scan count_l_2 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l_2)))) (PreH14 : (output_size = (Zlength (values_l_2)))) (PreH15 : ((Zlength (count_l_2)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l_2 max )) (PreH17 : (histogram_counts_bounded_111 count_l_2 n )) (PreH18 : (histogram_output_state_111 count_l_2 max scan keys_l_2 values_l_2 )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  ((output_size + 1 ) = (Zlength ((app (keys_l_2) ((cons (scan) ((@nil Z))))))))
.

Definition histogram_entail_wit_8_2 := 
(
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (keys_l_2: (@list Z)) (values_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : ((Znth scan count_l_2 0) <> max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= scan)) (PreH9 : (scan < 256)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= scan)) (PreH12 : (output_size = (Zlength (keys_l_2)))) (PreH13 : (output_size = (Zlength (values_l_2)))) (PreH14 : ((Zlength (count_l_2)) = 256)) (PreH15 : (histogram_scan_state_111 input_l n count_l_2 max )) (PreH16 : (histogram_counts_bounded_111 count_l_2 n )) (PreH17 : (histogram_output_state_111 count_l_2 max scan keys_l_2 values_l_2 )) (PreH18 : (valid_string input_l )) (PreH19 : (ascii_range_z input_l )) (PreH20 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 count_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg keys 0 output_size keys_l_2 )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l_2 )
  **  (IntArray.undef_seg values output_size 256 )
|--
  EX (count_l: (@list Z))  (values_l: (@list Z))  (keys_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= (scan + 1 )) ” 
  &&  “ ((scan + 1 ) <= 256) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (scan + 1 )) ” 
  &&  “ (output_size = (Zlength (keys_l))) ” 
  &&  “ (output_size = (Zlength (values_l))) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l n count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l n ) ” 
  &&  “ (histogram_output_state_111 count_l max (scan + 1 ) keys_l values_l ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.seg keys 0 output_size keys_l )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l )
  **  (IntArray.undef_seg values output_size 256 )
) \/
(
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (keys_l_2: (@list Z)) (values_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : ((Znth scan count_l_2 0) <> max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= scan)) (PreH9 : (scan < 256)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= scan)) (PreH12 : (output_size = (Zlength (keys_l_2)))) (PreH13 : (output_size = (Zlength (values_l_2)))) (PreH14 : ((Zlength (count_l_2)) = 256)) (PreH15 : (histogram_scan_state_111 input_l n count_l_2 max )) (PreH16 : (histogram_counts_bounded_111 count_l_2 n )) (PreH17 : (histogram_output_state_111 count_l_2 max scan keys_l_2 values_l_2 )) (PreH18 : (valid_string input_l )) (PreH19 : (ascii_range_z input_l )) (PreH20 : (problem_111_pre_z input_l )) ,
  TT && emp 
|--
  “ (histogram_output_state_111 count_l_2 max (scan + 1 ) keys_l_2 values_l_2 ) ”
  &&  emp
).

Definition histogram_entail_wit_8_2_split_goal_1 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (keys_l_2: (@list Z)) (values_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : ((Znth scan count_l_2 0) <> max)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= scan)) (PreH9 : (scan < 256)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= scan)) (PreH12 : (output_size = (Zlength (keys_l_2)))) (PreH13 : (output_size = (Zlength (values_l_2)))) (PreH14 : ((Zlength (count_l_2)) = 256)) (PreH15 : (histogram_scan_state_111 input_l n count_l_2 max )) (PreH16 : (histogram_counts_bounded_111 count_l_2 n )) (PreH17 : (histogram_output_state_111 count_l_2 max scan keys_l_2 values_l_2 )) (PreH18 : (valid_string input_l )) (PreH19 : (ascii_range_z input_l )) (PreH20 : (problem_111_pre_z input_l )) ,
  (histogram_output_state_111 count_l_2 max (scan + 1 ) keys_l_2 values_l_2 )
.

Definition histogram_entail_wit_8_3 := 
(
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (keys_l_2: (@list Z)) (values_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max <= 0)) (PreH2 : ((Znth scan count_l_2 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l_2)))) (PreH14 : (output_size = (Zlength (values_l_2)))) (PreH15 : ((Zlength (count_l_2)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l_2 max )) (PreH17 : (histogram_counts_bounded_111 count_l_2 n )) (PreH18 : (histogram_output_state_111 count_l_2 max scan keys_l_2 values_l_2 )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 count_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg keys 0 output_size keys_l_2 )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l_2 )
  **  (IntArray.undef_seg values output_size 256 )
|--
  EX (count_l: (@list Z))  (values_l: (@list Z))  (keys_l: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= (scan + 1 )) ” 
  &&  “ ((scan + 1 ) <= 256) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (scan + 1 )) ” 
  &&  “ (output_size = (Zlength (keys_l))) ” 
  &&  “ (output_size = (Zlength (values_l))) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l n count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l n ) ” 
  &&  “ (histogram_output_state_111 count_l max (scan + 1 ) keys_l values_l ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.seg keys 0 output_size keys_l )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l )
  **  (IntArray.undef_seg values output_size 256 )
) \/
(
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (keys_l_2: (@list Z)) (values_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max <= 0)) (PreH2 : ((Znth scan count_l_2 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l_2)))) (PreH14 : (output_size = (Zlength (values_l_2)))) (PreH15 : ((Zlength (count_l_2)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l_2 max )) (PreH17 : (histogram_counts_bounded_111 count_l_2 n )) (PreH18 : (histogram_output_state_111 count_l_2 max scan keys_l_2 values_l_2 )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  TT && emp 
|--
  “ (histogram_output_state_111 count_l_2 max (scan + 1 ) keys_l_2 values_l_2 ) ”
  &&  emp
).

Definition histogram_entail_wit_8_3_split_goal_1 := 
forall (n: Z) (input_l: (@list Z)) (count_l_2: (@list Z)) (keys_l_2: (@list Z)) (values_l_2: (@list Z)) (out: Z) (keys: Z) (values: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max <= 0)) (PreH2 : ((Znth scan count_l_2 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l_2)))) (PreH14 : (output_size = (Zlength (values_l_2)))) (PreH15 : ((Zlength (count_l_2)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l_2 max )) (PreH17 : (histogram_counts_bounded_111 count_l_2 n )) (PreH18 : (histogram_output_state_111 count_l_2 max scan keys_l_2 values_l_2 )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (histogram_output_state_111 count_l_2 max (scan + 1 ) keys_l_2 values_l_2 )
.

Definition histogram_return_wit_1 := 
(
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (max: Z) (count_l: (@list Z)) (values_l_2: (@list Z)) (keys_l_2: (@list Z)) (scan: Z) (output_size_2: Z) (values_2: Z) (keys_2: Z) (out: Z) (PreH1 : (scan >= 256)) (PreH2 : (out <> 0)) (PreH3 : (keys_2 <> 0)) (PreH4 : (values_2 <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= scan)) (PreH8 : (scan <= 256)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= scan)) (PreH11 : (output_size_2 = (Zlength (keys_l_2)))) (PreH12 : (output_size_2 = (Zlength (values_l_2)))) (PreH13 : ((Zlength (count_l)) = 256)) (PreH14 : (histogram_scan_state_111 input_l n count_l max )) (PreH15 : (histogram_counts_bounded_111 count_l n )) (PreH16 : (histogram_output_state_111 count_l max scan keys_l_2 values_l_2 )) (PreH17 : (valid_string input_l )) (PreH18 : (ascii_range_z input_l )) (PreH19 : (problem_111_pre_z input_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg keys_2 0 output_size_2 keys_l_2 )
  **  (CharArray.undef_seg keys_2 output_size_2 256 )
  **  (IntArray.seg values_2 0 output_size_2 values_l_2 )
  **  (IntArray.undef_seg values_2 output_size_2 256 )
|--
  EX (values_l: (@list Z))  (keys_l: (@list Z))  (output_size: Z)  (values: Z)  (keys: Z) ,
  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= 256) ” 
  &&  “ (output_size = (Zlength (keys_l))) ” 
  &&  “ (output_size = (Zlength (values_l))) ” 
  &&  “ (problem_111_spec_z input_l keys_l values_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg keys 0 output_size keys_l )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l )
  **  (IntArray.undef_seg values output_size 256 )
) \/
(
forall (n: Z) (input_l: (@list Z)) (max: Z) (count_l: (@list Z)) (values_l_2: (@list Z)) (keys_l_2: (@list Z)) (scan: Z) (output_size_2: Z) (values_2: Z) (keys_2: Z) (out: Z) (PreH1 : (scan >= 256)) (PreH2 : (out <> 0)) (PreH3 : (keys_2 <> 0)) (PreH4 : (values_2 <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= scan)) (PreH8 : (scan <= 256)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= scan)) (PreH11 : (output_size_2 = (Zlength (keys_l_2)))) (PreH12 : (output_size_2 = (Zlength (values_l_2)))) (PreH13 : ((Zlength (count_l)) = 256)) (PreH14 : (histogram_scan_state_111 input_l n count_l max )) (PreH15 : (histogram_counts_bounded_111 count_l n )) (PreH16 : (histogram_output_state_111 count_l max scan keys_l_2 values_l_2 )) (PreH17 : (valid_string input_l )) (PreH18 : (ascii_range_z input_l )) (PreH19 : (problem_111_pre_z input_l )) ,
  (CharArray.seg keys_2 0 output_size_2 keys_l_2 )
  **  (CharArray.undef_seg keys_2 output_size_2 256 )
  **  (IntArray.seg values_2 0 output_size_2 values_l_2 )
  **  (IntArray.undef_seg values_2 output_size_2 256 )
|--
  EX (values_l: (@list Z))  (keys_l: (@list Z)) ,
  “ (output_size_2 = (Zlength (keys_l))) ” 
  &&  “ (output_size_2 = (Zlength (keys_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys_2 <> 0) ” 
  &&  “ (values_2 <> 0) ” 
  &&  “ (0 <= (Zlength (keys_l))) ” 
  &&  “ ((Zlength (keys_l)) <= 256) ” 
  &&  “ ((Zlength (keys_l)) = (Zlength (values_l))) ” 
  &&  “ (problem_111_spec_z input_l keys_l values_l ) ”
  &&  (CharArray.seg keys_2 0 (Zlength (keys_l)) keys_l )
  **  (CharArray.undef_seg keys_2 (Zlength (keys_l)) 256 )
  **  (IntArray.seg values_2 0 (Zlength (keys_l)) values_l )
  **  (IntArray.undef_seg values_2 (Zlength (keys_l)) 256 )
).

Definition histogram_partial_solve_wit_1 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (PreH1 : (init < 256)) (PreH2 : (0 <= init)) (PreH3 : (init <= 256)) (PreH4 : (0 <= n)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (valid_string input_l )) (PreH8 : (ascii_range_z input_l )) (PreH9 : (problem_111_pre_z input_l )) ,
  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
  **  (IntArray.undef_seg ( &( "count" ) ) init 256 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (init < 256) ” 
  &&  “ (0 <= init) ” 
  &&  “ (init <= 256) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  (((( &( "count" ) ) + (init * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "count" ) ) (init + 1 ) 256 )
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
.

Definition histogram_partial_solve_wit_2 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (PreH1 : (init >= 256)) (PreH2 : (0 <= init)) (PreH3 : (init <= 256)) (PreH4 : (0 <= n)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (valid_string input_l )) (PreH8 : (ascii_range_z input_l )) (PreH9 : (problem_111_pre_z input_l )) ,
  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
  **  (IntArray.undef_seg ( &( "count" ) ) init 256 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (init >= 256) ” 
  &&  “ (0 <= init) ” 
  &&  “ (init <= 256) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
.

Definition histogram_partial_solve_wit_3_pure := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (init >= 256)) (PreH4 : (0 <= init)) (PreH5 : (init <= 256)) (PreH6 : (0 <= n)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (valid_string input_l )) (PreH10 : (ascii_range_z input_l )) (PreH11 : (problem_111_pre_z input_l )) ,
  ((( &( "max" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
|--
  “ (0 <= 256) ” 
  &&  “ (256 < INT_MAX) ”
.

Definition histogram_partial_solve_wit_3_aux := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= (n + 1 ))) (PreH3 : (init >= 256)) (PreH4 : (0 <= init)) (PreH5 : (init <= 256)) (PreH6 : (0 <= n)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (valid_string input_l )) (PreH10 : (ascii_range_z input_l )) (PreH11 : (problem_111_pre_z input_l )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
|--
  “ (0 <= 256) ” 
  &&  “ (256 < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (init >= 256) ” 
  &&  “ (0 <= init) ” 
  &&  “ (init <= 256) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
.

Definition histogram_partial_solve_wit_3 := histogram_partial_solve_wit_3_pure -> histogram_partial_solve_wit_3_aux.

Definition histogram_partial_solve_wit_4_pure := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (init >= 256)) (PreH5 : (0 <= init)) (PreH6 : (init <= 256)) (PreH7 : (0 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : ((Zlength (input_l)) = n)) (PreH10 : (valid_string input_l )) (PreH11 : (ascii_range_z input_l )) (PreH12 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full retval_2 256 )
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "init" ) )) # Int  |-> init)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
|--
  “ (0 <= 256) ” 
  &&  “ (256 < INT_MAX) ”
.

Definition histogram_partial_solve_wit_4_aux := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (init: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (init >= 256)) (PreH5 : (0 <= init)) (PreH6 : (init <= 256)) (PreH7 : (0 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : ((Zlength (input_l)) = n)) (PreH10 : (valid_string input_l )) (PreH11 : (ascii_range_z input_l )) (PreH12 : (problem_111_pre_z input_l )) ,
  (CharArray.undef_full retval_2 256 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
|--
  “ (0 <= 256) ” 
  &&  “ (256 < INT_MAX) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (init >= 256) ” 
  &&  “ (0 <= init) ” 
  &&  “ (init <= 256) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  (CharArray.undef_full retval_2 256 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg ( &( "count" ) ) 0 init (zeros (init)) )
.

Definition histogram_partial_solve_wit_4 := histogram_partial_solve_wit_4_pure -> histogram_partial_solve_wit_4_aux.

Definition histogram_partial_solve_wit_5 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : (out <> 0)) (PreH2 : (keys <> 0)) (PreH3 : (values <> 0)) (PreH4 : (n < INT_MAX)) (PreH5 : ((Zlength (input_l)) = n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= max)) (PreH9 : (max <= i)) (PreH10 : ((Zlength (count_l)) = 256)) (PreH11 : (histogram_scan_state_111 input_l i count_l max )) (PreH12 : (histogram_counts_bounded_111 count_l i )) (PreH13 : (valid_string input_l )) (PreH14 : (ascii_range_z input_l )) (PreH15 : (problem_111_pre_z input_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= max) ” 
  &&  “ (max <= i) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l i count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l i ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  (((test_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i test_pre i 0 (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_partial_solve_wit_6 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (n < INT_MAX)) (PreH6 : ((Zlength (input_l)) = n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= max)) (PreH10 : (max <= i)) (PreH11 : ((Zlength (count_l)) = 256)) (PreH12 : (histogram_scan_state_111 input_l i count_l max )) (PreH13 : (histogram_counts_bounded_111 count_l i )) (PreH14 : (valid_string input_l )) (PreH15 : (ascii_range_z input_l )) (PreH16 : (problem_111_pre_z input_l )) ,
  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= max) ” 
  &&  “ (max <= i) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l i count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l i ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  (((test_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i test_pre i 0 (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_partial_solve_wit_7 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (max: Z) (i: Z) (values: Z) (keys: Z) (out: Z) (PreH1 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 32)) (PreH2 : ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH3 : (out <> 0)) (PreH4 : (keys <> 0)) (PreH5 : (values <> 0)) (PreH6 : (n < INT_MAX)) (PreH7 : ((Zlength (input_l)) = n)) (PreH8 : (0 <= i)) (PreH9 : (i <= n)) (PreH10 : (0 <= max)) (PreH11 : (max <= i)) (PreH12 : ((Zlength (count_l)) = 256)) (PreH13 : (histogram_scan_state_111 input_l i count_l max )) (PreH14 : (histogram_counts_bounded_111 count_l i )) (PreH15 : (valid_string input_l )) (PreH16 : (ascii_range_z input_l )) (PreH17 : (problem_111_pre_z input_l )) ,
  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 32) ” 
  &&  “ ((Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0) <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= max) ” 
  &&  “ (max <= i) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l i count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l i ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  (((test_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (input_l) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i test_pre i 0 (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_partial_solve_wit_8 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (out <> 0)) (PreH2 : (keys <> 0)) (PreH3 : (values <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (0 <= ch)) (PreH7 : (ch < 256)) (PreH8 : (ch <> 32)) (PreH9 : (ch = (Znth (i) (input_l) (0)))) (PreH10 : (n < INT_MAX)) (PreH11 : ((Zlength (input_l)) = n)) (PreH12 : (0 <= max)) (PreH13 : (max <= i)) (PreH14 : ((Zlength (count_l)) = 256)) (PreH15 : (histogram_scan_state_111 input_l i count_l max )) (PreH16 : (histogram_counts_bounded_111 count_l i )) (PreH17 : (valid_string input_l )) (PreH18 : (ascii_range_z input_l )) (PreH19 : (problem_111_pre_z input_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch < 256) ” 
  &&  “ (ch <> 32) ” 
  &&  “ (ch = (Znth (i) (input_l) (0))) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= max) ” 
  &&  “ (max <= i) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l i count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l i ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  (((( &( "count" ) ) + (ch * sizeof(INT)))) # Int  |-> (Znth ch count_l 0))
  **  (IntArray.missing_i ( &( "count" ) ) ch 0 256 count_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_partial_solve_wit_9 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (i: Z) (ch: Z) (max: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (out <> 0)) (PreH3 : (keys <> 0)) (PreH4 : (values <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < n)) (PreH7 : (0 <= ch)) (PreH8 : (ch < 256)) (PreH9 : (ch <> 32)) (PreH10 : (ch = (Znth (i) (input_l) (0)))) (PreH11 : (n < INT_MAX)) (PreH12 : ((Zlength (input_l)) = n)) (PreH13 : (0 <= max)) (PreH14 : (max <= i)) (PreH15 : ((Zlength (count_l)) = 256)) (PreH16 : (histogram_scan_state_111 input_l i count_l max )) (PreH17 : (histogram_counts_bounded_111 count_l i )) (PreH18 : (valid_string input_l )) (PreH19 : (ascii_range_z input_l )) (PreH20 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch < 256) ” 
  &&  “ (ch <> 32) ” 
  &&  “ (ch = (Znth (i) (input_l) (0))) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= max) ” 
  &&  “ (max <= i) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l i count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l i ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  (((( &( "count" ) ) + (ch * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "count" ) ) ch 0 256 count_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_partial_solve_wit_10 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (keys_l: (@list Z)) (values_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (out <> 0)) (PreH2 : (keys <> 0)) (PreH3 : (values <> 0)) (PreH4 : (n < INT_MAX)) (PreH5 : ((Zlength (input_l)) = n)) (PreH6 : (0 <= scan)) (PreH7 : (scan < 256)) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= scan)) (PreH10 : (output_size = (Zlength (keys_l)))) (PreH11 : (output_size = (Zlength (values_l)))) (PreH12 : ((Zlength (count_l)) = 256)) (PreH13 : (histogram_scan_state_111 input_l n count_l max )) (PreH14 : (histogram_counts_bounded_111 count_l n )) (PreH15 : (histogram_output_state_111 count_l max scan keys_l values_l )) (PreH16 : (valid_string input_l )) (PreH17 : (ascii_range_z input_l )) (PreH18 : (problem_111_pre_z input_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  (CharArray.seg keys 0 output_size keys_l )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l )
  **  (IntArray.undef_seg values output_size 256 )
|--
  “ (0 <= (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= scan) ” 
  &&  “ (scan < 256) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= scan) ” 
  &&  “ (output_size = (Zlength (keys_l))) ” 
  &&  “ (output_size = (Zlength (values_l))) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l n count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l n ) ” 
  &&  “ (histogram_output_state_111 count_l max scan keys_l values_l ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  (((( &( "count" ) ) + (scan * sizeof(INT)))) # Int  |-> (Znth scan count_l 0))
  **  (IntArray.missing_i ( &( "count" ) ) scan 0 256 count_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg keys 0 output_size keys_l )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l )
  **  (IntArray.undef_seg values output_size 256 )
.

Definition histogram_partial_solve_wit_11 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (keys_l: (@list Z)) (values_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth scan count_l 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l)))) (PreH14 : (output_size = (Zlength (values_l)))) (PreH15 : ((Zlength (count_l)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l max )) (PreH17 : (histogram_counts_bounded_111 count_l n )) (PreH18 : (histogram_output_state_111 count_l max scan keys_l values_l )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg keys 0 output_size keys_l )
  **  (CharArray.undef_seg keys output_size 256 )
  **  (IntArray.seg values 0 output_size values_l )
  **  (IntArray.undef_seg values output_size 256 )
|--
  “ (max > 0) ” 
  &&  “ ((Znth scan count_l 0) = max) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= scan) ” 
  &&  “ (scan < 256) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= scan) ” 
  &&  “ (output_size = (Zlength (keys_l))) ” 
  &&  “ (output_size = (Zlength (values_l))) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l n count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l n ) ” 
  &&  “ (histogram_output_state_111 count_l max scan keys_l values_l ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  (((keys + (output_size * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i keys output_size output_size 256 )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.seg keys 0 output_size keys_l )
  **  (IntArray.seg values 0 output_size values_l )
  **  (IntArray.undef_seg values output_size 256 )
.

Definition histogram_partial_solve_wit_12 := 
forall (test_pre: Z) (n: Z) (input_l: (@list Z)) (count_l: (@list Z)) (keys_l: (@list Z)) (values_l: (@list Z)) (out: Z) (keys: Z) (values: Z) (scan: Z) (output_size: Z) (max: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth scan count_l 0) = max)) (PreH3 : (0 <= (n + 1 ))) (PreH4 : (out <> 0)) (PreH5 : (keys <> 0)) (PreH6 : (values <> 0)) (PreH7 : (n < INT_MAX)) (PreH8 : ((Zlength (input_l)) = n)) (PreH9 : (0 <= scan)) (PreH10 : (scan < 256)) (PreH11 : (0 <= output_size)) (PreH12 : (output_size <= scan)) (PreH13 : (output_size = (Zlength (keys_l)))) (PreH14 : (output_size = (Zlength (values_l)))) (PreH15 : ((Zlength (count_l)) = 256)) (PreH16 : (histogram_scan_state_111 input_l n count_l max )) (PreH17 : (histogram_counts_bounded_111 count_l n )) (PreH18 : (histogram_output_state_111 count_l max scan keys_l values_l )) (PreH19 : (valid_string input_l )) (PreH20 : (ascii_range_z input_l )) (PreH21 : (problem_111_pre_z input_l )) ,
  (CharArray.seg keys 0 (output_size + 1 ) (app (keys_l) ((cons (scan) ((@nil Z))))) )
  **  (CharArray.undef_seg keys (output_size + 1 ) 256 )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg values 0 output_size values_l )
  **  (IntArray.undef_seg values output_size 256 )
|--
  “ (max > 0) ” 
  &&  “ ((Znth scan count_l 0) = max) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (input_l)) = n) ” 
  &&  “ (0 <= scan) ” 
  &&  “ (scan < 256) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= scan) ” 
  &&  “ (output_size = (Zlength (keys_l))) ” 
  &&  “ (output_size = (Zlength (values_l))) ” 
  &&  “ ((Zlength (count_l)) = 256) ” 
  &&  “ (histogram_scan_state_111 input_l n count_l max ) ” 
  &&  “ (histogram_counts_bounded_111 count_l n ) ” 
  &&  “ (histogram_output_state_111 count_l max scan keys_l values_l ) ” 
  &&  “ (valid_string input_l ) ” 
  &&  “ (ascii_range_z input_l ) ” 
  &&  “ (problem_111_pre_z input_l ) ”
  &&  (((values + (output_size * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg values (output_size + 1 ) 256 )
  **  (CharArray.seg keys 0 (output_size + 1 ) (app (keys_l) ((cons (scan) ((@nil Z))))) )
  **  (CharArray.undef_seg keys (output_size + 1 ) 256 )
  **  (IntArray.full ( &( "count" ) ) 256 count_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharArray.full test_pre (n + 1 ) (app (input_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg values 0 output_size values_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_histogram_safety_wit_1 : histogram_safety_wit_1.
Axiom proof_of_histogram_safety_wit_2 : histogram_safety_wit_2.
Axiom proof_of_histogram_safety_wit_3 : histogram_safety_wit_3.
Axiom proof_of_histogram_safety_wit_4 : histogram_safety_wit_4.
Axiom proof_of_histogram_safety_wit_5 : histogram_safety_wit_5.
Axiom proof_of_histogram_safety_wit_6 : histogram_safety_wit_6.
Axiom proof_of_histogram_safety_wit_7 : histogram_safety_wit_7.
Axiom proof_of_histogram_safety_wit_8 : histogram_safety_wit_8.
Axiom proof_of_histogram_safety_wit_9 : histogram_safety_wit_9.
Axiom proof_of_histogram_safety_wit_10 : histogram_safety_wit_10.
Axiom proof_of_histogram_safety_wit_11 : histogram_safety_wit_11.
Axiom proof_of_histogram_safety_wit_12 : histogram_safety_wit_12.
Axiom proof_of_histogram_safety_wit_13 : histogram_safety_wit_13.
Axiom proof_of_histogram_safety_wit_14 : histogram_safety_wit_14.
Axiom proof_of_histogram_safety_wit_15 : histogram_safety_wit_15.
Axiom proof_of_histogram_safety_wit_16 : histogram_safety_wit_16.
Axiom proof_of_histogram_safety_wit_17 : histogram_safety_wit_17.
Axiom proof_of_histogram_safety_wit_18 : histogram_safety_wit_18.
Axiom proof_of_histogram_safety_wit_19 : histogram_safety_wit_19.
Axiom proof_of_histogram_safety_wit_20 : histogram_safety_wit_20.
Axiom proof_of_histogram_safety_wit_21 : histogram_safety_wit_21.
Axiom proof_of_histogram_safety_wit_22 : histogram_safety_wit_22.
Axiom proof_of_histogram_safety_wit_23 : histogram_safety_wit_23.
Axiom proof_of_histogram_safety_wit_24 : histogram_safety_wit_24.
Axiom proof_of_histogram_safety_wit_25 : histogram_safety_wit_25.
Axiom proof_of_histogram_safety_wit_26 : histogram_safety_wit_26.
Axiom proof_of_histogram_safety_wit_27 : histogram_safety_wit_27.
Axiom proof_of_histogram_safety_wit_28 : histogram_safety_wit_28.
Axiom proof_of_histogram_safety_wit_29 : histogram_safety_wit_29.
Axiom proof_of_histogram_safety_wit_30 : histogram_safety_wit_30.
Axiom proof_of_histogram_safety_wit_31 : histogram_safety_wit_31.
Axiom proof_of_histogram_safety_wit_32 : histogram_safety_wit_32.
Axiom proof_of_histogram_safety_wit_33 : histogram_safety_wit_33.
Axiom proof_of_histogram_safety_wit_34 : histogram_safety_wit_34.
Axiom proof_of_histogram_safety_wit_35 : histogram_safety_wit_35.
Axiom proof_of_histogram_entail_wit_1 : histogram_entail_wit_1.
Axiom proof_of_histogram_entail_wit_2 : histogram_entail_wit_2.
Axiom proof_of_histogram_entail_wit_3 : histogram_entail_wit_3.
Axiom proof_of_histogram_entail_wit_4 : histogram_entail_wit_4.
Axiom proof_of_histogram_entail_wit_5_1 : histogram_entail_wit_5_1.
Axiom proof_of_histogram_entail_wit_5_2 : histogram_entail_wit_5_2.
Axiom proof_of_histogram_entail_wit_5_3 : histogram_entail_wit_5_3.
Axiom proof_of_histogram_entail_wit_6 : histogram_entail_wit_6.
Axiom proof_of_histogram_entail_wit_7 : histogram_entail_wit_7.
Axiom proof_of_histogram_entail_wit_8_1 : histogram_entail_wit_8_1.
Axiom proof_of_histogram_entail_wit_8_2 : histogram_entail_wit_8_2.
Axiom proof_of_histogram_entail_wit_8_3 : histogram_entail_wit_8_3.
Axiom proof_of_histogram_return_wit_1 : histogram_return_wit_1.
Axiom proof_of_histogram_partial_solve_wit_1 : histogram_partial_solve_wit_1.
Axiom proof_of_histogram_partial_solve_wit_2 : histogram_partial_solve_wit_2.
Axiom proof_of_histogram_partial_solve_wit_3_pure : histogram_partial_solve_wit_3_pure.
Axiom proof_of_histogram_partial_solve_wit_3 : histogram_partial_solve_wit_3.
Axiom proof_of_histogram_partial_solve_wit_4_pure : histogram_partial_solve_wit_4_pure.
Axiom proof_of_histogram_partial_solve_wit_4 : histogram_partial_solve_wit_4.
Axiom proof_of_histogram_partial_solve_wit_5 : histogram_partial_solve_wit_5.
Axiom proof_of_histogram_partial_solve_wit_6 : histogram_partial_solve_wit_6.
Axiom proof_of_histogram_partial_solve_wit_7 : histogram_partial_solve_wit_7.
Axiom proof_of_histogram_partial_solve_wit_8 : histogram_partial_solve_wit_8.
Axiom proof_of_histogram_partial_solve_wit_9 : histogram_partial_solve_wit_9.
Axiom proof_of_histogram_partial_solve_wit_10 : histogram_partial_solve_wit_10.
Axiom proof_of_histogram_partial_solve_wit_11 : histogram_partial_solve_wit_11.
Axiom proof_of_histogram_partial_solve_wit_12 : histogram_partial_solve_wit_12.

End VC_Correct.
