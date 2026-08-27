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
Require Import coins_22.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function filter_integers -----*)

Definition filter_integers_safety_wit_1 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= values_size_pre)) (PreH3 : (values_size_pre < INT_MAX)) (PreH4 : (types_l = (py_value_tags (input_l)))) (PreH5 : (ints_l = (py_value_payloads (input_l)))) (PreH6 : (values_size_pre = (Zlength (types_l)))) (PreH7 : (values_size_pre = (Zlength (ints_l)))) (PreH8 : (problem_22_pre_z input_l )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  (IntArray.full types_pre values_size_pre types_l )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_integers_safety_wit_2 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= values_size_pre)) (PreH4 : (values_size_pre < INT_MAX)) (PreH5 : (types_l = (py_value_tags (input_l)))) (PreH6 : (ints_l = (py_value_payloads (input_l)))) (PreH7 : (values_size_pre = (Zlength (types_l)))) (PreH8 : (values_size_pre = (Zlength (ints_l)))) (PreH9 : (problem_22_pre_z input_l )) ,
  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 values_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  (IntArray.full types_pre values_size_pre types_l )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_integers_safety_wit_3 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (PreH1 : (i < values_size_pre)) (PreH2 : (types_l = (py_value_tags (input_l)))) (PreH3 : (ints_l = (py_value_payloads (input_l)))) (PreH4 : (values_size_pre = (Zlength (types_l)))) (PreH5 : (values_size_pre = (Zlength (ints_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= values_size_pre)) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_l)))) (PreH11 : (output_l = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) ,
  (IntArray.full types_pre values_size_pre types_l )
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size values_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_integers_safety_wit_4 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (PreH1 : ((Znth i types_l 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_l)))) (PreH12 : (output_l = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output_l) ((cons ((Znth i ints_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) values_size_pre )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.full types_pre values_size_pre types_l )
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
|--
  “ ((output_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (output_size + 1 )) ”
.

Definition filter_integers_safety_wit_5 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (PreH1 : ((Znth i types_l 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_l)))) (PreH12 : (output_l = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output_l) ((cons ((Znth i ints_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) values_size_pre )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.full types_pre values_size_pre types_l )
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition filter_integers_safety_wit_6 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (PreH1 : ((Znth i types_l 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_l)))) (PreH12 : (output_l = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output_l) ((cons ((Znth i ints_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) values_size_pre )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.full types_pre values_size_pre types_l )
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition filter_integers_safety_wit_7 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (PreH1 : ((Znth i types_l 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_l)))) (PreH12 : (output_l = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output_l) ((cons ((Znth i ints_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) values_size_pre )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.full types_pre values_size_pre types_l )
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size + 1 ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition filter_integers_safety_wit_8 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (PreH1 : ((Znth i types_l 0) <> 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_l)))) (PreH12 : (output_l = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.full types_pre values_size_pre types_l )
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size values_size_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition filter_integers_safety_wit_9 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (PreH1 : ((Znth i types_l 0) <> 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_l)))) (PreH12 : (output_l = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.full types_pre values_size_pre types_l )
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size values_size_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition filter_integers_entail_wit_1 := 
(
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= values_size_pre)) (PreH4 : (values_size_pre < INT_MAX)) (PreH5 : (types_l = (py_value_tags (input_l)))) (PreH6 : (ints_l = (py_value_payloads (input_l)))) (PreH7 : (values_size_pre = (Zlength (types_l)))) (PreH8 : (values_size_pre = (Zlength (ints_l)))) (PreH9 : (problem_22_pre_z input_l )) ,
  (IntArray.undef_full retval_2 values_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full types_pre values_size_pre types_l )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  “ (types_l = (py_value_tags (input_l))) ” 
  &&  “ (ints_l = (py_value_payloads (input_l))) ” 
  &&  “ (values_size_pre = (Zlength (types_l))) ” 
  &&  “ (values_size_pre = (Zlength (ints_l))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= values_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= 0) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (output_l = (filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l))))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full types_pre values_size_pre types_l )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.seg retval_2 0 output_size output_l )
  **  (IntArray.undef_seg retval_2 output_size values_size_pre )
) \/
(
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= values_size_pre)) (PreH4 : (values_size_pre < INT_MAX)) (PreH5 : (types_l = (py_value_tags (input_l)))) (PreH6 : (ints_l = (py_value_payloads (input_l)))) (PreH7 : (values_size_pre = (Zlength (types_l)))) (PreH8 : (values_size_pre = (Zlength (ints_l)))) (PreH9 : (problem_22_pre_z input_l )) ,
  (IntArray.undef_full retval_2 values_size_pre )
|--
  “ ((Zlength ((filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l)))))) <= 0) ” 
  &&  “ (0 <= (Zlength ((filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l))))))) ” 
  &&  “ (0 = (Zlength ((filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l))))))) ” 
  &&  “ (0 = (Zlength ((filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l))))))) ” 
  &&  “ (0 = (Zlength ((filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l))))))) ”
  &&  (IntArray.seg retval_2 0 (Zlength ((filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l)))))) (filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l)))) )
  **  (IntArray.undef_seg retval_2 (Zlength ((filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l)))))) values_size_pre )
).

Definition filter_integers_entail_wit_1_split_goal_1 := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= values_size_pre)) (PreH4 : (values_size_pre < INT_MAX)) (PreH5 : (types_l = (py_value_tags (input_l)))) (PreH6 : (ints_l = (py_value_payloads (input_l)))) (PreH7 : (values_size_pre = (Zlength (types_l)))) (PreH8 : (values_size_pre = (Zlength (ints_l)))) (PreH9 : (problem_22_pre_z input_l )) ,
  (IntArray.undef_full retval_2 values_size_pre )
|--
  “ ((Zlength ((filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l)))))) <= 0) ”
.

Definition filter_integers_entail_wit_1_split_goal_2 := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= values_size_pre)) (PreH4 : (values_size_pre < INT_MAX)) (PreH5 : (types_l = (py_value_tags (input_l)))) (PreH6 : (ints_l = (py_value_payloads (input_l)))) (PreH7 : (values_size_pre = (Zlength (types_l)))) (PreH8 : (values_size_pre = (Zlength (ints_l)))) (PreH9 : (problem_22_pre_z input_l )) ,
  (IntArray.undef_full retval_2 values_size_pre )
|--
  “ (0 <= (Zlength ((filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l))))))) ”
.

Definition filter_integers_entail_wit_1_split_goal_3 := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= values_size_pre)) (PreH4 : (values_size_pre < INT_MAX)) (PreH5 : (types_l = (py_value_tags (input_l)))) (PreH6 : (ints_l = (py_value_payloads (input_l)))) (PreH7 : (values_size_pre = (Zlength (types_l)))) (PreH8 : (values_size_pre = (Zlength (ints_l)))) (PreH9 : (problem_22_pre_z input_l )) ,
  (IntArray.undef_full retval_2 values_size_pre )
|--
  “ (0 = (Zlength ((filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l))))))) ”
.

Definition filter_integers_entail_wit_1_split_goal_4 := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= values_size_pre)) (PreH4 : (values_size_pre < INT_MAX)) (PreH5 : (types_l = (py_value_tags (input_l)))) (PreH6 : (ints_l = (py_value_payloads (input_l)))) (PreH7 : (values_size_pre = (Zlength (types_l)))) (PreH8 : (values_size_pre = (Zlength (ints_l)))) (PreH9 : (problem_22_pre_z input_l )) ,
  (IntArray.undef_full retval_2 values_size_pre )
|--
  “ (0 = (Zlength ((filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l))))))) ”
.

Definition filter_integers_entail_wit_1_split_goal_5 := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= values_size_pre)) (PreH4 : (values_size_pre < INT_MAX)) (PreH5 : (types_l = (py_value_tags (input_l)))) (PreH6 : (ints_l = (py_value_payloads (input_l)))) (PreH7 : (values_size_pre = (Zlength (types_l)))) (PreH8 : (values_size_pre = (Zlength (ints_l)))) (PreH9 : (problem_22_pre_z input_l )) ,
  (IntArray.undef_full retval_2 values_size_pre )
|--
  “ (0 = (Zlength ((filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l))))))) ”
.

Definition filter_integers_entail_wit_1_split_goal_spatial := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= values_size_pre)) (PreH4 : (values_size_pre < INT_MAX)) (PreH5 : (types_l = (py_value_tags (input_l)))) (PreH6 : (ints_l = (py_value_payloads (input_l)))) (PreH7 : (values_size_pre = (Zlength (types_l)))) (PreH8 : (values_size_pre = (Zlength (ints_l)))) (PreH9 : (problem_22_pre_z input_l )) ,
  (IntArray.undef_full retval_2 values_size_pre )
|--
  (IntArray.seg retval_2 0 (Zlength ((filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l)))))) (filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l)))) )
  **  (IntArray.undef_seg retval_2 (Zlength ((filter_tagged ((sublist (0) (0) (types_l))) ((sublist (0) (0) (ints_l)))))) values_size_pre )
.

Definition filter_integers_entail_wit_2_1 := 
(
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 (output_size_2 + 1 ) (app (output_l_2) ((cons ((Znth i ints_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size_2 + 1 ) values_size_pre )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.full types_pre values_size_pre types_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (output_size_2 + 1 ))
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  “ (types_l = (py_value_tags (input_l))) ” 
  &&  “ (ints_l = (py_value_payloads (input_l))) ” 
  &&  “ (values_size_pre = (Zlength (types_l))) ” 
  &&  “ (values_size_pre = (Zlength (ints_l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= values_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (output_l = (filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full types_pre values_size_pre types_l )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size values_size_pre )
) \/
(
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 (output_size_2 + 1 ) (app (output_l_2) ((cons ((Znth i ints_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size_2 + 1 ) values_size_pre )
|--
  “ ((Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))))) <= (i + 1 )) ” 
  &&  “ (0 <= (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ” 
  &&  “ ((output_size_2 + 1 ) = (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ” 
  &&  “ ((output_size_2 + 1 ) = (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ” 
  &&  “ ((output_size_2 + 1 ) = (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ”
  &&  (IntArray.seg data 0 (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))))) (filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))) )
  **  (IntArray.undef_seg data (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))))) values_size_pre )
).

Definition filter_integers_entail_wit_2_1_split_goal_1 := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 (output_size_2 + 1 ) (app (output_l_2) ((cons ((Znth i ints_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size_2 + 1 ) values_size_pre )
|--
  “ ((Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))))) <= (i + 1 )) ”
.

Definition filter_integers_entail_wit_2_1_split_goal_2 := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 (output_size_2 + 1 ) (app (output_l_2) ((cons ((Znth i ints_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size_2 + 1 ) values_size_pre )
|--
  “ (0 <= (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ”
.

Definition filter_integers_entail_wit_2_1_split_goal_3 := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 (output_size_2 + 1 ) (app (output_l_2) ((cons ((Znth i ints_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size_2 + 1 ) values_size_pre )
|--
  “ ((output_size_2 + 1 ) = (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ”
.

Definition filter_integers_entail_wit_2_1_split_goal_4 := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 (output_size_2 + 1 ) (app (output_l_2) ((cons ((Znth i ints_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size_2 + 1 ) values_size_pre )
|--
  “ ((output_size_2 + 1 ) = (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ”
.

Definition filter_integers_entail_wit_2_1_split_goal_5 := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 (output_size_2 + 1 ) (app (output_l_2) ((cons ((Znth i ints_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size_2 + 1 ) values_size_pre )
|--
  “ ((output_size_2 + 1 ) = (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ”
.

Definition filter_integers_entail_wit_2_1_split_goal_spatial := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 (output_size_2 + 1 ) (app (output_l_2) ((cons ((Znth i ints_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size_2 + 1 ) values_size_pre )
|--
  (IntArray.seg data 0 (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))))) (filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))) )
  **  (IntArray.undef_seg data (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))))) values_size_pre )
.

Definition filter_integers_entail_wit_2_2 := 
(
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) <> 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.full types_pre values_size_pre types_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 values_size_pre )
|--
  EX (output_l: (@list Z))  (output_size: Z) ,
  “ (types_l = (py_value_tags (input_l))) ” 
  &&  “ (ints_l = (py_value_payloads (input_l))) ” 
  &&  “ (values_size_pre = (Zlength (types_l))) ” 
  &&  “ (values_size_pre = (Zlength (ints_l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= values_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (output_l = (filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full types_pre values_size_pre types_l )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size values_size_pre )
) \/
(
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) <> 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 values_size_pre )
|--
  “ ((Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))))) <= (i + 1 )) ” 
  &&  “ (0 <= (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ” 
  &&  “ (output_size_2 = (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ” 
  &&  “ (output_size_2 = (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ” 
  &&  “ (output_size_2 = (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ”
  &&  (IntArray.seg data 0 (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))))) (filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))) )
  **  (IntArray.undef_seg data (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))))) values_size_pre )
).

Definition filter_integers_entail_wit_2_2_split_goal_1 := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) <> 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 values_size_pre )
|--
  “ ((Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))))) <= (i + 1 )) ”
.

Definition filter_integers_entail_wit_2_2_split_goal_2 := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) <> 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 values_size_pre )
|--
  “ (0 <= (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ”
.

Definition filter_integers_entail_wit_2_2_split_goal_3 := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) <> 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 values_size_pre )
|--
  “ (output_size_2 = (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ”
.

Definition filter_integers_entail_wit_2_2_split_goal_4 := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) <> 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 values_size_pre )
|--
  “ (output_size_2 = (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ”
.

Definition filter_integers_entail_wit_2_2_split_goal_5 := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) <> 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 values_size_pre )
|--
  “ (output_size_2 = (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l))))))) ”
.

Definition filter_integers_entail_wit_2_2_split_goal_spatial := 
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : ((Znth i types_l 0) <> 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size_2)) (PreH10 : (output_size_2 <= i)) (PreH11 : (output_size_2 = (Zlength (output_l_2)))) (PreH12 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.seg data 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data output_size_2 values_size_pre )
|--
  (IntArray.seg data 0 (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))))) (filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))) )
  **  (IntArray.undef_seg data (Zlength ((filter_tagged ((sublist (0) ((i + 1 )) (types_l))) ((sublist (0) ((i + 1 )) (ints_l)))))) values_size_pre )
.

Definition filter_integers_return_wit_1 := 
(
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data_2: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : (i >= values_size_pre)) (PreH2 : (types_l = (py_value_tags (input_l)))) (PreH3 : (ints_l = (py_value_payloads (input_l)))) (PreH4 : (values_size_pre = (Zlength (types_l)))) (PreH5 : (values_size_pre = (Zlength (ints_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= values_size_pre)) (PreH8 : (0 <= output_size_2)) (PreH9 : (output_size_2 <= i)) (PreH10 : (output_size_2 = (Zlength (output_l_2)))) (PreH11 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH12 : (out <> 0)) (PreH13 : (data_2 <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.full types_pre values_size_pre types_l )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.seg data_2 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data_2 output_size_2 values_size_pre )
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= values_size_pre) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (problem_22_spec_z input_l output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full types_pre values_size_pre types_l )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size values_size_pre )
) \/
(
forall (values_size_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data_2: Z) (out: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (PreH1 : (i >= values_size_pre)) (PreH2 : (types_l = (py_value_tags (input_l)))) (PreH3 : (ints_l = (py_value_payloads (input_l)))) (PreH4 : (values_size_pre = (Zlength (types_l)))) (PreH5 : (values_size_pre = (Zlength (ints_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= values_size_pre)) (PreH8 : (0 <= output_size_2)) (PreH9 : (output_size_2 <= i)) (PreH10 : (output_size_2 = (Zlength (output_l_2)))) (PreH11 : (output_l_2 = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH12 : (out <> 0)) (PreH13 : (data_2 <> 0)) ,
  (IntArray.seg data_2 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data_2 output_size_2 values_size_pre )
|--
  EX (output_l: (@list Z)) ,
  “ (output_size_2 = (Zlength (output_l))) ” 
  &&  “ (output_size_2 = (Zlength (output_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data_2 <> 0) ” 
  &&  “ (0 <= (Zlength (output_l))) ” 
  &&  “ ((Zlength (output_l)) <= values_size_pre) ” 
  &&  “ (problem_22_spec_z input_l output_l ) ”
  &&  (IntArray.seg data_2 0 (Zlength (output_l)) output_l )
  **  (IntArray.undef_seg data_2 (Zlength (output_l)) values_size_pre )
).

Definition filter_integers_partial_solve_wit_1 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (PreH1 : (0 <= values_size_pre)) (PreH2 : (values_size_pre < INT_MAX)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (problem_22_pre_z input_l )) ,
  (IntArray.full types_pre values_size_pre types_l )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
|--
  “ (0 <= values_size_pre) ” 
  &&  “ (values_size_pre < INT_MAX) ” 
  &&  “ (types_l = (py_value_tags (input_l))) ” 
  &&  “ (ints_l = (py_value_payloads (input_l))) ” 
  &&  “ (values_size_pre = (Zlength (types_l))) ” 
  &&  “ (values_size_pre = (Zlength (ints_l))) ” 
  &&  “ (problem_22_pre_z input_l ) ”
  &&  (IntArray.full types_pre values_size_pre types_l )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
.

Definition filter_integers_partial_solve_wit_2_pure := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= values_size_pre)) (PreH3 : (values_size_pre < INT_MAX)) (PreH4 : (types_l = (py_value_tags (input_l)))) (PreH5 : (ints_l = (py_value_payloads (input_l)))) (PreH6 : (values_size_pre = (Zlength (types_l)))) (PreH7 : (values_size_pre = (Zlength (ints_l)))) (PreH8 : (problem_22_pre_z input_l )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  (IntArray.full types_pre values_size_pre types_l )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
|--
  “ (0 <= values_size_pre) ” 
  &&  “ (values_size_pre < INT_MAX) ”
.

Definition filter_integers_partial_solve_wit_2_aux := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= values_size_pre)) (PreH3 : (values_size_pre < INT_MAX)) (PreH4 : (types_l = (py_value_tags (input_l)))) (PreH5 : (ints_l = (py_value_payloads (input_l)))) (PreH6 : (values_size_pre = (Zlength (types_l)))) (PreH7 : (values_size_pre = (Zlength (ints_l)))) (PreH8 : (problem_22_pre_z input_l )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full types_pre values_size_pre types_l )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
|--
  “ (0 <= values_size_pre) ” 
  &&  “ (values_size_pre < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= values_size_pre) ” 
  &&  “ (values_size_pre < INT_MAX) ” 
  &&  “ (types_l = (py_value_tags (input_l))) ” 
  &&  “ (ints_l = (py_value_payloads (input_l))) ” 
  &&  “ (values_size_pre = (Zlength (types_l))) ” 
  &&  “ (values_size_pre = (Zlength (ints_l))) ” 
  &&  “ (problem_22_pre_z input_l ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full types_pre values_size_pre types_l )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
.

Definition filter_integers_partial_solve_wit_2 := filter_integers_partial_solve_wit_2_pure -> filter_integers_partial_solve_wit_2_aux.

Definition filter_integers_partial_solve_wit_3 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (PreH1 : (i < values_size_pre)) (PreH2 : (types_l = (py_value_tags (input_l)))) (PreH3 : (ints_l = (py_value_payloads (input_l)))) (PreH4 : (values_size_pre = (Zlength (types_l)))) (PreH5 : (values_size_pre = (Zlength (ints_l)))) (PreH6 : (0 <= i)) (PreH7 : (i <= values_size_pre)) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_l)))) (PreH11 : (output_l = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full types_pre values_size_pre types_l )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size values_size_pre )
|--
  “ (i < values_size_pre) ” 
  &&  “ (types_l = (py_value_tags (input_l))) ” 
  &&  “ (ints_l = (py_value_payloads (input_l))) ” 
  &&  “ (values_size_pre = (Zlength (types_l))) ” 
  &&  “ (values_size_pre = (Zlength (ints_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= values_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (output_l = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (((types_pre + (i * sizeof(INT)))) # Int  |-> (Znth i types_l 0))
  **  (IntArray.missing_i types_pre i 0 values_size_pre types_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size values_size_pre )
.

Definition filter_integers_partial_solve_wit_4 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (PreH1 : ((Znth i types_l 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_l)))) (PreH12 : (output_l = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.full types_pre values_size_pre types_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size values_size_pre )
|--
  “ ((Znth i types_l 0) = 0) ” 
  &&  “ (i < values_size_pre) ” 
  &&  “ (types_l = (py_value_tags (input_l))) ” 
  &&  “ (ints_l = (py_value_payloads (input_l))) ” 
  &&  “ (values_size_pre = (Zlength (types_l))) ” 
  &&  “ (values_size_pre = (Zlength (ints_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= values_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (output_l = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (((int_values_pre + (i * sizeof(INT)))) # Int  |-> (Znth i ints_l 0))
  **  (IntArray.missing_i int_values_pre i 0 values_size_pre ints_l )
  **  (IntArray.full types_pre values_size_pre types_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size values_size_pre )
.

Definition filter_integers_partial_solve_wit_5 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (ints_l: (@list Z)) (types_l: (@list Z)) (input_l: (@list py_value)) (data: Z) (out: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (PreH1 : ((Znth i types_l 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (types_l = (py_value_tags (input_l)))) (PreH4 : (ints_l = (py_value_payloads (input_l)))) (PreH5 : (values_size_pre = (Zlength (types_l)))) (PreH6 : (values_size_pre = (Zlength (ints_l)))) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : (output_size = (Zlength (output_l)))) (PreH12 : (output_l = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l)))))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) ,
  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.full types_pre values_size_pre types_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size values_size_pre )
|--
  “ ((Znth i types_l 0) = 0) ” 
  &&  “ (i < values_size_pre) ” 
  &&  “ (types_l = (py_value_tags (input_l))) ” 
  &&  “ (ints_l = (py_value_payloads (input_l))) ” 
  &&  “ (values_size_pre = (Zlength (types_l))) ” 
  &&  “ (values_size_pre = (Zlength (ints_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= values_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (output_l = (filter_tagged ((sublist (0) (i) (types_l))) ((sublist (0) (i) (ints_l))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ”
  &&  (((data + (output_size * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) values_size_pre )
  **  (IntArray.full int_values_pre values_size_pre ints_l )
  **  (IntArray.full types_pre values_size_pre types_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_filter_integers_safety_wit_1 : filter_integers_safety_wit_1.
Axiom proof_of_filter_integers_safety_wit_2 : filter_integers_safety_wit_2.
Axiom proof_of_filter_integers_safety_wit_3 : filter_integers_safety_wit_3.
Axiom proof_of_filter_integers_safety_wit_4 : filter_integers_safety_wit_4.
Axiom proof_of_filter_integers_safety_wit_5 : filter_integers_safety_wit_5.
Axiom proof_of_filter_integers_safety_wit_6 : filter_integers_safety_wit_6.
Axiom proof_of_filter_integers_safety_wit_7 : filter_integers_safety_wit_7.
Axiom proof_of_filter_integers_safety_wit_8 : filter_integers_safety_wit_8.
Axiom proof_of_filter_integers_safety_wit_9 : filter_integers_safety_wit_9.
Axiom proof_of_filter_integers_entail_wit_1 : filter_integers_entail_wit_1.
Axiom proof_of_filter_integers_entail_wit_2_1 : filter_integers_entail_wit_2_1.
Axiom proof_of_filter_integers_entail_wit_2_2 : filter_integers_entail_wit_2_2.
Axiom proof_of_filter_integers_return_wit_1 : filter_integers_return_wit_1.
Axiom proof_of_filter_integers_partial_solve_wit_1 : filter_integers_partial_solve_wit_1.
Axiom proof_of_filter_integers_partial_solve_wit_2_pure : filter_integers_partial_solve_wit_2_pure.
Axiom proof_of_filter_integers_partial_solve_wit_2 : filter_integers_partial_solve_wit_2.
Axiom proof_of_filter_integers_partial_solve_wit_3 : filter_integers_partial_solve_wit_3.
Axiom proof_of_filter_integers_partial_solve_wit_4 : filter_integers_partial_solve_wit_4.
Axiom proof_of_filter_integers_partial_solve_wit_5 : filter_integers_partial_solve_wit_5.

End VC_Correct.
