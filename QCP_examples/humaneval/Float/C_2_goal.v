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
Require Import coins_2.
Local Open Scope sac.

(*----- Function truncate_number -----*)

Definition truncate_number_safety_wit_1 := 
forall (number_pre: fp32) (input_bits: Z) (fraction_bits: Z) (floor_bits: Z) (retval: fp32) (PreH1 : (fp32_eq retval (fp32_of_bits (floor_bits)))) (PreH2 : (floorf_rel_bits_2 input_bits floor_bits )) (PreH3 : (fp32_eq (fp32_sub (number_pre) (retval)) (fp32_of_bits (fraction_bits)))) (PreH4 : (fp32_isFinite (fp32_sub (number_pre) (retval)) )) (PreH5 : (floorf_fraction_bits_2 input_bits fraction_bits )) (PreH6 : (fp32_eq number_pre (fp32_of_bits (input_bits)))) (PreH7 : (problem_2_pre_bits input_bits )) ,
  ((( &( "integer_part" ) )) # Float  |-> retval)
  **  ((( &( "number" ) )) # Float  |-> number_pre)
|--
  “ (fp32_isFinite (fp32_sub (number_pre) (retval)) ) ”
.

Definition truncate_number_return_wit_1 := 
(
forall (number_pre: fp32) (input_bits: Z) (fraction_bits: Z) (floor_bits: Z) (retval: fp32) (PreH1 : (fp32_eq retval (fp32_of_bits (floor_bits)))) (PreH2 : (floorf_rel_bits_2 input_bits floor_bits )) (PreH3 : (fp32_eq (fp32_sub (number_pre) (retval)) (fp32_of_bits (fraction_bits)))) (PreH4 : (fp32_isFinite (fp32_sub (number_pre) (retval)) )) (PreH5 : (floorf_fraction_bits_2 input_bits fraction_bits )) (PreH6 : (fp32_eq number_pre (fp32_of_bits (input_bits)))) (PreH7 : (problem_2_pre_bits input_bits )) ,
  TT && emp 
|--
  EX (result_bits: Z) ,
  “ (fp32_eq (fp32_sub (number_pre) (retval)) (fp32_of_bits (result_bits))) ” 
  &&  “ (problem_2_spec_bits input_bits result_bits ) ”
  &&  emp
) \/
(
forall (number_pre: fp32) (input_bits: Z) (fraction_bits: Z) (floor_bits: Z) (retval: fp32) (PreH1 : (fp32_eq retval (fp32_of_bits (floor_bits)))) (PreH2 : (floorf_rel_bits_2 input_bits floor_bits )) (PreH3 : (fp32_eq (fp32_sub (number_pre) (retval)) (fp32_of_bits (fraction_bits)))) (PreH4 : (fp32_isFinite (fp32_sub (number_pre) (retval)) )) (PreH5 : (floorf_fraction_bits_2 input_bits fraction_bits )) (PreH6 : (fp32_eq number_pre (fp32_of_bits (input_bits)))) (PreH7 : (problem_2_pre_bits input_bits )) ,
  TT && emp 
|--
  EX (result_bits: Z) ,
  “ (fp32_eq (fp32_sub (number_pre) (retval)) (fp32_of_bits (result_bits))) ” 
  &&  “ (problem_2_spec_bits input_bits result_bits ) ”
  &&  emp
).

Definition truncate_number_partial_solve_wit_1_pure := 
forall (number_pre: fp32) (input_bits: Z) (PreH1 : (fp32_eq number_pre (fp32_of_bits (input_bits)))) (PreH2 : (problem_2_pre_bits input_bits )) ,
  ((( &( "integer_part" ) )) # Float  |->_)
  **  ((( &( "number" ) )) # Float  |-> number_pre)
|--
  “ (fp32_eq number_pre (fp32_of_bits (input_bits))) ” 
  &&  “ (problem_2_pre_bits input_bits ) ”
.

Definition truncate_number_partial_solve_wit_1_aux := 
forall (number_pre: fp32) (input_bits: Z) (PreH1 : (fp32_eq number_pre (fp32_of_bits (input_bits)))) (PreH2 : (problem_2_pre_bits input_bits )) ,
  TT && emp 
|--
  “ (fp32_eq number_pre (fp32_of_bits (input_bits))) ” 
  &&  “ (problem_2_pre_bits input_bits ) ” 
  &&  “ (fp32_eq number_pre (fp32_of_bits (input_bits))) ” 
  &&  “ (problem_2_pre_bits input_bits ) ”
  &&  emp
.

Definition truncate_number_partial_solve_wit_1 := truncate_number_partial_solve_wit_1_pure -> truncate_number_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_truncate_number_safety_wit_1 : truncate_number_safety_wit_1.
Axiom proof_of_truncate_number_return_wit_1 : truncate_number_return_wit_1.
Axiom proof_of_truncate_number_partial_solve_wit_1_pure : truncate_number_partial_solve_wit_1_pure.
Axiom proof_of_truncate_number_partial_solve_wit_1 : truncate_number_partial_solve_wit_1.

End VC_Correct.
