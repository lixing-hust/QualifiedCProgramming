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
From SimpleC.EE.Applications.minigmp Require Import gmp_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications.minigmp.GmpAux SimpleC.EE.Applications.minigmp.GmpNumber.
Import Aux.
Local Open Scope sac.

Lemma proof_of_gmp_abs_safety_wit_1 : gmp_abs_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_gmp_abs_safety_wit_2 : gmp_abs_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_gmp_cmp_safety_wit_1 : gmp_cmp_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_gmp_cmp_safety_wit_2 : gmp_cmp_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_gmp_cmp_safety_wit_3 : gmp_cmp_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_gmp_cmp_safety_wit_4 : gmp_cmp_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_gmp_cmp_return_wit_1 : gmp_cmp_return_wit_1.
Proof. Admitted. 

Lemma proof_of_gmp_cmp_return_wit_3 : gmp_cmp_return_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_copyi_safety_wit_1 : mpn_copyi_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_copyi_safety_wit_2 : mpn_copyi_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_copyi_partial_solve_wit_1 : mpn_copyi_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_copyi_partial_solve_wit_2 : mpn_copyi_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_copyi_partial_solve_wit_3 : mpn_copyi_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_safety_wit_1 : mpn_cmp_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_safety_wit_2 : mpn_cmp_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_safety_wit_3 : mpn_cmp_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_safety_wit_4 : mpn_cmp_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_safety_wit_5 : mpn_cmp_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_safety_wit_6 : mpn_cmp_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_safety_wit_7 : mpn_cmp_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_partial_solve_wit_1 : mpn_cmp_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_partial_solve_wit_2 : mpn_cmp_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_partial_solve_wit_3 : mpn_cmp_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_partial_solve_wit_4 : mpn_cmp_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_cmp_partial_solve_wit_5 : mpn_cmp_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_cmp4_safety_wit_1 : mpn_cmp4_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_cmp4_safety_wit_2 : mpn_cmp4_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_cmp4_safety_wit_3 : mpn_cmp4_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_cmp4_partial_solve_wit_1_pure : mpn_cmp4_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_mpn_cmp4_partial_solve_wit_1 : mpn_cmp4_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_safety_wit_1 : mpn_normalized_size_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_safety_wit_2 : mpn_normalized_size_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_safety_wit_3 : mpn_normalized_size_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_safety_wit_4 : mpn_normalized_size_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_safety_wit_5 : mpn_normalized_size_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_entail_wit_1 : mpn_normalized_size_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_partial_solve_wit_1 : mpn_normalized_size_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_normalized_size_partial_solve_wit_2 : mpn_normalized_size_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_safety_wit_1 : mpn_add_1_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_safety_wit_2 : mpn_add_1_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_safety_wit_3 : mpn_add_1_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_safety_wit_4 : mpn_add_1_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_safety_wit_5 : mpn_add_1_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_partial_solve_wit_1 : mpn_add_1_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_partial_solve_wit_2 : mpn_add_1_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_partial_solve_wit_3 : mpn_add_1_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_partial_solve_wit_4 : mpn_add_1_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_partial_solve_wit_5 : mpn_add_1_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_partial_solve_wit_6 : mpn_add_1_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_mpn_add_1_partial_solve_wit_7 : mpn_add_1_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_safety_wit_1 : mpn_add_n_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_safety_wit_2 : mpn_add_n_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_safety_wit_3 : mpn_add_n_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_safety_wit_4 : mpn_add_n_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_safety_wit_5 : mpn_add_n_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_safety_wit_6 : mpn_add_n_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_partial_solve_wit_1 : mpn_add_n_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_partial_solve_wit_2 : mpn_add_n_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_partial_solve_wit_3 : mpn_add_n_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_partial_solve_wit_4 : mpn_add_n_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_partial_solve_wit_5 : mpn_add_n_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_partial_solve_wit_6 : mpn_add_n_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_partial_solve_wit_7 : mpn_add_n_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_mpn_add_safety_wit_1 : mpn_add_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_entail_wit_1 : mpn_add_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_1_pure : mpn_add_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_1 : mpn_add_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_2_pure : mpn_add_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_2 : mpn_add_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_3_pure : mpn_add_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_3 : mpn_add_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_4 : mpn_add_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_5_pure : mpn_add_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_mpn_add_partial_solve_wit_5 : mpn_add_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpz_clear_return_wit_1 : mpz_clear_return_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_clear_return_wit_2 : mpz_clear_return_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_clear_partial_solve_wit_1 : mpz_clear_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_clear_partial_solve_wit_2 : mpz_clear_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_clear_partial_solve_wit_3 : mpz_clear_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_safety_wit_1_pos : mpz_realloc_safety_wit_1_pos.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_safety_wit_2_neg : mpz_realloc_safety_wit_2_neg.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_safety_wit_3_pos : mpz_realloc_safety_wit_3_pos.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_safety_wit_4_neg : mpz_realloc_safety_wit_4_neg.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_safety_wit_5_pos : mpz_realloc_safety_wit_5_pos.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_safety_wit_6_neg : mpz_realloc_safety_wit_6_neg.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_return_wit_3_pos : mpz_realloc_return_wit_3_pos.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_return_wit_4_neg : mpz_realloc_return_wit_4_neg.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_1_pos : mpz_realloc_partial_solve_wit_1_pos.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_2_neg : mpz_realloc_partial_solve_wit_2_neg.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_3_neg : mpz_realloc_partial_solve_wit_3_neg.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_4_pos : mpz_realloc_partial_solve_wit_4_pos.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_5_neg : mpz_realloc_partial_solve_wit_5_neg.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_6_pos : mpz_realloc_partial_solve_wit_6_pos.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_7_neg : mpz_realloc_partial_solve_wit_7_neg.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_8_pos_pure : mpz_realloc_partial_solve_wit_8_pos_pure.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_8_pos : mpz_realloc_partial_solve_wit_8_pos.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_9_neg : mpz_realloc_partial_solve_wit_9_neg.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_10_pos_pure : mpz_realloc_partial_solve_wit_10_pos_pure.
Proof. Admitted. 

Lemma proof_of_mpz_realloc_partial_solve_wit_10_pos : mpz_realloc_partial_solve_wit_10_pos.
Proof. Admitted. 

Lemma proof_of_mrz_realloc_if_partial_solve_wit_1_pos_pure : mrz_realloc_if_partial_solve_wit_1_pos_pure.
Proof. Admitted. 

Lemma proof_of_mrz_realloc_if_partial_solve_wit_1_pos : mrz_realloc_if_partial_solve_wit_1_pos.
Proof. Admitted. 

Lemma proof_of_mrz_realloc_if_partial_solve_wit_2_neg_pure : mrz_realloc_if_partial_solve_wit_2_neg_pure.
Proof. Admitted. 

Lemma proof_of_mrz_realloc_if_partial_solve_wit_2_neg : mrz_realloc_if_partial_solve_wit_2_neg.
Proof. Admitted. 

Lemma proof_of_mpz_sgn_safety_wit_1 : mpz_sgn_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_sgn_safety_wit_2 : mpz_sgn_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_sgn_safety_wit_3 : mpz_sgn_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_mpz_sgn_safety_wit_4 : mpz_sgn_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_mpz_sgn_safety_wit_5 : mpz_sgn_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_mpz_sgn_partial_solve_wit_1 : mpz_sgn_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_sgn_partial_solve_wit_2 : mpz_sgn_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_sgn_partial_solve_wit_3 : mpz_sgn_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_1 : mpz_swap_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_2 : mpz_swap_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_3 : mpz_swap_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_4 : mpz_swap_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_5 : mpz_swap_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_6 : mpz_swap_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_7 : mpz_swap_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_8 : mpz_swap_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_9 : mpz_swap_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_10 : mpz_swap_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_11 : mpz_swap_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_12 : mpz_swap_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_13 : mpz_swap_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_14 : mpz_swap_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_mpz_swap_partial_solve_wit_15 : mpz_swap_partial_solve_wit_15.
Proof. Admitted. 

