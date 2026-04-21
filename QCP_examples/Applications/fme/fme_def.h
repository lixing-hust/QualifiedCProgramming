/*@ Import Coq Require Import SimpleC.EE.Applications.fme.fme_lib */


/*@ Extern Coq (Constraint :: *) */
/*@ Extern Coq (BP :: *) */
/*@ Extern Coq (Zgcd : Z -> Z -> Z) */
/*@ Extern Coq (coef_Znth : Z -> Constraint -> Z -> Z) */
/*@ Extern Coq (coef_Zlength : Constraint -> Z) */
/*@ Extern Coq (coef_replace_Znth: Z -> Z -> Constraint -> Constraint) */
/*@ Extern Coq (coef_pre_eq: Z -> Constraint -> Constraint -> Prop) */
/*@ Extern Coq (coef_array : Z -> Z -> Constraint -> Assertion) */
/*@ Extern Coq (coef_array_missing_i_rec: Z -> Z -> Z -> Z -> Constraint -> Assertion) */
/*@ Extern Coq (InequList : Z -> Z -> list Constraint -> Assertion) */
/*@ Extern Coq (InequList_seg : Z -> Z -> Z -> list Constraint -> Assertion) */
/*@ Extern Coq (InequList_nth_pos : Z -> list Constraint -> Prop) */
/*@ Extern Coq (InequList_nth_neg : Z -> list Constraint -> Prop) */
/*@ Extern Coq (BoundPair : Z -> Z -> BP -> Assertion) */
/*@ Extern Coq (eliminate_xn : Z -> list Constraint -> BP -> Prop) */
/*@ Extern Coq (generate_new_constraint : Z -> Constraint -> Constraint -> Constraint -> Prop) */
/*@ Extern Coq (generate_new_constraint_partial : Z -> Z -> Z -> Z -> Constraint -> Constraint -> Constraint -> Prop) */
/*@ Extern Coq (generate_new_constraints : Z -> list Constraint -> list Constraint -> list Constraint -> Prop) */
/*@ Extern Coq (generate_new_constraints_partial : Z -> list Constraint -> Constraint -> list Constraint -> list Constraint -> list Constraint -> Prop) */
/*@ Extern Coq (form_BP : list Constraint -> list Constraint -> list Constraint -> BP -> Prop) */
/*@ Extern Coq (LP_implies : list Constraint -> list Constraint -> Prop) */
/*@ Extern Coq (in_int_range : Z -> Z -> Constraint -> Prop) */
/*@ Extern Coq (abs_in_int_range : Z -> Constraint -> Prop) */
/*@ Extern Coq (LP_abs_in_int_range : Z -> list Constraint -> Prop) 
               (UNSAT : list Constraint -> Prop)
               (NonPos : list Constraint -> Prop) 
               (InequList_Zeros : list Constraint -> Z -> Z -> Prop)
              */

/*@ include strategies "fme.strategies" */
