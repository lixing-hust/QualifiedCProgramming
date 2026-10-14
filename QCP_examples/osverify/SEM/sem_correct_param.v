
Require Import sem_sys. 
Require Import init.
Require Import invs. 

Require Import init_inv_satisfied.
Require Import step_inv_preserved.
Require Import good_code.
Require Import sem_destroy_preserves_inv.

Require Import rc_no_subabs.
Require Import rc_nknl_nkevt.
Require Import rc_int_code. 
Require Import asrt_sat_apis.
Require Import succ_gen. 
(* Require Import asrt_sat. *)

Require Import common_tacs. 

Require Import join_lib.

Definition init_sat_dtinv 
  (init: progunit -> tasks -> clientst -> osabst -> LAuxStMod.map -> Prop)
  (I: osabst -> LAuxStMod.map -> Prop) := 
  forall pu T cst O laump, init pu T cst O laump -> I O laump. 

Definition api_preserves_dtinv
  (apispec: fid -> option osapi) (I: osabst -> LAuxStMod.map -> Prop) :=  
  forall f vl cd cd' ac tp laump lau laump' lau' O O' t sc, 
    apispec f = Some (ac, tp) ->
    In cd (get_all_succs (ac vl)) ->
    head_asrt_sat cd lau ->
    spec_step sc cd O lau cd' O' lau' ->
    get O curtid = Some (oscurt t) ->
    get laump t = Some lau ->
    laump' = set laump t lau' ->
    I O laump ->
    I O' laump'. 

Definition init_sat_linv
  (init: progunit -> tasks -> clientst -> osabst -> LAuxStMod.map -> Prop)
  (li: LAuxSt -> Prop) :=
  forall pu T cst O laump t lau, init pu T cst O laump -> get laump t = Some lau -> li lau. 
  
Definition li_impl_hasrt_sat 
  (apispec: fid -> option osapi) (li: LAuxSt -> Prop) :=
  forall lau, 
    li lau ->
    forall f ac tp vl,
      apispec f = Some (ac, tp) ->
      head_asrt_sat (ac vl) lau. 

Definition hasrt_spec_step_preserve (apispec: fid -> option osapi) :=
  forall f ac tp, 
    apispec f = Some (ac, tp) ->  
    forall sc n vl cd O cd' O' lau lau',
      ac vl <> ABORT -> 
      nth_error (get_all_succs (ac vl)) n = Some cd -> 
      head_asrt_sat cd lau -> 
      spec_step sc cd O lau cd' O' lau' ->
      head_asrt_sat cd' lau'. 

Definition hasrt_spec_step_preserve_end (apispec: fid -> option osapi) (li: LAuxSt -> Prop) := 
  forall f ac tp, 
    apispec f = Some (ac, tp) ->
    forall sc n vl cd O vo O' lau lau',
      ac vl <> ABORT -> 
      nth_error (get_all_succs (ac vl)) n = Some cd ->
      head_asrt_sat cd lau -> 
      spec_step sc cd O lau (END vo) O' lau' ->
      li lau'.

Definition rc_dtinv (I: osabst -> LAuxStMod.map -> Prop) := 
  forall pu T cst O aust,
    good_client_code pu ->
    reachable (pu, os_spec') T cst O aust ->
    dtinv O aust. 


Lemma proof_method :
  forall apispec ini dti li, 
    init_sat_dtinv ini dti ->
    api_preserves_dtinv apispec dti ->
    init_sat_linv ini li ->
    li_impl_hasrt_sat apispec li ->
    hasrt_spec_step_preserve apispec ->
    hasrt_spec_step_preserve_end apispec li ->
    rc_dtinv dti. 
