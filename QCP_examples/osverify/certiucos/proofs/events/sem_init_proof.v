
Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import os_sem_cap.
Require Import ifun_spec.
Require Import abs_op.

(* absimp lemmas *)
Require Import abs_infer_step.
Require Import abs_infer_abt. 
Require Import ucos_frmaop.

Require Import hoare_tactics.
Require Import pure_auto.
Require Import ucos_pauto.
Require Import sep_auto.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import derived_rules.
Require Import hoare_conseq.
Require Import ucos_forward.
Require Import math_auto.

Require Import sem_lab.
Require Import symbolic_lemmas.
Require Import Aarray_new_common.

Require Import sem_common.
Require Import gjb_common.
Require Import gjb_sem_common.

Require Import partition_common.
Require Import part_pos_rgn_spec.
Require Import part_pos_rgn_proof.
Require Import partinv_lemmas.
Require Import protect.

Require Import ev_aux_code.
Require Import pos_list_common.
Require Import seplog_trm_tacs. 
Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import evtinv_lemmas.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Open Scope int_scope.

Lemma seminit_absimp_iserr:
  forall P vsem value posv vr_cre sch vr_temp_dom vr_temp_num,
    can_change_aop P ->
    absinfer sch
             ( <|| seminit (vsem :: Vint32 value :: posv :: vr_cre :: vr_temp_dom :: vr_temp_num :: nil) ||> ** P)
             (<|| END (Some (Vint32 Int.mone)) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma seminit_absimp_semerr:
  forall sch vsem value posv vr_cre P vr_temp_dom vr_temp_num,
    can_change_aop P ->
    (vsem = Vnull \/
     (exists a,
         vsem = Vptr a /\
         (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true))) ->
    absinfer sch 
             (<|| seminit (vsem :: Vint32 value :: posv :: vr_cre :: vr_temp_dom :: vr_temp_num :: nil) ||>  ** P)
             (<|| END (Some (Vint32 Int.mone)) ||> ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma seminit_absimp_valerr:
  forall sch vsem value posv vr_cre P vr_temp_dom vr_temp_num,
    can_change_aop P ->
    Int.ltu ($ SEM_VALUE_MAX) value = true ->
    absinfer sch 
             (<|| seminit (vsem :: Vint32 value :: posv :: vr_cre :: vr_temp_dom :: vr_temp_num :: nil) ||>  ** P)
             (<|| END (Some (Vint32 Int.mone)) ||> ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma seminit_absimp_pos_abt:
  forall sch posv P sembls s idx cpn left right,
    can_change_aop P ->
    left = OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned idx ->
    right = OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned idx + 1) ->
    (~ (exists pos tp sc, get sembls pos = Some (infonull, tp, sc) /\
                       left <= (Int.unsigned pos) < right)
     /\ posv <> Vint32 (Int.repr 255)
     \/
     (exists pos tp sc, get sembls pos = Some (infonull, tp, sc) /\ posv <> Vint32 pos)) ->
    absinfer sch 
             (<|| seminit_pos (| posv :: Vint32 idx :: Vint32 cpn :: nil |);; s ||>  ** HSEMInfo sembls ** P)
             (<|| ABORT ||> ** HSEMInfo sembls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HSEMInfo sembls ** P)) by can_change_aop_solver.
(*   do 3 (eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)). *)
  eapply absinfer_trans;
  try eapply absinfer_seq;
  try (eapply absinfer_seq_abt; try eauto);
  try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
  Unshelve.
  exact None.
  trivial. trivial.
Qed.

Lemma seminit_absimp_pos_cons:
  forall sch posv P sembls s idx cpn left right,
    can_change_aop P ->
    left = OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned idx ->
    right = OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned idx + 1) ->
    (~ (exists pos tp sc, get sembls pos = Some (infonull, tp, sc) /\ 
                       left <= (Int.unsigned pos) < right) /\
     posv = Vint32 (Int.repr 255) \/
     (exists pos tp sc, get sembls pos = Some (infonull, tp, sc) /\ posv = Vint32 pos)) ->
    absinfer sch 
             (<|| seminit_pos (| posv :: Vint32 idx :: Vint32 cpn :: nil |);; s ||>  ** HSEMInfo sembls ** P)
             (<|| s ||> ** HSEMInfo sembls ** P).
Proof.
  infer_solver 0%nat.
  exists posv sembls. do 4 eexists.
  left. splits; eauto.
  destruct s0 as [[[[]]]].
  substs.
  destruct H3. simpljoin1.
  simpl in *.
  destruct H5.
  simpl in *.
  subst x2.
  eapply OSAbstMod.join_sig_get in H4.
  auto.
  Unshelve.
  exact None.
Qed.

Lemma seminit_absimp_poserr:
  forall sch value pos vr_cre P vsem,
    can_change_aop P ->
    Int.eq pos (Int.repr 255) = true ->
    absinfer sch 
             (<|| seminit_poserr (|Vint32 pos :: nil|)
                  ?? seminit_set_placeholder (|Vint32 pos :: nil|);;
                       semcre (Vint32 value :: vr_cre :: nil);;
                       (seminit_set_ecb_ptr (|Vint32 pos :: vr_cre :: nil|) ?? seminit_holder_abt (| vr_cre :: nil |));; 
                              (seminit_create_err (|Vint32 pos :: vr_cre :: nil|)
                                ?? seminit_set_type (|Vint32 pos :: nil|) ;; 
                                    seminit_set_sem (|vsem :: Vint32 pos :: nil |)) ||>  ** P) 
             (<|| END (Some (Vint32 Int.mone)) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma seminit_absimp_set_placeholder: 
  forall sch pos sembls tp sc s0 P,
    can_change_aop P ->
    Int.eq pos (Int.repr 255) = false ->
    get sembls pos = Some (infonull, tp, sc) -> 
    absinfer sch 
             (<||seminit_poserr (|Vint32 pos :: nil|) ?? (seminit_set_placeholder (|Vint32 pos :: nil|) ;; s0) ||> ** 
                 HSEMInfo sembls ** P)
             (<|| s0 ||> ** HSEMInfo (set sembls pos (infohold, tp, sc)) ** P). 
Proof.
  intros.
  infer_solver 1%nat. 
Qed.

Lemma seminit_absimp_set_ecb_ptr_null:
  forall sch P s0 pos e tp sc sembls sembls' locmp ptrmp locmp' ptrmp' ct muxp semp qp, 
    can_change_aop P -> 
    Int.eq pos (Int.repr 255) = false -> 
    get sembls pos = Some (e, tp, sc) -> 
    locmp' = set locmp ct (Vint32 (Int.repr __EvLoc_normal)) ->
    get ptrmp ct = Some (muxp, semp, qp) -> 
    ptrmp' = set ptrmp ct (muxp, Vnull, qp) -> 
    sembls' = set sembls pos (infonull, tp, sc) -> 
    absinfer sch 
             (<|| (seminit_set_ecb_ptr (|Vint32 pos :: Vnull :: nil|) ?? seminit_holder_abt (| Vnull :: nil |)) ;; s0 ||> ** 
              HSEMInfo sembls ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P) 
             (<|| s0 ||> ** HSEMInfo sembls' ** HEvLoc locmp' ** HEvPtr ptrmp' ** HCurTCB ct ** P).   
Proof.
  introv Hcop Hrgn Heib0 Hlmp' Hpmp Hpmp' Heibs'.
  eapply absinfer_trans.
  eapply absinfer_seq. pure_auto. 
  instantiate (1:= HSEMInfo sembls' ** HEvLoc locmp' ** HEvPtr ptrmp' ** HCurTCB ct ** P).
  pure_auto.
  instantiate (1:=END None).
  infer_solver 0%nat.
  unfold tidsame.
  repeat (rewrite set_a_get_a'; eauto).
  eapply absinfer_seq_end; pure_auto.
  Unshelve.
Qed.

Lemma seminit_absimp_set_ecb_ptr_n_null: 
  forall sch P s0 pos e tp sc eid sembls sembls' locmp ptrmp locmp' ptrmp' ct muxp semp qp, 
    can_change_aop P -> 
    Int.eq pos (Int.repr 255) = false -> 
    get sembls pos = Some (e, tp, sc) -> 
    locmp' = set locmp ct (Vint32 (Int.repr __EvLoc_normal)) ->
    get ptrmp ct = Some (muxp, semp, qp) -> 
    ptrmp' = set ptrmp ct (muxp, Vnull, qp) -> 
    sembls' = set sembls pos (infotid eid, tp, sc) ->     
    eid <> vhold_addr -> 
    absinfer sch 
             (<|| (seminit_set_ecb_ptr (|Vint32 pos :: Vptr eid :: nil|) ?? seminit_holder_abt (| Vptr eid :: nil |));; s0 ||> **
              HSEMInfo sembls ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P) 
             (<|| s0 ||> ** HSEMInfo sembls' ** HEvLoc locmp' ** HEvPtr ptrmp' ** HCurTCB ct ** P).   
Proof.
  introv Hcop Hrgn Heib0 Hlmp' Hpmp Hpmp' Heibs' Hnhold.
  eapply absinfer_trans.
  eapply absinfer_seq. pure_auto. 
  instantiate (1:= HSEMInfo sembls' ** HEvLoc locmp' ** HEvPtr ptrmp' ** HCurTCB ct ** P).
  pure_auto.
  instantiate (1:=END None).
  subst.
  infer_solver 0%nat.
  unfold tidsame.
  repeat (rewrite set_a_get_a'; eauto).
  eapply absinfer_seq_end; pure_auto.
Qed.

Lemma seminit_absimp_set_ecb_holder_abt: 
  forall sch P s0 pos,
    can_change_aop P -> 
    absinfer sch 
             (<|| (seminit_set_ecb_ptr (|Vint32 pos :: Vptr vhold_addr :: nil|) ??
                      seminit_holder_abt (| Vptr vhold_addr :: nil |));; s0 ||> ** P)
             (<|| ABORT ||> ** P).   
Proof.
  introv Hcop.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1:=P). pure_auto. 
  eapply absinfer_choice2; can_change_aop_solver.
  intros; auto.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1:=P). pure_auto. 
  eapply absinfer_abt; can_change_aop_solver.
  absimp_abt_solver. 
  eapply absinfer_seq_abt; pure_auto.
  Unshelve.
  exact None.
Qed.

Lemma seminit_absimp_create_error:
  forall pos s0 sch P, 
    can_change_aop P ->
    Int.eq pos (Int.repr 255) = false -> 
    absinfer sch 
             (<|| seminit_create_err (|Vint32 pos :: Vnull :: nil|) ?? s0 ||> ** P) 
             (<|| END (Some (Vint32 Int.mone)) ||> ** P). 
Proof.
  introv Hcop. 
  infer_solver 0%nat. 
Qed.     

Lemma seminit_absimp_set_type: 
  forall sch P pos e tp sc semeibs semeibs' vr_b vr_i s0, 
    can_change_aop P ->
    get semeibs pos = Some (e, tp, sc) ->
    semeibs' = set semeibs pos (e, $ SEM_COUNTING, sc) ->
    absinfer sch
             (<|| seminit_create_err (|Vint32 pos :: Vptr (vr_b, vr_i) :: nil|)
                  ?? (seminit_set_type (|Vint32 pos :: nil|);; s0) ||>  ** HSEMInfo semeibs ** P)
             (<|| s0 ||> ** HSEMInfo semeibs' ** P). 
Proof.
  introv Hcop Hget H'.
  subst.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver.
  2: { intros; eauto. }
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1:=HSEMInfo (set semeibs pos (e, $ SEM_COUNTING, sc)) ** P). 
  can_change_aop_solver.
  instantiate (1 := END None). 
  infer_solver 0%nat. 
  eapply absinfer_seq_end; can_change_aop_solver.
  intros; auto.
Qed.

Lemma seminit_absimp_sem_pos:
  forall sch P vsem pos pbls,
    can_change_aop P ->
    cmpaddr Clt userAddrStart vsem = true ->
    cmpaddr Cle vsem userAddrEnd = true ->
    (exists posv, get pbls vsem = Some posv) ->
    absinfer sch 
             (<|| seminit_set_sem (| Vptr vsem :: Vint32 pos :: nil |) ||>  ** Hpbls pbls **P)
             (<|| END (Some (Vint32 Int.zero)) ||> ** Hpbls (set pbls vsem pos) ** P). 
Proof.
  infer_solver 0%nat.
Qed.

Lemma seminit_absimp_sem_pos_abt:
  forall sch P vsem pos pbls,
    can_change_aop P ->
    cmpaddr Clt userAddrStart vsem = true ->
    cmpaddr Cle vsem userAddrEnd = true ->
    ~(exists posv, get pbls vsem = Some posv) ->
    absinfer sch 
             (<|| seminit_set_sem (| Vptr vsem :: Vint32 pos :: nil |) ||>  ** Hpbls pbls ** P)
             (<|| ABORT ||> ** Hpbls pbls ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (Hpbls pbls ** P)) by can_change_aop_solver.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
Qed.

Open Scope Z_scope.
Open Scope int_scope.
Open Scope code_scope.

Lemma semb_get_not_null':
  forall semvl embls hld vll1 vll2 idx cpn,
    EIBArray_P (Vint32 Int.zero) semvl embls hld ->
    Seminfo_full_P' vll1 idx cpn ->
    vll1 ++ vll2 = semvl ->
    length vll1 = ∘ (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) * (Int.unsigned idx + 1)) ->
    length semvl = ∘ (OS_USER_MAX_EVENTS / 3) ->
   ~(exists i tp sc,
          get embls i = Some (infonull, tp, sc) /\ OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned idx <= (Int.unsigned i) < Z.of_nat (length vll1)).
Proof.
introv He Hf Heq Hl1 Hl.
funfold Hf.
introv H. 
do 3 destruct H.
eapply semb_corr_alt' in He; eauto.
instantiate (1:= x) in He.
destruct He. destruct H0. destruct H0. destruct H0.
destruct H. destructs H0.
unfold get in H, H2.
unfold EmbMap in H, H2.
rewrite H2 in H. inverts H. 
destruct H4.
destruct H. destruct H. tryfalse. 
destruct H. destruct H. tryfalse.
destruct H.
eapply Hf; eauto.
erewrite <- nth_error_eq_nth_vallist in *.
destruct H. destruct H0.
simpljoin.
unfold nat_of_Z.
symmetry.
rewrite nth_error_app1; auto with zarith.
eapply ge0_z_nat_le; auto with zarith.
apply Int.unsigned_range_2.
rewrite app_length.
auto with zarith.
Qed.

Lemma Z_div_mul_lt:
forall  x y z, 0 <= z < y -> 0 < x / y -> x / y * z < x.
Proof.
intros.
eapply Z.lt_le_trans; [ | eapply Z.mul_div_le with (b:= y)]; auto with zarith.
rewrite Z.mul_comm.
eapply Zmult_lt_compat_r; auto with zarith.
Qed.

Lemma Z_div_mul_le:
forall  x y z, 0 < z <= y -> 0 < x / y -> x / y * z <= x.
Proof.
intros.
eapply Z.le_trans; [ | eapply Z.mul_div_le with (b:= y)]; auto with zarith.
rewrite Z.mul_comm.
eapply Zmult_le_compat_r; auto with zarith.
Qed.

Lemma user_max_evts_part_succ_rgn:
forall cpn idx,
    1 <= Int.unsigned cpn ->
     Int.unsigned cpn <= 8 ->
     1 <= Int.unsigned (Int.divu ($ OS_USER_MAX_EVENTS / 3) cpn) ->
      Int.unsigned idx < Int.unsigned cpn ->
     1 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned idx + 1) <=  OS_USER_MAX_EVENTS / 3.
Proof.
pose proof usr_max_evts_rgn.
intros.
pose proof (Int.unsigned_range_2 idx).
unfold Int.divu in *.
rewrite Int.unsigned_repr in *; auto;
try solve_usr_max_evts_rgn; try conv_max_unsigned.
rewrite Int.unsigned_repr in *; auto;
try solve_usr_max_evts_rgn.
split; auto with zarith.
eapply Z_div_mul_le; auto with zarith.
rewrite Int.unsigned_repr ; auto; try solve_usr_max_evts_rgn.
split.
eapply Z.div_pos; auto with zarith.
eapply Z.le_trans with (m:= 79 / Int.unsigned cpn).
eapply Z.div_le_mono; auto with zarith.
eapply Z.le_trans with (m:= 79 / 1).
eapply Z.div_le_compat_l; auto with zarith.
rewrite Z.div_1_r; auto with zarith.
Qed.

Lemma semb_getnull':
  forall vl vll1 vll2 embls hld i idx cpn,
    EIBArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls hld ->
    nth_Seminfo_free_P' i (vll1 ++ vl :: vll2) idx cpn ->
    length vll1 = Z.to_nat i ->
    length (vll1 ++ vl :: vll2) = ∘ (OS_USER_MAX_EVENTS / 3) ->
    exists tp sc,
      get embls (Int.repr i) = Some (infonull, tp, sc) /\
      V_OSSINFOPevent vl = Some Vnull.
Proof.
  introv He Hf Hl1 Hl2.
  funfold Hf.
  unfold nat_of_Z in *.
  rewrite <- Hl1 in H0.
  rewrite nth_vallist_get_idx in H0; inverts H0.
  rewrite app_length in Hl2.
  simpl in Hl2.
  rewrite Hl1 in Hl2.
  assert (Hi: ( i < (OS_USER_MAX_EVENTS / 3))).
  auto with zarith.
  assert (Hi': 0 <= i <= Int.max_unsigned).
  split.
  eapply Z.le_trans; eauto.
  eapply Ztac.mul_le; try apply Int.unsigned_range_2.
  assert (Hc: Int.unsigned cpn = 0 \/ Int.unsigned cpn <> 0) by tauto.
  destruct Hc as [Hc | Hc].
  rewrite Hc.
  rewrite Zdiv_0_r; auto with zarith.
  eapply Z.div_pos; try solve_usr_max_evts_rgn.
  pose proof (Int.unsigned_range_2 cpn).
  auto with zarith.
  solve_usr_max_evts_rgn.
  eapply semb_corr with (i:= Int.repr i) in He; auto with zarith.
  destruct He as (eop & tp & sc & Hget & Hvtp & Hcases).
  unfold V_OSSINFOPevent in *.
  unfold get in *; simpl in *.
  rewrite Hget.
  destruct Hcases as [ ? | [ ? | ? ]]; simpljoin;
  match goal with
  H: nth_val ?n _ = _ , H': nth_val ?n _ = _ |- _ => rewrite H in H'; inverts H'; try rewrite H end.
  eauto.
  rewrite Int.unsigned_repr; auto with zarith.
  rewrite int_ltu_zero_eq_false; auto.
  rewrite Int.unsigned_repr; auto with zarith.
Qed.

Lemma SemInitProof: 
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api sem_init
              (seminit, (Tint32, Tptr Tint32 :: Tint32 :: nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api sem_init
              (seminit, (Tint32, Tptr Tint32 :: Tint32 :: nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api sem_init = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  do 5 (destruct v'; try apply absabort_rule).
  rename v1 into vr_temp_dom.
  rename v2 into vr_temp_num.

  rename x0 into vsem.
  rename H2 into Hptr.

  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).

  (* OSIntNesting *)
  hoare forward prim.
  unfold AGVars.
  hoare unfold.
  assert (Hit: Int.ltu ($ 0) v'34 = true \/ Int.ltu ($ 0) v'34 = false) by int auto.
  destruct Hit as [Hit | Hit].
  hoare forward; rewrite Hit. simpl; pure_auto.
  hoare forward.
  pure_auto.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply seminit_absimp_iserr; try pure_auto.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep pauto.
  auto.
  pure_auto.
  hoare forward.
  (*  end of retrun -1 *)
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  simpl in H3. destruct H3; tryfalse.
  hoare forward; rewrite Hit. simpl; pure_auto.
  hoare unfold. simpl in H3; tryfalse.
  instantiate (1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep pauto.
  auto.
  pure_auto.
  clear -Hptr.
  (* end add *)

  (* x ′ =ᶠ UserAddrCheck (·〈 (long) ∗ 〉 sem ′·);ₛ *)
  rename v'4 into er.
  hoare forward.
  pure_auto.
  pure_auto.
  simpl.
  inverts Hptr; mytac; try pauto.
  pure_auto.
  unfold retpost. introv Hsat.
  inverts Hsat; sep pauto.
  pure_auto.

  intros.
  destruct H.
  destruct H; try (sep pauto; instantiate (1:=init_lg); sep pauto).

  intros.
  sep pauto. instantiate (1:=init_lg). sep pauto.

  hoare unfold.
  eapply backward_rule1.
  intros.
  apply disj_split in H.
  eauto.
  eapply disj_rule.

  (* x = 0 *)
  hoare unfold.
  inverts H1.

  hoare forward.
  pure_auto.
  pure_auto.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply seminit_absimp_semerr.
  can_change_aop_solver.
  destruct H. inverts H. pauto.
  do 2 destruct H. inverts H. pauto.
  hoare forward.
  eapply hoare_disj_afalseP_l_pre. 
  change (Int.eq ($ 0) ($ 0)) with true. simpl.
  change (Int.ltu Int.zero Int.one) with true. simpl.
  hoare unfold.
  destruct (Int.ltu ($ SEM_VALUE_MAX) i); destruct H0; tryfalse.

  (*x != 0*)
  hoare unfold.
  inverts H1.

  hoare forward.
  pure_auto.
  pure_auto.
  change (Int.eq ($ 1) ($ 0)) with false.
  simpl.
  change (Int.ltu Int.zero Int.zero) with false.
  destruct (Int.ltu ($ SEM_VALUE_MAX) i) eqn: eq1;
  simpl.
  2:{
    change (Int.ltu Int.zero Int.zero) with false. simpl.
    hoare unfold. tryfalse.
  }
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply seminit_absimp_valerr.
  can_change_aop_solver. auto.
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  change (Int.eq ($ 1) ($ 0)) with false.
  simpl.
  change (Int.ltu Int.zero Int.zero) with false.
  destruct (Int.ltu ($ SEM_VALUE_MAX) i) eqn: eq1;
  simpl.
  change (Int.ltu Int.zero Int.one) with true. simpl.
  hoare unfold. destruct H; tryfalse.
  hoare unfold.
  clear H.

  assert (Hv_range: Int.unsigned i <= 65535).
  {
    unfold SEM_VALUE_MAX in eq1.
    int auto.
  }

  (*ENTER_CRITICAL;ₛ*)
  hoare forward prim.
  unfold EvtInv.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre ( R_Q_Data_P).
  eapply pure_split_rule'; introv Hrqdata.
  hoare unfold.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat PartitionInv.
  eapply unfold_PartitionInv_frm; eauto.
  unfold PartitionInv_part2.
  hoare normal pre.
  hoare_ex_intro.
  hoare_lifts_trms_pre R_Cpartnum_Dom2idx_P.
  eapply pure_split_rule'; introv Hrcpn0.
  hoare_lifts_trms_pre (AMqEIBs, AMuxEIBs, ASemEIBs).
  unfold ASemEIBs.
  unfold AMqEIBs.
  unfold AMuxEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (AMqCap, AMuxCap, ASemCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMqCap ?l1 ?vl1 ** AMuxCap ?l2 ?vl2 ** ASemCap ?l3 ?vl3 ** _ }} _ {{ _ }} =>
  rename l1 into lmq; rename l2 into lmux; rename l3 into lsem;
  rename vl1 into mqcapvl; rename vl2 into muxcapvl; rename vl3 into semcapvl end.
  hoare_lifts_trms_pre ( MqCapArray_P, length  mqcapvl, MuxCapArray_P, length muxcapvl,
                                              SemCapArray_P, length semcapvl).
  eapply pure_split_rule'; introv Hmqcap_vl.
  eapply pure_split_rule'; introv Hmqcap_len.
  eapply pure_split_rule'; introv Hmuxcap_vl.
  eapply pure_split_rule'; introv Hmuxcap_len.
  eapply pure_split_rule'; introv Hsemcap_vl.
  eapply pure_split_rule'; introv Hsemcap_len.
  hoare_lifts_trms_pre ( RH_SEM_NOT_IN_CORE_P, RH_Q_NOT_IN_CORE_P ).
  eapply pure_split_rule'; introv Hs_nc.
  eapply pure_split_rule'; introv Hq_nc.
  hoare unfold.
  unfold Adomain2index.
  unfold Adomain2index'.
  unfold AKsCurDomain.
  unfold ACorepartnum.
  hoare_lifts_trms_pre (array_type_vallist_match, RLH_Dom2idx_P, RHL_Dom2idx_P, Int.mone).
  eapply pure_split_rule'; introv Hdom_mat; destruct Hdom_mat as (Hdom_mat & Hlen_dom).
  eapply pure_split_rule'; introv Hlh_dom.
  eapply pure_split_rule'; introv Hhl_dom.
  eapply pure_split_rule'; introv Hcd_cases.
  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).

  hoare_lifts_trms_pre (Aop, kscurdom).
  match goal with
  | |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** HKsCurDomain ?idx ** _ }} _ {{ _ }} =>
     rename idx into vcurd
  end.
  assert(Hvcurd : vcurd = Int.mone \/ vcurd <> Int.mone) by tauto.
  destruct Hvcurd as [Habt | Hvcurd].
  eapply abscsq_rule.
  apply noabs_oslinv.
  do 3 try (eapply absinfer_trans; [ eapply absinfer_choice2; eauto; try can_change_aop_solver | idtac]).
  eapply absinfer_kscurdom_ext_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.
  eapply abscsq_rule.
  apply noabs_oslinv.
  do 3 try (eapply absinfer_trans; [ eapply absinfer_choice2; eauto; try can_change_aop_solver | idtac]).
  eapply absinfer_kscurdom_ext; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  destruct Hcd_cases as [Hcd_rgn | Hf]; try subst; tryfalse; auto.

  hoare_lifts_trms_pre (Aop, Domain2Index, ksCurDomain).
  match goal with
  | H: length ?vl = ?len
    |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** _ Domain2Index _ ?vl ** GV ksCurDomain @ _ |-> Vint32 ?idx ** _ }} _ {{ _ }} =>
     assert (Hle_len: (Z.to_nat (Int.unsigned idx) < len)%nat)
  end.
  solve_part_int_rgn.
  lets Hnth: Hle_len.
  eapply pure_lib.nthval'_has_value in Hnth; eauto.
  destruct Hnth as (rv_dom & Hnth & Hmat).
  hoare_lifts_trms_pre (Aop, kscurdom, domindexlist).
  match goal with
    H: RLH_Dom2idx_P _ _ |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** _ ** HDomain2index ?absdomls ** _ }} _ {{ _ }} =>
     rename absdomls into domls
  end.
  assert (Hget_dom:get domls  vcurd = Some rv_dom).
  eapply Hlh_dom; eauto.
  eapply inline_bittblfunctions.nth_val'2nth_val; eauto.

  assert (Hrv_dom: vr_temp_dom <> Vint32 rv_dom \/ vr_temp_dom = Vint32 rv_dom) by tauto.
  destruct Hrv_dom as [Habt | Hrv_dom].
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_get_temp_dom_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_get_temp_dom_succ; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  subst vr_temp_dom.

  hoare_lifts_trms_pre (Aop, cpartnum).
  match goal with
    | |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** Hcorepartnum ?cpn ** _ }} _ {{ _ }} =>
     rename cpn into rv_cpn
  end.
  assert (Hrv_num: vr_temp_num <> Vint32 rv_cpn \/ vr_temp_num = Vint32 rv_cpn) by tauto.
  destruct Hrv_num as [Habt | Hrv_num].
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_get_temp_num_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_get_temp_num_succ; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  subst vr_temp_num.

  (*y ′ =ᶠ getFreePos (·′ 0·);ₛ*)
  eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply calle_rule_lvar'; 
            [ intuition eauto  | 
              intros; do 5 try 
                         (apply rvl_elim;[ symbolic_execution | ]);
              first [apply rvl_nil | simpl;auto] | 
              intros;  unfold_spec |
              idtac |
              idtac |
              simpl;eauto | 
              sep_unfold_funpost |
              sep_unfold_funpre 
              ].
  (* hoare forward. *)
  unfold Adomain2index.
  unfold Adomain2index'.
  unfold AKsCurDomain.
  unfold ACorepartnum.
  sep normal. sep eexists.
  sep cancel Domain2Index.
  sep cancel ksCurDomain.
  sep cancel ACorepartnum'.
  sep cancel domindexlist.
  sep cancel cpartnum.
  sep cancel ASeminfo.
  sep cancel p_local.
  sep cancel APthreadMutex.
  sep cancel AMqAttr.
  trycancel.
  sep cancel A_isr_is_prop.
  sep cancel Aier.
  sep cancel Aop.
  sep cancel y.
  sep split; eauto.
  simpl. 
  eauto.
(*   eauto. *)
(*   auto. *)
  pure_auto.
(*   pure_auto. *)
  unfold retpost. introv Hsat.
  inverts Hsat; sep pauto.
  get_hsat Hsat;
  do 5 try (get_hsat Hsat; destruct Hsat; sep pauto).
 
  introv Hsat. 
  sep destruct Hsat.
  destruct Hsat as [Hsat | Hsat];
  do 5 (try destruct Hsat as [Hsat | Hsat];
   try (sep destruct Hsat;
  eexists; sep cancel p_local; simpl; auto)).
  
  intros.
  sep pauto. sep cancel p_local. sep auto.

  hoare unfold.
  eapply backward_rule1.
  introv Hsat.
  eapply disj_split in Hsat; eapply adisj_intro;
    destruct Hsat as [Hsat | Hsat]; [left; eauto | right].
  eapply disj_split in Hsat;
  destruct Hsat as [Hsat | Hsat]; [eauto | idtac].
  false.
  do 4 (eapply disj_split in Hsat;
  destruct Hsat as [Hsat | Hsat];
  [ sep normal in Hsat; sep destruct Hsat;
                   sep split in Hsat; tryfalse| idtac]).
  sep normal in Hsat; sep destruct Hsat;
                   sep split in Hsat; tryfalse.
  change ($ 0) with Int.zero in *.
  match goal with H: Some _ = Some _ /\ _ /\ _ /\ _ |- _ =>
  destruct H as (Heq & Hf & _) end.
  tryfalse.

  hoare forward;
  hoare normal pre;
  [ do 7 try (eapply ex_intro_rule; intros) | do 6 try (eapply ex_intro_rule; intros)];
  eapply ex_intro_rule; intro dom2index;
  eapply ex_intro_rule; intro domls';
  eapply ex_intro_rule; intro kscurd;
  eapply ex_intro_rule; intro cpn;
  eapply ex_intro_rule; intro idx;
[ eapply ex_intro_rule; intro lsem';
    eapply ex_intro_rule; intro lmux';
    eapply ex_intro_rule; intro lmq'
   | eapply ex_intro_rule; intro semvll1;
     eapply ex_intro_rule; intro semvll2;
     eapply ex_intro_rule; intro lsem';
     eapply ex_intro_rule; intro lmux';
     eapply ex_intro_rule; intro lmq'];
  hoare_lifts_trms_pre (DOMAIN_SIZE, R_Cpartnum_Dom2idx_P, nth_val');
  try (eapply pure_split_rule'; introv Hvcd_rgn;
           destruct Hvcd_rgn as (Hvcd_rgn1 & Hvcd_rgn2);
          eapply pure_split_rule'; introv Hrcpn;
          eapply pure_split_rule'; introv Hnth_dom);
  try (hoare_lifts_trms_pre ( semvll2, length semvll1);
           eapply pure_split_rule'; introv Hsem_eq;
           eapply pure_split_rule'; introv Hlen_semvll1;
           protect Hsem_eq);
  hoare unfold; try inverts H20; (* eq. on logicl *) 
  rewrite Hnth_dom in Hnth; inverts Hnth.

  (* start Seminfo_full_P *)
  2: {
    (* pos ′ =ₑ 〈 long 〉 y ′;ₛ *)
    hoare forward.
    hoare_lifts_trms_pre Aop.
    eapply assign_rule_lvar.
    split; sep pauto.
    intros.
    eapply cast_rv_tint8_tint32.
    symbolic_execution.
    simpl; auto.
    apply assign_type_match_true; simpl; auto.

    intros.
    sep pauto. sep cancel p_local. sep pauto.

    (* If (pos ′ ==ₑ ′ 255) *)
    hoare forward.
    rewrite Int.eq_true.
    hoare unfold.
    hoare_lifts_trms_pre (ASeminfo).
    match goal with | |- {| _ , _, _, _, _, _ |} |- _ {{ ASeminfo _ ?vl ** _ }} _ {{ _ }} =>
    hoare_assert_pure (length vl = ∘ (OS_USER_MAX_EVENTS / 3))
    end.
    {
      get_hsat Hsat.
      sep_lift_context_in Hsat ASeminfo.
      eapply aseminfo_len_frm in Hsat.
      auto.
    }
    hoare_split_pure_all.
    lets Hget_full: semb_get_not_null' H H18 Hsem_eq Hlen_semvll1 H21.
    rewrite Hlen_semvll1 in Hget_full.
    unfold nat_of_Z in Hget_full.
    rewrite Z2Nat.id in Hget_full; auto with zarith.
    2:{ pose proof (Int.unsigned_range_2 rv_dom).
           eapply Ztac.mul_le; auto with zarith.
           assert (Hc: Int.unsigned cpn = 0 \/ Int.unsigned cpn <> 0) by tauto.
           destruct Hc as [Hc | Hc].
            rewrite Hc.
            rewrite Zdiv_0_r; auto with zarith.
            eapply Z.div_pos; try solve_usr_max_evts_rgn.
            pose proof (Int.unsigned_range_2 cpn).
            auto with zarith. }
    hoare_lifts_trms_pre (Aop, seminfoid). 
    assert (Hv: v = V$ 255 \/ v <> V$ 255) by tauto.
    destruct Hv as [Hv | Hv].
    (* v <> V$ 255 *)
    2: {
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply seminit_absimp_pos_abt.
      can_change_aop_solver.
      eauto. eauto.
      left. splits; auto.
      eapply absinfer_eq.
      apply absabort_rule.
    }
    (* v = V$ 255 *)
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply seminit_absimp_pos_cons.
    can_change_aop_solver.
    eauto. eauto.
    left. splits; auto.
    eapply absinfer_eq.
    instantiate (1:= Afalse).
    subst v.
    
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply seminit_absimp_poserr.
    can_change_aop_solver. rewrite Int.eq_true; auto.
    eapply absinfer_eq.
    
    hoare_lifts_trms_pre (Aisr, Ais, Aier).
    transform_pre add_aemp_isr_is_prop  ltac:(sep cancel Aisr; sep cancel Ais; sep cancel Aier).

    (*EXIT_CRITICAL;ₛ*)
    hoare forward prim.
    unfold EvtInv.
    unfold ASemEIBs.
    sep cancel Aier.
    sep normal; sep eexists.
    sep cancel ASemCap.
    sep pauto; eauto.
    trycancel.
    sep cancel ASeminfo.
    sep cancel p_local.
    sep cancel APthreadAttr.
    unfold AMuxEIBs.
    unfold AMqEIBs.
    sep normal; sep eexists.
    sep cancel APthreadMutex.
    sep cancel AMqAttr.
    sep cancel AMuxCap.
    sep cancel AMqCap.
    sep split; eauto.
    eapply fold_PartitionInv_frm.
    unfold PartitionInv_part2.
    sep normal; sep eexists.
    trycancel_PartitionInv.
    sep cancel CapabilityInv.
    sep pauto; eauto.
    eauto.
    pure_auto.
    hoare forward. (*RETURN *)

    eapply hoare_disj_afalseP_l_pre.
    rewrite Int.eq_true. hoare_split_pure_all.
    match goal with H: val_inj _ = _ \/ _ |- _ => simpl in H; destruct H; tryfalse end.
  }
  (* end Seminfo_full_P *)

  (* start nth_Seminfo_free_P *)
   match goal with
   H: nth_Seminfo_free_P' ?vy _ ?vidx ?vcpn |- _ =>
   assert (Hy_range: 
                  (OS_USER_MAX_EVENTS / 3 / Int.unsigned vcpn * Int.unsigned vidx <= vy <
                  OS_USER_MAX_EVENTS / 3 / Int.unsigned vcpn * (Int.unsigned vidx + 1))%Z) by
   (funfold H; auto);
   hoare_assert_pure (1 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned vcpn * (Int.unsigned vidx + 1) 
                                        <= OS_USER_MAX_EVENTS / 3)
   end.
   { get_hsat Hsat.
      unfold ACorepartnum, ACorepartnum' in Hsat.
      sep split in Hsat. simpljoin.
      eapply user_max_evts_part_succ_rgn; auto with zarith.
      eapply Hrcpn0; eauto.
      eapply inline_bittblfunctions.nth_val'2nth_val; eauto.
    }
   eapply pure_split_rule'; introv Hy_range'.
   destruct Hy_range' as (Hy_rgn1 & Hy_rgn2).
   assert (Hdiv_rgn: 0 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn
                                                * Int.unsigned rv_dom).
{
   eapply Ztac.mul_le; auto with zarith.
   apply Int.unsigned_range_2.
}

  hoare forward.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_lvar.
  split; sep pauto.
  intros.
  eapply cast_rv_tint8_tint32. 
  symbolic_execution.
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  clear -Hy_range Hy_rgn2 Hdiv_rgn Hrgn3 Hrgn4.
  change (Byte.max_unsigned) with 255.
  simpljoin.
  rewrite Int.unsigned_repr; try (split; solve_usr_max_evts_rgn).
  match goal with | |- (if ?p then _ else _) = _ => destruct p eqn:eq1; auto with zarith end.
  simpl; auto.
  apply assign_type_match_true; simpl; auto.
  
  intros.
  sep pauto. sep cancel p_local. sep pauto. 

  match goal with H: OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn *
           Int.unsigned rv_dom <= ?v < _ |- _ =>
  assert (Hif_false: Int.eq ($ v) ($ 255) = false) end.
  { lets Hrgn: usr_max_evts_rgn.
    destruct Hrgn as (Hrgn3 & Hrgn4).
    clear -Hy_range Hy_rgn2 Hdiv_rgn Hrgn3 Hrgn4.
    int auto.
  }

  hoare forward. 
  pure_auto.
  rewrite Hif_false.
  hoare unfold.
  simpl val_inj in *. tryfalse.
  instantiate (1:=Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare_split_pure_all.
  match goal with H: val_inj _ = _ \/ _ , H': Int.eq ($ ?v) ($ 255)  = _ |- _ => rename v into vy; clear H end.
  (* val_inj ... = ... \/ ...*)
  destruct lsem' as (lsem_b & lsem_i).
  eapply backward_rule1.
  introv Hsat.
  sep_lift_context_in Hsat ASeminfo.
  eapply ASeminfo_unfold_any_idx_frm with (idx := Z.to_nat  vy) in Hsat; eauto.
  lets Hl: aseminfo_len_frm Hsat.
  clear -Hl Hy_range Hy_rgn2 Hdiv_rgn.
  rewrite Hl.
  unfold nat_of_Z in *.
  eapply Z2Nat.inj_lt;  auto with zarith.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  simpljoin.
  match goal with H: EIBArray_P _ (_ ++ ?vl :: _) ?abs _ |- _ =>
  rename abs into semls; rename vl into semvl end.
  assert (Hget_null:
            exists tp sc, get semls ($ vy) = Some (infonull, tp, sc) /\ V_OSSINFOPevent semvl = Some Vnull). 
  {
    eapply semb_getnull'; eauto. 
  }
  destruct Hget_null as (tp & sc & Hget_null & Hvnull). 

  hoare_lifts_trms_pre (Aop, seminfoid).
  assert (Hv: v = Vint32 ($ vy) \/ v <> Vint32 ($ vy)) by tauto.  
  destruct Hv as [Hv | Hv].
  (* v <> Vint32 ($ vy) *)
  2: {
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply seminit_absimp_pos_abt.
    can_change_aop_solver.
    eauto. eauto.
    right. do 3 eexists. splits; eauto.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  (* v = Vint32 ($ vy) *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply seminit_absimp_pos_cons.
  can_change_aop_solver.
  eauto. eauto.
  right. do 3 eexists. splits; eauto.
  eapply absinfer_eq.
  subst v.

  (*efield (Sem_info ′ [pos ′]) pevent =ₑ 〈 OS_EVENT ∗ 〉 os_mutex.PlaceHolder;ₛ *)
  (* unfold the vallist of  efield (Sem_info ′ [pos ′]) *)
  match goal with H: new_array_type_vallist_match _ (_ ++ ?vl :: _) |- _ =>
  lets Hsplit : H end.
  eapply new_array_type_vallist_match_split in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_9 Hsp.
  repeat try (destruct Hvl as (? & Hvl)). subst semvl.

  hoare forward.
  auto with zarith.
  unfold AOSTCBPrioTbl.
  {
    introv Hsat.
    unfold PlaceHolder.
    eapply cast_rv_tptr.
    eapply addrof_gvar_rv.
    apply astar_l_anotinlenv_intro.
    sep cancel (Agvarenv' OSPlaceHolder). 
    eauto.
    sep_lift_context_in Hsat A_dom_lenv.
    apply astar_l_adomlenv_elim in Hsat.
    destruct Hsat.
    match goal with H: eq_dom_env _ _ |- _ => clear -H; unfolds in H; rename H into Henv end.
    unfold EnvMod.indom.
    pure_auto.
    destruct H as [[]].
    assert (~ (ListSet.set_In (OSPlaceHolder, t)
                              ((value, long)
                                 :: (sem, (long) ∗)
                                 :: (os_code_defs.pos, long) :: (x, char_t) :: (y, char_t) :: (p, OS_EVENT ∗)  :: nil))).
    simpl. 
    repeat (eapply Classical_Prop.and_not_or; split; [pure_auto | idtac]).
    auto.
    pure_auto.
    eapply H0. rewrite Henv. pure_auto.
    simpl; auto.
  }
  (* end of assign PlaceHolder *)
  
  hoare unfold.
  hoare_lifts_trms_pre (Aop, seminfoid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply seminit_absimp_set_placeholder; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.
  
  hoare_lifts_trms_pre (Aisr, Ais, Aier).
  transform_pre add_aemp_isr_is_prop  ltac:(sep cancel Aisr; sep cancel Ais; sep cancel Aier).

  (* EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel Aier.
  unfold AOSTCBPrioTbl.
  unfold EvtInv.
  unfold ASemEIBs.
  assert (Hup: (x8 :: x7 :: x6 :: x0 :: x1 :: x2 :: x3 :: Vptr vhold_addr :: x5 :: nil) = 
               update_nth_val 7 (x8 :: x7 :: x6 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: nil) (Vptr vhold_addr))
  by (simpl; auto).
  sep normal; sep eexists.
  sep cancel ASemCap.
  sep pauto; eauto.
  trycancel.
  unfold AMuxEIBs. unfold AMqEIBs.
  sep normal; sep eexists.
  sep cancel AMuxCap. sep cancel AMqCap.
  sep cancel APthreadMutex. sep cancel AMqAttr.
  sep split; eauto.
  sep cancel p_local. 
  sep cancel APthreadAttr.
  eapply ASeminfo_select_sn_ex_strong.
  eexists.
  exists (Z.to_nat vy).
  eexists.
  exists (x8 :: x7 :: x6 :: x0 :: x1 :: x2 :: x3 :: Vptr vhold_addr :: x5 :: nil).
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep_lifts_trms PartitionInv.
  eapply fold_PartitionInv_frm.
  unfold PartitionInv_part2.
  sep normal; sep eexists.
  trycancel_PartitionInv.
  sep pauto; eauto.
  sep cancel CapabilityInv.
  eauto.
  match goal with H: length (_ ++ _ :: _) = ∘ (OS_USER_MAX_EVENTS / 3) |- _ =>
  rewrite <- H end.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  clear -Hsp Hup.
  simpl in Hsp. destruct Hsp as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & _).
  simpl. splits; auto.
  auto. (* RH_PrioTbl_P  *)
  auto. (* R_PrioTbl_P *)
  auto. (* RL_RTbl_PrioTbl_P *)
  auto.
  
  eapply eibref_distinct_null_holder_preserve; eauto.
  3: {
    eapply SEM_ECB_P_null_holder_preserve; eauto.
  }
  2: { 
    eapply MUX_ECB_P_null_holder_preserve; eauto.
  }
  eapply Q_ECB_P_null_holder_preserve; eauto.
  eapply RH_SEM_NOT_IN_CORE_P_hold_neid; eauto.
  introv Hf; simpljoin; tryfalse.
  eapply RH_SEM_EINFO_ECB_P_set_to_hold; eauto.
  eapply SemCapArray_P_hold; eauto.
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  {
    rewrite Hup.
    eapply EIBArray_P_hold_for_update_to_hold'; eauto.
    split; auto with zarith.
    try solve_usr_max_evts_rgn.
    eapply semb_corr with (i:= $ vy) in H; auto with zarith.
    unfold get in H, Hget_null; simpl in H, Hget_null.
    rewrite Hget_null in H; destruct H as (? & ? & ? & Hget & Hvtp & ?); inverts Hvtp; inverts Hget.
    unfolds; simpl; auto.
    rewrite Int.unsigned_repr; try solve_usr_max_evts_rgn.
    rewrite int_ltu_zero_eq_false; auto.
    apply Int.unsigned_range_2.
  }
  pure_auto.
  pure_auto.
  (* end of EXIT_CRITICAL;ₛ *)

  (*p ′ =ᶠ OSSemCreate (·〈 (Int16u) ∗ 〉 value ′·);ₛ*)
  hoare forward.  
  2: {
      change (Vint32 i :: v0 :: nil) with ((Vint32 i :: nil) ++ (v0 :: nil)) in *.
      instantiate (3:= v0). instantiate (3:= (Vint32 i :: nil)).
      sep cancel Aop.
      unfold init_lg.
      sep cancel p_local.
      eauto.
  }
  destruct_s s.
  simpl.

  get_hsat Hsat.
  clear -Hsat Hv_range. 
  sep_lifts_trms_in Hsat (Alvarmapsto value).
  destruct Hsat.
  simpljoin. simpl in H0,H2,H3. simpljoin.
  rewrite H6.
  rewrite Int.unsigned_zero in H7.
  eapply mapstoval_load in H7.
  eapply join_emp_eq in H1. subst x6.
  lets Hle: load_local H0 H7.
  rewrite Hle.
  simpl.
  eapply ecast_intlemma1 in Hv_range.
  rewrite Hv_range.
  splits; auto.
  simpl; auto.
  pure_auto.

  unfold retpost. introv Hsat.
  inverts Hsat; sep pauto.
  get_hsat Hsat. sep destruct Hsat.
  sep split in Hsat. simpljoin1. pure_auto.
  
  simpl. clear -Hv_range. pure_auto.  

  introv Hsat. sep destruct Hsat.
  sep pauto. sep cancel p_local. sep auto.

  introv Hsat. sep destruct Hsat. 
  sep pauto. sep cancel p_local. sep auto.

  hoare unfold.
  match goal with H: _ = Vnull /\ _ \/ _, H': _ :: _ = _ :: _ |- _ =>
  rename H into Hretor; inverts H' end.
  (* logic_val ... = logic_val ... *)

 (* ENTER_CRITICAL;ₛ *)
  hoare forward prim.
  unfold EvtInv.
  unfold ASemEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (ASemCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ ASemCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lsem; rename vl into semcapvl' end.
  hoare_lifts_trms_pre (SemCapArray_P, length semcapvl').
  eapply pure_split_rule'; introv Hsemcap_vl'.
  eapply pure_split_rule'; introv Hsemcap_len'.
  hoare unfold.
  destruct lsem as (lsem_b' & lsem_i').
  (*efield (Sem_info ′ [pos ′]) pevent =ₑ p ′;ₛ*)
  eapply backward_rule1.
  intros.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat ASeminfo. 
  eapply ASeminfo_unfold_any_idx_frm in Hsat. 
  instantiate (1:= Z.to_nat vy) in Hsat.
  eauto.
  lets Hl: aseminfo_len_frm Hsat. 
  clear -Hl H22 H23.
  rewrite Hl.
  unfold nat_of_Z.
  auto with zarith.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  mytac.
  (*assign rule*)
  (* unfold the vallist of  efield (Sem_info ′ [pos ′]) *)  
  match goal with H: new_array_type_vallist_match _ _ |- _ => 
  lets Hsplit : H end. (* new_array_type_vallist_match ... *)
  eapply new_array_type_vallist_match_split in Hsplit; eauto.
  clear Hsp1 Hsp2 Hsp.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_9 Hsp.
  repeat try (destruct Hvl as (? & Hvl)). subst.

  hoare forward; try auto with zarith.
  pure_auto.
  (* end of assign *)
   assert (Hvy_pos: 0 <= vy).
  { auto with zarith. }


  hoare_lifts_trms_pre (tcbllsegevaux,AOSTCBList, p_local).
  eapply backward_rule1.
  introv Hsat. 
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  match goal with H: SEM_ECB_P ?loc ?ptr ?ecb ?fecbh ?fecbvl ?sem ?mux ?mq |- _ =>
  rename loc into locmp; rename ptr into ptrmp; rename ecb into ecbls;
  rename sem into semeibs; rename mux into muxeibs; rename mq into mqeibs
  end.
  match goal with H: join (sig _ (_, ?vp, _)) _ _ |- _ => rename vp into cur_evp end.
  match goal with H : join (sig tid ?vt) _ ?abs, H' : join _ ?abs locmp |- _ => rename vt into vct end.
   assert (Hevptr: get ptrmp tid = Some (Vnull, cur_evp, Vnull)).  
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  assert (Hloc: get locmp tid = Some vct).
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  hoare_assign_evaux.
  hoare_assign_evaux.
  unfold isevloc; auto.
  match goal with H: join (sig _ (_, ?vp, _)) _ _ |- _ => rename vp into cur_evp end.
  assert (Heid: forall eid, cur_evp = Vptr eid -> (~ eib_ref semeibs muxeibs mqeibs eid) /\ is_sem ecbls eid).  
  {
    introv Hevp.
    subst cur_evp.
    destruct Hretor as [Hnull | Heptr].
    destruct Hnull; tryfalse.
    destruct Heptr as (_ & Hcre2 & Hs_nc').
    subst.
    eapply sem_ecb_cre2; eauto.
  } 
  assert (Hncre1: forall eid,
             cur_evp = Vptr eid ->
             ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid)). 
  {
    introv Hcp Hex. subst cur_evp.
    destruct Hex as (t & Htneq & Htle).
    destruct Hretor as [Hnull | Heptr].
    destruct Hnull. tryfalse.
    destruct Heptr. simpljoin. subst.
    eapply evcre_nodup_cre1_cre2_contra; eauto.
  }
  assert (Hncre2: forall eid,
             cur_evp = Vptr eid ->
             ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid)).
  {
    introv Hcp Hex. subst cur_evp.
    destruct Hex as (t & Htneq & Htle).
    destruct Hretor as [Hnull | Heptr].
    destruct Hnull. tryfalse.
    destruct Heptr. simpljoin. subst.
    eapply evcre_nodup_cre2_cre2_contra; eauto.
  }
  assert (Hndel: forall eid,
             cur_evp = Vptr eid ->
             ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel eid)).  
  {
    introv Hcp Hex. subst cur_evp.
    destruct Hex as (t & Htneq & Htle).
    destruct Hretor as [Hnull | Heptr].
    destruct Hnull. tryfalse.
    destruct Heptr. simpljoin. subst.
    specialize (Heid eid (eq_refl _)). destruct Heid.
    eapply ecbdel_sem_contra; eauto.    
  }
  fold_evaux_sem_loc (V$ os_code_defs.__EvLoc_normal) Vnull.

  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  assert (Hv: vy = Int.unsigned (Int.repr vy)).  
  { 
    rewrite int_usign_eq; auto with zarith.
    solve_usr_max_evts_rgn.
  }
  rewrite Hv in H41.
  lets H00: semb_corr H20 H41.
  match type of H00 with _ -> _ -> ?R => assert (R); [apply H00 | ] end.
  rewrite int_ltu_zero_eq_false; auto.
  apply Int.unsigned_range_2.
  clear H00.
  destruct H49 as (eid_opt & tp0 & sc0 & (Hget & Hvtp & Heidor)).

  destructs H52. (* isflag ... /\ isevloc ... /\ ... *)
  unfold isevptr, isptr in H52.
  destruct H52.

  (* p is null *)
  subst cur_evp. 
  hoare_lifts_trms_pre (Aop, seminfoid, evlocid, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply seminit_absimp_set_ecb_ptr_null; auto.
  can_change_aop_solver.
  simpl. intros; auto.  
  eauto.
  eauto.
  eapply absinfer_eq.

  (* preparation for EXIT_CRITICAL;ₛ *) 
  assert (Hset: set ptrmp tid (Vnull, Vnull, Vnull) = ptrmp) 
    by (rewrite get_set_same; eauto).
  unfold set at 3. unfold EvAuxPtrMap.
  unfold set, EvAuxPtrMap in Hset.
  rewrite Hset.
  
  (* EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  sep cancel CapabilityInv.
  sep cancel tcbdllflag.
  unfold p_local. sep normal. sep cancel CurTid.
  unfold LINV, OSLInv.
  sep pauto.
  2: { splits; eauto. unfold isevloc. left. auto. }
  unfold EvtInv.
  unfold tcbllsegevaux.
  sep pauto; eauto.
  sep cancel llsegevaux.
  assert (Hup: (x17 :: x16 :: x15 :: x9 :: x10 :: x11 :: x12 :: Vnull :: x14 :: nil)  = 
               update_nth_val 7 (x17 :: x16 :: x15 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: nil) Vnull) 
    by (simpl; auto).
  trycancel.
  unfold ASemEIBs.
  sep normal. sep eexists.
  sep cancel ASemCap.
  eapply ASeminfo_select_sn_ex_strong.
  eexists. exists (Z.to_nat vy). eexists.
  exists (x17 :: x16 :: x15 :: x9 :: x10 :: x11 :: x12 :: Vnull :: x14 :: nil).
  sep cancel APthreadAttr.
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel Aier.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep split; eauto.
  sep pauto.
  eapply RH_SEM_NOT_IN_CORE_P_hold_neid; eauto.
  introv Hf; simpljoin; tryfalse.
  eapply RH_SEM_EINFO_ECB_P_null_preserve; eauto.
  eapply SemCapArray_P_hold; eauto.
  rewrite Hup.
  rewrite <- Hv in H41.
  eapply EIBArray_P_hold_for_update_to_null'; eauto.
  solve_usr_max_evts_rgn.

  rewrite <- Hv in H41. splits; auto.

  rewrite <- H39. 
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  clear -Hsp Hup.
  simpl in Hsp. destruct Hsp as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & _).
  simpl. splits; auto.

  eapply eibref_distinct_infonull_preserve; eauto.
  eapply evdel_nodup_normal_preserve; eauto.
  eapply evcre_nodup_normal_preserve; eauto.
  3: { eapply sem_ecb_p_infonull_preserve; eauto. }
  2: { eapply mux_ecb_p_infonull_preserve; eauto. }
  eapply q_ecb_p_infonull_preserve; eauto.
  go.
  pure_auto.

  Focus 2.
  (* p is not null *)
  destruct H52. subst cur_evp.
  rename x18 into eid.
  specialize (Heid eid (eq_refl _)).
  destruct Heid as (Hnref & Hissem).

  casetac eid vhold_addr Heq Hne.
  (* eid = vhold_addr *)
  subst.
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply seminit_absimp_set_ecb_holder_abt; eauto.
  can_change_aop_solver.
  simpl. intros; auto.
  eapply absinfer_eq.
  apply absabort_rule.
  
  hoare_lifts_trms_pre (Aop, seminfoid, evlocid, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply seminit_absimp_set_ecb_ptr_n_null; auto.
  can_change_aop_solver.
  simpl. intros; auto.  
  eauto.
  eauto.
  eapply absinfer_eq.

  (* EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  sep cancel CapabilityInv.
  sep cancel tcbdllflag.
  unfold p_local. sep normal. sep cancel CurTid.
  unfold LINV, OSLInv.
  sep pauto.
  2: { splits; eauto. unfold isevloc. left. auto. }
  unfold EvtInv.
  unfold tcbllsegevaux.
  sep pauto; eauto.
  sep cancel llsegevaux.
  assert (Hup: (x17 :: x16 :: x15 :: x9 :: x10 :: x11 :: x12 :: Vptr eid :: x14 :: nil)  = 
               update_nth_val 7 (x17 :: x16 :: x15 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: nil) (Vptr eid)) 
    by (simpl; auto).
  trycancel.
  unfold ASemEIBs.
  sep normal. sep eexists.
  sep cancel ASemCap.
  eapply ASeminfo_select_sn_ex_strong.
  eexists. exists (Z.to_nat vy). eexists.
  exists (x17 :: x16 :: x15 :: x9 :: x10 :: x11 :: x12 :: (Vptr eid) :: x14 :: nil).
  sep cancel APthreadAttr.
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel Aier.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep split; eauto.
  sep pauto.
  eapply RH_SEM_NOT_IN_CORE_P_hold_eid_nref; eauto.
  destruct Hretor as [(Hnull & _) | (_ & Heq & (ptr & Heq2 & Hs_nc'))]; tryfalse.
  inverts Heq2; auto.
  eapply RH_SEM_EINFO_ECB_P_ptr_preserve; eauto.
  eapply SemCapArray_P_hold; eauto.
  rewrite Hup. rewrite <- Hv in H41.
  eapply EIBArray_P_hold_for_update_to_tid'; eauto.
  { match goal with H: length ?vl = _ |- _ = $ Z.of_nat (length ?vl) => rewrite H end.
     rewrite Z2Nat.id; auto.
  }
  {
    solve_usr_max_evts_rgn.
  }
  apply Int.unsigned_range_2.
  rewrite <- Hv in H41. splits; auto.
  rewrite <- H39.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.
  eapply new_array_type_vallist_match_compose_struct; auto.
  clear -Hsp Hup.
  simpl in Hsp. destruct Hsp as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & _).
  simpl. splits; auto.
  eapply eibref_distinct_noref_eid_preserve; eauto.
  eapply evdel_nodup_normal_null_preserve; eauto.
  eapply evcre_nodup_normal_null_preserve; eauto.
  eapply Q_ECB_P_normal_null_preserve; eauto.
  eapply MUX_ECB_P_normal_null_preserve; eauto.
  eapply SEM_ECB_P_normal_null_preserve; eauto.
  go.
  pure_auto.

  Unfocus.
  rename H22 into Hrgn1; rename H23 into Hrgn2.
  (* back to the case p = Vnull *)
  clear - H2 H3 eq1 Hv_range Hrgn1 Hrgn2 Hif_false.
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply seminit_absimp_create_error; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (* if  If (p ′ ==ₑ NULL){RETURN ′ (-1)};ₛ *) 
  hoare forward. 
  hoare unfold.
  hoare forward. 
  eapply hoare_disj_afalseP_l_pre.
  hoare_split_pure_all.
  destruct H; tryfalse.

  rename H22 into Hrgn1; rename H23 into Hrgn2.
  (* the remaining part for the case p <> Vnull *)
  clear - H2 H3 eq1 Hv_range Hrgn1 Hrgn2 Hif_false Hrgn3 Hrgn4 Hvy_pos.
  destruct eid as (vr_b, vr_i).
  hoare forward.
  pure_auto.
  hoare unfold. tryfalse.
  instantiate (1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare_split_pure_all.

  hoare forward prim.
  unfold EvtInv.
  unfold ASemEIBs.
  hoare normal pre.
  hoare_ex_intro.
  hoare_lifts_trms_pre (RH_SEM_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hs_nc.
  hoare_lifts_trms_pre (ASemCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ ASemCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lsem; rename vl into semcapvl end.
  hoare_lifts_trms_pre (SemCapArray_P, length semcapvl).
  eapply pure_split_rule'; introv Hsemcap_vl.
  eapply pure_split_rule'; introv Hsemcap_len.
  hoare unfold.
  destruct lsem as (lsem_b & lsem_i).
  (*split ASeminfo*)
  eapply backward_rule1.
  intros.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat ASeminfo.
  eapply ASeminfo_unfold_any_idx_frm in Hsat.
  instantiate (1:= Z.to_nat vy) in Hsat. 
  eauto.
  lets Hl: aseminfo_len_frm Hsat. 
  clear -Hl Hrgn1 Hrgn2.
  rewrite Hl.
  unfold nat_of_Z.
  auto with zarith.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  mytac.
  (* efield (Sem_info ′ [pos ′]) sem_type =ₑ SEM_COUNTING ′;ₛ *)
  (*assign rule*)
  (* unfold the vallist of  efield (Sem_info ′ [pos ′]) *)
  lets Hsplit : H5.
  eapply new_array_type_vallist_match_split in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_9 Hsp.
  repeat try (destruct Hvl as (? & Hvl)); subst.

  hoare forward.
  (* end of assignment *)
  assert (Hv: vy = Int.unsigned ($ vy)).
  {
    clear -Hrgn1 Hrgn2 Hrgn3 Hrgn4 Hvy_pos.
    int auto.
  }
  rewrite Hv in H16.
  assert (Hltuf: Int.ltu ($vy) Int.zero = false).
  {
    rewrite int_ltu_zero_eq_false; auto.
  }
  assert (Hle: Int.unsigned ($ vy) <= Int.max_unsigned).
  {
    clear -Hrgn1 Hrgn2 Hrgn3 Hrgn4 Hvy_pos.
    int auto.
  }
  lets H00: semb_corr H0 H16 Hltuf Hle.
  simpljoin1.

  hoare_lifts_trms_pre (Aop, seminfoid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply seminit_absimp_set_type; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  
  (* EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local. 
  sep cancel Aier.
  sep cancel CapabilityInv.
  unfold EvtInv.
  unfold ASemEIBs.
  assert (Hup: (V$ SEM_COUNTING :: x7 :: x6 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: nil)  = 
               update_nth_val 0 (x8 :: x7 :: x6 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: nil) (V$ SEM_COUNTING)).
  simpl; auto.
  sep normal. sep eexists.
  sep cancel ASemCap.
  trycancel.
  sep pauto; eauto.
  sep cancel APthreadAttr.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  eapply ASeminfo_select_sn_ex_strong.
  eexists. exists (Z.to_nat vy). eexists.
  exists  (V$ SEM_COUNTING :: x7 :: x6 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: nil).
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep pauto; eauto.
  splits; auto. congruence.
  rewrite <- H14.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  simpl. split; auto.
  simpl in Hsp.
  simpljoin1. splits; auto.
  eapply eibref_distinct_set_pos_semeib; eauto.
  3: { eapply SEM_ECB_P_set_sem_type_preserve; eauto. }
  2: { eapply MUX_ECB_P_set_sem_type_preserve; eauto. }
  eapply Q_ECB_P_set_sem_type_preserve; eauto.
  eapply RH_SEM_NOT_IN_CORE_P_hold_same_ptr; eauto.
  { eapply RH_SEM_EINFO_ECB_P_set_type_preserve; eauto. }
  eapply SemCapArray_P_hold; eauto.
  { 
    rewrite Hup.
    eapply EIBArray_P_hold_for_update_type'; eauto.
    rewrite H16.
    clear -Hrgn1 Hrgn2 Hrgn3 Hrgn4 Hvy_pos. int auto.
    rewrite H16.
    clear -Hrgn1 Hrgn2 Hrgn3 Hrgn4 Hvy_pos. int auto.
  }
  pure_auto.
  pure_auto.
  (* end of EXIT_CRITICAL *)  

  (*ENTER_CRITICAL;ₛ *)
  hoare forward prim.
  unfold EvtInv.
  unfold ASemEIBs.
  hoare normal pre.
  hoare_ex_intro.
  hoare_lifts_trms_pre (RH_SEM_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hs_nc'.
  hoare_lifts_trms_pre (ASemCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ ASemCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lsem; rename vl into semcapvl' end.
  hoare_lifts_trms_pre (SemCapArray_P, length semcapvl').
  eapply pure_split_rule'; introv Hsemcap_vl'.
  eapply pure_split_rule'; introv Hsemcap_len'.
  hoare unfold.
  destruct lsem as (lsem_b' & lsem_i').

  (*split ASeminfo*)
  eapply backward_rule1.
  intros.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat ASeminfo.
  eapply ASeminfo_unfold_any_idx_frm in Hsat. 
  instantiate (1:= Z.to_nat vy) in Hsat.
  eauto.
  lets Hl: aseminfo_len_frm Hsat.
  clear -Hl Hrgn1 Hrgn2.
  rewrite Hl.
  unfold nat_of_Z.
  auto with zarith.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  mytac.
  (* efield (Sem_info ′ [pos ′]) tasks_blocked =ₑ CFalse;ₛ *)
  (*assign rule*)
  (* unfold the vallist of  efield (Sem_info ′ [pos ′]) *)
  lets Hsplit : H24.
  eapply new_array_type_vallist_match_split in Hsplit; eauto.
  clear Hsp1 Hsp2 Hsp.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_9 Hsp.
  simpljoin.

  hoare forward.
  (* end of assign *)

  (* EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  sep cancel CapabilityInv.
  sep cancel APthreadAttr.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  unfold EvtInv.
  unfold ASemEIBs.
  assert (Hup: (x20 :: x19 :: x18 :: x12 :: x13 :: x14 :: Vint32 Int.zero :: x16 :: x17 :: nil)  = 
               update_nth_val 6 (x20 :: x19 :: x18 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: nil) (Vint32 Int.zero)). 
  simpl; auto.
  sep normal. sep eexists.
  sep cancel ASemCap.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  trycancel.
  eapply ASeminfo_select_sn_ex_strong.
  eexists. exists (Z.to_nat vy). eexists.
  exists (x20 :: x19 :: x18 :: x12 :: x13 :: x14 :: Vint32 Int.zero :: x16 :: x17 :: nil). 
  sep cancel Aarray_new.
  sep cancel Aarray_new.
   sep pauto; eauto.
  rewrite Hup.
  eapply EIBArray_P_hold_for_update_same'; eauto.
  rewrite H35.  clear -Hrgn1 Hrgn2 Hrgn3 Hrgn4 Hvy_pos. int auto.
  rewrite H35.
  clear -Hrgn1 Hrgn2 Hrgn3 Hrgn4 Hvy_pos. int auto.
  rewrite <- H33.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  clear -Hsp Hup.
  simpl in Hsp. destruct Hsp as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & _).
  simpl. splits; auto.
  pure_auto.
  pure_auto.
  (* end of EXIT_CRITICAL *)  

  (* ENTER_CRITICAL;ₛ *)
  hoare forward prim.
  unfold EvtInv.
  hoare unfold.
  hoare_lifts_trms_pre (Aop, pblsid).
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _ {{_ ** Hpbls ?abs ** _}} _ {{ _ }} =>
  rename abs into pbls end.
  assert (Hsem: (exists posv, get pbls x = Some posv) 
                \/ ~ (exists posv, get pbls x = Some posv)) by tauto.
  hoare_lifts_trms_pre (Aop, pblsid).
  destruct Hsem as [Hsem | Hsem].
  2 : {
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply seminit_absimp_sem_pos_abt; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  destruct Hsem as (posv & Hsem).
  (* split poslist *)
  eapply backward_rule1. 
  intros.
  eapply pos_list_split_frm.
  sep cancel APosblkList.
  eauto.
  eauto.
  unfold node.
  hoare unfold.
  (* ∗ sem ′ =ₑ pos ′;ₛ *)
  hoare_lifts_trms_pre (Aop, pblsid).
  simpl Astruct.
  hoare forward.
  hoare_lifts_trms_pre (Aop, pblsid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply seminit_absimp_sem_pos; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  
  (*  EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel CapabilityInv.
  unfold EvtInv.
  unfold APosblkList.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  eapply pos_sllseg_merge.
  sep cancel pos_sllseg.
  sep cancel pos_sllseg.
  sep cancel AMuxEIBs. sep cancel AMqEIBs.
  instantiate (2:= (set v'120 (v'122, Int.zero) ($ vy))).
  instantiate (3:= (V$ vy :: x22 :: nil)).
  unfold node.
  simpl Astruct.
  sep pauto.
  eapply PbMod.joinsig_set_set;eauto.
  instantiate (1:= $ vy).
  clear -H49. 
  unfold TcbJoin in *. unfold join,sig,set in *. unfold PbMap in *.
  unfold PbMod.join in *.
  intros.
  specialize H49 with (a:= a).
  rewrite PbMod.sig_sem in *.
  rewrite PbMod.set_sem in *.
  destruct (tidspec.beq (v'122, Int.zero) a) eqn: eq1; 
  destruct (PbMod.get v'121 a); tryfalse; auto.
  unfold ev_aux_code.V_posblk_pos. simpl. auto.
  split; auto. go.
  rewrite PbMod.map_get_set. auto.
  auto.
  pure_auto.
  (* end of EXIT_CRITICAL;ₛ *)
  hoare forward.
Qed. 
