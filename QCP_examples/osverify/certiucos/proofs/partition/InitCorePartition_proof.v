Require Import ucos_include.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import abs_op.
Require Import inv_prop.
Require Import symbolic_lemmas.
Require Import protect.
Require Import sem_lab.
Require Import cast_int_ptr_pure.
Require Import abs_op_partition_ext.
Require Import partition_common.

Require Import gjb_common.
Require Import tv_match.
Require Import Aarray_new_common.
Require Import symbolic_lemmas.
Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.
Open Scope list_scope.

Lemma mund_int_a2:
  forall i,
    Int.unsigned i <= 255 ->
    (if Int.unsigned i <=? Byte.max_unsigned then true else false) = true.
  intros.
  apply leb_bytemax_true_intro in H.
  rewrite H.
  auto.
Qed.

Definition get_ksdomscd_dom (j:nat) (dscd_vll :list dscheduleConfVal) kscd_dom :=
exists dscd_vl,
nth_vallist j dscd_vll = Some dscd_vl /\
V_DSdomain dscd_vl = Some (Vint32 kscd_dom).

Lemma Avalid_compose_strong:
 forall  addr_vl1 ehdrvll1 addr_vl2 ehdrvll2 s,
     s |= Avalid addr_vl1 ehdrvll1 ** 
             Avalid  addr_vl2 ehdrvll2->
     s |= Avalid (addr_vl1 ++ addr_vl2) (ehdrvll1 ++ ehdrvll2) .
Proof.
induction addr_vl1; induction ehdrvll1;
unfold Avalid in *; fold Avalid in *; introv Hsat.
sep pauto.
eapply astar_l_afalse_elim in Hsat; simpl in Hsat; tryfalse.
destruct a; try (eapply astar_l_afalse_elim in Hsat; simpl in Hsat; tryfalse).
destruct a; try (eapply astar_l_afalse_elim in Hsat; simpl in Hsat; tryfalse).
do 2 rewrite <- app_comm_cons.
unfold Avalid; fold Avalid.
sep pauto.
Qed.

Lemma Avalid_compose_strong_frm:
 forall  addr_vl1 ehdrvll1 addr_vl2 ehdrvll2 s P,
     s |= Avalid addr_vl1 ehdrvll1 ** 
             Avalid  addr_vl2 ehdrvll2 ** P->
     s |= Avalid (addr_vl1 ++ addr_vl2) (ehdrvll1 ++ ehdrvll2) ** P.
Proof.
intros.
sep cancel P.
eapply Avalid_compose_strong; eauto.
Qed.

Lemma Avalid_compose_strong':
 forall  addr_vl1 ehdrvll1 addr_vl2 ehdrvll2 s addr_v ehdrvl,
     s |= Avalid addr_vl1 ehdrvll1 **
             Astruct addr_v Elf32_Ehdr ehdrvl **
             [|struct_type_vallist_match Elf32_Ehdr ehdrvl|] **
             Avalid  addr_vl2 ehdrvll2->
     s |= Avalid (addr_vl1 ++ (Vptr addr_v ::  addr_vl2)) (ehdrvll1 ++ (ehdrvl :: ehdrvll2)) .
Proof.
intros.
eapply Avalid_compose_strong.
sep pauto.
Qed.

Lemma Avalid_compose_strong_frm':
 forall  addr_vl1 ehdrvll1 addr_vl2 ehdrvll2 s addr_v ehdrvl P,
     s |= Avalid addr_vl1 ehdrvll1 **
             Astruct addr_v Elf32_Ehdr ehdrvl **
             [|struct_type_vallist_match Elf32_Ehdr ehdrvl|] **
             Avalid  addr_vl2 ehdrvll2** P ->
     s |= Avalid (addr_vl1 ++ (Vptr addr_v ::  addr_vl2)) (ehdrvll1 ++ (ehdrvl :: ehdrvll2)) ** P.
Proof.
intros.
sep cancel P.
eapply Avalid_compose_strong'; eauto.
Qed.

Lemma Avalid_unfold_any_idx_frm:
 forall  addr_vl ehdrvll idx s P,
     (idx < length addr_vl)%nat ->
     s |= Avalid addr_vl ehdrvll ** P->
     s |= (EX addr_vl1 ehdrvll1 addr_vl2 ehdrvll2 addr_v ehdrvl,
             Avalid addr_vl1 ehdrvll1 **
             Astruct addr_v Elf32_Ehdr ehdrvl **
             [|struct_type_vallist_match Elf32_Ehdr ehdrvl|] **
             Avalid  addr_vl2 ehdrvll2 **
             [| addr_vl = (addr_vl1 ++ (Vptr addr_v ::  addr_vl2)) |] **
             [| ehdrvll = (ehdrvll1 ++ (ehdrvl :: ehdrvll2)) |] **
             [| length addr_vl1 = idx /\ length addr_vl2 = Nat.sub (length addr_vl) (S idx)|] **
             [| length ehdrvll1 = idx /\ length ehdrvll2 = Nat.sub (length ehdrvll) (S idx)|]) ** P.
Proof.
induction addr_vl; introv Hidx Hsat;
simpl length in *.
false.
auto with zarith.
unfold Avalid in Hsat; fold Avalid in Hsat;
destruct a; try solve[ try eapply astar_l_afalse_elim in Hsat; simpl in Hsat; tryfalse].
destruct ehdrvll; try solve[ try eapply astar_l_afalse_elim in Hsat; simpl in Hsat; tryfalse].
destruct idx.
sep normal.
exists (nil: list val) (nil: list (list val)) addr_vl ehdrvll a l.
simpl length.
do 2 rewrite app_nil_l.
sep pauto.
split; auto with zarith.
split; auto with zarith.
sep lift 3%nat in Hsat.
rewrite <- Nat.succ_lt_mono in Hidx.
eapply IHaddr_vl in Hsat; eauto.
sep normal in Hsat.
sep destruct Hsat.
sep normal.
exists (Vptr a :: x) (l :: x0) x1 x2 x3 x4.
unfold Avalid. fold Avalid.
simpl length.
sep pauto;eauto.
Qed.

Lemma Avalid_unfold_any_idx:
 forall  addr_vl ehdrvll idx s,
     (idx < length addr_vl)%nat ->
     s |= Avalid addr_vl ehdrvll ->
     s |= (EX addr_vl1 ehdrvll1 addr_vl2 ehdrvll2 addr_v ehdrvl,
             Avalid addr_vl1 ehdrvll1 **
             Astruct addr_v Elf32_Ehdr ehdrvl **
             [|struct_type_vallist_match Elf32_Ehdr ehdrvl|] **
             Avalid  addr_vl2 ehdrvll2 **
             [| addr_vl = (addr_vl1 ++ (Vptr addr_v ::  addr_vl2)) |] **
             [| ehdrvll = (ehdrvll1 ++ (ehdrvl :: ehdrvll2)) |] **
             [| length addr_vl1 = idx /\ length addr_vl2 = Nat.sub (length addr_vl) (S idx)|] **
             [| length ehdrvll1 = idx /\ length ehdrvll2 = Nat.sub (length ehdrvll) (S idx)|]).
Proof.
intros.
eapply Avalid_unfold_any_idx_frm with (P:= Aemp) (s:= s) in H; eauto.
sep pauto; eauto.
sep pauto; eauto.
Qed.

Lemma cast_int_vl_to_ptr_nil:
forall baddr_vl addr_vl,
          cast_int_vl_to_ptr baddr_vl addr_vl ->
          baddr_vl = nil <-> addr_vl = nil.
Proof.
unfold cast_int_vl_to_ptr.
intros.
simpljoin.
split; intros; subst.
simpl in *.
erewrite <- length_zero_nil; auto.
erewrite <- length_zero_nil; auto.
Qed.

Lemma get_cpu_ksdom_binaddr_nil:
forall baddr_vl ksdomscdlen dscd_vll dom_vll,
   get_cpu_ksdom_binaddr ksdomscdlen dscd_vll dom_vll baddr_vl ->
   baddr_vl = nil <-> ksdomscdlen = Int.zero.
Proof.
unfold get_cpu_ksdom_binaddr.
introv Hget.
destruct Hget as (Hget & Hzero).
pose proof (Int.unsigned_range_2 ksdomscdlen).
destruct H as (H & _).
split; intros; subst.
simpl length in *.
symmetry in Hzero.
change 0%nat with (Z.to_nat 0) in Hzero.
rewrite Z2Nat.inj_iff in Hzero; auto with zarith.
eapply Int.unsigned_eq_zero in Hzero; subst.
auto.
rewrite Int.unsigned_zero in Hzero.
change (Z.to_nat 0) with 0%nat in Hzero.
eapply length_zero_nil in Hzero; subst.
auto.
Qed.

Lemma good_frm_Avalid:
forall vll1 vll2,  GoodFrm (Avalid vll1 vll2).
Proof.
induction vll1; induction vll2; unfold Avalid; fold Avalid.
go.
go.
destruct a; go.
destruct a; try solve go.
unfold GoodFrm; fold GoodFrm.
splits; auto.
go.
Qed.

Hint Resolve good_frm_Avalid : good_frm_lemmas.
Hint Resolve GoodFrm_AOSCSpacePrioTbl : good_frm_lemmas.

Lemma struct_type_vallist_match_attr_hold1:
forall vl v ,
struct_type_vallist_match pthread_attr_t vl->
struct_type_vallist_match pthread_attr_t (update_nth_val 1 vl (Vint32 v)).
Proof.
  intros.
  lets Hsp: struct_type_vallist_match_elim_3 H.
  simpljoin.
  simpl in *.
  simpljoin.
  splits; auto.
Qed.

Lemma struct_type_vallist_match_attr_hold2:
forall vl v ,
(if Int.unsigned v <=? Byte.max_unsigned then true else false) = true ->
struct_type_vallist_match pthread_attr_t vl->
struct_type_vallist_match pthread_attr_t (update_nth_val 2 vl (Vint32 v)).
Proof.
  intros.
  lets Hsp: struct_type_vallist_match_elim_3 H0.
  simpljoin.
  simpl in *.
  simpljoin.
  splits; auto.
Qed.

Require Import CapSpec.

Definition new_osq_spec_list :=
  (ios_cap_defs.ucos_CNode_Delete, ucos_CNode_Delete_spec) :: osq_spec_list.
Definition new_OS_spec := convert_spec new_osq_spec_list.

Lemma InitCorePartition_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal InitCorePartition vl logicl InitCorePartitionPre ct->
      Some r =
      BuildRetI os_internal InitCorePartition vl logicl InitCorePartitionPost ct->
      exists t d1 d2 s,
        os_internal InitCorePartition = Some (t, d1, d2, s) /\
        {|new_OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
init spec.
inverts H3.
substs.
rename v' into vi.
rename v'0 into vj.
rename v'1 into vuconf.
rename v'2 into vpt.
rename v'3 into ventry.
rename v'4 into vprio.
rename v'5 into vx.
rename v'6 into vy.
rename v'7 into s.
rename v'8 into er.

rename v'11 into rtsk_vll.
rename v'12 into absrtsk.
rename v'13 into vattr.
rename v'14 into pattr_vl.
rename v'15 into cnum.
rename v'19 into cpuc.

match goal with
 H: nth_error _ (Z.to_nat _) = Some (?v1, ?v2, ?v3, ?v4) |- _ =>
rename v1 into cpu_vl; rename v2 into drtbl_vl; rename v3 into dscd_vll; rename v4 into dom_vll
end.
match goal with
 H : get_cpu_ksdom_binaddr ?v dscd_vll dom_vll ?v1 |- _ =>
 rename v into ksdomscdlen; rename v1 into baddr_vl
end.
match goal with H: cast_int_vl_to_ptr _ ?v2 |- _ => rename v2 into addr_vl end.
match goal with H: forall _  _, nth_vallist _ ?vl = Some _ -> _ |- _ => rename vl into ehdrvll end.
match goal with H: CSPACEList_P ?v _ ?v1 |- _ => rename v into ptrvl; rename v1 into cspacels end.

rename v'31 into pb; rename v'32 into pi;
rename v'34 into priotbl.

match goal with H: Int.unsigned _ < CORENUM |- _ => rename H into Hcnum end.

(* uconf ′ =ₑ 〈 ucos_conf_t ∗ 〉 eptrconst BOOT_DATA_ADDRESS;ₛ *)
hoare_lifts_trms_pre Aop.
hoare forward.
eapply assign_rule_lvar.
split; introv Hsat; sep cancel uconf; eauto.
introv Hsat.
eapply cast_rv_tptr.
eapply ptrconst_rv.
go.
eapply eq_vptr; eauto.
introv Hsat; eexists; sep cancel p_local; simpl; auto.
(* entry ′ =ₑ 〈 (Void) ∗ 〉 NULL;ₛ *)
hoare forward.
(* j ′ =ₑ ′ 0;ₛ *)
hoare forward.

(* unfold (uconf ′ → cpus) [coreNum ′]) *)
destruct_absuconf v'10.
simpl AucosConf.
unfold node.
unfold ACPUs.
hoare unfold.

(* hoare normal pre; hoare_ex_intro.
hoare_split_pure_all.
destruct H17 as (H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24).
destruct H15. *)
(* hoare unfold. *)
unfold_bootaddr boot_b.
protect Heqboot_b.
inversion H14.
subst v'0.
subst.
destruct v'2 as (cpu_b, cpu_i).
match goal with H: length cpuc = _ |- _ => rename H into Hlen_cpu end.

eapply backward_rule1.
introv Hsat.
sep_lifts_trms_in Hsat Acpus'.
eapply Acpus'_unfold_any_idx_frm with (idx:= Z.to_nat (Int.unsigned cnum)); eauto.
rewrite Hlen_cpu.
unfold CORENUM in *; unfold nat_of_Z; auto with zarith.
unfold node_offt.
(* hoare normal pre; hoare_ex_intro.
hoare_split_pure_all.
substs.
destruct H32, H36.
destruct cpu_vl. *)
hoare unfold.
(* unfold node_offt.
hoare normal pre.
hoare_ex_intro.
hoare_split_pure_all.
destruct H14 as (Heq & Hmat_cpu).
inversion Heq. *)
match goal with H: id_addrval (boot_b, Int.zero) cpus ucos_conf_t = Some (?cb, ?cpu_i) |- _ => rename cb into cpu_b end.


rewrite <- H40 in H6.
rewrite nth_error_middle in H6.
inverts H6.
inverts H7.
(* destruct cpu_vl. *)
match goal with H: CPU_ksDomScLength_Good _ |- _ =>
unfolds in H ; destruct H as (ksdomscdlen' & Heq_scdlen & Hscdlen);
inverts Heq_scdlen; destruct Hscdlen as (Hscdlen_rgn1 & Hscdlen_rgn2);
rename ksdomscdlen' into ksdomscdlen end.

match goal with H: length dscd_vll = _ |- _ => rename H into Hdscd_len end.
match goal with H: length dom_vll = _ |- _ => rename H into Hdom_len end.
match goal with H: CPU_ksDomains_Good _ |- _ => rename H into Hdom_good end.
match goal with H: CPU_ksDomSchdule_Good _ |- _ => rename H into Hdscd_good end.

assert (Hcnum_rgn: (if Int.unsigned cnum <=? Byte.max_unsigned then true else false) = true).
{
clear -Hcnum.
eapply mund_int_a2.
unfold CORENUM in *.
auto with zarith.
}

(*  WHILE  ((uconf ′ → cpus) [coreNum ′]) .. cpu_ksDomScheduleLength >ₑ j ′ *)

(*1: remember irrelevant sep-conjunctions*)
(* hoare_lifts_trms_pre (ASeminfo, Alvarmapsto i).
hoare remember (1 :: 2 :: nil)%nat pre. *)

  (*2: get the while loop inv into the pre-condition,
    so the pre-condition after the while statement
    can be correctly instantiated
   *)

eapply backward_rule1 with (p := (*below is the loop inv*)
     (  EX er (* ehdrvll *) ptrvl priotbl cspacels vi vj vx vy ventry pattr_vl vprio pb pi s,
    Aisr empisr ** Aie false ** Ais nil ** Acs (true::nil) ** Aier er ** A_isr_is_prop **
    <|| s ||> **
    LV j @ char_t |-> (Vint32 vj) **
    LV entry @ (Void) ∗ |-> ventry **
    LV uconf @ ucos_conf_t ∗ |-> Vptr (boot_b, Int.zero) **
    LV y @ long |-> vy **
    LV os_code_defs.x @ long |-> vx **
    LV ios_cap_defs.prio @ char_t |-> vprio **
    LV pt @ long |-> vpt **
    LV ios_cap_defs.i @ char_t |-> vi **
    LV attr @ pthread_attr_t ∗ |-> Vptr vattr **
    LV coreNum @ char_t |-> Vint32 cnum **
    A_dom_lenv
    ((attr, pthread_attr_t ∗)
     :: (coreNum, char_t)
        :: (ios_cap_defs.i, char_t)
           :: (j, char_t)
              :: (uconf, ucos_conf_t ∗)
                 :: (pt, long)
                    :: (entry, (Void) ∗)
                       :: (ios_cap_defs.prio, char_t) :: (os_code_defs.x, long) :: (y, long) :: nil)%list **
    AIntrDomainMux (boot_b, Int.zero) v'17 m **
    AAllArea (boot_b, Int.zero) v'18 a **
    AksDomains' (Vptr v'9) dom_vll **
  AksDomSchedule' (Vptr v'8) dscd_vll **
  Aarray v'7 (Tarray char_t ∘ 2) drtbl_vl **
  Astruct (cpu_b, cpu_i +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned cnum) * (typelen cpu_conf_t)))
    cpu_conf_t (Vint32 i11 :: x4 :: Vint32 ksdomscdlen :: Vint32 i9 :: x9 :: x10 :: nil) **
  Acpus' (Vptr (cpu_b, cpu_i)) v' **
  Acpus'
    (Vptr
       (cpu_b,
       cpu_i +ᵢ
       $ Z.of_nat (S (Z.to_nat (Int.unsigned cnum)) * typelen cpu_conf_t)))
    v'0 **
    (* Acpus' (Vptr (cpu_b, cpu_i)) cpuc ** *)
    AChannelTbl (boot_b, Int.zero) v'20 m1 **
    APortTbl (boot_b, Int.zero) v'22 m3 **
    Astruct (boot_b, Int.zero) ucos_conf_t (Vint32 i8 :: Vint32 i7 :: Vint32 i4 :: Vint32 i3
                                            :: Vint32 i2 :: Vint32 i1 :: x6 :: x5 :: x :: x0 
                                            :: Vint32 i0 :: x2 :: x3 :: Vint32 i6 :: nil) **
    (* AucosConf (v'16, v'17, v'18, cpuc, v'20, v'21, v'22)
                           (u, u0, u1, u2, u3, u4, m, a, m0, m1, u5, m2, m3, u6) ** *)
    ARootTaskStk rtsk_vll absrtsk **
    Astruct vattr pthread_attr_t pattr_vl **
   [|struct_type_vallist_match pthread_attr_t pattr_vl|] **
   Avalid addr_vl ehdrvll **
    (* condition about PthreadCreatePre' *)
    (EX ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls tcbls (* t ct *) vhold ptfree lfree ptls pattrb
                   scapl mcapl qcapl, 
                   (* AOSMapTbl ** AOSUnMapTbl ** *) AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold ** 
                   AOSTCBList' p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls ptfree **
                   AOSTCBFreeList' ptfree lfree ct tcbls**
                   AOSRdyTblGrp rtbl rgrp ** (* AOSTime (Vint32 t) ** *)
                   HTCBList tcbls ** (* HTime t ** *) HCurTCB ct ** (* AGVars ** *)
                   APthreadAttr pattrb **
                   EvtInv ecbls p1 (tcbl1 ++ tcbcur :: tcbl2) tcbls vhold scapl mcapl qcapl **
                   [| RH_TCBList_ECBList_P ecbls tcbls ct|]) **
   (* condition about ucos_CNode_DeletePre' *)
    AOSCSpacePrioTbl (pb, pi) ptrvl priotbl cspacels **
    [|CSPACEList_P ptrvl 0 cspacels |] **
    [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] **
    p_local OSLInv ct init_lg **
    [| (Int.eq vj ksdomscdlen = true) \/ (* out of loop *)
        (Int.ltu vj ksdomscdlen = true /\ 
          (* i′ =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomSchedule)[j′])..ds_domain;ₛ *)
          (0 < Int.unsigned vj ->
             exists vi', vi = Vint32 vi' /\ get_ksdomscd_dom (Z.to_nat((Int.unsigned vj) - 1)) dscd_vll vi'(*  /\
            exists vx', vx = Vint32 vx' /\
                                (vx' = Int.zero \/
                                  (vx' = Int.one /\ 
                                    
                                    )) *)
            ) (* /\ *)
          ) |] (* still in the loop *)
    )
    ).
introv Hsat.
sep eexists.
sep auto.
lets Hlen_rgn: Int.unsigned_range_2 ksdomscdlen.
change ($ 0) with Int.zero.
clear -Hlen_rgn.
rewrite Inteq_true_is_Zeq.
rewrite Intlt_true_is_Zlt.
change (Int.unsigned Int.zero) with 0.
destruct Hlen_rgn as (Hlen & _).
eapply Zle_lt_or_eq in Hlen.
destruct Hlen; auto.
right; split; auto.
introv Hf; false; auto with zarith.
go.

 (*3: apply the 'seq_rule' to get the while statement
    off the remaining statements, then apply the 'while_rule'
   *)
eapply seq_rule.

(*4: prove the condition expression of while is legal *)
eapply while_rule with (tp := Int32u).
(*prove the condition expression of while is legal *)

introv Hsat.
sep destruct Hsat.
(*  Rv ((uconf ′ → cpus) [coreNum ′]) .. cpu_ksDomScheduleLength >ₑ j ′ @ *)
eexists.
eapply bop_rv.
sep get rv.
2:{
sep_get_rv_array_struct_conf.
go.
}
sep split in Hsat.
clear -H14 Hscdlen_rgn2.
unfold DSCHEDULE_SIZE in *.
eapply mund_int_a2.
destruct H14.
eapply sem_lab.semacc_int_eq_true in H; subst.
auto with zarith.
destruct H.
rewrite Intlt_true_is_Zlt in H.
auto with zarith.

simpl; eauto.
pure_auto.
simpl; auto.

(*Aistrue (j′ <ₑ  (((uconf′→ cpus)[coreNum′])..cpu_ksDomScheduleLength))*)
eapply backward_rule1 with (p := 
( EX er (* ehdrvll *) ptrvl priotbl cspacels vi vj vx vy ventry pattr_vl vprio pb pi s,
    Aisr empisr ** Aie false ** Ais nil ** Acs (true::nil) ** Aier er ** A_isr_is_prop **
    <|| s ||> **
    LV j @ char_t |-> (Vint32 vj) **
    LV entry @ (Void) ∗ |-> ventry **
    LV uconf @ ucos_conf_t ∗ |-> Vptr (boot_b, Int.zero) **
    LV y @ long |-> vy **
    LV os_code_defs.x @ long |-> vx **
    LV ios_cap_defs.prio @ char_t |-> vprio **
    LV pt @ long |-> vpt **
    LV ios_cap_defs.i @ char_t |-> vi **
    LV attr @ pthread_attr_t ∗ |-> Vptr vattr **
    LV coreNum @ char_t |-> Vint32 cnum **
    A_dom_lenv
    ((attr, pthread_attr_t ∗)
     :: (coreNum, char_t)
        :: (ios_cap_defs.i, char_t)
           :: (j, char_t)
              :: (uconf, ucos_conf_t ∗)
                 :: (pt, long)
                    :: (entry, (Void) ∗)
                       :: (ios_cap_defs.prio, char_t) :: (os_code_defs.x, long) :: (y, long) :: nil)%list **
    AIntrDomainMux (boot_b, Int.zero) v'17 m **
    AAllArea (boot_b, Int.zero) v'18 a **
    AksDomains' (Vptr v'9) dom_vll **
  AksDomSchedule' (Vptr v'8) dscd_vll **
  Aarray v'7 (Tarray char_t ∘ 2) drtbl_vl **
  Astruct (cpu_b, cpu_i +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned cnum) * (typelen cpu_conf_t)))
    cpu_conf_t (Vint32 i11 :: x4 :: Vint32 ksdomscdlen :: Vint32 i9 :: x9 :: x10 :: nil) **
  Acpus' (Vptr (cpu_b, cpu_i)) v' **
  Acpus'
    (Vptr
       (cpu_b,
       cpu_i +ᵢ
       $ Z.of_nat (S (Z.to_nat (Int.unsigned cnum)) * typelen cpu_conf_t)))
    v'0 **
    (* Acpus' (Vptr (cpu_b, cpu_i)) cpuc ** *)
    AChannelTbl (boot_b, Int.zero) v'20 m1 **
    APortTbl (boot_b, Int.zero) v'22 m3 **
    Astruct (boot_b, Int.zero) ucos_conf_t (Vint32 i8 :: Vint32 i7 :: Vint32 i4 :: Vint32 i3
                                            :: Vint32 i2 :: Vint32 i1 :: x6 :: x5 :: x :: x0 
                                            :: Vint32 i0 :: x2 :: x3 :: Vint32 i6 :: nil) **
    (* AucosConf (v'16, v'17, v'18, cpuc, v'20, v'21, v'22)
                           (u, u0, u1, u2, u3, u4, m, a, m0, m1, u5, m2, m3, u6) ** *)
    ARootTaskStk rtsk_vll absrtsk **
    Astruct vattr pthread_attr_t pattr_vl **
   [|struct_type_vallist_match pthread_attr_t pattr_vl|] **
   Avalid addr_vl ehdrvll **
    (* condition about PthreadCreatePre' *)
    (EX ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls tcbls (* t ct *) vhold ptfree lfree ptls pattrb
                   scapl mcapl qcapl, 
                   (* AOSMapTbl ** AOSUnMapTbl ** *) AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold ** 
                   AOSTCBList' p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls ptfree **
                   AOSTCBFreeList' ptfree lfree ct tcbls**
                   AOSRdyTblGrp rtbl rgrp ** (* AOSTime (Vint32 t) ** *)
                   HTCBList tcbls ** (* HTime t ** *) HCurTCB ct ** (* AGVars ** *)
                   APthreadAttr pattrb **
                   EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl**
                   [| RH_TCBList_ECBList_P ecbls tcbls ct|]) **
   (* condition about ucos_CNode_DeletePre' *)
    AOSCSpacePrioTbl (pb, pi) ptrvl priotbl cspacels **
    [|CSPACEList_P ptrvl 0 cspacels |] **
    [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] **
    p_local OSLInv ct init_lg **
    [| (* (Int.eq vj ksdomscdlen = true) \/ (* out of loop *) *)
        (Int.ltu vj ksdomscdlen = true /\ 
          (* i′ =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomSchedule)[j′])..ds_domain;ₛ *)
          (0 < Int.unsigned vj ->
             exists vi', vi = Vint32 vi' /\ get_ksdomscd_dom (Z.to_nat((Int.unsigned vj) - 1)) dscd_vll vi'(*  /\
            exists vx', vx = Vint32 vx' /\
                                (vx' = Int.zero \/
                                  (vx' = Int.one /\ 
                                    
                                    )) *)
            ) (* /\ *)
          ) |] (* still in the loop *)
    )
).
introv Hsat.
destruct Hsat as (Hsat & Histrue).
sep destruct Hsat.
lets Hcp: aconj_intro Hsat Histrue.
eapply sep_aconj_r_aistrue_to_astar in Hcp; eauto.
2:{
clear Hsat Hcp.
introv Hsat.
eapply bop_rv.
sep get rv.
2:{
sep_get_rv_array_struct_conf.
go.
}
sep split in Hsat.
clear -H14 Hscdlen_rgn2.
unfold DSCHEDULE_SIZE in *.
eapply mund_int_a2.
destruct H14.
eapply sem_lab.semacc_int_eq_true in H; subst.
auto with zarith.
destruct H.
rewrite Intlt_true_is_Zlt in H.
auto with zarith.
simpl; eauto.
pure_auto.
simpl; auto.
}
clear -Hcp.
sep split in Hcp.
destruct H3 as (Hif & _).
destruct (Int.ltu x14 ksdomscdlen) eqn: eq1;
simpl in Hif; tryfalse.
sep auto.
rewrite Int.eq_sym in H2.
rewrite ltu_eq_false in H2; auto.
destruct H2; tryfalse.
rewrite eq1 in *. auto.

hoare normal pre.
apply ex_intro_rule; intro er0.
apply ex_intro_rule; intro ptrvl0.
apply ex_intro_rule; intro priotbl0.
apply ex_intro_rule; intro cspacels0.
apply ex_intro_rule; intro vi0.
apply ex_intro_rule; intro vj0.
apply ex_intro_rule; intro vx0.
apply ex_intro_rule; intro vy0.
apply ex_intro_rule; intro ventry0.
apply ex_intro_rule; intro pattr_vl0.
repeat (apply ex_intro_rule; intro).
hoare_split_pure_all.
destruct H15 as (Hvj_lt & Hvj_pos).
lets Hvj_lt': Hvj_lt. rewrite Intlt_true_is_Zlt in Hvj_lt'.

assert (Hvj_rgn: (if Int.unsigned vj0 <=? Byte.max_unsigned then true else false) = true).
{
eapply mund_int_a2.
solve_part_int_rgn.
}
assert (Hvj_rgn': Int.unsigned vj0 < DSCHEDULE_SIZE).
{
solve_part_int_rgn.
}

(* unfold ksDomSchedule *)
destruct v'8 as (scd_b & scd_i).
eapply backward_rule1.
introv Hsat.
sep_lifts_trms_in Hsat AksDomSchedule'.
eapply AksDomSchedule'_unfold_any_idx_frm with (idx:= Z.to_nat (Int.unsigned vj0)); eauto.
rewrite Hdscd_len.
unfold DSCHEDULE_SIZE in *.
unfold nat_of_Z in *.
auto with zarith.

unfold node_offt.
hoare normal pre.
repeat (apply ex_intro_rule; intro).
hoare_split_pure_all.
destruct H15 as (Hptr & Hscd_mat).
inverts Hptr.

inverts H32.
(*  i′ =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomSchedule)[j′])..ds_domain;ₛ *)
hoare forward.
hoare_lifts_trms_pre Aop.
(* eapply assign_rule_array_struct_aop_general; *)
eapply assign_rule_lvar.
intros; split; intro Hsat.
sep cancel ios_cap_defs.i; eauto.
sep auto.
(*  Rv ((((uconf ′ → cpus) [coreNum ′]) .. cpu_ksDomSchedule) [j ′]) .. ds_domain *)
{
sep_get_rv_array_struct_conf'.
}
eapply eq_int; eauto.
introv Hsat; eexists; sep cancel p_local; simpl; auto.

(* os_code_defs.x ′ =ᶠ is_ELFProgramValid
                              (·〈 (Void) ∗
                                〉 ((((uconf ′ → cpus) [coreNum ′])
                                    .. cpu_ksDomains) [
                                   ios_cap_defs.i ′]) .. binAddress,
                              ((((uconf ′ → cpus) [coreNum ′])
                                .. cpu_ksDomains) [
                               ios_cap_defs.i ′]) .. vAddress,
                              ((((uconf ′ → cpus) [coreNum ′])
                                .. cpu_ksDomains) [
                               ios_cap_defs.i ′]) .. vAddress +ₑ
                              ((((uconf ′ → cpus) [coreNum ′])
                                .. cpu_ksDomains) [
                               ios_cap_defs.i ′]) .. dom_len·);ₛ *)

(* unfold ksDomains *)
hoare unfold.
simpl nth_val' in *.
rename i14 into vi0'.
assert(Hvi_rgn: Int.unsigned vi0' < DOMAIN_SIZE).
{ clear -H15 Hvj_rgn' Hdscd_good.
   destruct Hdscd_good as (Hdscd_dom & _).
   specialize (Hdscd_dom (Int.unsigned vj0)).
   unfold nat_of_Z in*.
   rewrite <- H15 in Hdscd_dom.
   rewrite nth_error_middle in Hdscd_dom.
   destruct Hdscd_dom as (x & dscd_vl & Heq & Hvdom & Hrgn).
   split; auto. apply Int.unsigned_range_2.
   inverts Heq; inverts Hvdom; simpljoin; auto.
}

destruct v'9 as (dom_b & dom_i).
eapply backward_rule1.
introv Hsat.
sep_lifts_trms_in Hsat AksDomains'.
eapply AksDomains'_unfold_any_idx_frm with (idx:= Z.to_nat (Int.unsigned vi0')); eauto.
rewrite Hdom_len.
unfold nat_of_Z in *.
solve_part_int_rgn.

unfold node_offt.
hoare normal pre.
repeat (apply ex_intro_rule; intro).
hoare_split_pure_all.
destruct H26 as (Hptr & Hcap_mat); inverts Hptr.
destruct H47 as (Hptr & Hdom_mat); inverts Hptr.

inverts H25.
lets Hdom_mat': Hdom_mat.
lets Hdom_vl: struct_type_vallist_match_domain_conf_t Hdom_mat.
simpljoin.
simpl in Hdom_mat'.
simpljoin.
repeat try(match goal with
   H: match ?x with
         | Vint32 _ => _
         | _ => _
        end = true |- _ =>
   destruct x; tryfalse end).

assert (Hvi_rgn': (if Int.unsigned vi0' <=? Byte.max_unsigned then true else false) = true).
{
  clear -Hvi_rgn.
  eapply mund_int_a2.
  solve_part_int_rgn.
}

match goal with H: cast_int_vl_to_ptr _ _ |- _ => rename H into Hcast end.
match goal with H: get_cpu_ksdom_binaddr _ _ _ _ |- _ => rename H into Hget_baddr end.
lets Haddr_vl_len: Hcast.
destruct Haddr_vl_len as (Hcast' & Haddr_vl_len).
lets Hbaddr_vl_len: Hget_baddr.
destruct Hbaddr_vl_len as (Hget_baddr' & Hbaddr_vl_len).

match goal with H: _ = Z.to_nat (Int.unsigned vj0) |- _ => rename H into Hvj_len end.
match goal with H: _ = Z.to_nat (Int.unsigned vi0') |- _ => rename H into Hvi_len end.

assert (Hvbaddr: nth_val (Z.to_nat (Int.unsigned vj0)) baddr_vl = Some (Vint32 i23)).
{
   clear -Hvj_len Hget_baddr' Hvj_lt' Hvi_len.
   specialize (Hget_baddr' (Int.unsigned vj0)).
   destruct Hget_baddr'.
   split; auto with zarith.
   apply Int.unsigned_range_2.
   rewrite <- Hvj_len in *.
   rewrite nth_vallist_get_idx in *.
   simpljoin.
   inverts H.
   inverts H0.
   rewrite <- Hvi_len in *.
   rewrite nth_error_middle in H1.
   inverts H1.
   inverts H2.
   auto.
}
lets Hvaddr: Hcast' Hvbaddr.

(* unfold Astruct about Elf32_Ehdr *)
eapply backward_rule1.
introv Hsat.
sep_lifts_trms_in Hsat Avalid.
eapply Avalid_unfold_any_idx_frm with (idx:= Z.to_nat (Int.unsigned vj0)); eauto.
rewrite <- Haddr_vl_len.
rewrite Hbaddr_vl_len.
rewrite <- Z2Nat.inj_lt; auto with zarith.
apply Int.unsigned_range_2.

hoare normal pre.
repeat (apply ex_intro_rule; intro).
hoare_split_pure_all.
simpljoin.

match goal with 
Hvaddr : nth_val (Z.to_nat (Int.unsigned vj0)) (?vll ++ _ :: _) = Some (Vptr (int32_to_ptr _)),
H: length ?vll = Z.to_nat (Int.unsigned vj0) |- _ => rename H into Hvj_len' end.
rewrite <- Hvj_len' in Hvaddr.
rewrite nth_val_length_imp in Hvaddr; auto.
inverts Hvaddr.

match goal with H: forall _ _,  _ -> exists _, V_e_entry _ = _ |- _ => rename H into Hentry end.
match goal with H: length ?vll = Z.to_nat (Int.unsigned vj0) |- _ => rename H into Hehdr_len end.
lets Hventry: Hentry (Z.to_nat (Int.unsigned vj0)).
rewrite <- Hehdr_len in Hventry; rewrite nth_vallist_get_idx in Hventry.
specialize (Hventry _ (eq_refl _)).
destruct Hventry as (ventry' & Hventry).

(* hoare unfold. *)

eapply seq_rule.
hoare_lifts_trms_pre Aop.
eapply calle_rule_lvar'.
intuition eauto.
introv Hsat; do 3 try apply rvl_elim.
{
eapply cast_rv_int32_to_ptr.
sep_get_rv_array_struct_conf'.
simpl; eauto.
}
{
sep_get_rv_array_struct_conf'.
}
{
eapply bop_rv.
sep_get_rv_array_struct_conf'.
sep_get_rv_array_struct_conf'.
simpl; eauto.
eauto.
simpl; eauto.
}
apply rvl_nil.

simpl nth_val'.
introv Hsat;  unfold_spec.
sep normal.
sep eexists.
trycancel.
sep cancel A_isr_is_prop.
sep cancel Aop.
sep cancel Aier.
sep split; eauto.
sep cancel Elf32_Ehdr.
sep cancel p_local.
sep cancel os_code_defs.x.
eauto.
go.
(* retpost is_ELFProgramValidPost *)
unfold retpost.
unfold is_ELFProgramValidPost.
unfold is_ELFProgramValidPost'.
unfold getasrt.
introv Hsat.
sep pauto.
(* tl_vl_match *)
simpl;auto.
sep_unfold_funpost.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
sep_unfold_funpre.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.

simpl nth_val'.
unfold is_ELFProgramValidPost.
unfold is_ELFProgramValidPost'.
unfold getasrt.
hoare normal pre.
repeat (apply ex_intro_rule; intro).
hoare_split_pure_all.
simpljoin.
repeat try (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
match goal with H: Some _ = Some _ |- _ => inverts H end.
match goal with
 Hv: V_e_entry _ = Some (Vptr ventry') , Hv1: V_e_entry _ = Some (Vptr _) |- _ =>
 rewrite Hv1 in Hv; inverts Hv end.
match goal with H: isflag (Vint32 ?v) |- _ => rename H into Hrv_x; rename v into rv_x end.

destruct Hrv_x as [Hrv_x | Hrv_x]; inverts Hrv_x.
(* case 1: rv_x = 0 *)
2:{ eapply forward_rule1.
       2:{ eapply if_rule2'.
              introv Hsat. sep get rv.
              hoare forward.
              instantiate (1:= Afalse).
              hoare_lifts_trms_pre val_inj.
              eapply pure_split_rule'; introv Hval_inj.
              rewrite Int.eq_true in Hval_inj;simpl in Hval_inj; destruct Hval_inj; tryfalse.
            }
      rewrite Int.eq_true.
      simpl val_inj.
      introv Hsat.
      destruct Hsat as [Hsat | Hsat].
      2:{ simpl in Hsat; simpljoin; tryfalse. }
      sep normal. sep eexists.
      trycancel.
      sep cancel A_isr_is_prop.
      sep cancel Aop.
      sep cancel Aier.
      sep cancel EvtInv.
      sep pauto; eauto.
      sep cancel AOSTCBList'.
      sep cancel AOSTCBFreeList'.
      sep cancel APthreadAttr.
      sep cancel A_dom_lenv.
      sep cancel AOSCSpacePrioTbl.
      eapply AksDomains'_select_sn_strong_frm; eauto.
      solve_part_int_rgn.
      unfold node_offt.
      sep normal; sep eexists.
      sep cancel AksDomains'.
      sep cancel AksDomains'.
      sep cancel ADeviceioTbl'.
      sep pauto; eauto.
      sep cancel cap_conf_t.
      sep cancel Aarray.
      sep cancel domain_conf_t.
      eapply AksDomSchedule'_select_sn_strong_frm; eauto.
      solve_part_int_rgn.
      unfold node_offt.
      sep normal; sep eexists.
      sep cancel AksDomSchedule'.
      sep cancel AksDomSchedule'.
      sep pauto; eauto.
      sep cancel dschedule_conf_t.
      eapply Avalid_compose_strong'; eauto.
      sep pauto.
      go.
(*       split; auto. go. *)
(*       split; auto. go. *)
      {
      clear - Hvj_lt' Hscdlen_rgn1 Hscdlen_rgn2 Hget_baddr' Hvj_len.
      destruct (Int.eq (vj0 +ᵢ  $ 1) ksdomscdlen) eqn: eq1; auto.
      right.
      rewrite Inteq_false_is_Zneq in eq1.
      rewrite Intlt_true_is_Zlt.
      assert (Hvj'_eq: Int.unsigned (vj0 +ᵢ  $ 1) = Int.unsigned vj0 +1).
      {  pose proof (Int.unsigned_range_2 vj0).
         unfold Int.add.
         change (Int.unsigned ($ 1)) with 1.
         rewrite Int.unsigned_repr; auto.
         split; solve_part_int_rgn.
       }
      rewrite Hvj'_eq.
      rewrite Z.add_simpl_r.
      split.
      solve_part_int_rgn.
      introv Hnz.
      repeat eexists; eauto.
      rewrite <- Hvj_len. rewrite nth_vallist_get_idx; eauto.
      unfolds; simpl; auto.
       }
      go.
}

(* case 2: rv_x = 1 *)
eapply forward_rule1;
[idtac |
eapply if_rule2';
[introv Hsat; sep get rv | instantiate (1:= Afalse) | idtac]
].
introv Hsat.
destruct Hsat as [Hsat | Hsat].
simpl in Hsat; simpljoin; tryfalse.
sep split in Hsat.
exact Hsat.
hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hval_inj.
rewrite math_prop_l2 in Hval_inj; destruct Hval_inj; tryfalse.
rewrite math_prop_l2.
hoare_split_pure_all.
(* entry ′ =ᶠ LoadElf2Mem''
                        (·〈 (Void) ∗
                          〉 ((((uconf ′ → cpus) [coreNum ′]) .. cpu_ksDomains) [ios_cap_defs.i ′])
                            .. binAddress·);ₛ *)
eapply seq_rule.
hoare_lifts_trms_pre Aop.
eapply calle_rule_lvar'.
intuition eauto.
introv Hsat; apply rvl_elim.
{
eapply cast_rv_int32_to_ptr.
sep_get_rv_array_struct_conf'.
simpl; eauto.
}
apply rvl_nil.

simpl nth_val'.
introv Hsat;  unfold_spec.
sep normal.
sep eexists.
trycancel.
sep cancel A_isr_is_prop.
sep cancel Aop.
sep cancel Aier.
sep split; eauto.
sep cancel Elf32_Ehdr.
sep cancel p_local.
sep cancel entry.
eauto.
go.
unfolds; simpl; eauto.
go.
(* retpost LoadElf2Mem''Post *)
unfold retpost.
unfold LoadElf2Mem''Post.
unfold LoadElf2Mem''Post'.
unfold getasrt.
introv Hsat.
sep normal in Hsat.
sep destruct Hsat.
sep split in Hsat.
simpljoin.
pure_auto.
(* sep pauto. *)
(* tl_vl_match *)
simpl;auto.
sep_unfold_funpost.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
sep_unfold_funpre.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.

simpl nth_val'.
unfold LoadElf2Mem''Post.
unfold LoadElf2Mem''Post'.
unfold getasrt.
hoare normal pre.
repeat (apply ex_intro_rule; intro).
hoare_split_pure_all.
simpljoin.
match goal with H: V_e_entry _ = Some (Vptr ?v) |- _ => rename v into rv_ventry; inverts H end.
repeat try (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
match goal with H: Some _ = Some _ |- _ => inverts H end.
match goal with
 Hv: V_e_entry _ = Some (Vptr ventry') , Hv1: V_e_entry _ = Some (Vptr _) |- _ =>
 rewrite Hv in Hv1; inverts Hv1 end.

(* fold Astruct about Elf32_Ehdr *)
eapply backward_rule1.
introv Hsat.
match goal with
H: length _ = (length (?vl1 ++ Vptr (int32_to_ptr _) :: ?vl2) - _)%nat |- _ =>
sep_lifts_trms_in Hsat (Avalid vl1, int32_to_ptr , Avalid vl2);
eapply Avalid_compose_strong_frm' with (addr_vl1:= vl1) (addr_vl2 := vl2);
sep cancel (Avalid vl1); sep cancel (Avalid vl2);
sep cancel 1%nat 1%nat;
sep split; eauto
end.
go.

(* attr ′ → stackaddr =ₑ
RootTaskStk ′
[((((uconf ′ → cpus) [coreNum ′]) .. cpu_ksDomains) [ios_cap_defs.i ′])
 .. dom_ID];ₛ *)

rename i24 into domid.
assert (Hdomid_rgn: 0 <= Int.unsigned domid < PARTITION_NUM).
{
lets Hdomid_rgn: Hdom_good.
clear -Hvi_len Hdomid_rgn Hvi_rgn.
destruct Hdomid_rgn as (_ & _ & Hdomid_rgn & _).
specialize (Hdomid_rgn (Int.unsigned vi0')).
unfold nat_of_Z in Hdomid_rgn.
rewrite <- Hvi_len in Hdomid_rgn.
rewrite nth_error_middle in Hdomid_rgn.
destruct Hdomid_rgn.
split; solve_part_int_rgn.
apply Int.unsigned_range_2.
simpljoin.
inverts H.
inverts H0.
auto.
}
destruct Hdomid_rgn as (Hdomid_pos & Hdomid_rgn).

(* unfold RootTaskStk *)
unfold ARootTaskStk.
hoare_lifts_trms_pre ARootTaskStk'.
hoare_assert_pure (length rtsk_vll = ∘ PARTITION_NUM).
{ match goal with H: _ |= _ |- _ => eapply ARootTaskStk'_len_frm in H; eauto end. }
eapply pure_split_rule'; introv Hrtsk_vll_len.

eapply backward_rule1.
introv Hsat.
eapply ARootTaskStk'_unfold_any_idx_frm with (idx:= Z.to_nat (Int.unsigned domid)); eauto.
rewrite Hrtsk_vll_len.
unfold nat_of_Z.
solve_part_int_rgn.

hoare normal pre.
repeat (apply ex_intro_rule; intro).
hoare_split_pure_all.
simpljoin.

eapply seq_rule.
hoare_lifts_trms_pre Aop.
eapply assign_rule_struct_aop_typeneq;
                          [ intro s_; split; intro Hsat; try sep pauto
                          | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                          | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                          | simpl;auto
                          | simpl; auto
                          | unfold id_nth; simpl; auto
                          | simpl; auto
                          | intros; intro; tryfalse
                          | intros; intro; tryfalse
                          | auto
                          | idtac
                          | apply assign_type_match_true; simpl; auto
                          | simpl
                          | simpl; auto
                          | li_sepauto li ].
(* Rv RootTaskStk ′
   [((((uconf ′ → cpus) [coreNum ′]) .. cpu_ksDomains) [ios_cap_defs.i ′])
    .. dom_ID] @ ?tp2 == ?v *)
introv Hsat.
eapply cast_rv_tptr.
eapply addrof_array_elem_rv.
sep get rv.
sep_get_rv_array_struct_conf'.
simpl; eauto.
eauto.
eauto.
unfold rule_type_val_match; auto.
simpl; auto.
auto with zarith.
(* pthread_attr_init (­ attr ′­);ₛ *)
hoare forward.
match goal with H: _ |= _ |- _ => rename H into Hsat end.
sep_lifts_trms_in Hsat (Astruct vattr).
eauto.
simpl; eauto.
go.
go.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.

unfold PthreadInitPost.
unfold PthreadInitPost'.
unfold getasrt.
hoare normal pre.
repeat (apply ex_intro_rule; intro).
hoare_split_pure_all.
simpljoin.
repeat try (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
match goal with
 H: nth_val _ (Vptr vattr :: _) = Some (Vptr ?v) |- _ =>
  rename v into vattr'; inverts H; rename vattr' into vattr
end.

(* attr ′ → os_code_defs.stacksize =ₑ ′ 2 × ′ PTHREAD_STACK_MIN;ₛ *)
match goal with H: struct_type_vallist_match pthread_attr_t _ |- _ => rename H into Hattr_mat end.
match goal with
H: struct_type_vallist_match pthread_attr_t ?vl,
Hlen: nth_val _ ?vl = Some _  |- _ =>
assert (Hattr_len: (2 < length vl)%nat) by
(eapply OSTimeTickPure.nth_val_length in Hlen; auto with zarith)
end.

hoare forward.
(* attr ′ → sched_priority =ₑ 
     ((((uconf ′ → cpus)  [coreNum ′]) .. cpu_ksDomains)  [ios_cap_defs.i ′]) .. RootTaskPrio;ₛ *)
eapply seq_rule.
hoare_lifts_trms_pre Aop.
eapply assign_rule_struct_aop_typeneq;
                          [ intro s_; split; intro Hsat; try sep pauto
                          | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                          | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
                          | simpl;auto
                          | simpl; auto
                          | unfold id_nth; simpl; auto
                          | simpl; auto
                          | intros; intro; tryfalse
                          | intros; intro; tryfalse
                          | auto
                          | idtac
                          | apply assign_type_match_true; simpl; auto
                          | simpl
                          | simpl; auto
                          | li_sepauto li ].
sep_get_rv_array_struct_conf'.
simpl; eauto.
rewrite update_nth_val_len_eq; auto.
(*  ios_cap_defs.prio ′ =ₑ  attr ′ → sched_priority;ₛ *)
lets Hattr: struct_type_vallist_match_elim_3 Hattr_mat.
destruct Hattr as (vstk_addr & vstk_size & vscd_pr & Hattr_eq).
subst.
simpl nth_val'.
hoare forward.
(* do 2 rewrite update_nth_val_len_eq; auto. *)
eapply struct_type_vallist_match_attr_hold2; eauto.
eapply struct_type_vallist_match_attr_hold1; eauto.

(* y′ =ᶠ pthread_create(· &ₐ pt′ , attr′ , entry′ , 〈 (Void) ∗ 〉  NULL ·);ₛ *)
simpl update_nth_val.
hoare_lifts_trms_pre pt.
hoare remember (1 :: nil)%nat pre.
eapply backward_rule1.
unfold Alvarmapsto; eauto.
subst.
hoare normal pre.
apply ex_intro_rule; intro pt_b.

eapply seq_rule.
hoare_lifts_trms_pre Aop.
eapply calle_rule_lvar'.
intuition eauto.
introv Hsat.
do 4 try apply rvl_elim; try sep get rv.
{
eapply addrof_lvar_rv.
sep cancel pt.
eauto.
}
apply rvl_nil.

introv Hsat;  unfold_spec.
sep normal.
sep eexists.
trycancel.
sep cancel A_isr_is_prop.
sep cancel Aop.
sep cancel Aier.
sep split; eauto.
sep cancel p_local.
sep cancel AOSTCBList'.
sep cancel EvtInv.
sep cancel AOSTCBFreeList'.
sep cancel APthreadAttr.
sep pauto.
go.
(* retpost PthreadCreatePost *)
unfold retpost.
unfold PthreadCreatePost.
unfold PthreadCreatePost'.
unfold getasrt.
introv Hsat.
sep normal in Hsat.
sep destruct Hsat.
sep split in Hsat.
simpljoin.
pure_auto.
(* tl_vl_match *)
simpl;auto.
sep_unfold_funpost.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
sep_unfold_funpre.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.

unfold PthreadCreatePost.
unfold PthreadCreatePost'.
unfold getasrt.
hoare normal pre.
repeat (apply ex_intro_rule; intro).
hoare_split_pure_all.
simpljoin.
repeat try (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
match goal with H: Some _ = Some _ |- _ => inverts H end.

(* fold AksDomSchedule' *)
eapply backward_rule1.
introv Hsat.
match goal with
 H: Z.of_nat (S (Z.to_nat (Int.unsigned vj0))) <= Z.of_nat (length (?vll1 ++ (_ :: _ :: _) :: ?vll2)) |- _ =>
        rename vll1 into kscd_vll1; rename vll2 into kscd_vll2
end.
eapply AksDomSchedule'_select_sn_strong_frm
               with (idx:= Z.to_nat (Int.unsigned vj0)) (vll1:= kscd_vll1) (vll2:= kscd_vll2); eauto.
solve_part_int_rgn.
unfold node_offt.
sep normal; sep eexists.
sep cancel kscd_vll1.
sep cancel kscd_vll2.
sep split; eauto.
sep cancel dschedule_conf_t.
eauto.
split; auto.
go.
(* fold ARootTaskStk' *)
eapply backward_rule1.
introv Hsat.
eapply ARootTaskStk'_select_sn_strong_frm.
sep normal.
exists (Z.to_nat (Int.unsigned domid)).
sep eexists.
sep split; eauto.
sep pauto; eauto.

hoare_lifts_trms_pre y.
match goal with  | |- {|_ , _, _, _, _, _|}|-_ {{   LV y @ _ |-> Vint32 ?v ** _ }} _ {{ _ }} => rename v into rv_y end.

destruct (Int.eq rv_y ($ OS_NO_ERR)) eqn: eq1.
2:{ (* case1: rv_y <> OS_NO_ERR  *)
eapply forward_rule1;
[idtac |
eapply if_rule2';
[introv Hsat; sep get rv | idtac | instantiate (1:= Afalse)]
].
introv Hsat.
destruct Hsat as [Hsat | Hsat].
2:{ simpl in Hsat; simpljoin; tryfalse. }
sep split in Hsat.
exact Hsat.
pure_auto.
pure_auto.
2:{
hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hval_inj.
rewrite eq1 in Hval_inj; simpl in Hval_inj;
try change (Int.notbool Int.zero) with Int.one in Hval_inj;
destruct Hval_inj; tryfalse.
}
hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hval_inj.
eapply forward_rule1; [ | hoare forward].
introv Hsat.
sep normal. sep eexists.
trycancel.
sep cancel Aier.
sep cancel A_isr_is_prop.
sep cancel Aop.
sep cancel EvtInv.
sep cancel (Astruct vattr).
sep pauto; eauto.
sep cancel AOSTCBList'.
sep cancel AOSTCBFreeList'.
sep cancel APthreadAttr.
sep cancel A_dom_lenv.
sep cancel AOSCSpacePrioTbl.
unfold Alvarmapsto.
sep normal.
sep eexists.
sep cancel pt.
sep cancel vpt.
eapply AksDomains'_select_sn_strong; eauto.
solve_part_int_rgn.
unfold node_offt.
sep normal; sep eexists.
sep cancel AksDomains'.
sep cancel AksDomains'.
sep cancel ADeviceioTbl'.
sep pauto; eauto.
{
clear - Hvj_lt' Hscdlen_rgn1 Hscdlen_rgn2 Hget_baddr' Hvj_len.
destruct (Int.eq (vj0 +ᵢ  $ 1) ksdomscdlen) eqn: eq1; auto.
right.
rewrite Inteq_false_is_Zneq in eq1.
rewrite Intlt_true_is_Zlt.
assert (Hvj'_eq: Int.unsigned (vj0 +ᵢ  $ 1) = Int.unsigned vj0 +1).
{  pose proof (Int.unsigned_range_2 vj0).
   unfold Int.add.
   change (Int.unsigned ($ 1)) with 1.
   rewrite Int.unsigned_repr; auto.
   split; solve_part_int_rgn.
 }
rewrite Hvj'_eq.
rewrite Z.add_simpl_r.
split.
solve_part_int_rgn.
introv Hnz.
repeat eexists; eauto.
rewrite <- Hvj_len. rewrite nth_vallist_get_idx; eauto.
unfolds; simpl; auto.
 }
go.
clear -Hattr_mat. simpl in Hattr_mat; simpljoin; auto.
}
(* case2: rv_y = OS_NO_ERR  *)
eapply forward_rule1;
[idtac |
eapply if_rule2';
[introv Hsat; sep get rv | instantiate (1:= Afalse) | idtac]
].
introv Hsat.
destruct Hsat as [Hsat | Hsat].
simpl in Hsat; simpljoin; tryfalse.
sep split in Hsat.
exact Hsat.
pure_auto.
pure_auto.
hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hval_inj.
rewrite eq1 in Hval_inj; simpl in Hval_inj;
try change (Int.notbool Int.one) with Int.zero in Hval_inj;
destruct Hval_inj; tryfalse.
hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hval_inj.
(* pre condition process, If ((((((uconf ′ → cpus) [coreNum ′]) .. cpu_ksDomains) [ios_cap_defs.i ′])
     .. CapEnTbl) .. TaskEn ==ₑ ′ 0) *)
assert (Heq: Int.mul ($ Z.of_nat 99) vi0' =  $ Z.of_nat (Z.to_nat (Int.unsigned vi0') * 99)).
{ rewrite Nat2Z.inj_mul;
  rewrite Z2Nat.id; try solve [apply Int.unsigned_range_2];
  rewrite Int.mul_commut.
  unfold Int.mul;
  rewrite Int.unsigned_repr; try split; auto with zarith.
  solve_part_int_rgn.
}
match goal with
H: id_addrval _ CapEnTbl domain_conf_t = _ |- _=> inverts H end.
lets Hcap_vl: struct_type_vallist_match_elim_6 Hcap_mat.
(* destruct Hcap_vl as (tsk_en & part_en & icom_en & sem_en & mux_en & q_en & Hcap_vl). *)
(* subst. *)
simpljoin.
lets Hcap_mat': Hcap_mat.
simpl in Hcap_mat'.
simpljoin.
repeat try (match goal with
H: (match ?v0 with
      | Vint32 _ => if Int.unsigned _ <=? _ then true else false
      | _ => _
      end) = true
 |- _ => destruct v0; tryfalse
end).

match goal with H: CPU_ksDomain_prio_Good _ |- _ =>
lets Hprio_rgn: H; destruct Hprio_rgn as (tsk_prio & Heq_prio & Hprio_rgn);
inverts Heq_prio; destruct Hprio_rgn as (Hprio_pos & Hprio_rgn)
end.

hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop).
transform_pre a_isr_is_prop_split ltac:(idtac).

hoare_lifts_trms_pre (Aie, Ais, Acs, Aisr, Aier, Aop, AOSCSpacePrioTbl, p_local, A_dom_lenv, ios_cap_defs.prio).

Require Import CapPure.

match goal with
  | |- {|_ , _, _, _, _, _|}|-_ {{Aie _ ** Ais _ ** Acs _ ** Aisr _ ** Aier _ **
                                              <|| ?s ||>  **
                                              AOSCSpacePrioTbl (?pb, ?pi) ?ptrvl ?priotbl ?cspacels ** ?P}} _ {{ _ }} =>
assert (Hrv_cap:  forall (id: ident) n tid decl (ie0 : ie) (is0: is) (cs0 : cs) (isr0: isr) (ier0: ier) s pb pi ptrvl priotbl cspacels,
                                  cap_conf_t = STRUCT tid ­{ decl }­ ->
                                  nth_id n decl = Some id ->
                                  Aie ie0 ** Ais is0 ** Acs cs0 ** Aisr isr0 ** Aier ier0 **
                                  <|| s ||>  **
                                  AOSCSpacePrioTbl (pb, pi) ptrvl priotbl cspacels ** P ==> 
                                  Rv (((((uconf ′ → cpus) [coreNum ′]) .. cpu_ksDomains) [ios_cap_defs.i ′])
                                          .. CapEnTbl) .. id @ Int8u ==
                                                                 nth_val' n (Vint32 i30 :: Vint32 i29 :: Vint32 i28 ::
                                                                                       Vint32 i27 :: Vint32 i24 :: Vint32 i19 :: nil))
end.
{
   introv Hdecl Hid Hsat; unfold cap_conf_t in Hdecl; inverts Hdecl.
   eapply expr_struct_member_rv';
[ idtac
   | idtac
   | idtac
   | idtac
   | simpl; eauto
   |  eapply addrof_rv_to_lv;
      eapply struct_offset_rv;
      [ eapply addrof_array_elem_rv;
         [  sep_get_rv_array_struct_array
            | sep get rv
            | auto
            | eauto ]
       | unfold domain_conf_t; eauto
       | unfold field_offset; simpl; eauto
       | simpl; eauto ]
    | unfold fst,snd;
       simpl typelen;
       rewrite Heq;
       sep cancel cap_conf_t;
       eauto
    | unfold cap_conf_t; eauto
    | simpl; eauto
    | unfold ftype; simpl; eauto
    | idtac ].
introv Hf; tryfalse.
introv Hf; tryfalse.
introv Hf; tryfalse.
simpl in Hid.
do 7 try destruct n; tryfalse;
simpl nth_val'; go.
simpl; eauto.
simpl in Hid.
do 7 try destruct n; inverts Hid; go.
eapply nth_val_imp_nth_val'_2.
simpl length.
simpl in Hid.
do 7 try destruct n; tryfalse; auto with zarith.
}

hoare remember (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: 10 :: nil)%nat pre.

eapply seq_rule with (p':=
 (EX s' pb' pi' ptrvl' priotbl' cspacels',
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  Aisr empisr **
  Aier v'76 **
   <|| s' ||>  **
  AOSCSpacePrioTbl (pb', pi') ptrvl' priotbl' cspacels' **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((attr, pthread_attr_t ∗)
     :: (coreNum, char_t)
        :: (ios_cap_defs.i, char_t)
           :: (j, char_t)
              :: (uconf, ucos_conf_t ∗)
                 :: (pt, long)
                    :: (entry, (Void) ∗)
                       :: (ios_cap_defs.prio, char_t)
                          :: (os_code_defs.x, long) :: (y, long) :: nil) **
  LV ios_cap_defs.prio @ char_t |-> Vint32 tsk_prio ** H78 **
  [| CSPACEList_P ptrvl' 0%nat cspacels' |] **
  [| ptrvl_to_cspace_to_ptrvl ptrvl' cspacels' |] **
  [| Int.eq i30 Int.zero = false ->
       (s' = v'72 /\ pb' = v'2 /\ pi' = v'3 /\ ptrvl' = ptrvl0 /\ priotbl' = priotbl0 /\ cspacels' = cspacels0) |]
  )).
destruct (Int.eq i30 Int.zero) eqn: eq2.
2:{ (* case1 : TaskEn <> 0 *)
eapply forward_rule1.
2:{
eapply ift_rule'.
introv Hsat.
eapply bop_rv.
eapply Hrv_cap with (n:= 0%nat);
 [match goal with |- ?tp = _ => try unfold tp end; eauto | simpl; eauto | eauto ].
sep get rv.
simpl; eauto.
pure_auto.
simpl; eauto.
change ($ 0) with Int.zero.
instantiate(1:= Afalse).
hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hval_inj'.
rewrite eq2 in Hval_inj'; simpl in Hval_inj';
destruct Hval_inj'; tryfalse.
}
introv Hsat.
destruct Hsat as [Hsat | Hsat].
simpl in Hsat; simpljoin; tryfalse.
sep normal.
sep eexists.
trycancel.
sep cancel A_dom_lenv.
sep cancel Aop.
sep cancel Aier.
sep split in Hsat.
sep split; eauto.
intros; splits; auto.
}
(* case 2 : TaskEn = 0 *)
(* eapply seq_rule. *)
eapply forward_rule1.
2:{
eapply ift_rule'.
introv Hsat.
eapply bop_rv.
eapply Hrv_cap with (n:= 0%nat);
 [match goal with |- ?tp = _ => try unfold tp end; eauto | simpl; eauto | eauto ].
sep get rv.
simpl; eauto.
pure_auto.
simpl; eauto.

(* ios_cap_defs.ucos_CNode_Delete (-ios_cap_defs.prio ′, ′ CAP_TASK_CLASS -) *)
hoare forward.
simpl nth_val; eauto.
simpl nth_val; eauto.
(* sep cancel AOSCSpacePrioTbl. *)
(* eauto. *)
(* eauto. *)
(* eauto. *)
(* 4:{ simpl nth_val; eauto. } *)
(* 4:{ simpl nth_val; eauto. } *)
(* unfold CAP_TASK_CLASS.
change (Int.unsigned ($ 2)) with 2.
auto with zarith.
auto with zarith. *)
subst. go.

introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
eapply true_if_else_true; eauto.
}

unfold CapSpec.ucos_CNode_DeletePost.
unfold CapSpec.ucos_CNode_DeletePost'.
unfold getasrt.
introv Hsat.
destruct Hsat as [Hsat | Hsat].
sep normal in Hsat.
sep destruct Hsat.
sep_lifts_trms_in Hsat logic_cs.
eapply sep_pure_split in Hsat; destruct Hsat as (Heq_lg & Hsat).
inverts Heq_lg.
sep normal.
sep eexists.
trycancel.
sep cancel A_dom_lenv.
sep cancel Aop.
sep cancel Aier.
sep split in Hsat.
sep split; eauto.
sep cancel AOSCSpacePrioTbl.
sep cancel p_local.
sep cancel ios_cap_defs.prio.
sep cancel H78.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
introv Hf; tryfalse.
sep_lifts_trms_in Hsat val_inj.
eapply sep_pure_split in Hsat; destruct Hsat as (Hval_inj' & Hsat).
change ($ 0) with Int.zero in Hval_inj'.
rewrite eq2 in Hval_inj'; simpl in Hval_inj';
destruct Hval_inj'; tryfalse.

hoare normal pre.
apply ex_intro_rule; intro s1.
apply ex_intro_rule; intro pb1.
apply ex_intro_rule; intro pi1.
apply ex_intro_rule; intro ptrvl1.
apply ex_intro_rule; intro priotbl1.
apply ex_intro_rule; intro cspacels1.
hoare_split_pure_all.

(* If ((((((uconf ′ → cpus) [coreNum ′]) .. cpu_ksDomains) [ios_cap_defs.i ′])
     .. CapEnTbl) .. PartitionEn ==ₑ ′ 0) *)
eapply seq_rule with (p':=
 (EX s' pb' pi' ptrvl' priotbl' cspacels',
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  Aisr empisr **
  Aier v'76 **
   <|| s' ||>  **
  AOSCSpacePrioTbl (pb', pi') ptrvl' priotbl' cspacels' **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((attr, pthread_attr_t ∗)
     :: (coreNum, char_t)
        :: (ios_cap_defs.i, char_t)
           :: (j, char_t)
              :: (uconf, ucos_conf_t ∗)
                 :: (pt, long)
                    :: (entry, (Void) ∗)
                       :: (ios_cap_defs.prio, char_t)
                          :: (os_code_defs.x, long) :: (y, long) :: nil) **
  LV ios_cap_defs.prio @ char_t |-> Vint32 tsk_prio ** H78 **
  [| CSPACEList_P ptrvl' 0%nat cspacels' |] **
  [| ptrvl_to_cspace_to_ptrvl ptrvl' cspacels' |] **
  [| Int.eq i29 Int.zero = false ->
       (s' = s1 /\ pb' = pb1 /\ pi' = pi1 /\ ptrvl' = ptrvl1 /\ priotbl' = priotbl1 /\ cspacels' = cspacels1) |]
  )).
destruct (Int.eq i29 Int.zero) eqn: eq2.
2:{ (* case1 : PartitionEn <> 0 *)
eapply forward_rule1.
2:{
eapply ift_rule'.
introv Hsat.
eapply bop_rv.
eapply Hrv_cap with (n:= 1%nat);
 [match goal with |- ?tp = _ => try unfold tp end; eauto | simpl; eauto | eauto ].
sep get rv.
simpl; eauto.
pure_auto.
simpl; eauto.
change ($ 0) with Int.zero.
instantiate(1:= Afalse).
hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hval_inj'.
rewrite eq2 in Hval_inj'; simpl in Hval_inj';
destruct Hval_inj'; tryfalse.
}
introv Hsat.
destruct Hsat as [Hsat | Hsat].
simpl in Hsat; simpljoin; tryfalse.
sep normal.
sep eexists.
trycancel.
sep cancel A_dom_lenv.
sep cancel Aop.
sep cancel Aier.
sep split in Hsat.
sep split; eauto.
intros; splits; auto.
}
(* case 2 : PartitionEn = 0 *)
eapply forward_rule1.
2:{
eapply ift_rule'.
introv Hsat.
eapply bop_rv.
eapply Hrv_cap with (n:= 1%nat);
 [match goal with |- ?tp = _ => try unfold tp end; eauto | simpl; eauto | eauto ].
sep get rv.
simpl; eauto.
pure_auto.
simpl; eauto.

hoare forward.
simpl nth_val; eauto.
simpl nth_val; eauto.
(* 3:{ simpl nth_val; eauto. }
3:{ simpl nth_val; eauto. }
unfold CAP_PARTITION_CLASS.
change (Int.unsigned ($ 1)) with 1.
auto with zarith.
auto with zarith. *)
subst. go.

introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
eapply true_if_else_true; eauto.
}

unfold CapSpec.ucos_CNode_DeletePost.
unfold CapSpec.ucos_CNode_DeletePost'.
unfold getasrt.
introv Hsat.
destruct Hsat as [Hsat | Hsat].
sep normal in Hsat.
sep destruct Hsat.
sep_lifts_trms_in Hsat logic_cs.
eapply sep_pure_split in Hsat; destruct Hsat as (Heq_lg & Hsat).
inverts Heq_lg.
sep normal.
sep eexists.
trycancel.
sep cancel A_dom_lenv.
sep cancel Aop.
sep cancel Aier.
sep split in Hsat.
sep split; eauto.
sep cancel AOSCSpacePrioTbl.
sep cancel p_local.
sep cancel ios_cap_defs.prio.
sep cancel H78.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
introv Hf; tryfalse.
sep_lifts_trms_in Hsat val_inj.
eapply sep_pure_split in Hsat; destruct Hsat as (Hval_inj' & Hsat).
change ($ 0) with Int.zero in Hval_inj'.
rewrite eq2 in Hval_inj'; simpl in Hval_inj';
destruct Hval_inj'; tryfalse.

hoare normal pre.
apply ex_intro_rule; intro s2.
apply ex_intro_rule; intro pb2.
apply ex_intro_rule; intro pi2.
apply ex_intro_rule; intro ptrvl2.
apply ex_intro_rule; intro priotbl2.
apply ex_intro_rule; intro cspacels2.
hoare_split_pure_all.

(* If ((((((uconf ′ → cpus) [coreNum ′]) .. cpu_ksDomains) [ios_cap_defs.i ′])
     .. CapEnTbl) .. InterCommEn ==ₑ ′ 0) *)
eapply seq_rule with (p':=
 (EX s' pb' pi' ptrvl' priotbl' cspacels',
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  Aisr empisr **
  Aier v'76 **
   <|| s' ||>  **
  AOSCSpacePrioTbl (pb', pi') ptrvl' priotbl' cspacels' **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((attr, pthread_attr_t ∗)
     :: (coreNum, char_t)
        :: (ios_cap_defs.i, char_t)
           :: (j, char_t)
              :: (uconf, ucos_conf_t ∗)
                 :: (pt, long)
                    :: (entry, (Void) ∗)
                       :: (ios_cap_defs.prio, char_t)
                          :: (os_code_defs.x, long) :: (y, long) :: nil) **
  LV ios_cap_defs.prio @ char_t |-> Vint32 tsk_prio ** H78 **
  [| CSPACEList_P ptrvl' 0%nat cspacels' |] **
  [| ptrvl_to_cspace_to_ptrvl ptrvl' cspacels' |] **
  [| Int.eq i28 Int.zero = false ->
       (s' = s2 /\ pb' = pb2 /\ pi' = pi2 /\ ptrvl' = ptrvl2 /\ priotbl' = priotbl2 /\ cspacels' = cspacels2) |]
  )).
destruct (Int.eq i28 Int.zero) eqn: eq2.
2:{ (* case1 : InterCommEn <> 0 *)
eapply forward_rule1.
2:{
eapply ift_rule'.
introv Hsat.
eapply bop_rv.
eapply Hrv_cap with (n:= 2%nat);
 [match goal with |- ?tp = _ => try unfold tp end; eauto | simpl; eauto | eauto ].
sep get rv.
simpl; eauto.
pure_auto.
simpl; eauto.
change ($ 0) with Int.zero.
instantiate(1:= Afalse).
hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hval_inj'.
rewrite eq2 in Hval_inj'; simpl in Hval_inj';
destruct Hval_inj'; tryfalse.
}
introv Hsat.
destruct Hsat as [Hsat | Hsat].
simpl in Hsat; simpljoin; tryfalse.
sep normal.
sep eexists.
trycancel.
sep cancel A_dom_lenv.
sep cancel Aop.
sep cancel Aier.
sep split in Hsat.
sep split; eauto.
intros; splits; auto.
}
(* case 2 : InterCommEn = 0 *)
eapply forward_rule1.
2:{
eapply ift_rule'.
introv Hsat.
eapply bop_rv.
eapply Hrv_cap with (n:= 2%nat);
 [match goal with |- ?tp = _ => try unfold tp end; eauto | simpl; eauto | eauto ].
sep get rv.
simpl; eauto.
pure_auto.
simpl; eauto.

hoare forward.
simpl nth_val; eauto.
simpl nth_val; eauto.
(* 3:{ simpl nth_val; eauto. }
3:{ simpl nth_val; eauto. }
unfold CAP_CHANNEL_CLASS.
change (Int.unsigned ($ 16)) with 16.
auto with zarith.
auto with zarith. *)
subst. go.

introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
eapply true_if_else_true; eauto.

(* unfold CapSpec.ucos_CNode_DeletePost.
unfold CapSpec.ucos_CNode_DeletePost'.
unfold getasrt. *)
unfold CapSpec.ucos_CNode_DeletePost.
unfold CapSpec.ucos_CNode_DeletePost'.
unfold getasrt.
hoare normal pre.
simpl nth_val.
repeat try (apply ex_intro_rule; intro).
hoare_lifts_trms_pre logic_cs.
eapply pure_split_rule'; introv Heq_lg.
inverts Heq_lg.
instantiate (1:= 
(EX priotbl2', 
  EX v : option val,
  POST [CapSpec.ucos_CNode_DeletePost,
  (Vint32 tsk_prio :: V$ ios_cap_defs.CAP_PORT_CLASS :: nil), v,
  logic_cs (true :: nil)
  :: logic_isr empisr :: logic_ier v'76 :: logic_cspacel priotbl2'
  :: logic_code s2 :: logic_abscap cspacels2 :: logic_lv ptrvl2 :: nil, ct] **
  A_dom_lenv
    ((attr, pthread_attr_t ∗)
     :: (coreNum, char_t)
        :: (ios_cap_defs.i, char_t)
           :: (j, char_t)
              :: (uconf, ucos_conf_t ∗)
                 :: (pt, long)
                    :: (entry, (Void) ∗)
                       :: (ios_cap_defs.prio, char_t)
                          :: (os_code_defs.x, long) :: (y, long) :: nil) **
  LV ios_cap_defs.prio @ char_t |-> Vint32 tsk_prio ** H78)).

hoare forward.
simpl nth_val; eauto.
simpl nth_val; eauto.
(* 3:{ simpl nth_val; eauto. }
3:{ simpl nth_val; eauto. }
unfold CAP_PORT_CLASS.
change (Int.unsigned ($ 10)) with 10.
auto with zarith.
auto with zarith. *)
subst. go.
unfold GoodFrm; fold GoodFrm.
repeat splits; auto.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
eapply true_if_else_true; eauto.
match goal with H: ?s |= _ |- ?s |= _ => rename H into Hsat end.
instantiate (1:= v'104).
instantiate (1:= x1).
sep cancel 1%nat 1%nat.
sep cancel A_dom_lenv.
sep split in Hsat.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
}

unfold CapSpec.ucos_CNode_DeletePost.
unfold CapSpec.ucos_CNode_DeletePost'.
unfold getasrt.
introv Hsat.
destruct Hsat as [Hsat | Hsat].
sep normal in Hsat.
sep destruct Hsat.
sep_lifts_trms_in Hsat logic_cs.
eapply sep_pure_split in Hsat; destruct Hsat as (Heq_lg & Hsat).
inverts Heq_lg.
sep normal.
sep eexists.
trycancel.
sep cancel A_dom_lenv.
sep cancel Aop.
sep cancel Aier.
sep split in Hsat.
sep split; eauto.
sep cancel AOSCSpacePrioTbl.
sep cancel p_local.
sep cancel ios_cap_defs.prio.
sep cancel H78.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
introv Hf; tryfalse.
sep_lifts_trms_in Hsat val_inj.
eapply sep_pure_split in Hsat; destruct Hsat as (Hval_inj' & Hsat).
change ($ 0) with Int.zero in Hval_inj'.
rewrite eq2 in Hval_inj'; simpl in Hval_inj';
destruct Hval_inj'; tryfalse.

hoare normal pre.
apply ex_intro_rule; intro s3.
apply ex_intro_rule; intro pb3.
apply ex_intro_rule; intro pi3.
apply ex_intro_rule; intro ptrvl3.
apply ex_intro_rule; intro priotbl3.
apply ex_intro_rule; intro cspacels3.
hoare_split_pure_all.

(* If ((((((uconf ′ → cpus) [coreNum ′]) .. cpu_ksDomains) [ios_cap_defs.i ′])
     .. CapEnTbl) .. IntraCommSemEn ==ₑ ′ 0) *)
eapply seq_rule with (p':=
 (EX s' pb' pi' ptrvl' priotbl' cspacels',
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  Aisr empisr **
  Aier v'76 **
   <|| s' ||>  **
  AOSCSpacePrioTbl (pb', pi') ptrvl' priotbl' cspacels' **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((attr, pthread_attr_t ∗)
     :: (coreNum, char_t)
        :: (ios_cap_defs.i, char_t)
           :: (j, char_t)
              :: (uconf, ucos_conf_t ∗)
                 :: (pt, long)
                    :: (entry, (Void) ∗)
                       :: (ios_cap_defs.prio, char_t)
                          :: (os_code_defs.x, long) :: (y, long) :: nil) **
  LV ios_cap_defs.prio @ char_t |-> Vint32 tsk_prio ** H78 **
  [| CSPACEList_P ptrvl' 0%nat cspacels' |] **
  [| ptrvl_to_cspace_to_ptrvl ptrvl' cspacels' |] **
  [| Int.eq i27 Int.zero = false ->
       (s' = s3 /\ pb' = pb3 /\ pi' = pi3 /\ ptrvl' = ptrvl3 /\ priotbl' = priotbl3 /\ cspacels' = cspacels3) |]
  )).
destruct (Int.eq i27 Int.zero) eqn: eq2.
2:{ (* case1 : IntraCommSemEn <> 0 *)
eapply forward_rule1.
2:{
eapply ift_rule'.
introv Hsat.
eapply bop_rv.
eapply Hrv_cap with (n:= 3%nat);
 [match goal with |- ?tp = _ => try unfold tp end; eauto | simpl; eauto | eauto ].
sep get rv.
simpl; eauto.
pure_auto.
simpl; eauto.
change ($ 0) with Int.zero.
instantiate(1:= Afalse).
hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hval_inj'.
rewrite eq2 in Hval_inj'; simpl in Hval_inj';
destruct Hval_inj'; tryfalse.
}
introv Hsat.
destruct Hsat as [Hsat | Hsat].
simpl in Hsat; simpljoin; tryfalse.
sep normal.
sep eexists.
trycancel.
sep cancel A_dom_lenv.
sep cancel Aop.
sep cancel Aier.
sep split in Hsat.
sep split; eauto.
intros; splits; auto.
}
(* case 2 : IntraCommSemEn = 0 *)
eapply forward_rule1.
2:{
eapply ift_rule'.
introv Hsat.
eapply bop_rv.
eapply Hrv_cap with (n:= 3%nat);
 [match goal with |- ?tp = _ => try unfold tp end; eauto | simpl; eauto | eauto ].
sep get rv.
simpl; eauto.
pure_auto.
simpl; eauto.

hoare forward.
simpl nth_val; eauto.
simpl nth_val; eauto.
(* 3:{ simpl nth_val; eauto. }
3:{ simpl nth_val; eauto. }
unfold CAP_SEM_CLASS.
change (Int.unsigned ($ 9)) with 9.
auto with zarith.
auto with zarith. *)
subst. go.

introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
eapply true_if_else_true; eauto.
}

unfold CapSpec.ucos_CNode_DeletePost.
unfold CapSpec.ucos_CNode_DeletePost'.
unfold getasrt.
introv Hsat.
destruct Hsat as [Hsat | Hsat].
sep normal in Hsat.
sep destruct Hsat.
sep_lifts_trms_in Hsat logic_cs.
eapply sep_pure_split in Hsat; destruct Hsat as (Heq_lg & Hsat).
inverts Heq_lg.
sep normal.
sep eexists.
trycancel.
sep cancel A_dom_lenv.
sep cancel Aop.
sep cancel Aier.
sep split in Hsat.
sep split; eauto.
sep cancel AOSCSpacePrioTbl.
sep cancel p_local.
sep cancel ios_cap_defs.prio.
sep cancel H78.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
introv Hf; tryfalse.
sep_lifts_trms_in Hsat val_inj.
eapply sep_pure_split in Hsat; destruct Hsat as (Hval_inj' & Hsat).
change ($ 0) with Int.zero in Hval_inj'.
rewrite eq2 in Hval_inj'; simpl in Hval_inj';
destruct Hval_inj'; tryfalse.

hoare normal pre.
apply ex_intro_rule; intro s4.
apply ex_intro_rule; intro pb4.
apply ex_intro_rule; intro pi4.
apply ex_intro_rule; intro ptrvl4.
apply ex_intro_rule; intro priotbl4.
apply ex_intro_rule; intro cspacels4.
hoare_split_pure_all.

(* If ((((((uconf ′ → cpus) [coreNum ′]) .. cpu_ksDomains) [ios_cap_defs.i ′])
     .. CapEnTbl) .. IntraCommQueueEn ==ₑ ′ 0) *)
eapply seq_rule with (p':=
 (EX s' pb' pi' ptrvl' priotbl' cspacels',
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  Aisr empisr **
  Aier v'76 **
   <|| s' ||>  **
  AOSCSpacePrioTbl (pb', pi') ptrvl' priotbl' cspacels' **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((attr, pthread_attr_t ∗)
     :: (coreNum, char_t)
        :: (ios_cap_defs.i, char_t)
           :: (j, char_t)
              :: (uconf, ucos_conf_t ∗)
                 :: (pt, long)
                    :: (entry, (Void) ∗)
                       :: (ios_cap_defs.prio, char_t)
                          :: (os_code_defs.x, long) :: (y, long) :: nil) **
  LV ios_cap_defs.prio @ char_t |-> Vint32 tsk_prio ** H78 **
  [| CSPACEList_P ptrvl' 0%nat cspacels' |] **
  [| ptrvl_to_cspace_to_ptrvl ptrvl' cspacels' |] **
  [| Int.eq i19 Int.zero = false ->
       (s' = s4 /\ pb' = pb4 /\ pi' = pi4 /\ ptrvl' = ptrvl4 /\ priotbl' = priotbl4 /\ cspacels' = cspacels4) |]
  )).
destruct (Int.eq i19 Int.zero) eqn: eq2.
2:{ (* case1 : IntraCommQueueEn <> 0 *)
eapply forward_rule1.
2:{
eapply ift_rule'.
introv Hsat.
eapply bop_rv.
eapply Hrv_cap with (n:= 5%nat);
 [match goal with |- ?tp = _ => try unfold tp end; eauto | simpl; eauto | eauto ].
sep get rv.
simpl; eauto.
pure_auto.
simpl; eauto.
change ($ 0) with Int.zero.
instantiate(1:= Afalse).
hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hval_inj'.
rewrite eq2 in Hval_inj'; simpl in Hval_inj';
destruct Hval_inj'; tryfalse.
}
introv Hsat.
destruct Hsat as [Hsat | Hsat].
simpl in Hsat; simpljoin; tryfalse.
sep normal.
sep eexists.
trycancel.
sep cancel A_dom_lenv.
sep cancel Aop.
sep cancel Aier.
sep split in Hsat.
sep split; eauto.
intros; splits; auto.
}
(* case 2 : IntraCommQueueEn = 0 *)
eapply forward_rule1.
2:{
eapply ift_rule'.
introv Hsat.
eapply bop_rv.
eapply Hrv_cap with (n:= 5%nat);
 [match goal with |- ?tp = _ => try unfold tp end; eauto | simpl; eauto | eauto ].
sep get rv.
simpl; eauto.
pure_auto.
simpl; eauto.

hoare forward.
simpl nth_val; eauto.
simpl nth_val; eauto.
(* 3:{ simpl nth_val; eauto. }
3:{ simpl nth_val; eauto. }
unfold CAP_QUEUE_CLASS.
change (Int.unsigned ($ 5)) with 5.
auto with zarith.
auto with zarith. *)
subst. go.

introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
eapply true_if_else_true; eauto.
}

unfold CapSpec.ucos_CNode_DeletePost.
unfold CapSpec.ucos_CNode_DeletePost'.
unfold getasrt.
introv Hsat.
destruct Hsat as [Hsat | Hsat].
sep normal in Hsat.
sep destruct Hsat.
sep_lifts_trms_in Hsat logic_cs.
eapply sep_pure_split in Hsat; destruct Hsat as (Heq_lg & Hsat).
inverts Heq_lg.
sep normal.
sep eexists.
trycancel.
sep cancel A_dom_lenv.
sep cancel Aop.
sep cancel Aier.
sep split in Hsat.
sep split; eauto.
sep cancel AOSCSpacePrioTbl.
sep cancel p_local.
sep cancel ios_cap_defs.prio.
sep cancel H78.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
introv Hf; tryfalse.
sep_lifts_trms_in Hsat val_inj.
eapply sep_pure_split in Hsat; destruct Hsat as (Hval_inj' & Hsat).
change ($ 0) with Int.zero in Hval_inj'.
rewrite eq2 in Hval_inj'; simpl in Hval_inj';
destruct Hval_inj'; tryfalse.

hoare normal pre.
apply ex_intro_rule; intro s5.
apply ex_intro_rule; intro pb5.
apply ex_intro_rule; intro pi5.
apply ex_intro_rule; intro ptrvl5.
apply ex_intro_rule; intro priotbl5.
apply ex_intro_rule; intro cspacels5.
hoare_split_pure_all.

(* If ((((((uconf ′ → cpus) [coreNum ′]) .. cpu_ksDomains) [ios_cap_defs.i ′])
     .. CapEnTbl) .. IntraCommMutexEn ==ₑ ′ 0) *)
eapply seq_rule with (p':=
 (EX s' pb' pi' ptrvl' priotbl' cspacels',
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  Aisr empisr **
  Aier v'76 **
   <|| s' ||>  **
  AOSCSpacePrioTbl (pb', pi') ptrvl' priotbl' cspacels' **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((attr, pthread_attr_t ∗)
     :: (coreNum, char_t)
        :: (ios_cap_defs.i, char_t)
           :: (j, char_t)
              :: (uconf, ucos_conf_t ∗)
                 :: (pt, long)
                    :: (entry, (Void) ∗)
                       :: (ios_cap_defs.prio, char_t)
                          :: (os_code_defs.x, long) :: (y, long) :: nil) **
  LV ios_cap_defs.prio @ char_t |-> Vint32 tsk_prio ** H78 **
  [| CSPACEList_P ptrvl' 0%nat cspacels' |] **
  [| ptrvl_to_cspace_to_ptrvl ptrvl' cspacels' |] **
  [| Int.eq i24 Int.zero = false ->
       (s' = s5 /\ pb' = pb5 /\ pi' = pi5 /\ ptrvl' = ptrvl5 /\ priotbl' = priotbl5 /\ cspacels' = cspacels5) |]
  )).
destruct (Int.eq i24 Int.zero) eqn: eq2.
2:{ (* case1 : IntraCommMutexEn <> 0 *)
eapply forward_rule1.
2:{
eapply ift_rule'.
introv Hsat.
eapply bop_rv.
eapply Hrv_cap with (n:= 4%nat);
 [match goal with |- ?tp = _ => try unfold tp end; eauto | simpl; eauto | eauto ].
sep get rv.
simpl; eauto.
pure_auto.
simpl; eauto.
change ($ 0) with Int.zero.
instantiate(1:= Afalse).
hoare_lifts_trms_pre val_inj.
eapply pure_split_rule'; introv Hval_inj'.
rewrite eq2 in Hval_inj'; simpl in Hval_inj';
destruct Hval_inj'; tryfalse.
}
introv Hsat.
destruct Hsat as [Hsat | Hsat].
simpl in Hsat; simpljoin; tryfalse.
sep normal.
sep eexists.
trycancel.
sep cancel A_dom_lenv.
sep cancel Aop.
sep cancel Aier.
sep split in Hsat.
sep split; eauto.
intros; splits; auto.
}
(* case 2 : IntraCommMutexEn = 0 *)
eapply forward_rule1.
2:{
eapply ift_rule'.
introv Hsat.
eapply bop_rv.
eapply Hrv_cap with (n:= 4%nat);
 [match goal with |- ?tp = _ => try unfold tp end; eauto | simpl; eauto | eauto ].
sep get rv.
simpl; eauto.
pure_auto.
simpl; eauto.

hoare forward.
simpl nth_val; eauto.
simpl nth_val; eauto.
(* 3:{ simpl nth_val; eauto. }
3:{ simpl nth_val; eauto. }
unfold CAP_MUTEX_CLASS.
change (Int.unsigned ($ 8)) with 8.
auto with zarith.
auto with zarith. *)
subst. go.

introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
introv Hsat; sep pauto; sep cancel p_local; simpl; auto.
eapply true_if_else_true; eauto.
}

unfold CapSpec.ucos_CNode_DeletePost.
unfold CapSpec.ucos_CNode_DeletePost'.
unfold getasrt.
introv Hsat.
destruct Hsat as [Hsat | Hsat].
sep normal in Hsat.
sep destruct Hsat.
sep_lifts_trms_in Hsat logic_cs.
eapply sep_pure_split in Hsat; destruct Hsat as (Heq_lg & Hsat).
inverts Heq_lg.
sep normal.
sep eexists.
trycancel.
sep cancel A_dom_lenv.
sep cancel Aop.
sep cancel Aier.
sep split in Hsat.
sep split; eauto.
sep cancel AOSCSpacePrioTbl.
sep cancel p_local.
sep cancel ios_cap_defs.prio.
sep cancel H78.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
eapply adisj_elim in Hsat; destruct Hsat as [Hsat | Hsat]; sep split in Hsat; auto.
introv Hf; tryfalse.
sep_lifts_trms_in Hsat val_inj.
eapply sep_pure_split in Hsat; destruct Hsat as (Hval_inj' & Hsat).
change ($ 0) with Int.zero in Hval_inj'.
rewrite eq2 in Hval_inj'; simpl in Hval_inj';
destruct Hval_inj'; tryfalse.

hoare normal pre.
apply ex_intro_rule; intro s6.
apply ex_intro_rule; intro pb6.
apply ex_intro_rule; intro pi6.
apply ex_intro_rule; intro ptrvl6.
apply ex_intro_rule; intro priotbl6.
apply ex_intro_rule; intro cspacels6.
hoare_split_pure_all.

(* ++ j ′ *)
subst.
hoare_lifts_trms_pre (Aisr, Ais).
transform_pre add_a_isr_is_prop ltac:(sep cancel Aisr;
                                        sep cancel Ais).
hoare forward.
trycancel.
sep cancel Aop.
sep cancel Aier.
sep cancel A_dom_lenv.
unfold Alvarmapsto.
sep_lifts_trms AksDomains'.
eapply AksDomains'_select_sn_strong_frm; eauto.
solve_part_int_rgn.
unfold node_offt.
sep normal; sep eexists.
sep cancel AksDomains'.
sep cancel AksDomains'.
sep cancel ADeviceioTbl'.
simpl typelen.
sep pauto; eauto.
sep cancel cap_conf_t.
sep cancel Aarray.
sep cancel domain_conf_t.
sep cancel EvtInv.
sep cancel AOSTCBList'.
sep cancel AOSTCBFreeList'.
sep cancel APthreadAttr.
sep cancel AOSCSpacePrioTbl.
sep cancel pt.
sep cancel vpt.
auto.
{
    clear - Hvj_lt' Hscdlen_rgn1 Hscdlen_rgn2 Hget_baddr' Hvj_len.
    destruct (Int.eq (vj0 +ᵢ  $ 1) ksdomscdlen) eqn: eq1; auto.
    right.
    rewrite Inteq_false_is_Zneq in eq1.
    rewrite Intlt_true_is_Zlt.
    assert (Hvj'_eq: Int.unsigned (vj0 +ᵢ  $ 1) = Int.unsigned vj0 +1).
    {  pose proof (Int.unsigned_range_2 vj0).
       unfold Int.add.
       change (Int.unsigned ($ 1)) with 1.
       rewrite Int.unsigned_repr; auto.
       split; solve_part_int_rgn.
     }
    rewrite Hvj'_eq.
    rewrite Z.add_simpl_r.
    split.
    solve_part_int_rgn.
    introv Hnz.
    repeat eexists; eauto.
    rewrite <- Hvj_len. rewrite nth_vallist_get_idx; eauto.
    unfolds; simpl; auto.
}
auto.
auto.
go.
clear -Hattr_mat. simpl in Hattr_mat; simpljoin; auto.
auto.
(* end of Aistrue *)

(*Aisfalse (j′ <ₑ  (((uconf′→ cpus)[coreNum′])..cpu_ksDomScheduleLength))*)
eapply backward_rule1 with (p := 
( EX er (* ehdrvll *) ptrvl priotbl cspacels vi vj vx vy ventry pattr_vl vprio pb pi s,
    Aisr empisr ** Aie false ** Ais nil ** Acs (true::nil) ** Aier er ** A_isr_is_prop **
    <|| s ||> **
    LV j @ char_t |-> (Vint32 vj) **
    LV entry @ (Void) ∗ |-> ventry **
    LV uconf @ ucos_conf_t ∗ |-> Vptr (boot_b, Int.zero) **
    LV y @ long |-> vy **
    LV os_code_defs.x @ long |-> vx **
    LV ios_cap_defs.prio @ char_t |-> vprio **
    LV pt @ long |-> vpt **
    LV ios_cap_defs.i @ char_t |-> vi **
    LV attr @ pthread_attr_t ∗ |-> Vptr vattr **
    LV coreNum @ char_t |-> Vint32 cnum **
    A_dom_lenv
    ((attr, pthread_attr_t ∗)
     :: (coreNum, char_t)
        :: (ios_cap_defs.i, char_t)
           :: (j, char_t)
              :: (uconf, ucos_conf_t ∗)
                 :: (pt, long)
                    :: (entry, (Void) ∗)
                       :: (ios_cap_defs.prio, char_t) :: (os_code_defs.x, long) :: (y, long) :: nil)%list **
    AIntrDomainMux (boot_b, Int.zero) v'17 m **
    AAllArea (boot_b, Int.zero) v'18 a **
    AksDomains' (Vptr v'9) dom_vll **
  AksDomSchedule' (Vptr v'8) dscd_vll **
  Aarray v'7 (Tarray char_t ∘ 2) drtbl_vl **
  Astruct (cpu_b, cpu_i +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned cnum) * (typelen cpu_conf_t)))
    cpu_conf_t (Vint32 i11 :: x4 :: Vint32 ksdomscdlen :: Vint32 i9 :: x9 :: x10 :: nil) **
  Acpus' (Vptr (cpu_b, cpu_i)) v' **
  Acpus'
    (Vptr
       (cpu_b,
       cpu_i +ᵢ
       $ Z.of_nat (S (Z.to_nat (Int.unsigned cnum)) * typelen cpu_conf_t)))
    v'0 **
    (* Acpus' (Vptr (cpu_b, cpu_i)) cpuc ** *)
    AChannelTbl (boot_b, Int.zero) v'20 m1 **
    APortTbl (boot_b, Int.zero) v'22 m3 **
    Astruct (boot_b, Int.zero) ucos_conf_t (Vint32 i8 :: Vint32 i7 :: Vint32 i4 :: Vint32 i3
                                            :: Vint32 i2 :: Vint32 i1 :: x6 :: x5 :: x :: x0 
                                            :: Vint32 i0 :: x2 :: x3 :: Vint32 i6 :: nil) **
    (* AucosConf (v'16, v'17, v'18, cpuc, v'20, v'21, v'22)
                           (u, u0, u1, u2, u3, u4, m, a, m0, m1, u5, m2, m3, u6) ** *)
    ARootTaskStk rtsk_vll absrtsk **
    Astruct vattr pthread_attr_t pattr_vl **
   [|struct_type_vallist_match pthread_attr_t pattr_vl|] **
   Avalid addr_vl ehdrvll **
    (* condition about PthreadCreatePre' *)
    (EX ptbl p1 p2 tcbl1 tcbcur tcbl2 rtbl rgrp ecbls tcbls (* t ct *) vhold ptfree lfree ptls pattrb
        scapl mcapl qcapl, 
                   (* AOSMapTbl ** AOSUnMapTbl ** *) AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold ** 
                   AOSTCBList' p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls ptfree **
                   AOSTCBFreeList' ptfree lfree ct tcbls**
                   AOSRdyTblGrp rtbl rgrp ** (* AOSTime (Vint32 t) ** *)
                   HTCBList tcbls ** (* HTime t ** *) HCurTCB ct ** (* AGVars ** *)
                   APthreadAttr pattrb **
                   EvtInv ecbls p1 (tcbl1 ++ tcbcur :: tcbl2) tcbls vhold scapl mcapl qcapl **
                   [| RH_TCBList_ECBList_P ecbls tcbls ct|]) **
   (* condition about ucos_CNode_DeletePre' *)
    AOSCSpacePrioTbl (pb, pi) ptrvl priotbl cspacels **
    [|CSPACEList_P ptrvl 0 cspacels |] **
    [|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] **
    p_local OSLInv ct init_lg **
    [| (Int.eq vj ksdomscdlen = true) (* out of loop *) |]
    )
).
introv Hsat.
destruct Hsat as (Hsat & Hisfalse).
sep destruct Hsat.
lets Hcp: aconj_intro Hsat Hisfalse.
eapply sep_aconj_r_aisfalse_to_astar in Hcp; eauto.
2:{
clear Hsat Hcp.
introv Hsat.
eapply bop_rv.
sep get rv.
2:{
sep_get_rv_array_struct_conf.
go.
}
sep split in Hsat.
clear -H14 Hscdlen_rgn2.
unfold DSCHEDULE_SIZE in *.
eapply mund_int_a2.
destruct H14.
eapply sem_lab.semacc_int_eq_true in H; subst.
auto with zarith.
destruct H.
rewrite Intlt_true_is_Zlt in H.
auto with zarith.
simpl; eauto.
pure_auto.
simpl; auto.
}
clear -Hcp.
sep split in Hcp.
rename H3 into Hif.
destruct (Int.ltu x14 ksdomscdlen) eqn: eq1;
simpl in Hif; destruct Hif; tryfalse.
destruct H2 as [Heq_len | Hf].
2:{ simpljoin; tryfalse. }
sep auto.

(* RETURN *)
(* unprotect Heqboot_b.
subst boot_b. *)
hoare forward.
sep cancel AOSCSpacePrioTbl.
sep cancel Avalid.
sep cancel pthread_attr_t.
sep cancel ARootTaskStk.
instantiate(1:= (u, u0, u1, u2, u3, u4, m, a, m0, m1,u5, m2, m3, u6)).
unfold AucosConf.
unfold node.
unfold RHL_ucnodeosconft_P.
sep normal.
exists boot_b boot_b Int.zero.
unfold BOOT_DATA_ADDRESS.
rewrite <- Heqboot_b.
unfold ACPUs.
sep pauto; eauto.
eapply Acpus'_select_sn_strong_frm; eauto.
solve_part_int_rgn.
unfold node_offt.
sep cancel Acpus'.
sep cancel Acpus'.
sep pauto; eauto.
sep auto.
unfold CPU_ksDomScLength_Good.
eexists. unfold V_CPUksDomScheduleLength; simpl.
splits; eauto.
split; auto.
go.
splits; auto.
splits; auto.
unfolds; simpl.
splits; try(rewrite leb_bytemax_true_intro); auto.
auto.
auto.
auto.
eauto.
eauto.
4:{ simpl; eauto. }
2:{ match goal with H: length _ = Z.to_nat (Int.unsigned cnum) |- _ =>
       rewrite <- H end.
       rewrite nth_error_middle; eauto. }
unfolds; simpl; auto.
auto.
auto.
auto.
Unshelve.
trivial.
Qed.