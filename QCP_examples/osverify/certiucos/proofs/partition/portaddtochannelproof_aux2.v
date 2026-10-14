Require Import ucos_include.
Require Import Lia.

Require Import aux_pureLib.

Require Import abs_op_corecommu_rules.
Require Import corecommu_sep_added.
Require Import corecommu_tactics.
Require Import partition_rules.
Require Import partition_seprules.
Require Import partition_absrules.
Require Import partition_symrules.
Require Import partition_tactics.
Require Import corecommu_rules.
Require Import partition_initrules.
Require Import portaddtochannelproof_aux.

Local Open Scope Z_scope.
Local Open Scope int_scope.


Lemma channel_V_srcdstkport_dsthead_node: forall n chanptr chanvl chann dstkp dstkportl chanl chandstkportll kportvl kportl dportl dpptrl,
  nth_error chanvl n =Some (Vptr chanptr) ->
  nth_error chanl n = Some chann ->
  nth_error chandstkportll n = Some ((dstkp :: dstkportl)) ->
  OS_Channel_V_dstPortsHead chann = Some (Vptr dstkp) ->
  channel_V_srcdstkport chanvl chanl chandstkportll kportvl kportl dportl dpptrl ->
  (exists n kport, nth_error kportvl n = Some (Vptr dstkp)  /\  nth_error kportl n = Some kport  /\ 
    OS_K_Port_V_channel kport = Some (Vptr chanptr) /\
    exists pid dmptr dmport, OS_K_Port_V_dmport kport = Some (Vptr dmptr) /\ 
                            nth_error dpptrl pid = Some dmptr /\ nth_error dportl pid = Some dmport /\ 
                            OS_Port_V_direction dmport = Some (Vint32 (Int.repr DESTINATION))).
Proof.
  induction n;intros.
  - destruct chanvl, chanl;simpl in H, H0;try  discriminate.
    inversion H. subst. inversion H0. subst.
    destruct chandstkportll; cbn in H1; try contradiction.
    destruct H3 as [? _]. 
    destruct H3. simpljoin1. tryfalse.
    destruct H3 as [? [? [_ ?]]]. 
    inversion H3;subst x.
    inversion H1;subst l.
    destruct H4 as [? _]. 
    apply H4;eauto.
  - destruct chanvl, chanl;simpl in H, H0;try  discriminate.
    destruct chandstkportll; cbn in H1. contradiction.
    destruct H3 as [_ ?].
    eapply IHn; eauto.
Qed.

Lemma OSPortAddToChannel_incore_SourcePort: forall (ct: tid) 
(err_l: addrval) (Herrtp: isptr (Vptr err_l))  res_v
(p_b: block) (p_i: int32) (H2: isptr (Vptr (p_b, p_i))) 
(srcp_v: val) (aop: spec_code) (ier: ier) 
(err_v curdomain: int32)  (domainv: addrval) (domainvl: list val) (vsem: val) 
(Hcurd: Int.eq Int.zero curdomain = true \/ Int.lt Int.zero curdomain = true /\ Int.lt curdomain ($ 8) = true) 
(portchanid: int32)  
(p1 p2: val) (tcbl1: list vallist) (tcbcur: vallist) (tcbl2: list vallist) (rtbl: vallist) (tcbls: TcbMod.map) (ecbls: EcbMod.map) 
(vhold: addrval) (scapl mcapl qcapl: list vallist) (dportlptr: val) (dportl1: list vallist) (dport: vallist) (dportl2: list vallist) (dportmsgll1: list (list vallist)) (msgl: list vallist) (dportmsgll2: list (list vallist)) (dpptrl otherppl: list addrval) (otherpl: list vallist) (othermsgll: list (list vallist)) (kportfptr: val) (kportfl: list vallist) (chanfptr: val) (chanfl: list vallist) (dportls1: DomainPortMod.map) (pcn: port_coreNum) (pd: port_domain) (pid: port_id) (pst: port_status) (pintick: port_intick) (poutick: port_outick) (pt: Portt)  
(portattrv: addrval) (portattrvl: list val)
(kp_b: block) (kportvl1 kportvl2: vallist) 
(x0 x4: val) (i i0 i1 i2: int32) (kportl1 kportl2: list vallist) (kp: list val) (Heqkp: kp = Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) 
(Hptptr: RL_PortPtrList dportlptr (dportl1 ++ dport :: dportl2) dpptrl)
(Hinecb: Forall (fun x : addrval => exists wt, get ecbls x = Some (absport, wt)) dpptrl)
(H6: DomainportNode_P dport (pcn, pd, pid, SourceP, pst, pintick, poutick, pt) msgl)
(H1: R_Kernelport_DomainPort_init (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) (kportl1 ++ kp :: kportl2)        (dportl1 ++ dport :: dportl2) dpptrl) 
(Hnthkpl: nth_error (kportl1 ++ kp :: kportl2) ∘ (Int.unsigned ($ Z.of_nat pid)) = Some kp) 
(H5: length dportmsgll1 = length dportl1) 
(Hdptp: struct_type_vallist_match' OS_Port_Seg_dls dport)
(chanl1 chanl2: list vallist) (chandstportll1 chandstportll2: list (list addrval)) (v'8: list addrval) (x3 x5 x6 x7: val) (i3 i4 i5 i6: int32) (v': block) 
(chanvl1 chanvl2: list val)
(Hchtail: channel_V_dstPortsTail (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2)
(chandstportll1 ++ v'8 :: chandstportll2))
(Hportch: channel_V_srcdstkport_aux  (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2)  (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2)             (chandstportll1 ++ v'8 :: chandstportll2) (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)             (kportl1 ++ kp :: kportl2) (dportl1 ++ dport :: dportl2) dpptrl) 
(pri: priority) (st: taskstatus) (msg: msg) (sus: susstatus) 
(p_nextv: val) (pptr: addrval) (H10: OS_Port_V_nextPort dport = Some p_nextv) 
(Hkpid: OS_K_Port_V_portID kp = Some (V$ Z.of_nat pid)) 
(Hkpdm: OS_K_Port_V_dmport kp = Some (Vptr (p_b, p_i))) 
(Hkpcn: OS_K_Port_V_coreNum kp = OS_Port_V_coreNum dport) 
(Hporid: OS_Port_V_portID dport = Some (V$ Z.of_nat pid)) 
(Hdpqstart: OS_Port_V_OSQStart dport = Some (Vptr pptr))
(H22: forall (id1 id2 : nat) (p1 p2 : addrval),
id1 <> id2 ->
nth_val id1 (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) = Some (Vptr p1) ->
nth_val id2 (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) = Some (Vptr p2) -> p1 <> p2)
(H21: array_type_vallist_match OS_K_Port ∗ (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2))
(H27: forall (id1 id2 : nat) (p1 p2 : addrval),
id1 <> id2 ->
nth_val id1 (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) = Some (Vptr p1) ->
nth_val id2 (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) = Some (Vptr p2) -> p1 <> p2)
(H26: array_type_vallist_match OS_Channel ∗ (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2))
(H23: length (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) = ∘ PORT_NUMS) 
(H28: length (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) = ∘ CHANNEL_NUMS) 
(Hlenchanvl1: length chanvl1 = Z.to_nat (Int.unsigned portchanid)) 
(H31: Int.unsigned i2 <= 255) 
(H32: Int.unsigned i1 <= 255) 
(H33: isptr x0) 
(H34: isptr Vnull) 
(H35: Int.unsigned i0 <= 255) 
(H36: Int.unsigned i <= 255) 
(H45: length chanl1 = length chanvl1) 
(H46: length chandstportll1 = length chanvl1) 
(H40: Int.unsigned i6 <= 255) 
(H41: Int.unsigned i5 <= 255) 
(H42: Int.unsigned i4 <= 255) 
(H47: Int.unsigned i3 <= 255) 
(H48: isptr x3) 
(H49: isptr x5) 
(H50: isptr x6) 
(H51: isptr x7) 
(H39: Int.eq i3 ($ DEFAULT_CHANNLE_SEMAPHROE) = true) 
(H57: struct_type_vallist_match OS_K_Port kp) 
(H55: length kportvl1 = ∘ (Int.unsigned ($ Z.of_nat pid))) 
(H56: length kportl1 = ∘ (Int.unsigned ($ Z.of_nat pid)))
(H30: asrt)
(HeqH30: H30 =
LV kport @ OS_K_Port ∗ |-> Vptr (kp_b, Int.zero) **
kportNode_P kportvl1 kportl1 **
kportNode_P kportvl2 kportl2 **
LV resource_get_res @ char_t |-> res_v **
LV semaphore @ char_t |-> Vint32 i3 **
ChannelNode chanvl1 chanl1 chandstportll1 **
ChannelNode chanvl2 chanl2 chandstportll2 **
Channel_dstkport_get x3 Vnull ∘ (Int.unsigned i4) v'8 **
LV channel @ OS_Channel ∗ |-> Vptr (v', Int.zero) **
GAarray OSChannelIDTbl (Tarray OS_Channel ∗ ∘ CHANNEL_NUMS) (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) **
GAarray OSKernelPortIDTbl (Tarray OS_K_Port ∗ ∘ PORT_NUMS) (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) **
Aie false **
Ais nil **
Acs (true :: nil) **
Aisr empisr **
A_isr_is_prop **
Aier ier **
GV ksCurDomain @ long |-> Vint32 curdomain **
GV ksDomains @ OSdomain_t ∗ |-> Vptr domainv **
Astruct (get_off_addr domainv (Int.mul ($ 34) curdomain)) OSdomain_t domainvl **
GV OSPortAttrTbl @ OSport_attr_t ∗ |-> Vptr portattrv **
Astruct (get_off_addr portattrv (Int.mul ($ 12) ($ Z.of_nat pid))) OSport_attr_t portattrvl **
p_local OSLInv ct init_lg **
LV flag @ long |-> (V$ 1) **
APortStruct (p_b, p_i) dport **
([|OS_Port_V_mode dport = Some (Vint32 (ZToInt SAMPLE))|] ** dmportp_sllseg_sampleport_msg pptr msgl \\//
(EX (qend qin qout : addrval) (qsize qentries : int32) (vl2 : list vallist),
  [|OS_Port_V_mode dport = Some (Vint32 (ZToInt QUEUE))|] **
  [|OS_Port_V_OSQEnd dport = Some (Vptr qend)|] **
  [|OS_Port_V_OSQIn dport = Some (Vptr qin)|] **
  [|OS_Port_V_OSQOut dport = Some (Vptr qout)|] **
  [|OS_Port_V_OSQSize dport = Some (Vint32 qsize) /\ Int.unsigned qsize <= 65535|] **
  [|OS_Port_V_OSQEntries dport = Some (Vint32 qentries) /\ Int.unsigned qentries <= Int.unsigned qsize|] **
  [|Qport_msg_ptrs_P pptr qend qout qin (Int.unsigned qsize)|] **
  dmportp_sllseg_qport_msg qout qin pptr qend ∘ (Int.unsigned qentries) msgl **
  dmportp_sllseg_qport_msg qin qout pptr qend ∘ (Int.unsigned qsize - Int.unsigned qentries) vl2)) **
dmportp_sllseg p_nextv Vnull dportl2 dportmsgll2 OS_Port_V_nextPort **
dmportp_sllseg dportlptr (Vptr (p_b, p_i)) dportl1 dportmsgll1 OS_Port_V_nextPort **
GV OSDomainPortPtrList @ OS_Port ∗ |-> dportlptr **
AOSKernelPortFreeList kportfptr kportfl **
AOSChannelFreeList chanfptr chanfl **
OtherPortPtrList otherppl otherpl othermsgll **
kport_V_OSEventPtr (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) (kportl1 ++ kp :: kportl2)
  (dportl1 ++ dport :: dportl2) dpptrl **
EvtInv ecbls p1 (tcbl1 ++ tcbcur :: tcbl2) tcbls vhold scapl mcapl qcapl **
AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls **
LV re @ OS_Port ∗ |-> Vnull **
GV OSRunning @ char_t |-> Vint32 Int.zero **
PV err_l @ char_t |-> Vint32 err_v **
LV srcPort @ OS_Port ∗ |-> srcp_v **
LV err @ (char_t) ∗ |-> Vptr err_l **
LV port_ptr @ OS_Port ∗ |-> Vptr (p_b, p_i) ** LV channelID @ long |-> Vint32 portchanid ** A_dom_lenv ((err, (char_t) ∗) :: (port_ptr, OS_Port ∗) 
  :: (channelID, long) :: (semaphore, char_t) :: (resource_get_res, char_t) :: (kport, OS_K_Port ∗) :: (channel, OS_Channel ∗) :: (re, OS_Port ∗) :: (flag, long) :: (srcPort, OS_Port ∗) :: nil))
,
{|OS_spec, GetHPrio, OSLInv, I,
fun v : option val =>
((EX v0 : val, LV err @ (char_t) ∗ |-> v0) **
 (EX v0 : val, LV port_ptr @ OS_Port ∗ |-> v0) **
 (EX v0 : val, LV channelID @ long |-> v0) **
 (EX v0 : val, LV semaphore @ char_t |-> v0) **
 (EX v0 : val, LV resource_get_res @ char_t |-> v0) **
 (EX v0 : val, LV kport @ OS_K_Port ∗ |-> v0) **
 (EX v0 : val, LV channel @ OS_Channel ∗ |-> v0) **
 (EX v0 : val, LV re @ OS_Port ∗ |-> v0) ** (EX v0 : val, LV flag @ long |-> v0) ** (EX v0 : val, LV srcPort @ OS_Port ∗ |-> v0) ** Aemp) **
OSPortAddToChannelPost' (rev (Vptr err_l :: Vptr (p_b, p_i) :: Vint32 portchanid :: nil)) v
  (logic_val (Vint32 curdomain) :: logic_val (Vptr domainv) :: logic_lv domainvl :: logic_code aop :: logic_ier ier  :: logic_val (V$ Z.of_nat pid) :: logic_val (Vptr portattrv) :: logic_lv portattrvl :: logic_val p1
  :: logic_val p2 :: logic_llv tcbl1 :: logic_lv tcbcur :: logic_llv tcbl2 :: logic_lv rtbl :: logic_abstcb tcbls
  :: logic_absecb ecbls :: logic_val (Vptr vhold) :: logic_llv scapl :: logic_llv mcapl :: logic_llv qcapl
  :: logic_val dportlptr :: logic_llv dportl1 :: logic_lv dport
  :: logic_llv dportl2 :: logic_la dpptrl :: logic_lllv dportmsgll1 :: logic_llv msgl
  :: logic_lllv dportmsgll2 :: logic_la otherppl :: logic_lv (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) :: logic_llv (kportl1 ++ kp :: kportl2)
  :: logic_lv (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) :: 
  logic_llv (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2)
  :: logic_lla (chandstportll1 ++ v'8 :: chandstportll2) :: nil)
  ct **
A_dom_lenv
  ((err, (char_t) ∗)
   :: (port_ptr, OS_Port ∗)
      :: (channelID, long)
         :: (semaphore, char_t)
            :: (resource_get_res, char_t)
               :: (kport, OS_K_Port ∗) :: (channel, OS_Channel ∗) :: (re, OS_Port ∗) :: (flag, long) :: (srcPort, OS_Port ∗) :: nil), Afalse|}|- ct
{{ <|| END None;; aop ||>  **
  Astruct' (kp_b, Int.zero) OS_K_Port_Seg_dls (firstn 6 kp) **
  Astruct (v', Int.zero) OS_Channel (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) ** H30}} 
  (sseq
  (sifthen
     (ebinop oand (ebinop oeq (evar semaphore) (econst32 (Int.repr DEFAULT_CHANNLE_SEMAPHROE)))
        (eunop oppsite
           (ebinop oeq (efield (ederef (evar channel)) dstPortsHead) (ecast enull (Tptr OS_K_Port)))))
     (sifthen
        (eunop oppsite
           (ebinop oeq (efield (ederef (efield (ederef (evar channel)) dstPortsHead)) coreNum)
              (efield (ederef (evar kport)) coreNum)))
        (sseq
           (sassign (ederef (evar err)) (ecast (econst32 (Int.repr OS_PORT_ERR_MULTICORE)) Tint8))
           (srete (evar re)))))
  (sseq (sassign (efield (ederef (evar channel)) srcPort) (evar kport))
     (sseq (sassign (efield (ederef (evar channel)) srcPortsNum) (econst32 (Int.repr (Zpos xH))))
        (sseq (sassign (efield (ederef (evar kport)) channelID) (evar channelID))
           (sseq (sassign (efield (ederef (evar kport)) channel) (evar channel))
              (sifthen
                 (eunop oppsite
                    (ebinop oeq (evar semaphore) (econst32 (Int.repr DEFAULT_CHANNLE_SEMAPHROE))))
                 (sprim (scsl_semrel (evar semaphore)))))))))
{{ <|| END None;; aop ||>  **
  [|SourceP = SourceP|] **
  Astruct' (kp_b, Int.zero) OS_K_Port_Seg_dls (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i :: nil) **
  Astruct (v', Int.zero) OS_Channel (Vint32 i6 :: V$ 1 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: Vptr (kp_b, Int.zero) :: x7 :: nil) ** H30}}.
Proof.
  intros.
  pure intro.
  (* If (semaphore ′ ==ₑ ′ DEFAULT_CHANNLE_SEMAPHROE &&ₑ channel ′ → dstPortsHead !=ₑ 〈 OS_K_Port ∗ 〉 NULL) { .. } *)
  hoare name lift (Astruct (v', Int.zero) OS_Channel) (kportNode_P kportvl1 kportl1)
   (Astruct' (kp_b, Int.zero)) (kportNode_P kportvl2 kportl2) Channel_dstkport_get pre.
  hoare remember (1::2::3::4::5::nil)%nat pre.
  hoare forward;pauto.
  rewrite H39. clear - H48. cbn. destruct H48 as [ | [[? ?] ?]];subst;pauto.
  { (* if yes*)
    instantiate (1:= 
    [| (exists (dstkp : addrval) (dstkportl : list addrval), x3 = Vptr dstkp /\ v'8 = dstkp :: dstkportl /\ 
      exists n kport,
      nth_error (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) n = Some (Vptr dstkp) /\
      nth_error
        (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) n =
      Some kport /\
      OS_K_Port_V_channel kport = Some (Vptr (v', Int.zero)) /\ OS_K_Port_V_coreNum kport = Some (Vint32 i0) )
      |]**
    Astruct (v', Int.zero) OS_Channel
    (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) **
    kportNode_P kportvl1 kportl1 **
    Astruct' (kp_b, Int.zero) OS_K_Port_Seg_dls
      (firstn 6 (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)) **
    kportNode_P kportvl2 kportl2 ** 
    Channel_dstkport_get x3 Vnull ∘ (Int.unsigned i4) v'8 ** H).
    pure intro.
    rewrite H39 in H0. 
    destruct H48 as [ | [dstkp ?]];subst;simpl in H0.
    { exfalso. clear - H0. cbn in H0. mauto. }
    clear H0 H4 H3.
    (* If ((channel ′ → dstPortsHead) → coreNum !=ₑ kport ′ → coreNum) *)
    hoare name lift Channel_dstkport_get pre.
    rename v'8 into dstkportl.
    assert ((∘ (Int.unsigned i4)) = 0 \/ ∘ (Int.unsigned i4) > 0)%nat as [ | ]by lia.
    { rewrite H.
      eapply backward_rule1.
      { eapply Channel_dstkport_get_length. 
      }
      pure intro.
      destruct dstkportl; [ | simpl in H0;tryfalse].
      cbn [Channel_dstkport_get].
      pure intro.
      inversion H3.
    }
    eapply backward_rule1.
    { eapply Channel_dstkport_get_length.  }
    pure intro.
    destruct dstkportl; [ simpl in H0;lia | ].
    hoare_assert_pure (a = dstkp).
    { assert (∘ (Int.unsigned i4) = S  (∘ (Int.unsigned i4) - 1)) by lia.
      rewrite H4 in H3.
      cbn [Channel_dstkport_get] in H3.
      sep normal in H3.
      sep destruct H3.
      sep split in H3.
      inversion H9.
      auto.
    }
    pure intro.
    destruct Hportch as [Hportch Hnodupkp].
    eapply channel_V_srcdstkport_dsthead_node in Hportch as ?.
    2: eapply nth_error_middle.
    2: rewrite <- H45;eapply nth_error_middle.
    2: rewrite <- H46;eapply nth_error_middle.
    2: cbn;eauto.
    destruct H3 as (dst_n & dstkport & Hnthdstkpvl & Hdstkpchan & Hnthdstkpl & ?).
    destruct H3 as (dstpid & dstdptr & dstdport & Hdstdp & Hnthdstdpptrl & Hnthdstdportl  & Hdstdire).
    eapply backward_rule1. 
    { intros s Hs. kport_combine kportvl1 kportvl2.  rewrite H55. auto. }
    eapply backward_rule1.
    { eapply kportNode_P_getsome_frm with (n := dst_n);eauto. }
    pure intro.
    rename v'1 into kportvl3. rename v'2 into kportvl4. rename v'3 into kportl3. rename v'4 into kportl4.
    rename H7 into Hdstkportl. rename H4 into Hdstkportvl.
    remember ((Vint32 i10 :: Vint32 i9 :: x1 :: x2 :: Vint32 i8 :: Vint32 i7 :: x9 :: nil)) as dstkport.
    assert (OS_Channel_V_dstPortsHead   (Vint32 i6
    :: Vint32 i5
       :: Vint32 i4
          :: Vint32 i3 :: Vptr (v'0, Int.zero) :: x5 :: x6 :: x7 :: nil)= Some (Vptr (v'0, Int.zero)) ).
    { cbn. auto. }
    eapply forward_rule2.
    eapply ift_rule''.
    { symbolic_exe_port.
      { eapply channel_dstPortsHead_coreNum_rv with (kport := dstkport);eauto.
        3: sep autocancel;exact H7.
        pauto.
        subst dstkport. pauto. }
      { kport_combine kportvl3 kportvl4.
        2: subst dstkport;pauto.
        sep remember (1::nil)%nat in H7.
        assert (s |= kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) ** H16) as Hs.
        { rewrite Hdstkportl, Hdstkportvl. exact H7. }
        clear H7.
        subst H16.
        eapply KPort_coreNum_rv_kportnode with (kpptr := (kp_b, Int.zero));eauto.
        2:sep autocancel;exact Hs.
        rewrite <- H55. apply nth_error_middle. }
      subst dstkport. cbn. pauto.
      pauto.
      subst dstkport. cbn. pauto.
      pauto. }
    { (* yes*)
      instantiate (1:= Afalse).
      pure intro.
      cbn in H7.
      assert (Int.eq i8 i0 =false) by pauto.
      clear H16 H17 H7.
      eapply backward_rule1.
      { intros s Hs. kport_combine kportvl3 kportvl4. pauto. }
      hoare forward.
      assert ((Int.modu ($ OS_PORT_ERR_MULTICORE) ($ Byte.modulus)) =$ OS_PORT_ERR_MULTICORE).
      { clear. unfold OS_PORT_ERR_MULTICORE. mauto. } 
      rewrite H7;clear H7.
      hoare abscsq;[apply noabs_oslinv | | ].
      eapply absinfer_seq_end;[ | | intros s Hs; exact Hs].
      1,2: can_change_aop_solver'.
      (* RETURN re ′ *)
      eapply rete_rule.
      intros s Hs.
      split.
      2:{ symbolic_execution.  }
      unfold OSPortAddToChannelPost'.
      sep normal. 
      sep eexists.
      sep autocancel.
      sep split;[ | cbn;eauto].
      right.

      port_combine.
      chann_combine chanvl1 chanvl2.
      2: pauto.
      unfold  AOSDomainPortPtrList, AOSKernelPortIDTbl, AOSChannelIDTbl.
      sep normal;sep eexists.
      sep split;eauto.
      unfold dmportp_sll.
      sep autocancel.
      rewrite Hdstkportl, Hdstkportvl.
      sep auto.
      { right.
        do 7 eexists. split.
        { unfold OSPortAddToChannel_portchanninfo.
          splits;eauto.
          rewrite <- H55. eapply nth_error_middle.
          instantiate (2:= portchanid).
          unfold nat_of_Z. rewrite <- Hlenchanvl1. apply nth_error_middle.
          unfold nat_of_Z. rewrite <- Hlenchanvl1, <- H45.  eapply nth_error_middle.
          unfold nat_of_Z. rewrite <- Hlenchanvl1, <- H46. eapply nth_error_middle.
        }
        left.
        splits;auto.
        { clear - H6. unfold DomainportNode_P, Domainport_direction_P in *. simpljoin1.
          auto. } 
        left.
        split;auto.
        unfold OSPortAddToChannel_retvalue_case2_1.
        cbn.
        do 2 eexists.
        splits;eauto.
        rewrite Hdstkportvl.
        do 2 eexists.
        cbn;splits;eauto.
        apply nth_error_middle.
        cbn. unfold not;intros. inversion H7. subst. clear - H18. rewrite Int.eq_true in H18. tryfalse.
        }
        split;auto.
        split;auto.
      }
    intros s Hs.
    destruct Hs as [Hs | Hs].
    sep split in Hs. tryfalse.
    
    sep normal in Hs.
    sep normal.
    sep autocancel.
    kport_combine kportvl3 kportvl4.
    2: subst;pauto.
    sep split;eauto.
    unfold vallist in Hs,  Hdstkportl, Hdstkportvl.
    rewrite <- Hdstkportl, <- Hdstkportvl in Hs.  
    apply kportNode_P_app_frm in Hs. sep autocancel.
    sep auto.
    rewrite H55. auto.
    unfold vallist in Hdstkportl, Hdstkportvl. unfold vallist.
    rewrite Hdstkportl, Hdstkportvl.
    exists ((v'0, Int.zero) ) dstkportl.
    splits;auto.
    do 2 eexists.
    cbn;splits;eauto.
    apply nth_error_middle.
    rewrite <- H9. apply nth_error_middle.
    sep split in Hs.
    subst dstkport. cbn in H7. 
    assert (Int.eq i8 i0 = true).
    { destruct (Int.eq i8 i0);auto.
      clear - H7;destruct H7;tryfalse. }
    apply Int_eq_dec in H16. subst i8.
    auto.
    }
  eapply backward_rule1.
  { instantiate (1:= 
  [| (exists (dstkp : addrval) (dstkportl : list addrval), x3 = Vptr dstkp /\ v'8 = dstkp :: dstkportl /\ 
  exists n kport,
  nth_error (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) n = Some (Vptr dstkp) /\
  nth_error
    (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) n =
  Some kport /\
  OS_K_Port_V_channel kport = Some (Vptr (v', Int.zero)) /\ OS_K_Port_V_coreNum kport = Some (Vint32 i0) ) \/ 
   x3 = Vnull |] **
  Astruct (v', Int.zero) OS_Channel (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) **
  kportNode_P kportvl1 kportl1 **
  Astruct' (kp_b, Int.zero) OS_K_Port_Seg_dls (firstn 6 (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)) **
  kportNode_P kportvl2 kportl2 ** Channel_dstkport_get x3 Vnull ∘ (Int.unsigned i4) v'8 ** H).
  intros s Hs.
  destruct Hs as [Hs | Hs].
  sep normal in Hs.
  sep autocancel.
  sep split in Hs. sep split;auto.

  sep normal in Hs.
  sep autocancel.
  sep split in Hs. sep split. sep auto.
  right.
  rewrite H39 in H0.
  destruct H48 as [ | [[? ?] ?]];subst;auto.
  clear - H0. cbn in H0. exfalso. mauto.
  }
  pure intro.  rename H0 into Hsinglecore.
  (* channel ′ → srcPort =ₑ kport ′;ₛ *)
  eapply seq_rule.
  hoare name lift (Astruct (v', Int.zero) OS_Channel) pre.
  hoare name lift (Alvarmapsto channel) pre.
  hoare name lift Aop pre.
  eapply assign_rule_struct_aop; 
  [intros s;split;intros Hs;exact Hs | unfold OS_Channel;simpl;eauto 
  | simpl; eauto
  | unfold id_nth; simpl; eauto
  | simpl; eauto
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | symbolic_exe_port
  | apply assign_type_match_true; simpl; auto
  | simpl; try lia
  | simpl; auto
  | li_sepauto li ].
  (* channel ′ → srcPortsNum =ₑ ′ 1;ₛ *)
  eapply seq_rule.
  eapply assign_rule_struct_aop; 
  [intros s;split;intros Hs;exact Hs | unfold OS_Channel;simpl;eauto 
  | simpl; eauto
  | unfold id_nth; simpl; eauto
  | simpl; eauto
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | symbolic_exe_port
  | apply assign_type_match_true; simpl; auto
  | simpl; try lia
  | simpl; auto
  | li_sepauto li ].
  (* kport ′ → channelID =ₑ channelID ′;ₛ *)
  eapply seq_rule.
  hoare name lift (Astruct' (kp_b, Int.zero) OS_K_Port_Seg_dls) pre.
  hoare name lift (Alvarmapsto kport) pre.
  hoare name lift Aop pre.
  eapply assign_rule_struct_aop_typeneq with (tp1 := OS_K_Port');
  [ intros s;split;intros Hs;[
    unfold Astruct, OS_K_Port'; exact Hs | 
    unfold Astruct, OS_K_Port' in Hs; exact Hs]
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | simpl;auto
  | simpl; auto
  | unfold id_nth; simpl; auto
  | simpl; auto
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | symbolic_exe_port
  | apply assign_type_match_true; simpl; auto
  | simpl; try lia
  | simpl; auto
  | li_sepauto li ].
  (* kport ′ → channel =ₑ channel ′ *)
  eapply seq_rule.
  hoare name lift (Astruct' (kp_b, Int.zero) OS_K_Port_Seg_dls) pre.
  hoare name lift (Alvarmapsto kport) pre.
  hoare name lift Aop pre.
  eapply assign_rule_struct_aop_typeneq with (tp1 := OS_K_Port');
  [ intros s;split;intros Hs;[
    unfold Astruct, OS_K_Port'; exact Hs | 
    unfold Astruct, OS_K_Port' in Hs; exact Hs]
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
  | simpl;auto
  | simpl; auto
  | unfold id_nth; simpl; auto
  | simpl; auto
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | intros; intro; tryfalse
  | symbolic_exe_port
  | apply assign_type_match_true; simpl; auto
  | simpl; try lia
  | simpl; auto
  | li_sepauto li ].
  (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) {CSLSEMREL (semaphore ′)} *)
  hoare forward;pauto.
  { instantiate (1:= Afalse).
    pure intro.
    rewrite H39 in H.
    clear - H. exfalso. mauto.
  }
  sep normal in H.
  destruct H.
  { sep split in H. tryfalse. }   
  sep autocancel.
  unfold Astruct, OS_K_Port' in H.
  sep auto.
Qed.

Lemma portaddtochannelproof_incore_destionation_endpart1: forall aop P r (ct: tid) pid v' i6 i5 i4 i3 i2 i1 i i0 x0 x3 x4 x5 x6 x7 
 dstkportl_ori  kp_b kportvl1 kportvl2 kportl1 kportl2 dportl dpptrl portchanid dportlptr ecbls (chanvl1 chanvl2: list val) chanl1 chanl2 chandstportll1 chandstportll2
 p_b p_i n dport
(Haop: can_change_aop P)
(Heqfa: Int.eq portchanid ($ CHANNEL_NUMS) = false)
(H0: Int.ltu ($ CHANNEL_NUMS) portchanid = false)
(H: RL_PortPtrList dportlptr dportl dpptrl)
(Hinecb: Forall (fun x : addrval => exists wt, get ecbls x = Some (absport, wt)) dpptrl)
(Hportch: channel_V_srcdstkport_aux (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) (chanl1 ++
 (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2)
(chandstportll1 ++ dstkportl_ori :: chandstportll2)
(kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
(kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)
 :: kportl2) dportl dpptrl)
(Hchtail: channel_V_dstPortsTail
   (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2)
   (chandstportll1 ++ dstkportl_ori :: chandstportll2))
(Hkpdp: R_Kernelport_DomainPort_init (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
(kportl1 ++
 (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) dportl dpptrl)
(Hkpdm: OS_K_Port_V_dmport (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) = Some (Vptr (p_b, p_i)))
(H4: nth_error dpptrl n = Some (p_b, p_i)) 
(H5: nth_error dportl n = Some dport) 
(Hdptp: OS_Port_V_direction dport = Some (V$ DESTINATION) )
(H22: forall (id1 id2 : nat) (p1 p2 : addrval),       id1 <> id2 ->       nth_val id1 (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) = Some (Vptr p1) ->       nth_val id2 (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) = Some (Vptr p2) -> p1 <> p2) 
(H23: length (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) = ∘ PORT_NUMS) 
(H21: array_type_vallist_match OS_K_Port ∗ (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)) 
(H24: Int.unsigned ($ Z.of_nat pid) < 64) 
(H25: Int.unsigned portchanid < 32) 
(H27: forall (id1 id2 : nat) (p1 p2 : addrval),       id1 <> id2 ->       nth_val id1 (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) = Some (Vptr p1) ->       nth_val id2 (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) = Some (Vptr p2) -> p1 <> p2) 
(H28: length (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) = ∘ CHANNEL_NUMS) 
(H26: array_type_vallist_match OS_Channel ∗ (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2)) 
(Hlenchanvl1: length chanvl1 = Z.to_nat (Int.unsigned portchanid)) 
(Hnthvalchan: nth_val' (Z.to_nat (Int.unsigned portchanid)) (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) =               Vptr (v', Int.zero)) 
(H31: Int.unsigned i2 <= 255) 
(H32: Int.unsigned i1 <= 255) 
(H33: isptr x0) 
(H34: isptr Vnull) 
(H35: Int.unsigned i0 <= 255) 
(H36: Int.unsigned i <= 255) 
(H37: isptr x4) 
(H29: nth_error (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2)         (length chanvl1) = Some (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil)) 
(H38: nth_error (chandstportll1 ++ dstkportl_ori :: chandstportll2) (length chanvl1) =    Some (dstkportl_ori)) 
(H45: length chanl1 = length chanvl1) 
(H46: length chandstportll1 = length chanvl1) 
(H40: Int.unsigned i6 <= 255) 
(H41: Int.unsigned i5 <= 255) 
(H42: Int.unsigned i4 <= 255) 
(Hi4le: Int.unsigned i4 <= 254)
(H47: Int.unsigned i3 <= 255) 
(H48: isptr x3) 
(H49: isptr x5) 
(H50: isptr x6) 
(H51: isptr x7) 
(H39: Int.eq i3 ($ DEFAULT_CHANNLE_SEMAPHROE) = true) 
(H57: struct_type_vallist_match OS_K_Port (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)) 
(H55: length kportvl1 = ∘ (Int.unsigned ($ Z.of_nat pid))) 
(H56: length kportl1 = ∘ (Int.unsigned ($ Z.of_nat pid))),
{|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- ct
{{ EX (kptailv : addrval) (dstkportl : list addrval),
   [| Int.unsigned i4 > 0 |] **
   [| dstkportl_ori = (dstkportl ++ kptailv :: nil)  |] **
   [| exists tailkp, struct_type_vallist_match OS_K_Port tailkp  /\ OS_K_Port_V_OSEventPtr tailkp = Some Vnull|] **
   <||  END None;; aop ||> **
   LV channel @ OS_Channel ∗ |-> Vptr (v', Int.zero) **
   Astruct (v', Int.zero) OS_Channel
      (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) **
   Channel_dstkport_get x3 (Vptr kptailv) (∘ (Int.unsigned i4) - 1)
      dstkportl **
   PV get_off_addr kptailv ($ 12) @ (Void) ∗ |-> Vptr (kp_b, Int.zero) **
   Channel_dstkport_get Vnull Vnull 0 nil **
   LV kport @ OS_K_Port ∗ |-> Vptr (kp_b, Int.zero) **
   kport_V_OSEventPtr (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
    (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)
     :: kportl2) dportl dpptrl **
   kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
    (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)
     :: kportl2) **
   LV semaphore @ char_t |-> Vint32 i3 **
   LV channelID @ long |-> Vint32 portchanid **  
   p_local OSLInv ct init_lg **
   A_dom_lenv
    ((err, (char_t) ∗)
     :: (port_ptr, OS_Port ∗)
        :: (channelID, long)
           :: (semaphore, char_t)
              :: (resource_get_res, char_t)
                 :: (kport, OS_K_Port ∗)
                    :: (channel, OS_Channel ∗)
                       :: (re, OS_Port ∗)
                          :: (flag, long)
                             :: (srcPort, OS_Port ∗) :: nil) ** P }}
channel ′ → dstPortsTail =ₑ kport ′;ₛ
++ channel ′ → dstPortsNum;ₛ 
kport ′ → channelID =ₑ channelID ′;ₛ
kport ′ → channel =ₑ channel ′;ₛ
kport ′ → OSEventPtr =ₑ 〈 (Void) ∗ 〉 NULL;ₛ
If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
{CSLSEMREL (semaphore ′)}
{{ [|RLH_PortPtrINecb dportlptr dportl dpptrl ecbls|] **
  [|R_Kernelport_DomainPort_init
      (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
      (kportl1 ++ (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i :: x4 :: nil)
       :: kportl2) dportl dpptrl|] **
  [|channel_V_srcdstkport_aux (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2)
      (chanl1 ++ (Vint32 i6  :: Vint32 i5 :: Vint32 (i4 +ᵢ  $ 1) :: Vint32 i3 :: x3:: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil) :: chanl2)
      (chandstportll1 ++ (dstkportl_ori ++ (kp_b, Int.zero) :: nil)
       :: chandstportll2)
      (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
      (kportl1 ++ (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i :: x4 :: nil)
       :: kportl2) dportl dpptrl|] **
   [|  channel_V_dstPortsTail
   (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 (i4 +ᵢ  $ 1) :: Vint32 i3 :: x3 :: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil) :: chanl2)
   (chandstportll1 ++ (dstkportl_ori ++ (kp_b, Int.zero) :: nil) :: chandstportll2)|] **
   [| struct_type_vallist_match OS_Channel (Vint32 i6 :: Vint32 i5 :: Vint32 (i4 +ᵢ  $ 1) :: Vint32 i3 :: x3 :: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil) |] **
   <|| END None ;; aop ||>  **
  LV channel @ OS_Channel ∗ |-> Vptr (v', Int.zero) **
  Astruct (v', Int.zero) OS_Channel
    (Vint32 i6
     :: Vint32 i5 :: Vint32  (i4 +ᵢ  $ 1) :: Vint32 i3 :: x3 :: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil) **
  Channel_dstkport_get x3 Vnull ∘ (Int.unsigned (i4 +ᵢ  $ 1))
    (dstkportl_ori ++ (kp_b, Int.zero) :: nil) **
  LV kport @ OS_K_Port ∗ |-> Vptr (kp_b, Int.zero) **
  kport_V_OSEventPtr (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
    (kportl1 ++
     (Vint32 i2
      :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i :: x4 :: nil)
     :: kportl2) dportl dpptrl **
  kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
    (kportl1 ++
     (Vint32 i2
      :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i :: x4 :: nil)
     :: kportl2) **
  LV semaphore @ char_t |-> Vint32 i3 **
  LV channelID @ long |-> Vint32 portchanid **
  p_local OSLInv ct init_lg **
  A_dom_lenv
    ((err, (char_t) ∗)
     :: (port_ptr, OS_Port ∗)
        :: (channelID, long)
           :: (semaphore, char_t)
              :: (resource_get_res, char_t)
                 :: (kport, OS_K_Port ∗)
                    :: (channel, OS_Channel ∗)
                       :: (re, OS_Port ∗)
                          :: (flag, long)
                             :: (srcPort, OS_Port ∗) :: nil) **  P}}.
Proof.
   intros.
   naive pure intro.
   rename v'0 into kptailv. rename v'1 into dstkportl.
   destruct H3 as [tailkp [Htailkptp Heptr]].
   subst dstkportl_ori.
   (* channel ′ → dstPortsTail =ₑ kport ′;ₛ *)
   eapply seq_rule.
   hoare name lift (Astruct (v', Int.zero) OS_Channel) pre.
   hoare name lift (Alvarmapsto channel) pre.
   hoare name lift Aop pre.
   eapply assign_rule_struct_aop; 
   [intros s;split;intros Hs;exact Hs | unfold OS_Channel;simpl;eauto 
   | simpl; eauto
   | unfold id_nth; simpl; eauto
   | simpl; eauto
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | symbolic_exe_port
   | apply assign_type_match_true; simpl; auto
   | simpl; try lia
   | simpl; auto
   | li_sepauto li ].
   (* ++ channel ′ → dstPortsNum;ₛ *)
   eapply seq_rule.
   hoare name lift (Astruct (v', Int.zero) OS_Channel) pre.
   hoare name lift (Alvarmapsto channel) pre.
   hoare name lift Aop pre.
   eapply assign_rule_struct_aop; 
   [intros s;split;intros Hs;exact Hs | unfold OS_Channel;simpl;eauto 
   | simpl; eauto
   | unfold id_nth; simpl; eauto
   | simpl; eauto
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | symbolic_exe_port
   | apply assign_type_match_true; simpl; auto
   | simpl; try lia
   | simpl; auto
   | li_sepauto li ].
   { pauto. }
   (* kport ′ → channelID =ₑ channelID ′;ₛ *)
   hoare name lift kportNode_P pre.
   eapply backward_rule1.
   { eapply kportNode_P_app_frm;eauto. rewrite H55. auto. }
   naive pure intro. rename H2 into Hkptp.
   eapply seq_rule.
   hoare name lift (Astruct' (kp_b, Int.zero) OS_K_Port_Seg_dls) pre.
   hoare name lift (Alvarmapsto kport) pre.
   hoare name lift Aop pre.
   eapply assign_rule_struct_aop_typeneq with (tp1 := OS_K_Port');
   [ intros s;split;intros Hs;[
      unfold Astruct, OS_K_Port'; exact Hs | 
      unfold Astruct, OS_K_Port' in Hs; exact Hs]
   | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
   | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
   | simpl;auto
   | simpl; auto
   | unfold id_nth; simpl; auto
   | simpl; auto
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | symbolic_exe_port
   | apply assign_type_match_true; simpl; auto
   | simpl; try lia
   | simpl; auto
   | li_sepauto li ].
   (* kport ′ → channel =ₑ channel ′;ₛ *)
   eapply seq_rule.
   hoare name lift (Astruct' (kp_b, Int.zero) OS_K_Port_Seg_dls) pre.
   hoare name lift (Alvarmapsto kport) pre.
   hoare name lift Aop pre.
   eapply assign_rule_struct_aop_typeneq with (tp1 := OS_K_Port');
   [ intros s;split;intros Hs;[
      unfold Astruct, OS_K_Port'; exact Hs | 
      unfold Astruct, OS_K_Port' in Hs; exact Hs]
   | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
   | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
   | simpl;auto
   | simpl; auto
   | unfold id_nth; simpl; auto
   | simpl; auto
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | symbolic_exe_port
   | apply assign_type_match_true; simpl; auto
   | simpl; try lia
   | simpl; auto
   | li_sepauto li ].
   (* merge kportNode_P *)
   change ((Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i :: nil)) 
   with (firstn 6 (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i ::x4:: nil)).   
   eapply backward_rule1.
   { unfold Astruct at 1. unfold OS_K_Port'. intros s Hs. kport_combine kportvl1 kportvl2. 
     rewrite H55. auto.
     clear - H57 H25.
     cbn in *.
     simpljoin1.
     splits;auto.  
     clear - H25. 
     assert (Int.unsigned portchanid <= 255) by lia.
     pauto. }
   (* kport ′ → OSEventPtr =ₑ 〈 (Void) ∗ 〉 NULL;ₛ *)
   hoare name lift kport_V_OSEventPtr pre.
   eapply backward_rule1.
   {  eapply kport_V_OSEventPtr_app_frm;eauto. rewrite H55. auto. }
   cbn [kport_V_OSEventPtr].
   hoare lift 2%nat pre.
   eapply backward_rule1.
   {  intros s Hs.
      eapply disj_star_elim_disj  in Hs.
      destruct Hs as [Hs  | Hs].
      2:{  exact Hs. } 
      exfalso.
      unfold OS_K_Port_V_channel in Hs.
      sep normal in Hs.
      sep destruct Hs.
      sep split  in Hs.
      destruct H3 as [? H3].
      cbn in H3.
      inversion H3. }
   naive pure intro.
   clear H2.
   (* kport ′ → OSEventPtr =ₑ 〈 (Void) ∗ 〉 NULL;ₛ *)
   eapply seq_rule.
   hoare name lift (Alvarmapsto kport) pre.
   hoare name lift Aop pre.
   eapply assign_rule_struct_member with (tp1 := OS_K_Port) (t' := (Void) ∗);
   [ | intro s;split;intros Hs;exact Hs | 
      unfold OS_K_Port;reflexivity | cbn;auto | cbn;auto 
      |  |  | symbolic_execution |  intros s Hs;sep auto|  idtac .. ].
   cbn;auto.  cbn;auto. apply eq_vptr. eauto.
   (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) {CSLSEMREL (semaphore ′)} *)
   hoare normal pre.
   hoare name lift Aop pre.
   eapply forward_rule2.
   hoare forward.
   { pauto. }
   { pauto. }
   { pauto. }
   naive pure intro.
   instantiate (1:= Afalse).
   rewrite H39 in H2. destruct H2 as [? _]. exfalso. clear - H2. mauto.
   intros s Hs.
   destruct Hs as [Hs | Hs].
   { sep normal in Hs. sep split in Hs. tryfalse.  }
   sep normal in Hs.
   sep autocancel.
   sep split.
   { sep name lift kport_V_OSEventPtr.
   eapply kport_V_OSEventPtr_app_frm. rewrite H55. auto.
   cbn [kport_V_OSEventPtr].
   sep autocancel.
   eapply disj_split.
   left.
   sep normal.
   exists n (p_b, p_i) dport.
   sep split;[ | cbn;eauto .. ].
   eapply disj_split.
   right.
   sep split;auto.
   sep auto.
   assert (∘ (Int.unsigned (i4 +ᵢ  $ 1)) = S (S (∘ (Int.unsigned i4) - 1) + 0 )).
   { rewrite Int_add_one_Sn. unfold nat_of_Z. 
     lia.
     lia. 
   }
   sep name lift Channel_dstkport_get in Hs.
   eapply Channel_dstkport_get_length in Hs.
   sep split in Hs.
   rewrite H3.
   eapply Channel_dstkport_get_compose with (vn := Vnull) (vl:= (Vint32 i2
   :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i :: Vnull :: nil)).
   { rewrite app_length.  rewrite H6.  cbn. lia. }
   { cbn;lia. }
   { clear - H57 H25.
   simpl in *.
   simpljoin1.
   splits;auto.
   clear - H25.
   mauto. }
   { cbn;auto. }
   sep autocancel.
   assert ((S (∘ (Int.unsigned i4) - 1)) = (S (∘ (Int.unsigned i4) - 1  + 0))) by lia.
   rewrite H7. clear H7.
   eapply Channel_dstkport_get_compose with (vn := (Vptr (kp_b, Int.zero))) (vl:= (update_nth_val 6 tailkp (Vptr (kp_b, Int.zero))));auto.
   { clear - Htailkptp. 
     do 7 (destruct tailkp as [ | ? tailkp];simpl in Htailkptp;tryfalse;destruct Htailkptp as [? Htailkptp];split;auto).
   }
   unfold OS_K_Port_V_OSEventPtr in *. port_nth_val_solve.
   sep autocancel.
   cbn.
   split;auto. }
   { cbn.
     splits;pauto.
     clear - Hi4le.
     rewrite Int_add_one_Sn' by lia.
     assert (Int.unsigned i4 + 1 <= 255) by lia.
     clear - H. pauto.
   }
   {  clear  s Hs.
      assert (length chanl1 = length chandstportll1). 
      { rewrite H46. auto. }
      apply channel_V_dstPortsTail_app in Hchtail as [Hchtail1  [? Hchtail2]];auto.
      apply channel_V_dstPortsTail_app; auto.
      split;auto.
      split;auto.
      right.
      cbn. 
      do 2 eexists.
      split;eauto.
   }
   {  destruct Hportch as [Hportch Hnodupkp].
      split;auto.
      apply channel_V_srcdstkport_app;auto.
      apply channel_V_srcdstkport_app in Hportch;auto.
      destruct Hportch as [Hportch1 [Hportch Hportch2]].
      split.
      { eapply channel_V_srcdstkport_update_kport with (kport :=  (Vint32 i2
      :: Vint32 i1
         :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)).
      rewrite H55. auto. 
      cbn;auto.
      auto. }
      split;auto.
      { unfold channel_V_srcdstkport_P.
        right.
        eexists.
        split;eauto.
        unfold channel_V_srcdstkport_P in Hportch.
        destruct Hportch.
        simpljoin1. tryfalse.
        simpljoin1.
        inversion H2. subst x.
        splits;eauto.
        { eapply channel_V_src_P_update_kport;eauto.
        rewrite H55. auto.
        cbn;auto. }
        eapply channel_V_dst_P_update_kport_adddst;eauto.
        rewrite H55. auto.
        cbn;auto.
        cbn.
        do 3 eexists.
        splits;eauto.
      }
      eapply channel_V_srcdstkport_update_kport with (kport :=  (Vint32 i2
      :: Vint32 i1
         :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)).
      rewrite H55. auto. 
      cbn;auto.
      auto.
   }
   { eapply  R_Kernelport_DomainPort_init_upd_kport with (kport :=  (Vint32 i2
     :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil));eauto.
     clear - H57 H25.
     simpl in *.
     simpljoin1.
     splits;auto.
     clear - H25.
     mauto. }
   split;auto.
   Unshelve. eauto.
Qed.

Lemma portaddtochannelproof_incore_destionation_endpart2: 
forall aop P r (ct: tid) pid v' i6 i5 i4 i3 i2 i1 i i0 x0 x3 x4 x5 x6 x7 
dportlptr  dpptrl ecbls kportvl1 kp_b kportvl2 kportl1 kportl2
chanvl1  chanvl2 chanl1 chanl2 chandstportll1 chandstportll2
p_b p_i n  portchanid dstkportl_ori
(Haop: can_change_aop P)
(Heqfa: Int.eq portchanid ($ CHANNEL_NUMS) = false)
(H0: Int.ltu ($ CHANNEL_NUMS) portchanid = false)
(Hinecb: Forall (fun x : addrval => exists wt, get ecbls x = Some (absport, wt)) dpptrl)
(Hchtail: channel_V_dstPortsTail
   (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2)
   (chandstportll1 ++ dstkportl_ori :: chandstportll2))
(Hkpdm: OS_K_Port_V_dmport (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) = Some (Vptr (p_b, p_i)))
(H4: nth_error dpptrl n = Some (p_b, p_i)) 
(H22: forall (id1 id2 : nat) (p1 p2 : addrval),       id1 <> id2 ->       nth_val id1 (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) = Some (Vptr p1) ->       nth_val id2 (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) = Some (Vptr p2) -> p1 <> p2) 
(H23: length (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) = ∘ PORT_NUMS) 
(H21: array_type_vallist_match OS_K_Port ∗ (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)) 
(H24: Int.unsigned ($ Z.of_nat pid) < 64) 
(H25: Int.unsigned portchanid < 32) 
(H27: forall (id1 id2 : nat) (p1 p2 : addrval),       id1 <> id2 ->       nth_val id1 (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) = Some (Vptr p1) ->       nth_val id2 (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) = Some (Vptr p2) -> p1 <> p2) 
(H28: length (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) = ∘ CHANNEL_NUMS) 
(H26: array_type_vallist_match OS_Channel ∗ (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2)) 
(Hlenchanvl1: length chanvl1 = Z.to_nat (Int.unsigned portchanid)) 
(Hnthvalchan: nth_val' (Z.to_nat (Int.unsigned portchanid)) (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) = Vptr (v', Int.zero)) 
(H31: Int.unsigned i2 <= 255) 
(H32: Int.unsigned i1 <= 255) 
(H33: isptr x0) 
(H34: isptr Vnull) 
(H35: Int.unsigned i0 <= 255) 
(H36: Int.unsigned i <= 255) 
(H37: isptr x4) 
(H29: nth_error (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2) (length chanvl1) = Some (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil)) 
(H38: nth_error (chandstportll1 ++ dstkportl_ori :: chandstportll2) (length chanvl1) =    Some (dstkportl_ori)) 
(H45: length chanl1 = length chanvl1) 
(H46: length chandstportll1 = length chanvl1) 
(H40: Int.unsigned i6 <= 255) 
(H41: Int.unsigned i5 <= 255) 
(H42: Int.unsigned i4 <= 255) 
(H47: Int.unsigned i3 <= 255) 
(H48: isptr x3) 
(H49: isptr x5) 
(H50: isptr x6) 
(H51: isptr x7) 
(H39: Int.eq i3 ($ DEFAULT_CHANNLE_SEMAPHROE) = true) 
(H57: struct_type_vallist_match OS_K_Port (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)) 
(H55: length kportvl1 = ∘ (Int.unsigned ($ Z.of_nat pid))) 
(H56: length kportl1 = ∘ (Int.unsigned ($ Z.of_nat pid))),
{|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- ct
{{(EX (dport: vallist) (dportl : list vallist) (dportmsgll : list (list vallist)),
[|x3 = Vnull /\ dstkportl_ori = nil /\ i4 = Int.zero |] **
[| nth_error dportl n = Some dport /\  OS_Port_V_direction dport = Some (V$ DESTINATION) |] ** 
[|RLH_PortPtrINecb dportlptr dportl dpptrl ecbls|] **
[|R_Kernelport_DomainPort_init (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
    (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) dportl dpptrl|] **
[|channel_V_srcdstkport_aux (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2)
    (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: V$ 0 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2)
    (chandstportll1 ++ dstkportl_ori :: chandstportll2) (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
    (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) dportl dpptrl|] **
 <|| END None;; aop ||>  **
LV channel @ OS_Channel ∗ |-> Vptr (v', Int.zero) **
Astruct (v', Int.zero) OS_Channel (Vint32 i6 :: Vint32 i5 :: V$ 0 :: Vint32 i3 :: Vptr (kp_b, Int.zero) :: x5 :: x6 :: x7 :: nil) **
Channel_dstkport_get x3 Vnull ∘ (Int.unsigned ($ 0)) dstkportl_ori **
LV kport @ OS_K_Port ∗ |-> Vptr (kp_b, Int.zero) **
kport_V_OSEventPtr (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
  (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) dportl dpptrl **
kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
  (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) **
dmportp_sllseg dportlptr Vnull dportl dportmsgll OS_Port_V_nextPort **
   LV semaphore @ char_t |-> Vint32 i3 **
   LV channelID @ long |-> Vint32 portchanid **  
   p_local OSLInv ct init_lg **
   A_dom_lenv
    ((err, (char_t) ∗)
     :: (port_ptr, OS_Port ∗)
        :: (channelID, long)
           :: (semaphore, char_t)
              :: (resource_get_res, char_t)
                 :: (kport, OS_K_Port ∗)
                    :: (channel, OS_Channel ∗)
                       :: (re, OS_Port ∗)
                          :: (flag, long)
                             :: (srcPort, OS_Port ∗) :: nil) ** P)}}
channel ′ → dstPortsTail =ₑ kport ′;ₛ
++ channel ′ → dstPortsNum;ₛ
kport ′ → channelID =ₑ channelID ′;ₛ
kport ′ → channel =ₑ channel ′;ₛ
kport ′ → OSEventPtr =ₑ 〈 (Void) ∗ 〉 NULL;ₛ
If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE)
{CSLSEMREL (semaphore ′)}
{{EX (head : val) (dportl : list vallist) (dportmsgll : list (list vallist)),
  [|RLH_PortPtrINecb dportlptr dportl dpptrl ecbls|] **
  [|R_Kernelport_DomainPort_init (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
      (kportl1 ++ (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) dportl
      dpptrl|] **
  [|channel_V_srcdstkport_aux (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2)
      (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 (i4 +ᵢ  $ 1) :: Vint32 i3 :: head :: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil) :: chanl2)
      (chandstportll1 ++ (dstkportl_ori ++ (kp_b, Int.zero) :: nil) :: chandstportll2) (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
      (kportl1 ++ (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) dportl
      dpptrl|] **
  [|channel_V_dstPortsTail
      (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 (i4 +ᵢ  $ 1) :: Vint32 i3 :: head :: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil) :: chanl2)
      (chandstportll1 ++ (dstkportl_ori ++ (kp_b, Int.zero) :: nil) :: chandstportll2)|] **
  [| struct_type_vallist_match OS_Channel (Vint32 i6 :: Vint32 i5 :: Vint32 (i4 +ᵢ  $ 1) :: Vint32 i3 :: head :: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil) |] **
   <|| END None;; aop ||>  **
  LV channel @ OS_Channel ∗ |-> Vptr (v', Int.zero) **
  Astruct (v', Int.zero) OS_Channel
    (Vint32 i6 :: Vint32 i5 :: Vint32 (i4 +ᵢ  $ 1) :: Vint32 i3 :: head :: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil) **
  Channel_dstkport_get head Vnull ∘ (Int.unsigned (i4 +ᵢ  $ 1)) (dstkportl_ori ++ (kp_b, Int.zero) :: nil) **
  LV kport @ OS_K_Port ∗ |-> Vptr (kp_b, Int.zero) **
  kport_V_OSEventPtr (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
    (kportl1 ++ (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) dportl dpptrl **
  kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
    (kportl1 ++ (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) **
  dmportp_sllseg dportlptr Vnull dportl dportmsgll OS_Port_V_nextPort ** 
  LV semaphore @ char_t |-> Vint32 i3 **
   LV channelID @ long |-> Vint32 portchanid **  
   p_local OSLInv ct init_lg **
   A_dom_lenv
      ((err, (char_t) ∗)
      :: (port_ptr, OS_Port ∗)
         :: (channelID, long)
            :: (semaphore, char_t)
               :: (resource_get_res, char_t)
                  :: (kport, OS_K_Port ∗)
                     :: (channel, OS_Channel ∗)
                        :: (re, OS_Port ∗)
                           :: (flag, long)
                              :: (srcPort, OS_Port ∗) :: nil) ** P}}.
Proof.
   intros.
   naive pure intro. 
   rename v'0 into dport.
   rename v'1 into dportl. rename v'2 into dstkportl.
   simpljoin1. 
   (* channel ′ → dstPortsTail =ₑ kport ′;ₛ *)
   eapply seq_rule.
   hoare name lift (Astruct (v', Int.zero) OS_Channel) pre.
   hoare name lift (Alvarmapsto channel) pre.
   hoare name lift Aop pre.
   eapply assign_rule_struct_aop; 
   [intros s;split;intros Hs;exact Hs | unfold OS_Channel;simpl;eauto 
   | simpl; eauto
   | unfold id_nth; simpl; eauto
   | simpl; eauto
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | symbolic_exe_port
   | apply assign_type_match_true; simpl; auto
   | simpl; try lia
   | simpl; auto
   | li_sepauto li ].
   (* ++ channel ′ → dstPortsNum;ₛ *)
   eapply seq_rule.
   hoare name lift (Astruct (v', Int.zero) OS_Channel) pre.
   hoare name lift (Alvarmapsto channel) pre.
   hoare name lift Aop pre.
   eapply assign_rule_struct_aop; 
   [intros s;split;intros Hs;exact Hs | unfold OS_Channel;simpl;eauto 
   | simpl; eauto
   | unfold id_nth; simpl; eauto
   | simpl; eauto
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | symbolic_exe_port
   | apply assign_type_match_true; simpl; auto
   | simpl; try lia
   | simpl; auto
   | li_sepauto li ].
   { pauto. }
   (* kport ′ → channelID =ₑ channelID ′;ₛ *)
   hoare name lift kportNode_P pre.
   eapply backward_rule1.
   { eapply kportNode_P_app_frm;eauto. rewrite H55. auto. }
   naive pure intro. rename H2 into Hkptp.
   eapply seq_rule.
   hoare name lift (Astruct' (kp_b, Int.zero) OS_K_Port_Seg_dls) pre.
   hoare name lift (Alvarmapsto kport) pre.
   hoare name lift Aop pre.
   eapply assign_rule_struct_aop_typeneq with (tp1 := OS_K_Port');
   [ intros s;split;intros Hs;[
      unfold Astruct, OS_K_Port'; exact Hs | 
      unfold Astruct, OS_K_Port' in Hs; exact Hs]
   | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
   | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
   | simpl;auto
   | simpl; auto
   | unfold id_nth; simpl; auto
   | simpl; auto
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | symbolic_exe_port
   | apply assign_type_match_true; simpl; auto
   | simpl; try lia
   | simpl; auto
   | li_sepauto li ].
   (* kport ′ → channel =ₑ channel ′;ₛ *)
   eapply seq_rule.
   hoare name lift (Astruct' (kp_b, Int.zero) OS_K_Port_Seg_dls) pre.
   hoare name lift (Alvarmapsto kport) pre.
   hoare name lift Aop pre.
   eapply assign_rule_struct_aop_typeneq with (tp1 := OS_K_Port');
   [ intros s;split;intros Hs;[
      unfold Astruct, OS_K_Port'; exact Hs | 
      unfold Astruct, OS_K_Port' in Hs; exact Hs]
   | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
   | (match goal with |- ?tp = Tstruct _ _ => try unfold tp end); auto
   | simpl;auto
   | simpl; auto
   | unfold id_nth; simpl; auto
   | simpl; auto
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | intros; intro; tryfalse
   | symbolic_exe_port
   | apply assign_type_match_true; simpl; auto
   | simpl; try lia
   | simpl; auto
   | li_sepauto li ].
   (* merge kportNode_P *)
   change ((Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i :: nil)) 
   with (firstn 6 (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i ::x4:: nil)).   
   eapply backward_rule1.
   { unfold Astruct at 1. unfold OS_K_Port'. intros s Hs. kport_combine kportvl1 kportvl2. 
     rewrite H55. auto.
     clear - H57 H25.
     cbn in *.
     simpljoin1.
     splits;auto.  
     clear - H25. 
     assert (Int.unsigned portchanid <= 255) by lia.
     pauto. }
   (* kport ′ → OSEventPtr =ₑ 〈 (Void) ∗ 〉 NULL;ₛ *)
   hoare name lift kport_V_OSEventPtr pre.
   eapply backward_rule1.
   {  eapply kport_V_OSEventPtr_app_frm;eauto. rewrite H55. auto. }
   cbn [kport_V_OSEventPtr].
   hoare lift 2%nat pre.
   eapply backward_rule1.
   {  intros s Hs.
      eapply disj_star_elim_disj  in Hs.
      destruct Hs as [Hs  | Hs].
      2:{  exact Hs. } 
      exfalso.
      unfold OS_K_Port_V_channel in Hs.
      sep normal in Hs.
      sep destruct Hs.
      sep split  in Hs.
      destruct H7 as [? H7].
      cbn in H7.
      inversion H7. }
   naive pure intro.
   clear H2.
   (* kport ′ → OSEventPtr =ₑ 〈 (Void) ∗ 〉 NULL;ₛ *)
   eapply seq_rule.
   hoare name lift (Alvarmapsto kport) pre.
   hoare name lift Aop pre.
   eapply assign_rule_struct_member with (tp1 := OS_K_Port) (t' := (Void) ∗);
   [ | intro s;split;intros Hs;exact Hs | 
      unfold OS_K_Port;reflexivity | cbn;auto | cbn;auto 
      |  |  | symbolic_execution |  intros s Hs;sep auto|  idtac .. ].
   cbn;auto.  cbn;auto. apply eq_vptr. eauto.
   (* If (semaphore ′ !=ₑ ′ DEFAULT_CHANNLE_SEMAPHROE) {CSLSEMREL (semaphore ′)} *)
   hoare normal pre.
   hoare name lift Aop pre.
   eapply forward_rule2.
   hoare forward.
   { pauto. }
   { pauto. }
   { pauto. }
   naive pure intro.
   instantiate (1:= Afalse).
   rewrite H39 in H2. destruct H2 as [? _]. exfalso. clear - H2. mauto.
   intros s Hs.
   destruct Hs as [Hs | Hs].
   { sep normal in Hs. sep split in Hs. tryfalse.  }
   sep normal in Hs.
   sep normal. sep eexists.
   sep autocancel.
   sep split.
   { sep name lift kport_V_OSEventPtr.
   eapply kport_V_OSEventPtr_app_frm. rewrite H55. auto.
   cbn [kport_V_OSEventPtr].
   sep autocancel.
   eapply disj_split.
   left.
   sep normal.
   exists n (p_b, p_i) dport.
   sep split;[ | cbn;eauto .. ].
   eapply disj_split.
   right.
   sep split;auto.
   sep auto.
   assert (∘ (Int.unsigned ($ 0)) = O).
   {  unfold nat_of_Z.
     clear. mauto.  
   }
   assert (∘ (Int.unsigned (Int.zero +ᵢ  $ 1)) = S O).
   { rewrite Int_add_one_Sn. unfold nat_of_Z. clear. mauto.
     lia.
   }
   rewrite H8. rewrite H7 in Hs.
   rewrite app_nil_l.
   cbn [Channel_dstkport_get] in *.
   sep normal.
   exists  (Vint32 i2
   :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero) :: Vint32 i0 :: Vint32 i :: Vnull :: nil).
   exists Vnull.
   sep auto.
   { clear - H57 H25.
   simpl in *.
   simpljoin1.
   splits;auto.
   clear - H25.
   mauto. }  }
   {  pauto. }
   {  clear  s Hs.
      assert (length chanl1 = length chandstportll1). 
      { rewrite H46. auto. }
      apply channel_V_dstPortsTail_app in Hchtail as [Hchtail1  [? Hchtail2]];auto.
      apply channel_V_dstPortsTail_app; auto.
      split;auto.
      split;auto.
      right.
      cbn.
      do 2 eexists.
      split;eauto.
      instantiate (1:= nil).
      simpl. auto.
   }
   {  destruct H5 as [Hportch Hnodupkp].
      split;auto.
      apply channel_V_srcdstkport_app;auto.
      apply channel_V_srcdstkport_app in Hportch;auto.
      destruct Hportch as [Hportch1 [Hportch Hportch2]].
      split.
      { eapply channel_V_srcdstkport_update_kport with (kport :=  (Vint32 i2
      :: Vint32 i1
         :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)).
      rewrite H55. auto. 
      cbn;auto.
      auto. }
      split;auto.
      { unfold channel_V_srcdstkport_P.
        right.
        eexists.
        split;eauto.
        unfold channel_V_srcdstkport_P in Hportch.
        destruct Hportch.
        simpljoin1. tryfalse.
        simpljoin1.
        inversion H2. subst x.
        splits;eauto.
        { eapply channel_V_src_P_update_kport;eauto.
        rewrite H55. auto.
        cbn;auto. }
        eapply channel_V_dst_P_update_kport_adddst;eauto.
        rewrite H55. auto.
        cbn;auto.
        cbn.
        do 3 eexists.
        splits;eauto.
      }
      eapply channel_V_srcdstkport_update_kport with (kport :=  (Vint32 i2
      :: Vint32 i1
         :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)).
      rewrite H55. auto. 
      cbn;auto.
      auto.
   }
   { eapply  R_Kernelport_DomainPort_init_upd_kport with (kport :=  (Vint32 i2
     :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil));eauto.
     clear - H57 H25.
     simpl in *.
     simpljoin1.
     splits;auto.
     clear - H25.
     mauto. }
   auto.
   Unshelve. eauto.
Qed. 

Lemma portaddtochannelproof_incore_destionation:
forall P
(ct: tid) (err_l: addrval) (Herrtp: isptr (Vptr err_l)) 
(p_b: block) (p_i: int32) (H2: isptr (Vptr (p_b, p_i))) 
(sem_v res_v kp_lv chan_lv re_v srcp_v: val) (aop: spec_code) (ier: ier) (err_v curdomain: int32) 
(domainv: addrval) (domainvl: list val) (vsem: val) 
(Hcurd: Int.eq Int.zero curdomain = true \/ Int.lt Int.zero curdomain = true /\ Int.lt curdomain ($ 8) = true) 
(* (H3: struct_type_vallist_match OSdomain_t domainvl)  *)
(portchanid: int32) (Heqfa: Int.eq portchanid ($ CHANNEL_NUMS) = false) 
(H0: Int.ltu ($ CHANNEL_NUMS) portchanid = false) 
(p1 p2: val) (tcbl1: list vallist) (tcbcur: vallist) (tcbl2: list vallist) (rtbl: vallist) (tcbls: TcbMod.map) (ecbls: EcbMod.map) 
(vhold: addrval) (scapl mcapl qcapl: list vallist) (dportlptr: val) (dportl1: list vallist) (dport: vallist) (dportl2: list vallist) (dportmsgll1: list (list vallist)) (msgl: list vallist) (dportmsgll2: list (list vallist)) (dpptrl otherppl: list addrval) (otherpl: list vallist) (othermsgll: list (list vallist)) (kportfptr: val) (kportfl: list vallist) (chanfptr: val) (chanfl: list vallist) (dportls1: DomainPortMod.map) (pcn: port_coreNum) (pd: port_domain) (pid: port_id) (next: option addrval) (pst: port_status) (pintick: port_intick) (poutick: port_outick) (pt: Portt) (portattrv: addrval) (portattrvl: list val) (Hattrporid: OS_Port_V_portID dport = Some (V$ Z.of_nat pid)) 
(* (Hattrvl_type: struct_type_vallist_match OSport_attr_t portattrvl)  *)
(H: RL_PortPtrList dportlptr (dportl1 ++ dport :: dportl2) dpptrl) 
(Hinecb: Forall (fun x : addrval => exists wt, get ecbls x = Some (absport, wt)) dpptrl) 
(kp_b: block) (kportvl1 kportvl2: vallist) (Hntnkpvl: nth_error (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) ∘ (Int.unsigned ($ Z.of_nat pid)) = Some (Vptr (kp_b, Int.zero))) 
(x0 x4: val) (i i0 i1 i2: int32) (kportl1 kportl2: list vallist) (Hnthkpl: nth_error (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2)             ∘ (Int.unsigned ($ Z.of_nat pid)) = Some (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)) 
(H1: R_Kernelport_DomainPort_init (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)        (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2)        (dportl1 ++ dport :: dportl2) dpptrl) 
(H4: nth_error dpptrl (length dportl1) = Some (p_b, p_i)) 
(H5: length dportmsgll1 = length dportl1) 
(H6: DomainportNode_P dport (pcn, pd, pid, DestinationP next, pst, pintick, poutick, pt) msgl) 
(H7: get dportls1 (p_b, p_i) = Some (pcn, pd, pid, DestinationP next, pst, pintick, poutick, pt)) 
(chanl1 chanl2: list vallist) (chandstportll1 chandstportll2: list (list addrval)) (v'8: list addrval) (x3 x5 x6 x7: val) (i3 i4 i5 i6: int32) 
(Hchtail: channel_V_dstPortsTail (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2)             (chandstportll1 ++ v'8 :: chandstportll2)) 
(v': block) (Hvsem: forall (chanp : addrval) (chann : vallist) (sem : int32),         Some (Vptr (v', Int.zero)) = Some (Vptr chanp) ->         nth_error (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2)           (Z.to_nat (Int.unsigned portchanid)) = Some chann -> OS_Channel_V_semaphore chann = Some (Vint32 sem) -> vsem = Vint32 sem) 
(chanvl1 chanvl2: list val) (Hportch: channel_V_srcdstkport_aux (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2)             (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2)             (chandstportll1 ++ v'8 :: chandstportll2) (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)             (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2)             (dportl1 ++ dport :: dportl2) dpptrl) 
(Hqueuechan: forall (chanp : addrval) (chann : vallist) (dstkportl : list addrval),              
               Some (Vptr (v', Int.zero)) = Some (Vptr chanp) ->              
               nth_error (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2)        
                        (Z.to_nat (Int.unsigned portchanid)) = Some chann ->              
               nth_error (chandstportll1 ++ v'8 :: chandstportll2) (Z.to_nat (Int.unsigned portchanid)) = Some dstkportl ->                                         
               OS_Port_V_direction dport = Some (V$ DESTINATION) ->              
               (forall (dstnum : int32), OS_Channel_V_dstPortsNum chann = Some (Vint32 dstnum) ->  Int.unsigned dstnum <= 254) /\              
               (OS_Port_V_mode dport = Some (V$ QUEUE) -> OS_Port_V_OSQEntries dport = Some (V$ 0) /\              
               channel_V_src_P' chann dstkportl (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)  
               (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2)  
                (dportl1 ++ dport :: dportl2) dpptrl QUEUE)) 
(pri: priority) (st: taskstatus) (msg: msg) (sus: susstatus) (H8: get tcbls ct = Some (pri, st, msg, sus)) 
(p_nextv: val) (pptr: addrval) (H10: OS_Port_V_nextPort dport = Some p_nextv) 
(H11: struct_type_vallist_match' OS_Port_Seg_dls dport) 
(H12: OS_Port_V_OSQStart dport = Some (Vptr pptr)) 
(pavl: int32) (en: nth_val 0 portattrvl = Some (Vint32 pavl)) (H9: Int.eq Int.zero pavl = false) 
(parid dmvl: int32) (H13: nth_val 1 portattrvl = Some (Vint32 parid)) 
(H14: nth_val 1 domainvl = Some (Vint32 dmvl)) 
(H15: Int.eq parid dmvl = true) 
(H16: nth_val 5 portattrvl = Some (Vint32 portchanid)) 
(H17: Int.eq portchanid portchanid = true) 
(Hporid: OS_Port_V_portID dport = Some (V$ Z.of_nat pid)) 
(Hkpcn: OS_K_Port_V_coreNum (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) = OS_Port_V_coreNum dport) 
(Hkpdm: OS_K_Port_V_dmport (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) = Some (Vptr (p_b, p_i))) 
(Hkpid: OS_K_Port_V_portID (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) = Some (V$ Z.of_nat pid)) 
(H19: forall (id1 id2 : nat) (p1 p2 : addrval),       id1 <> id2 ->       nth_val id1 (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) = Some (Vptr p1) ->       nth_val id2 (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) = Some (Vptr p2) -> p1 <> p2) 
(H20: length (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) = ∘ PORT_NUMS) 
(H18: array_type_vallist_match OS_K_Port ∗ (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)) 
(H21: Int.unsigned ($ Z.of_nat pid) < 64) 
(H22: Int.unsigned portchanid < 32) 
(H24: forall (id1 id2 : nat) (p1 p2 : addrval),       id1 <> id2 ->       nth_val id1 (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) = Some (Vptr p1) ->       nth_val id2 (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) = Some (Vptr p2) -> p1 <> p2) 
(H25: length (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) = ∘ CHANNEL_NUMS) 
(H23: array_type_vallist_match OS_Channel ∗ (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2)) 
(Hlenchanvl1: length chanvl1 = Z.to_nat (Int.unsigned portchanid)) 
(Hnthvalchan: nth_val' (Z.to_nat (Int.unsigned portchanid)) (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) = Vptr (v', Int.zero)) 
(H28: Int.unsigned i2 <= 255) 
(H29: Int.unsigned i1 <= 255) 
(H30: isptr x0) 
(H31: isptr Vnull) 
(H32: Int.unsigned i0 <= 255) 
(H33: Int.unsigned i <= 255) 
(H34: isptr x4) 
(H26: nth_error (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2) (length chanvl1) =       Some (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil)) 
(H35: nth_error (chandstportll1 ++ v'8 :: chandstportll2) (length chanvl1) = Some v'8) 
(H42: length chanl1 = length chanvl1) 
(H43: length chandstportll1 = length chanvl1) 
(H36: Int.unsigned i6 <= 255) 
(H37: Int.unsigned i5 <= 255) 
(H38: Int.unsigned i4 <= 255) 
(Hi4le: Int.unsigned i4 <= 254)
(H39: Int.unsigned i3 <= 255) 
(H44: isptr x3) 
(H45: isptr x5) 
(H46: isptr x6) 
(H47: isptr x7) 
(H48: Int.eq i3 ($ DEFAULT_CHANNLE_SEMAPHROE) = true) 
(H54: struct_type_vallist_match OS_K_Port (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)) 
(H52: length kportvl1 = ∘ (Int.unsigned ($ Z.of_nat pid))) 
(H53: length kportl1 = ∘ (Int.unsigned ($ Z.of_nat pid))) 
(HeqP: P = 
GAarray OSChannelIDTbl (Tarray OS_Channel ∗ ∘ CHANNEL_NUMS)
(chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) **
GAarray OSKernelPortIDTbl (Tarray OS_K_Port ∗ ∘ PORT_NUMS)
(kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) **
GV ksCurDomain @ long |-> Vint32 curdomain **
GV ksDomains @ OSdomain_t ∗ |-> Vptr domainv **
Astruct (get_off_addr domainv (Int.mul ($ 34) curdomain)) OSdomain_t domainvl **
GV OSPortAttrTbl @ OSport_attr_t ∗ |-> Vptr portattrv **
Astruct (get_off_addr portattrv (Int.mul ($ 12) ($ Z.of_nat pid))) OSport_attr_t portattrvl **
LV flag @ long |-> (V$ 1) **
AOSKernelPortFreeList kportfptr kportfl **
AOSChannelFreeList chanfptr chanfl **
OtherPortPtrList otherppl otherpl othermsgll **
EvtInv ecbls p1 (tcbl1 ++ tcbcur :: tcbl2) tcbls vhold scapl mcapl qcapl **
AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls)
, {|OS_spec, GetHPrio, OSLInv, I, (fun v : option val =>
((EX v0 : val, LV err @ (char_t) ∗ |-> v0) **
 (EX v0 : val, LV port_ptr @ OS_Port ∗ |-> v0) **
 (EX v0 : val, LV channelID @ long |-> v0) **
 (EX v0 : val, LV semaphore @ char_t |-> v0) **
 (EX v0 : val, LV resource_get_res @ char_t |-> v0) **
 (EX v0 : val, LV kport @ OS_K_Port ∗ |-> v0) **
 (EX v0 : val, LV channel @ OS_Channel ∗ |-> v0) **
 (EX v0 : val, LV re @ OS_Port ∗ |-> v0) **
 (EX v0 : val, LV flag @ long |-> v0) **
 (EX v0 : val, LV srcPort @ OS_Port ∗ |-> v0) ** Aemp) **
OSPortAddToChannelPost' (rev (Vptr err_l :: (Vptr (p_b,p_i)) :: Vint32 portchanid :: nil)) v 
(logic_val (Vint32 curdomain) :: logic_val (Vptr domainv) :: logic_lv domainvl :: logic_code aop :: logic_ier ier  :: logic_val (V$ Z.of_nat pid) :: logic_val (Vptr portattrv) :: logic_lv portattrvl :: logic_val p1 :: logic_val p2:: logic_llv tcbl1 :: logic_lv tcbcur :: logic_llv tcbl2
  :: logic_lv rtbl :: logic_abstcb tcbls :: logic_absecb ecbls :: logic_val (Vptr vhold)  :: logic_llv scapl :: logic_llv mcapl :: logic_llv qcapl
  :: logic_val dportlptr
  :: logic_llv dportl1 :: logic_lv dport  :: logic_llv dportl2  :: logic_la dpptrl :: logic_lllv dportmsgll1  :: logic_llv msgl
  :: logic_lllv dportmsgll2 :: logic_la otherppl  :: logic_lv (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
  :: logic_llv (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2)  :: logic_lv  (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) 
  :: logic_llv (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2)
  :: logic_lla (chandstportll1 ++  v'8 :: chandstportll2)  :: nil) ct **
A_dom_lenv
  ((err, (char_t) ∗)
   :: (port_ptr, OS_Port ∗)
      :: (channelID, long)
         :: (semaphore, char_t)
            :: (resource_get_res, char_t)
               :: (kport, OS_K_Port ∗)
                  :: (channel, OS_Channel ∗)
                     :: (re, OS_Port ∗) :: (flag, long) :: (srcPort, OS_Port ∗) :: nil)) , Afalse|}
|- ct
{{ <||  END None;; aop ||>  **
   Astruct' (kp_b, Int.zero) OS_K_Port_Seg_dls
   (firstn 6 (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)) **
   Astruct (v', Int.zero) OS_Channel (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) **
   LV kport @ OS_K_Port ∗ |-> Vptr (kp_b, Int.zero) **
   kportNode_P kportvl1 kportl1 **
   kportNode_P kportvl2 kportl2 **
   LV resource_get_res @ char_t |-> res_v **
   LV semaphore @ char_t |-> Vint32 i3 **
   ChannelNode chanvl1 chanl1 chandstportll1 **
   ChannelNode chanvl2 chanl2 chandstportll2 **
   Channel_dstkport_get x3 Vnull ∘ (Int.unsigned i4) v'8 **
   LV channel @ OS_Channel ∗ |-> Vptr (v', Int.zero) **
   APortStruct (p_b, p_i) dport **
   ([|OS_Port_V_mode dport = Some (Vint32 (ZToInt SAMPLE))|] ** dmportp_sllseg_sampleport_msg pptr msgl \\//
   (EX (qend qin qout : addrval) (qsize qentries : int32) (vl2 : list vallist),
   [|OS_Port_V_mode dport = Some (Vint32 (ZToInt QUEUE))|] **
   [|OS_Port_V_OSQEnd dport = Some (Vptr qend)|] **
   [|OS_Port_V_OSQIn dport = Some (Vptr qin)|] **
   [|OS_Port_V_OSQOut dport = Some (Vptr qout)|] **
   [|OS_Port_V_OSQSize dport = Some (Vint32 qsize) /\ Int.unsigned qsize <= 65535|] **
   [|OS_Port_V_OSQEntries dport = Some (Vint32 qentries) /\ Int.unsigned qentries <= Int.unsigned qsize|] **
   [|Qport_msg_ptrs_P pptr qend qout qin (Int.unsigned qsize)|] **
   dmportp_sllseg_qport_msg qout qin pptr qend ∘ (Int.unsigned qentries) msgl **
   dmportp_sllseg_qport_msg qin qout pptr qend ∘ (Int.unsigned qsize - Int.unsigned qentries) vl2)) **
   dmportp_sllseg p_nextv Vnull dportl2 dportmsgll2 OS_Port_V_nextPort **
   dmportp_sllseg dportlptr (Vptr (p_b, p_i)) dportl1 dportmsgll1 OS_Port_V_nextPort **
   GV OSDomainPortPtrList @ OS_Port ∗ |-> dportlptr **
   kport_V_OSEventPtr (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
   (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) (dportl1 ++ dport :: dportl2) dpptrl **
  LV re @ OS_Port ∗ |-> Vnull **
  GV OSRunning @ char_t |-> Vint32 Int.zero **
  PV err_l @ char_t |-> Vint32 err_v **
  LV srcPort @ OS_Port ∗ |-> srcp_v **
  LV err @ (char_t) ∗ |-> Vptr err_l **
  LV port_ptr @ OS_Port ∗ |-> Vptr (p_b, p_i) **
  LV channelID @ long |-> Vint32 portchanid ** 
  p_local OSLInv ct init_lg **
  A_dom_lenv
  ((err, (char_t) ∗)
   :: (port_ptr, OS_Port ∗)
      :: (channelID, long)
         :: (semaphore, char_t)
            :: (resource_get_res, char_t)
               :: (kport, OS_K_Port ∗)
                  :: (channel, OS_Channel ∗)
                     :: (re, OS_Port ∗) :: (flag, long) :: (srcPort, OS_Port ∗) :: nil) ** 
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  Aisr empisr **
  A_isr_is_prop **
  Aier ier ** P}} 
                     (sif
                     (ebinop oeq
                        (efield (ederef (evar port_ptr))
                           os_code_defs.direction)
                        (econst32 (Int.repr DESTINATION)))
                     (sseq
                        (sif
                           (eunop oppsite
                              (ebinop oeq
                                 (efield (ederef (evar channel))
                                    dstPortsNum) (econst32 (Int.repr Z0))))
                           (sseq
                              (sifthen
                                 (ebinop oand
                                    (ebinop oeq (evar semaphore)
                                       (econst32
                                          (Int.repr
                                             DEFAULT_CHANNLE_SEMAPHROE)))
                                    (eunop oppsite
                                       (ebinop oeq
                                          (efield (ederef (evar channel))
                                             srcPort)
                                          (ecast enull (Tptr OS_K_Port)))))
                                 (sifthen
                                    (eunop oppsite
                                       (ebinop oeq
                                          (efield
                                             (ederef
                                                (efield
                                                   (ederef (evar channel))
                                                   srcPort)) coreNum)
                                          (efield (ederef (evar kport))
                                             coreNum)))
                                    (sseq
                                       (sassign (ederef (evar err))
                                          (ecast
                                             (econst32
                                                (Int.repr
                                                   OS_PORT_ERR_MULTICORE))
                                             Tint8)) (srete (evar re)))))
                              (sseq
                                 (sifthen
                                    (ebinop oand
                                       (ebinop oeq (evar semaphore)
                                          (econst32
                                             (Int.repr
                                                DEFAULT_CHANNLE_SEMAPHROE)))
                                       (eunop oppsite
                                          (ebinop oeq
                                             (efield
                                                (ederef (evar channel))
                                                dstPortsHead)
                                             (ecast enull (Tptr OS_K_Port)))))
                                    (sifthen
                                       (eunop oppsite
                                          (ebinop oeq
                                             (efield
                                                (ederef
                                                   (efield
                                                      (ederef
                                                      (evar channel))
                                                      dstPortsHead))
                                                coreNum)
                                             (efield (ederef (evar kport))
                                                coreNum)))
                                       (sseq
                                          (sassign (ederef (evar err))
                                             (ecast
                                                (econst32
                                                   (Int.repr
                                                      OS_PORT_ERR_MULTICORE))
                                                Tint8)) 
                                          (srete (evar re)))))
                                 (sassign
                                    (efield
                                       (ederef
                                          (efield (ederef (evar channel))
                                             dstPortsTail)) OSEventPtr)
                                    (ecast (evar kport) (Tptr Tvoid)))))
                           (sseq
                              (sifthen
                                 (ebinop oand
                                    (ebinop oeq (evar semaphore)
                                       (econst32
                                          (Int.repr
                                             DEFAULT_CHANNLE_SEMAPHROE)))
                                    (eunop oppsite
                                       (ebinop oeq
                                          (efield (ederef (evar channel))
                                             srcPort)
                                          (ecast enull (Tptr OS_K_Port)))))
                                 (sifthen
                                    (eunop oppsite
                                       (ebinop oeq
                                          (efield
                                             (ederef
                                                (efield
                                                   (ederef (evar channel))
                                                   srcPort)) coreNum)
                                          (efield (ederef (evar kport))
                                             coreNum)))
                                    (sseq
                                       (sassign (ederef (evar err))
                                          (ecast
                                             (econst32
                                                (Int.repr
                                                   OS_PORT_ERR_MULTICORE))
                                             Tint8)) (srete (evar re)))))
                              (sseq
                                 (sassign
                                    (efield (ederef (evar channel))
                                       dstPortsHead) (evar kport))
                                 (sifthen
                                    (ebinop oand
                                       (ebinop oeq
                                          (efield (ederef (evar port_ptr))
                                             mode)
                                          (econst32 (Int.repr QUEUE)))
                                       (eunop oppsite
                                          (ebinop oeq
                                             (efield
                                                (ederef (evar channel))
                                                srcPort)
                                             (ecast enull (Tptr OS_K_Port)))))
                                    (sifthen
                                       (eunop oppsite
                                          (ebinop oeq
                                             (efield
                                                (ederef
                                                   (efield
                                                      (ederef
                                                      (evar channel))
                                                      srcPort)) dmport)
                                             (ecast enull (Tptr OS_Port))))
                                       (sseq
                                          (sassign (evar srcPort)
                                             (efield
                                                (ederef
                                                   (efield
                                                      (ederef
                                                      (evar channel))
                                                      srcPort)) dmport))
                                          (sseq
                                             (swhile
                                                (ebinop olt
                                                   (efield
                                                      (ederef
                                                      (evar port_ptr))
                                                      OSQSize)
                                                   (efield
                                                      (ederef
                                                      (evar srcPort))
                                                      OSQEntries))
                                                (sseq
                                                   (sassign
                                                      (efield
                                                      (ederef
                                                      (evar srcPort))
                                                      OSQOut)
                                                      (ebinop oplus
                                                      (efield
                                                      (ederef
                                                      (evar srcPort))
                                                      OSQOut)
                                                      (econst32
                                                      (Int.repr (Zpos xH)))))
                                                   (sseq
                                                      (sassign
                                                      (efield
                                                      (ederef
                                                      (evar srcPort))
                                                      OSQEntries)
                                                      (ebinop ominus
                                                      (efield
                                                      (ederef
                                                      (evar srcPort))
                                                      OSQEntries)
                                                      (ecast
                                                      (econst32
                                                      (Int.repr (Zpos xH)))
                                                      Tint16)))
                                                      (sifthen
                                                      (ebinop oeq
                                                      (efield
                                                      (ederef
                                                      (evar srcPort))
                                                      OSQOut)
                                                      (efield
                                                      (ederef
                                                      (evar srcPort))
                                                      OSQEnd))
                                                      (sassign
                                                      (efield
                                                      (ederef
                                                      (evar srcPort))
                                                      OSQOut)
                                                      (efield
                                                      (ederef
                                                      (evar srcPort))
                                                      OSQStart))))))
                                             (swhile
                                                (ebinop olt
                                                   (econst32 (Int.repr Z0))
                                                   (efield
                                                      (ederef
                                                      (evar srcPort))
                                                      OSQEntries))
                                                (sseq
                                                   (sassign
                                                      (efield
                                                      (ederef
                                                      (efield
                                                      (ederef
                                                      (evar port_ptr))
                                                      OSQIn)) len)
                                                      (efield
                                                      (ederef
                                                      (efield
                                                      (ederef
                                                      (evar srcPort))
                                                      OSQOut)) len))
                                                   (sseq
                                                      (scall memcpy
                                                      (@cons expr
                                                      (eaddrof
                                                      (earrayelem
                                                      (efield
                                                      (ederef
                                                      (efield
                                                      (ederef
                                                      (evar port_ptr))
                                                      OSQIn)) data)
                                                      (econst32
                                                      (Int.repr Z0))))
                                                      (@cons expr
                                                      (eaddrof
                                                      (earrayelem
                                                      (efield
                                                      (ederef
                                                      (efield
                                                      (ederef
                                                      (evar srcPort))
                                                      OSQOut)) data)
                                                      (econst32
                                                      (Int.repr Z0))))
                                                      (@cons expr
                                                      (ecast
                                                      (efield
                                                      (ederef
                                                      (efield
                                                      (ederef
                                                      (evar srcPort))
                                                      OSQOut)) len) Tint32)
                                                      (@nil expr)))))
                                                      (sseq
                                                      (sassign
                                                      (efield
                                                      (ederef
                                                      (evar port_ptr))
                                                      OSQIn)
                                                      (ebinop oplus
                                                      (efield
                                                      (ederef
                                                      (evar port_ptr))
                                                      OSQIn)
                                                      (econst32
                                                      (Int.repr (Zpos xH)))))
                                                      (sseq
                                                      (sassign
                                                      (efield
                                                      (ederef
                                                      (evar port_ptr))
                                                      OSQEntries)
                                                      (ebinop oplus
                                                      (efield
                                                      (ederef
                                                      (evar port_ptr))
                                                      OSQEntries)
                                                      (econst32
                                                      (Int.repr (Zpos xH)))))
                                                      (sseq
                                                      (sifthen
                                                      (ebinop oeq
                                                      (efield
                                                      (ederef
                                                      (evar port_ptr))
                                                      OSQIn)
                                                      (efield
                                                      (ederef
                                                      (evar port_ptr))
                                                      OSQEnd))
                                                      (sassign
                                                      (efield
                                                      (ederef
                                                      (evar port_ptr))
                                                      OSQIn)
                                                      (efield
                                                      (ederef
                                                      (evar port_ptr))
                                                      OSQStart)))
                                                      (sseq
                                                      (sassign
                                                      (efield
                                                      (ederef
                                                      (evar srcPort))
                                                      OSQOut)
                                                      (ebinop oplus
                                                      (efield
                                                      (ederef
                                                      (evar srcPort))
                                                      OSQOut)
                                                      (econst32
                                                      (Int.repr (Zpos xH)))))
                        (sseq
                            (sassign (efield  (ederef (evar srcPort))  OSQEntries) (ebinop ominus (efield (ederef  (evar srcPort))  OSQEntries)  (ecast  (econst32 (Int.repr (Zpos xH)))  Tint16)))
                        (sifthen  (ebinop oeq (efield (ederef  (evar srcPort)) OSQOut)(efield (ederef (evar srcPort)) OSQEnd))
                        (sassign  (efield (ederef (evar srcPort))  OSQOut) (efield  (ederef (evar srcPort)) OSQStart))))))))))))))))))
                        (sseq
                           (sassign
                              (efield (ederef (evar channel)) dstPortsTail)
                              (evar kport))
                           (sseq
                              (sassign
                                 (efield (ederef (evar channel))
                                    dstPortsNum)
                                 (ebinop oplus
                                    (efield (ederef (evar channel))
                                       dstPortsNum)
                                    (econst32 (Int.repr (Zpos xH)))))
                              (sseq
                                 (sassign
                                    (efield (ederef (evar kport)) channelID)
                                    (evar channelID))
                                 (sseq
                                    (sassign
                                       (efield (ederef (evar kport))
                                          channel) (evar channel))
                                    (sseq
                                       (sassign
                                          (efield (ederef (evar kport))
                                             OSEventPtr)
                                          (ecast enull (Tptr Tvoid)))
                                       (sifthen
                                          (eunop oppsite
                                             (ebinop oeq 
                                                (evar semaphore)
                                                (econst32
                                                   (Int.repr
                                                      DEFAULT_CHANNLE_SEMAPHROE))))
                                          (sprim
                                             (scsl_semrel (evar semaphore))))))))))
                     (sseq
                        (sifthen
                           (eunop oppsite
                              (ebinop oeq (evar semaphore)
                                 (econst32
                                    (Int.repr DEFAULT_CHANNLE_SEMAPHROE))))
                           (sprim (scsl_semrel (evar semaphore))))
                        (sseq
                           (sassign (ederef (evar err))
                              (ecast (econst32 (Int.repr OS_PORT_ERR_TYPE))
                                 Tint8)) (srete (evar re)))))
{{ EX (head srcpv : val) (dportl : list vallist)
(dportmsgll : list (list vallist)),
[|RLH_PortPtrINecb dportlptr dportl dpptrl ecbls|] **
[|R_Kernelport_DomainPort_init
    (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
    (kportl1 ++
     (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero)  :: Vint32 i0 :: Vint32 i :: x4 :: nil)
     :: kportl2) dportl dpptrl|] **
[|channel_V_srcdstkport_aux (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2)
    (chanl1 ++
    (Vint32 i6 :: Vint32 i5 :: Vint32 (i4 +ᵢ  $ 1) :: Vint32 i3 :: head :: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil)
     :: chanl2)
    (chandstportll1 ++
     (v'8 ++ (kp_b, Int.zero) :: nil) :: chandstportll2)
    (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
    (kportl1 ++ (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero)  :: Vint32 i0 :: Vint32 i :: x4 :: nil)
     :: kportl2) dportl dpptrl|] **
[|channel_V_dstPortsTail
            (chanl1 ++
             (Vint32 i6 :: Vint32 i5 :: Vint32 (i4 +ᵢ  $ 1) :: Vint32 i3 :: head :: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil)
             :: chanl2) (chandstportll1 ++ (v'8 ++ (kp_b, Int.zero) :: nil) :: chandstportll2)|] **
[| struct_type_vallist_match OS_Channel 
(Vint32 i6 :: Vint32 i5 :: Vint32 (i4 +ᵢ  $ 1) :: Vint32 i3 :: head :: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil) |] **
 <|| END None;; aop ||>  **
LV channel @ OS_Channel ∗ |-> Vptr (v', Int.zero) **
Astruct (v', Int.zero) OS_Channel
  (Vint32 i6
   :: Vint32 i5
      :: Vint32 (i4 +ᵢ  $ 1) :: Vint32 i3 :: head :: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil) **
Channel_dstkport_get head Vnull ∘ (Int.unsigned (i4 +ᵢ  $ 1))
  (v'8 ++ (kp_b, Int.zero) :: nil) **
LV kport @ OS_K_Port ∗ |-> Vptr (kp_b, Int.zero) **
kport_V_OSEventPtr (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
  (kportl1 ++ (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero)  :: Vint32 i0 :: Vint32 i :: x4 :: nil)
   :: kportl2) dportl dpptrl **
kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
  (kportl1 ++  (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero)  :: Vint32 i0 :: Vint32 i :: x4 :: nil)
   :: kportl2) **
dmportp_sllseg dportlptr Vnull dportl dportmsgll OS_Port_V_nextPort **
LV srcPort @ OS_Port ∗ |-> srcpv **
LV port_ptr @ OS_Port ∗ |-> Vptr (p_b, p_i) **
LV resource_get_res @ char_t |-> res_v **
LV semaphore @ char_t |-> Vint32 i3 **
ChannelNode chanvl1 chanl1 chandstportll1 **
ChannelNode chanvl2 chanl2 chandstportll2 **
GV OSDomainPortPtrList @ OS_Port ∗ |-> dportlptr **
LV re @ OS_Port ∗ |-> Vnull **
GV OSRunning @ char_t |-> Vint32 Int.zero **
PV err_l @ char_t |-> Vint32 err_v **
LV err @ (char_t) ∗ |-> Vptr err_l **
LV channelID @ long |-> Vint32 portchanid **
p_local OSLInv ct init_lg **
A_dom_lenv
  ((err, (char_t) ∗)
   :: (port_ptr, OS_Port ∗)
      :: (channelID, long)
         :: (semaphore, char_t)
            :: (resource_get_res, char_t)
               :: (kport, OS_K_Port ∗)
                  :: (channel, OS_Channel ∗)
                     :: (re, OS_Port ∗)
                        :: (flag, long)
                           :: (srcPort, OS_Port ∗) :: nil) **
Aie false **
Ais nil **
Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier ier ** P }}.
Proof.
   intros.
   eapply forward_rule2.
   (* IF (port_ptr ′ → os_code_defs.direction ==ₑ ′ DESTINATION) *)
   hoare name lift (Alvarmapsto port_ptr) pre.
   hoare name lift Aop pre.
   eapply if_rule2';[ subst;symbolic_exe_port | | ].
   2:{ instantiate (1:= Afalse).
      pure intro.
      exfalso.
      clear - H3. unfold DESTINATION in H3. mauto. }
   2: {  instantiate (1:= EX (head srcpv : val) (dportl : list vallist)
   (dportmsgll : list (list vallist)),
   [|RLH_PortPtrINecb dportlptr dportl dpptrl ecbls|] **
   [|R_Kernelport_DomainPort_init
       (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
       (kportl1 ++
        (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero)  :: Vint32 i0 :: Vint32 i :: x4 :: nil)
        :: kportl2) dportl dpptrl|] **
   [|channel_V_srcdstkport_aux (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2)
       (chanl1 ++
       (Vint32 i6 :: Vint32 i5 :: Vint32 (i4 +ᵢ  $ 1) :: Vint32 i3 :: head :: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil)
        :: chanl2)
       (chandstportll1 ++
        (v'8 ++ (kp_b, Int.zero) :: nil) :: chandstportll2)
       (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
       (kportl1 ++ (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero)  :: Vint32 i0 :: Vint32 i :: x4 :: nil)
        :: kportl2) dportl dpptrl|] **
   [|channel_V_dstPortsTail
               (chanl1 ++
                (Vint32 i6 :: Vint32 i5 :: Vint32 (i4 +ᵢ  $ 1) :: Vint32 i3 :: head :: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil)
                :: chanl2) (chandstportll1 ++ (v'8 ++ (kp_b, Int.zero) :: nil) :: chandstportll2)|] **
   [| struct_type_vallist_match OS_Channel 
      (Vint32 i6 :: Vint32 i5 :: Vint32 (i4 +ᵢ  $ 1) :: Vint32 i3 :: head :: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil) |] **
    <|| END None;; aop ||>  **
   LV channel @ OS_Channel ∗ |-> Vptr (v', Int.zero) **
   Astruct (v', Int.zero) OS_Channel
     (Vint32 i6
      :: Vint32 i5
         :: Vint32 (i4 +ᵢ  $ 1) :: Vint32 i3 :: head :: Vptr (kp_b, Int.zero) :: x6 :: x7 :: nil) **
   Channel_dstkport_get head Vnull ∘ (Int.unsigned (i4 +ᵢ  $ 1))
     (v'8 ++ (kp_b, Int.zero) :: nil) **
   LV kport @ OS_K_Port ∗ |-> Vptr (kp_b, Int.zero) **
   kport_V_OSEventPtr (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
     (kportl1 ++ (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero)  :: Vint32 i0 :: Vint32 i :: x4 :: nil)
      :: kportl2) dportl dpptrl **
   kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
     (kportl1 ++  (Vint32 i2 :: Vint32 portchanid :: x0 :: Vptr (v', Int.zero)  :: Vint32 i0 :: Vint32 i :: x4 :: nil)
      :: kportl2) **
   dmportp_sllseg dportlptr Vnull dportl dportmsgll OS_Port_V_nextPort **
   LV srcPort @ OS_Port ∗ |-> srcpv **
   LV port_ptr @ OS_Port ∗ |-> Vptr (p_b, p_i) **
   LV resource_get_res @ char_t |-> res_v **
   LV semaphore @ char_t |-> Vint32 i3 **
   ChannelNode chanvl1 chanl1 chandstportll1 **
   ChannelNode chanvl2 chanl2 chandstportll2 **
   GV OSDomainPortPtrList @ OS_Port ∗ |-> dportlptr **
   LV re @ OS_Port ∗ |-> Vnull **
   GV OSRunning @ char_t |-> Vint32 Int.zero **
   PV err_l @ char_t |-> Vint32 err_v **
   LV err @ (char_t) ∗ |-> Vptr err_l **
   LV channelID @ long |-> Vint32 portchanid **
   p_local OSLInv ct init_lg **
   A_dom_lenv
     ((err, (char_t) ∗)
      :: (port_ptr, OS_Port ∗)
         :: (channelID, long)
            :: (semaphore, char_t)
               :: (resource_get_res, char_t)
                  :: (kport, OS_K_Port ∗)
                     :: (channel, OS_Channel ∗)
                        :: (re, OS_Port ∗)
                           :: (flag, long)
                              :: (srcPort, OS_Port ∗) :: nil) **
   Aie false **
   Ais nil **
   Acs (true :: nil) ** Aisr empisr ** A_isr_is_prop ** Aier ier ** P ).
   intros s Hs.
   destruct Hs as [Hs | Hs].
   sep pauto.
   exfalso.
   sep split in Hs.
   tryfalse. }
   pure intro.
   clear H3 H27 H40.
   (* merge Domainport *)
   eapply backward_rule1.
   intros s Hs.
   port_combine.
   (* merge Kernelport *)
   eapply backward_rule1.
   intros s Hs.
   kport_combine kportvl1 kportvl2. lia.
   (* IF (channel ′ → dstPortsNum !=ₑ ′ 0)  { .. } *)
   rename v'8 into dstkportl.
   hoare name lift (Alvarmapsto srcPort) pre.
   hoare name lift (kport_V_OSEventPtr) pre.
   hoare name lift (Alvarmapsto kport) pre.
   hoare name lift Channel_dstkport_get pre.
   hoare name lift (Astruct (v', Int.zero) OS_Channel) pre.
   hoare name lift (Alvarmapsto channel) pre.
   hoare name lift Aop pre. 
   hoare remember (1::2::3::4::5::6::8::9::7::nil)%nat pre.
   eapply seq_rule.
   { eapply if_rule2';[ subst;symbolic_exe_port | | ].
   { pauto. }
   - (* dstPortsNum != 0 *)
      instantiate (1:= ( EX kptailv dstkportl',  
      [| Int.unsigned i4 > 0 |] **
      [| dstkportl = dstkportl' ++ kptailv :: nil|] **
      [| exists tailkp, struct_type_vallist_match OS_K_Port tailkp  /\ OS_K_Port_V_OSEventPtr tailkp = Some Vnull|] **
      <|| END None;; aop ||>  **
      LV channel @ OS_Channel ∗ |-> Vptr (v', Int.zero) **
      Astruct (v', Int.zero) OS_Channel
        (Vint32 i6
         :: Vint32 i5
            :: Vint32 i4 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) **
      Channel_dstkport_get x3 (Vptr kptailv) (∘ (Int.unsigned i4) - 1) dstkportl' **
      PV get_off_addr kptailv ($ 12) @ (Void) ∗ |-> Vptr (kp_b, Int.zero) **
      Channel_dstkport_get Vnull Vnull 0 nil **
      LV kport @ OS_K_Port ∗ |-> Vptr (kp_b, Int.zero) ** 
      kport_V_OSEventPtr
         (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
         (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0  :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)  :: kportl2) (dportl1 ++ dport :: dportl2) dpptrl **
      kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
         (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) **
      dmportp_sllseg dportlptr Vnull (dportl1 ++ dport :: dportl2) 
            (dportmsgll1 ++ msgl :: dportmsgll2) OS_Port_V_nextPort **
      LV srcPort @ OS_Port ∗ |-> srcp_v **  H3)).
      pure intro.
      assert (Int.eq i4 ($ 0) = false) by pauto.
      clear H27 H40 H41. rename H3 into Heqi4.
      hoare_assert_pure (length dstkportl = ∘ (Int.unsigned i4))%nat.
      { sep name lift Channel_dstkport_get in H3.
        eapply Channel_dstkport_get_length in H3.
        sep split in H3. auto. } 
      pure intro.
      assert (length dstkportl >= 1)%nat as Hlendstkportl.
      { rewrite H3.
        clear - Heqi4.
        pose proof Int.unsigned_range_2 i4.
        simpl_intltbool.
        unfold nat_of_Z in *. lia. }  
      pose proof Hchtail as Hchtail'.
      eapply channel_V_dstPortsTail_app in Hchtail' as [Hchtail1 Hchtail2];[ | lia].
      cbn in Hchtail2.
      destruct Hchtail2 as [Hcurtail Hchtail2].
      destruct Hcurtail as [[_ ?] | Hcurtail];[subst dstkportl; simpl in Hlendstkportl;lia | ].
      destruct Hcurtail as (kptailv & dstkportl' & ? & ?).
      inversion H27;subst x5. clear H27. subst dstkportl.
      hoare name lift Channel_dstkport_get pre.
      eapply backward_rule1.
      eapply Channel_dstkport_get_app_frm.
      { simpl in H3. 
        rewrite app_length in H3.
        cbn in H3.
        instantiate (1:= (∘ (Int.unsigned i4) - 1)%nat).
        lia. }
      hoare normal pre.
      naive pure intro. 
      pose proof H27. rename H27 into Htailkport.
      pure intro. 
      cbn in H40. inversion H40;subst v'1.
      assert ((∘ (Int.unsigned i4) - (∘ (Int.unsigned i4) - 1) - 1) = O)%nat by lia.
      rewrite H57;clear H57.
      hoare_assert_pure (x9 = Vnull).
      { cbn [Channel_dstkport_get] in H57. sep pauto. }
      pure intro.
      (* If (semaphore ′ ==ₑ ′ DEFAULT_CHANNLE_SEMAPHROE &&ₑ channel ′ → srcPort !=ₑ 〈 OS_K_Port ∗ 〉 NULL) *)
      hoare name lift (Astruct (v', Int.zero) OS_Channel) kportNode_P pre.
      hoare remember (1::2::nil)%nat pre.
      hoare forward;pauto.
      rewrite H48. clear - H46. cbn. destruct H46 as [ | [[? ?] ?]];subst;pauto.
      { (* if yes*) 
        instantiate (1:= 
        [| (exists (srckp : addrval), x6 = Vptr srckp /\ 
          exists n kport,
          nth_error (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) n = Some (Vptr srckp) /\
          nth_error (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) n =
          Some kport /\
          OS_K_Port_V_channel kport = Some (Vptr (v', Int.zero)) /\ OS_K_Port_V_coreNum kport = Some (Vint32 i0) )
          |]**
        Astruct (v', Int.zero) OS_Channel
          (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: Vptr kptailv :: x6 :: x7 :: nil) **
        kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
          (kportl1 ++
           (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) ** H40).
        pure intro.
        rewrite H48 in H57. destruct H46 as [ | [srckp ?]];subst. 
        { clear - H57.  exfalso. cbn in H57. mauto. }
        (* If ((channel ′ → srcPort) → coreNum !=ₑ kport ′ → coreNum) *)
        clear H59 H58 H57.
        destruct Hportch as [Hportch Hnodupkp].
        eapply channel_V_srcdstkport_src_node in Hportch as ?.
        2: eapply nth_error_middle.
        2: rewrite <- H42;eapply nth_error_middle.
        2: cbn;eauto.
        destruct H40 as (src_n & srckport & Hnthsrckpvl & Hsrckpchan & Hnthsrckpl & ?).
        destruct H40 as (srcpid & srcdptr & srcdport & Hsrcdp & Hnthsrcdpptrl & Hnthsrcdportl  & Hsrcdire).
        hoare name lift kportNode_P pre.
        eapply backward_rule1.
        { eapply kportNode_P_getsome_frm with (n := src_n);eauto. }
        pure intro.
        rename v'1 into kportvl3. rename v'2 into kportvl4. rename v'3 into kportl3. rename v'4 into kportl4.
        rename H57 into Hsrckportl. rename H46 into Hsrckportvl.
        remember (Vint32 i14 :: Vint32 i13 :: x5 :: x6 :: Vint32 i12 :: Vint32 i11 :: x10 :: nil) as srckport.
        assert (OS_Channel_V_srcPort (Vint32 i6
        :: Vint32 i5
           :: Vint32 i4 :: Vint32 i3 :: x3 :: Vptr kptailv :: Vptr (v'0, Int.zero) :: x7 :: nil) = Some (Vptr (v'0, Int.zero)) ).
        { cbn. auto. }
        eapply forward_rule2.
        eapply ift_rule''.
        { symbolic_exe_port.
          { eapply channel_srcPort_coreNum_rv with (kport := srckport);eauto.
            3: sep autocancel;exact H57.
            pauto.
            subst srckport. pauto. }
          { kport_combine kportvl3 kportvl4.
            2: subst srckport;pauto.
            unfold vallist in Hsrckportl, Hsrckportvl, H57.
            rewrite <- Hsrckportl, <- Hsrckportvl in H57. 
            eapply KPort_coreNum_rv_kportnode with (kpptr := (kp_b, Int.zero)) (kport := (Vint32 i2
            :: Vint32 i1
               :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil));eauto.
            sep autocancel;exact H57. }
          subst srckport. cbn. pauto.
          pauto.
          subst srckport. cbn. pauto.
          pauto. }
        { (* yes*)
        instantiate (1:= Afalse).
        pure intro.
        cbn in H57.
        assert (Int.eq i12 i0 =false) by pauto.
        clear H66 H65 H57.
        eapply backward_rule1.
        { intros s Hs. kport_combine kportvl3 kportvl4. pauto. }
        hoare forward.
        assert ((Int.modu ($ OS_PORT_ERR_MULTICORE) ($ Byte.modulus)) =$ OS_PORT_ERR_MULTICORE).
        { clear. unfold OS_PORT_ERR_MULTICORE. mauto. } 
        rewrite H57;clear H57.
        hoare abscsq;[apply noabs_oslinv | | ].
        eapply absinfer_seq_end;[ | | intros s Hs; exact Hs].
        1,2: can_change_aop_solver'.
        (* RETURN re ′ *)
        eapply rete_rule.
        intros s Hs.
        split.
        2:{ symbolic_execution.  }
        unfold OSPortAddToChannelPost'.
        sep normal. 
        sep eexists.
        sep autocancel.
        sep split;[ | cbn;eauto ].
        right.

        sep name lift (Channel_dstkport_get Vnull Vnull 0 nil) in Hs.
        sep name lift (Aptrmapsto (get_off_addr kptailv ($ 12))) in Hs.
        sep name lift (Channel_dstkport_get x3 (Vptr kptailv)) in Hs.
        sep remember (1::2::3::nil)%nat in Hs.
        sep name lift H57 in Hs.
        eapply astar_mono in Hs.
        2: {  intros s' Hs';exact Hs'. }
        2: {  clear s Hs.  intros s Hs.  
              eapply Channel_dstkport_get_length in Hs.
              sep split in Hs.
              assert (∘ (Int.unsigned (i4)) = (S (∘ (Int.unsigned i4) - 1 + 0))) by lia.
              eapply Channel_dstkport_get_compose in Hs;auto.
              rewrite <- H66 in Hs.
              exact Hs.
              eapply Htailkport.
              cbn. auto. }
        subst H57.
        sep normal in Hs.
        chann_combine chanvl1 chanvl2.
        unfold  AOSDomainPortPtrList, AOSKernelPortIDTbl, AOSChannelIDTbl.
        sep normal;sep eexists.
        sep autocancel.
        sep split;eauto.
        unfold dmportp_sll.
        sep autocancel.
        rewrite Hsrckportl, Hsrckportvl.
        sep autocancel.
        { right.
          do 7 eexists. split.
          { unfold OSPortAddToChannel_portchanninfo.
            splits;eauto.
            instantiate (2:= portchanid).
            unfold nat_of_Z. rewrite <- Hlenchanvl1. apply nth_error_middle.
            unfold nat_of_Z. rewrite <- Hlenchanvl1, <- H42.  eapply nth_error_middle.
            unfold nat_of_Z. rewrite <- Hlenchanvl1, <- H43. eapply nth_error_middle.
          }
          right.
          splits;auto.
          { clear - H6. unfold DomainportNode_P, Domainport_direction_P in *. simpljoin1.
            auto. } 
          left.
          split;auto.
          left.
          unfold OSPortAddToChannel_retvalue_case3_1.
          cbn.
          do 2 eexists.
          splits;eauto.
          rewrite Hsrckportvl.
          do 2 eexists.
          cbn;splits;eauto.
          apply nth_error_middle.
          cbn. unfold not;intros. inversion H57. subst. clear - H67. rewrite Int.eq_true in H67. tryfalse.
          }
          split;auto.
          split;auto.
          pauto.
        }
        intros s Hs.
        destruct Hs as [Hs | Hs].
        { sep split in Hs. tryfalse. }
        sep autocancel.
        kport_combine kportvl3 kportvl4.
        2: subst;pauto.
        sep split;eauto.
        unfold vallist in Hs,  Hsrckportl, Hsrckportvl.
        rewrite <- Hsrckportl, <- Hsrckportvl in Hs.
        sep auto.
        eexists.
        splits;eauto.
        do 2 eexists.
        unfold vallist. unfold vallist in  Hsrckportl, Hsrckportvl.
        rewrite Hsrckportl, Hsrckportvl.
        splits;eauto.
        apply nth_error_middle.
        rewrite <- H59. apply nth_error_middle.
        subst. cbn. sep split in Hs.
        cbn in H57.
        destruct (Int.eq i12 i0) eqn:?.
        apply Int_eq_dec in Heqb. subst. reflexivity.
        clear - H57. destruct H57;mauto.
      }
      eapply backward_rule1.
      { instantiate (1:= 
      [| (exists srckp,
      x6 = Vptr srckp /\
      (exists n kport,
       nth_error (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) n = Some (Vptr srckp) /\
       nth_error
         (kportl1 ++
          (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) n =
       Some kport /\
       OS_K_Port_V_channel kport = Some (Vptr (v', Int.zero)) /\
       OS_K_Port_V_coreNum kport = Some (Vint32 i0))) \/ 
      x6 = Vnull |] **
      Astruct (v', Int.zero) OS_Channel
      (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: Vptr kptailv :: x6 :: x7 :: nil) **
      kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
      (kportl1 ++
      (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) ** H40).
      intros s Hs.
      destruct Hs as [Hs | Hs].
      sep normal in Hs.
      sep autocancel.
      sep split in Hs. sep split;auto.

      sep normal in Hs.
      sep autocancel.
      sep split in Hs. sep split. sep auto.
      right.
      rewrite H48 in H57.
      destruct H46 as [ | [[? ?] ?]];subst;auto.
      clear - H57. cbn in H57. exfalso. mauto.
      }
      pure intro.  rename H57 into HSrcsinglecore.
      (* If (semaphore ′ ==ₑ ′ DEFAULT_CHANNLE_SEMAPHROE &&ₑ channel ′ → dstPortsHead !=ₑ 〈 OS_K_Port ∗ 〉 NULL) *)
      hoare name lift (Astruct (v', Int.zero) OS_Channel) kportNode_P pre.
      hoare remember (1::2::nil)%nat pre.
      hoare forward;pauto.
      rewrite H48. clear - H44. cbn. destruct H44 as [ | [[? ?] ?]];subst;pauto.
      { (* if yes*)
        instantiate (1:= [| (exists (dstkp : addrval) (dstkportl : list addrval), 
        x3 = Vptr dstkp /\ (dstkportl' ++ kptailv :: nil) = dstkp :: dstkportl /\ 
        exists n kport,
        nth_error (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) n = Some (Vptr dstkp) /\
        nth_error (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) n =
        Some kport /\
        OS_K_Port_V_channel kport = Some (Vptr (v', Int.zero)) /\ 
        OS_K_Port_V_coreNum kport = Some (Vint32 i0) )|]** 
        Astruct (v', Int.zero) OS_Channel (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: x3 :: Vptr kptailv :: x6 :: x7 :: nil) **
        kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
        (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) ** H40 ).
        pure intro.
        rewrite H48 in H57. 
        destruct H44 as [ | [dstkp ?]];subst. 
        {  exfalso. clear- H57. simpl in H57. mauto. }
        clear H57 H58 H59.
        (* If ((channel ′ → dstPortsHead) → coreNum !=ₑ kport ′ → coreNum) *)
        destruct ((dstkportl' ++ kptailv :: nil)) as [ | a ? ] eqn: Heqdstkportl.
        { simpl in Hlendstkportl; lia. }
        hoare_assert_pure (a = dstkp).
        { sep name lift (Channel_dstkport_get (Vptr dstkp)) 
          (Aptrmapsto (get_off_addr kptailv ($ 12))) (Channel_dstkport_get Vnull Vnull) in H40.
          sep remember (1::2::3::nil)%nat in H40.
          sep name lift H44 in H40.
          eapply astar_mono  with (P':= H44) in H40.
          2: sep auto.
          2: {  clear s0 H40. intros s Hs.
                eapply Channel_dstkport_get_length in Hs.
                sep split in Hs.
                eapply Channel_dstkport_get_compose in Hs;eauto. }
          subst H44.
          sep normal in H40.
          sep name lift Channel_dstkport_get in H40.
          assert ((∘ (Int.unsigned i4) - 1 + 0) = (∘ (Int.unsigned i4) - 1))%nat by lia.
          rewrite H44 in H40.
          rewrite Heqdstkportl in H40.
          cbn [Channel_dstkport_get] in H40.
          sep normal in H40.
          sep destruct H40.
          sep split in H40.
          inversion H59.
          auto.
        }
        pure intro.
        destruct Hportch as [Hportch Hnodupkp].
        eapply channel_V_srcdstkport_dsthead_node in Hportch as ?.
        2: eapply nth_error_middle.
        2: rewrite <- H42;eapply nth_error_middle.
        2: rewrite <- H43;eapply nth_error_middle.
        2: cbn;eauto.
        destruct H40 as (dst_n & dstkport & Hnthdstkpvl & Hdstkpchan & Hnthdstkpl & ?).
        destruct H40 as (dstpid & dstdptr & dstdport & Hdstdp & Hnthdstdpptrl & Hnthdstdportl  & Hdstdire).
        hoare name lift kportNode_P pre. 
        eapply backward_rule1.
        { eapply kportNode_P_getsome_frm with (n := dst_n);eauto. }
        pure intro.
        rename v'1 into kportvl3. rename v'2 into kportvl4. rename v'3 into kportl3. rename v'4 into kportl4.
        rename H57 into Hdstkportl. rename H44 into Hdstkportvl.
        remember (Vint32 i14 :: Vint32 i13 :: x3 :: x5 :: Vint32 i12 :: Vint32 i11 :: x10 :: nil) as dstkport.
        assert (OS_Channel_V_dstPortsHead   (Vint32 i6
        :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vptr (v'0, Int.zero) :: Vptr kptailv :: x6 :: x7 :: nil)= Some (Vptr (v'0, Int.zero)) ).
        { cbn. auto. }
        eapply forward_rule2.
        eapply ift_rule''.
        { symbolic_exe_port.
          { eapply channel_dstPortsHead_coreNum_rv with (kport := dstkport);eauto.
            3: sep autocancel;exact H57.
            pauto.
            subst dstkport. pauto. }
          { kport_combine kportvl3 kportvl4.
            2: subst dstkport;pauto.
            unfold vallist in Hdstkportl, Hdstkportvl, H57.
            rewrite <- Hdstkportl, <- Hdstkportvl in H57.
            eapply KPort_coreNum_rv_kportnode with (kpptr := (kp_b, Int.zero))
            (kport := (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil));eauto.
            sep autocancel. exact H57. }
          subst dstkport. cbn. pauto.
          pauto.
          subst dstkport. cbn. pauto.
          pauto. }
        { (* yes*)
          instantiate (1:= Afalse).
          pure intro.
          cbn in H57.
          assert (Int.eq i12 i0 =false) by pauto.
          clear H66 H65 H57.
          eapply backward_rule1.
          { intros s Hs. kport_combine kportvl3 kportvl4. pauto. }
          hoare forward.
          assert ((Int.modu ($ OS_PORT_ERR_MULTICORE) ($ Byte.modulus)) =$ OS_PORT_ERR_MULTICORE).
          { clear. unfold OS_PORT_ERR_MULTICORE. mauto. } 
          rewrite H57;clear H57.
          hoare abscsq;[apply noabs_oslinv | | ].
          eapply absinfer_seq_end;[ | | intros s Hs; exact Hs].
          1,2: can_change_aop_solver'.
          (* RETURN re ′ *)
          eapply rete_rule.
          intros s Hs.
          split.
          2:{ symbolic_execution.  }
          unfold OSPortAddToChannelPost'.
          sep normal. 
          sep eexists.
          sep autocancel.
          sep split;[ |cbn;eauto].
          right.

          sep name lift (Channel_dstkport_get Vnull Vnull 0 nil) in Hs.
          sep name lift (Aptrmapsto (get_off_addr kptailv ($ 12))) in Hs.
          sep name lift (Channel_dstkport_get (Vptr (v'0, Int.zero)) (Vptr kptailv)) in Hs.
          sep remember (1::2::3::nil)%nat in Hs.
          sep name lift H57 in Hs.
          eapply astar_mono in Hs.
          2: {  intros s' Hs';exact Hs'. }
          2: {  clear s Hs.  intros s Hs.  
                eapply Channel_dstkport_get_length in Hs.
                sep split in Hs.
                assert (∘ (Int.unsigned (i4)) = (S (∘ (Int.unsigned i4) - 1 + 0))) by lia.
                eapply Channel_dstkport_get_compose in Hs;auto.
                rewrite <- H66 in Hs.
                exact Hs.
                eapply Htailkport.
                cbn. auto. }
          subst H57.
          sep normal in Hs.
          chann_combine chanvl1 chanvl2.
          2: pauto.
          unfold  AOSDomainPortPtrList, AOSKernelPortIDTbl, AOSChannelIDTbl.
          sep normal;sep eexists.
          sep autocancel.
          sep split;eauto.
          unfold dmportp_sll.
          sep autocancel.
          rewrite Hdstkportl, Hdstkportvl.
          sep auto.
          { right.
            do 7 eexists. split.
            { unfold OSPortAddToChannel_portchanninfo.
              splits;eauto.
              instantiate (2:= portchanid).
              unfold nat_of_Z. rewrite <- Hlenchanvl1. apply nth_error_middle.
              unfold nat_of_Z. rewrite <- Hlenchanvl1, <- H42.  eapply nth_error_middle.
              unfold nat_of_Z. rewrite <- Hlenchanvl1, <- H43. eapply nth_error_middle.
            }
            right.
            splits;auto.
            { clear - H6. unfold DomainportNode_P, Domainport_direction_P in *. simpljoin1.
              auto. } 
            left.
            rewrite Heqdstkportl.
            splits;auto.
            right.
            unfold OSPortAddToChannel_retvalue_case2_1.
            cbn.
            do 2 eexists.
            splits;eauto.
            rewrite Hdstkportvl.
            do 2 eexists.
            cbn;splits;eauto.
            apply nth_error_middle.
            cbn. unfold not;intros. inversion H57. subst. clear - H67. 
            rewrite Int.eq_true in H67. tryfalse.
            }
            rewrite Heqdstkportl.
            split;auto.
            rewrite Heqdstkportl. auto.
            split;auto.
          }
        intros s Hs.
        destruct Hs as [Hs | Hs].
        sep split in Hs. tryfalse.
        
        sep normal in Hs.
        sep normal.
        sep autocancel.
        kport_combine kportvl3 kportvl4.
        2: subst;pauto.
        sep split;eauto.
        unfold vallist in Hs,  Hdstkportl, Hdstkportvl.
        rewrite <- Hdstkportl, <- Hdstkportvl in Hs.   sep autocancel.
        sep auto.
        unfold vallist in Hdstkportl, Hdstkportvl. unfold vallist.
        rewrite Hdstkportl, Hdstkportvl.
        exists ((v'0, Int.zero) ) l.
        splits;auto.
        do 2 eexists.
        cbn;splits;eauto.
        apply nth_error_middle.
        rewrite <- H59. apply nth_error_middle.
        sep split in Hs.
        subst dstkport. cbn in H57. 
        assert (Int.eq i12 i0 = true).
        { destruct (Int.eq i12 i0);auto.
          clear - H57;destruct H57;tryfalse. }
        apply Int_eq_dec in H65. subst i12.
        auto.
        }
      hoare forward.
      2:{ pure intro.
          rewrite H48 in H57. 
          destruct H44 as [ | [[? ?] ?]];subst.
          2:{ exfalso. clear - H57. destruct H57;mauto. }
          hoare name lift (Channel_dstkport_get Vnull (Vptr kptailv)) pre.
          eapply backward_rule1.
          { eapply Channel_dstkport_get_headVnull. }
          pure intro. 
          inversion H40. }
      naive pure intro. rename H57 into Hdstsinglecore.
      clear H58. subst H40.
      (* (channel ′ → dstPortsTail) → OSEventPtr =ₑ 〈 (Void) ∗ 〉 kport ′ *)
      eapply forward_rule2.
      hoare name lift (Astruct (v', Int.zero) OS_Channel) pre.
      hoare name lift (Alvarmapsto channel) pre.
      hoare name lift (Alvarmapsto kport) pre.
      hoare name lift (get_off_addr kptailv) pre.
      hoare name lift Aop pre.
      eapply assign_rule_general with (tp1:=  (Void) ∗ ) (tp2:=  (Void) ∗ ). 
      { intros.
        eapply symbolic_lemmas.struct_offset_rv with (t:= OS_K_Port).
        eapply symbolic_lemmas.addrof_deref_rv.
        sep_get_port_rv.
        pauto.
        unfold OS_K_Port;reflexivity.
        cbn. reflexivity.
        cbn. auto. }
      { assert ( ($ 1 +ᵢ ($ 1 +ᵢ ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero)))))) = $ 12) by (clear;mauto).
        rewrite H40.
        unfold get_off_addr.
        intro s;split;intros Hs;exact Hs. }
      { symbolic_exe_port. }
      { eapply eq_vptr. do 2 eexists. split;eauto. }
      { intros s Hs.  sep auto. }
      intros s Hs.
      assert ( ($ 1 +ᵢ ($ 1 +ᵢ ($ 4 +ᵢ  ($ 4 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero)))))) = $ 12) by (clear;mauto).
      rewrite H40 in Hs;clear H40.
      assert ((fst kptailv, snd kptailv +ᵢ  $ 12) = get_off_addr kptailv ($ 12)). { unfold get_off_addr;auto. }
      rewrite H40 in Hs;clear H40.
      sep eexists.
      sep autocancel.
      sep pauto.
      exists (Vint32 i10 :: Vint32 i9 :: x1 :: x2 :: Vint32 i8 :: Vint32 i7 :: Vnull :: nil).
      split;auto. 
      simpl_intltbool. pose proof Int.unsigned_range_2 i4. lia.
   -  (* dstPortsNum == 0 *)
      instantiate (1:= ( EX srcpv (dport: vallist) (dportl : list vallist) (dportmsgll : list (list vallist)),
      [|x3 = Vnull /\ dstkportl = nil /\ i4 = Int.zero |] **
      [| nth_error dportl (length dportl1) = Some dport /\  OS_Port_V_direction dport = Some (V$ DESTINATION) |] ** 
      [|RLH_PortPtrINecb dportlptr dportl dpptrl ecbls|] **
      [| R_Kernelport_DomainPort_init (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0  :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)  :: kportl2) dportl dpptrl |] **
      [| channel_V_srcdstkport_aux
         (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2)
         (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: V$ 0 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) :: chanl2) (chandstportll1 ++ dstkportl :: chandstportll2)
         (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
         (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)
         :: kportl2) dportl dpptrl |] **
      <||  END None;; aop ||>  **
      LV channel @ OS_Channel ∗ |-> Vptr (v', Int.zero) **
      Astruct (v', Int.zero) OS_Channel
      (Vint32 i6
         :: Vint32 i5
            :: Vint32 ($ 0) :: Vint32 i3 :: (Vptr (kp_b, Int.zero)) :: x5 :: x6 :: x7 :: nil) **
      Channel_dstkport_get x3 Vnull ∘ (Int.unsigned ($ 0)) dstkportl **
      LV kport @ OS_K_Port ∗ |-> Vptr (kp_b, Int.zero) ** 
      kport_V_OSEventPtr
         (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
         (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0  :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)  :: kportl2) dportl dpptrl **
      kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
         (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) **
      dmportp_sllseg dportlptr Vnull dportl dportmsgll OS_Port_V_nextPort **
      LV srcPort @ OS_Port ∗ |-> srcpv **  H3)).
      pure intro.
      assert (Int.eq i4 ($ 0) = true).
      { destruct (Int.eq i4 ($ 0));auto.
        clear - H27.
        mauto. }
      clear H27.
      apply Int_eq_dec in H3.
      subst i4.
      (* If (semaphore ′ ==ₑ ′ DEFAULT_CHANNLE_SEMAPHROE &&ₑ channel ′ → srcPort !=ₑ 〈 OS_K_Port ∗ 〉 NULL) *)
      hoare name lift (Astruct (v', Int.zero) OS_Channel) kportNode_P pre.
      hoare remember (1::2::nil)%nat pre.
      hoare forward;pauto.
      {  rewrite H48. clear - H46. destruct H46 as [ | [[? ?] ?]];subst;mauto. }
      { (* if yes*) 
        instantiate (1:= 
        [| (exists (srckp : addrval), x6 = Vptr srckp /\ 
          exists n kport,
          nth_error (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) n = Some (Vptr srckp) /\
          nth_error (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) n =
          Some kport /\
          OS_K_Port_V_channel kport = Some (Vptr (v', Int.zero)) /\ OS_K_Port_V_coreNum kport = Some (Vint32 i0) /\ 
          exists pid dmptr dmport,
          OS_K_Port_V_dmport kport = Some (Vptr dmptr) /\
          nth_error dpptrl pid = Some dmptr /\
          nth_error (dportl1 ++ dport :: dportl2) pid = Some dmport /\ OS_Port_V_direction dmport = Some (V$ SOURCE) )
          |]**
        Astruct (v', Int.zero) OS_Channel
          (Vint32 i6 :: Vint32 i5 :: V$ 0 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) **
        kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
          (kportl1 ++
           (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) **
        H3).
        pure intro.
        rewrite H48 in H27. destruct H46 as [ | [srckp ?]];subst. 
        { clear - H27.  exfalso. cbn in H27. mauto. }
        (* If ((channel ′ → srcPort) → coreNum !=ₑ kport ′ → coreNum) *)
        clear H41 H40 H27.
        destruct Hportch as [Hportch Hnodupkp].
        eapply channel_V_srcdstkport_src_node in Hportch as ?.
        2: eapply nth_error_middle.
        2: rewrite <- H42;eapply nth_error_middle.
        2: cbn;eauto.
        destruct H3 as (src_n & srckport & Hnthsrckpvl & Hsrckpchan & Hnthsrckpl & ?).
        destruct H3 as (srcpid & srcdptr & srcdport & Hsrcdp & Hnthsrcdpptrl & Hnthsrcdportl  & Hsrcdire).
        hoare name lift kportNode_P pre.
        eapply backward_rule1.
        { eapply kportNode_P_getsome_frm with (n := src_n);eauto. }
        pure intro.
        rename v'1 into kportvl3. rename v'2 into kportvl4. rename v'3 into kportl3. rename v'4 into kportl4.
        rename H40 into Hsrckportl. rename H27 into Hsrckportvl.
        remember (Vint32 i9 :: Vint32 i8 :: x1 :: x2 :: Vint32 i7 :: Vint32 i4 :: x9 :: nil) as srckport.
        assert (OS_Channel_V_srcPort (Vint32 i6
        :: Vint32 i5 :: V$ 0 :: Vint32 i3 :: x3 :: x5 :: Vptr (v'0, Int.zero) :: x7 :: nil) = Some (Vptr (v'0, Int.zero)) ).
        { cbn. auto. }
        eapply forward_rule2.
        eapply ift_rule''.
        { symbolic_exe_port.
          { eapply channel_srcPort_coreNum_rv with (kport := srckport);eauto.
            3: sep autocancel;exact H40.
            pauto.
            subst srckport. pauto. }
          { kport_combine kportvl3 kportvl4.
            2: subst srckport;pauto.
            unfold vallist in Hsrckportl, Hsrckportvl, H40.
            rewrite <- Hsrckportl, <- Hsrckportvl in H40. 
            eapply KPort_coreNum_rv_kportnode with (kpptr := (kp_b, Int.zero)) (kport := (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil));eauto.
            sep autocancel;exact H40. }
          subst srckport. cbn. pauto.
          pauto.
          subst srckport. cbn. pauto.
          pauto. }
        { (* yes*)
        instantiate (1:= Afalse).
        pure intro.
        cbn in H40.
        assert (Int.eq i7 i0 =false) by pauto.
        clear H58 H57 H40.
        eapply backward_rule1.
        { intros s Hs. kport_combine kportvl3 kportvl4. pauto. }
        hoare forward.
        assert ((Int.modu ($ OS_PORT_ERR_MULTICORE) ($ Byte.modulus)) =$ OS_PORT_ERR_MULTICORE).
        { clear. unfold OS_PORT_ERR_MULTICORE. mauto. } 
        rewrite H40;clear H40.
        hoare abscsq;[apply noabs_oslinv | | ].
        eapply absinfer_seq_end;[ | | intros s Hs; exact Hs].
        1,2: can_change_aop_solver'.
        (* RETURN re ′ *)
        eapply rete_rule.
        intros s Hs.
        split.
        2:{ symbolic_execution.  }
        unfold OSPortAddToChannelPost'.
        sep normal. 
        sep eexists.
        sep autocancel.
        sep split;[ |cbn;eauto].
        right.
  
        chann_combine chanvl1 chanvl2.
        2: pauto.
        unfold  AOSDomainPortPtrList, AOSKernelPortIDTbl, AOSChannelIDTbl.
        sep normal;sep eexists.
        sep autocancel.
        sep split;eauto.
        unfold dmportp_sll.
        sep autocancel.
        rewrite Hsrckportl, Hsrckportvl.
        sep autocancel.
        { right.
          do 7 eexists. split.
          { unfold OSPortAddToChannel_portchanninfo.
            splits;eauto.
            instantiate (2:= portchanid).
            unfold nat_of_Z. rewrite <- Hlenchanvl1. apply nth_error_middle.
            unfold nat_of_Z. rewrite <- Hlenchanvl1, <- H42.  eapply nth_error_middle.
            unfold nat_of_Z. rewrite <- Hlenchanvl1, <- H43. eapply nth_error_middle.
          }
          right.
          splits;auto.
          { clear - H6. unfold DomainportNode_P, Domainport_direction_P in *. simpljoin1.
            auto. } 
          left.
          split;auto.
          left.
          unfold OSPortAddToChannel_retvalue_case3_1.
          cbn.
          do 2 eexists.
          splits;eauto.
          rewrite Hsrckportvl.
          do 2 eexists.
          cbn;splits;eauto.
          apply nth_error_middle.
          cbn. unfold not;intros. inversion H40. subst. clear - H59. rewrite Int.eq_true in H59. tryfalse.
          }
          split;auto.
          split;auto.
        }
        intros s Hs.
        destruct Hs as [Hs | Hs].
        { sep split in Hs. tryfalse. }
        sep autocancel.
        kport_combine kportvl3 kportvl4.
        2: subst;pauto.
        sep split;eauto.
        unfold vallist in Hs,  Hsrckportl, Hsrckportvl.
        rewrite <- Hsrckportl, <- Hsrckportvl in Hs.
        sep auto.
        eexists.
        splits;eauto.
        do 2 eexists.
        unfold vallist. unfold vallist in  Hsrckportl, Hsrckportvl.
        rewrite Hsrckportl, Hsrckportvl.
        splits;eauto.
        apply nth_error_middle.
        rewrite <- H46. apply nth_error_middle.
        subst. cbn. sep split in Hs.
        cbn in H40.
        destruct (Int.eq i7 i0) eqn:?.
        apply Int_eq_dec in Heqb. subst. reflexivity.
        clear - H40. destruct H40;mauto.
        do 3 eexists.
        splits;eauto.
      }
      eapply backward_rule1.
      { instantiate (1:= 
      [| ((exists (srckp : addrval), x6 = Vptr srckp /\ 
      exists n kport,
      nth_error (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) n = Some (Vptr srckp) /\
      nth_error (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) n =
      Some kport /\
      OS_K_Port_V_channel kport = Some (Vptr (v', Int.zero)) /\ OS_K_Port_V_coreNum kport = Some (Vint32 i0) /\ 
      exists pid dmptr dmport,
      OS_K_Port_V_dmport kport = Some (Vptr dmptr) /\
      nth_error dpptrl pid = Some dmptr /\
      nth_error (dportl1 ++ dport :: dportl2) pid = Some dmport /\ OS_Port_V_direction dmport = Some (V$ SOURCE) )) \/ 
      x6 = Vnull |] **
      Astruct (v', Int.zero) OS_Channel (Vint32 i6 :: Vint32 i5 :: V$ 0 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil) **
      kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) ** H3).
      intros s Hs.
      destruct Hs as [Hs | Hs].
      sep normal in Hs.
      sep autocancel.
      sep split in Hs. sep split;auto.

      sep normal in Hs.
      sep autocancel.
      sep split in Hs. sep split. sep auto.
      right.
      rewrite H48 in H27.
      destruct H46 as [ | [[? ?] ?]];subst;auto.
      clear - H27. cbn in H27. exfalso. mauto.
      }
      pure intro.  rename H27 into HSrcsinglecore.
      (* channel ′ → dstPortsHead =ₑ  kport ′;ₛ *)
      eapply seq_rule.
      hoare name lift (Astruct (v', Int.zero) OS_Channel) pre.
      hoare name lift (Alvarmapsto channel) pre.
      hoare name lift Aop pre.
      eapply assign_rule_struct_aop; 
      [intros s;split;intros Hs;exact Hs | unfold OS_Channel;simpl;eauto 
      | simpl; eauto
      | unfold id_nth; simpl; eauto
      | simpl; eauto
      | intros; intro; tryfalse
      | intros; intro; tryfalse
      | intros; intro; tryfalse
      | symbolic_exe_port
      | apply assign_type_match_true; simpl; auto
      | simpl; try lia
      | simpl; auto
      | li_sepauto li ].
      (* If (port_ptr ′ → mode ==ₑ ′ QUEUE &&ₑ channel ′ → srcPort !=ₑ 〈 OS_K_Port ∗ 〉 NULL) { .. } *)
      eapply backward_rule1.
      {  intros s Hs.
         sep name lift dmportp_sllseg in Hs.
         eapply dmportp_sllseg_app'_frm in Hs;eauto. }
      cbn [dmportp_sllseg].
      pure intro. rename v'0 into dport_nextv. rename v'2 into qstart.
      hoare remember (4::1::2::3::5::6::7::8::9::10::11::12::nil)%nat pre.
      eapply forward_rule2.
      eapply ift_rule''; [subst;symbolic_exe_port|idtac].
      { pauto. }  
      { clear - H46. destruct H46 as [ |[[? ?] ?]];subst; pauto. }
      { clear - H46. destruct H46 as [ |[[? ?] ?]];subst; pauto. } 
      { destruct pt; clear - H46; destruct H46 as [ |[[? ?] ?]];subst; pauto. }  
      +  (* queue and srcport != null *)  
      instantiate (1:= ( EX srcdpr (dport: vallist) (dportl : list vallist) (dportmsgll : list (list vallist)),
      [|x3 = Vnull /\ dstkportl = nil  |] **
      [| nth_error dportl (length dportl1) = Some dport /\  OS_Port_V_direction dport = Some (V$ DESTINATION) |] ** 
      [| RLH_PortPtrINecb dportlptr dportl dpptrl ecbls|] **
      [| R_Kernelport_DomainPort_init (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0  :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)  :: kportl2) dportl dpptrl |] **
      [| channel_V_srcdstkport_aux
      (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2)
      (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: V$ 0 :: Vint32 i3 :: x3 :: x5 :: x6 :: x7 :: nil)
       :: chanl2) (chandstportll1 ++ dstkportl :: chandstportll2)
      (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
      (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)
       :: kportl2) dportl dpptrl |] **
      <||  END None;; aop ||>  **
      LV channel @ OS_Channel ∗ |-> Vptr (v', Int.zero) **
      Astruct (v', Int.zero) OS_Channel
      (Vint32 i6
         :: Vint32 i5
            :: Vint32 ($ 0) :: Vint32 i3 :: (Vptr (kp_b, Int.zero)) :: x5 :: x6 :: x7 :: nil) **
      Channel_dstkport_get x3 Vnull ∘ (Int.unsigned ($ 0)) dstkportl **
      LV kport @ OS_K_Port ∗ |-> Vptr (kp_b, Int.zero) ** 
      kport_V_OSEventPtr
         (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
         (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0  :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)  :: kportl2) dportl dpptrl **
      kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
         (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) **
      dmportp_sllseg dportlptr Vnull dportl dportmsgll OS_Port_V_nextPort ** 
      LV srcPort @ OS_Port ∗ |-> srcdpr ** H3)).
      subst.
      pure intro.
      destruct pt.
      { exfalso. clear - H3 H46.  destruct H46 as [ |[[? ?] ?]];subst; pauto. }
      destruct H46 as [ |[[srckp_b srckp_i] ?]];subst.
      { exfalso. clear - H3. pauto. } 
      (* If ((channel ′ → srcPort)  → dmport !=ₑ 〈 OS_Port ∗ 〉 NULL) *)
      clear H50 H49 H3.
      destruct Hportch as [Hportch Hnodupkp].
      destruct HSrcsinglecore as [[? [? H3]] | ].
      2: { inversion H3. }
      inversion H46;subst x. clear H46.
      destruct H3 as (src_n & srckport & Hnthsrckpvl & Hsrckpchan & Hnthsrckpl & Hkpcorenum & ? ).
      destruct H3 as (srcpid & srcdptr & srcdport & Hsrcdp & Hnthsrcdpptrl & Hnthsrcdportl  & Hsrcdire).
      hoare name lift kportNode_P pre.
      eapply backward_rule1.
      { eapply kportNode_P_getsome_frm with (n := src_n);eauto. }
      pure intro.
      rename v'1 into kportvl3. rename v'2 into kportvl4. rename v'3 into kportl3. rename v'4 into kportl4.
      rename H49 into Hsrckportl. rename H46 into Hsrckportvl.
      remember ((Vint32 i9 :: Vint32 i8 :: x1 :: x2 :: Vint32 i7 :: Vint32 i4 :: x9 :: nil)) as srckport.
      assert (OS_Channel_V_srcPort (Vint32 i6
      :: Vint32 i5 :: V$ 0 :: Vint32 i3 :: Vptr (kp_b, Int.zero) :: x5 :: Vptr (v'0, Int.zero) :: x7 :: nil) = Some (Vptr (v'0, Int.zero)) ).
      { cbn. auto. } 
      eapply forward_rule2.
      eapply ift_rule'';[subst;symbolic_exe_port | ].
      pauto.
      subst;pauto.
      destruct H55 as [ | [[? ?] ?]];subst;pauto.
      destruct H55 as [ | [[? ?] ?]];subst;pauto.
      { (* if yes *)
         instantiate (1:= EX srcdpr (dport: vallist) (dportl : list vallist) (dportmsgll : list (list vallist)),
         [|x3 = Vnull /\ dstkportl = nil  |] **
         [| nth_error dportl (length dportl1) = Some dport /\  OS_Port_V_direction dport = Some (V$ DESTINATION) |] ** 
         [|RLH_PortPtrINecb dportlptr dportl dpptrl ecbls|] **
         [|R_Kernelport_DomainPort_init (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
             (kportl1 ++
              (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)
              :: kportl2) dportl dpptrl|] **
         [| channel_V_srcdstkport_aux
         (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2)
         (chanl1 ++ (Vint32 i6 :: Vint32 i5 :: V$ 0 :: Vint32 i3 :: x3 :: x5 :: Vptr (v'0, Int.zero)  :: x7 :: nil)
         :: chanl2) (chandstportll1 ++ dstkportl :: chandstportll2)
         (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
         (kportl1 ++ (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil)
         :: kportl2) dportl dpptrl |] ** 
          <|| END None;; aop ||>  **
         LV channel @ OS_Channel ∗ |-> Vptr (v', Int.zero) **
         Astruct (v', Int.zero) OS_Channel
           (Vint32 i6
            :: Vint32 i5
               :: V$ 0
                  :: Vint32 i3 :: Vptr (kp_b, Int.zero) :: x5 :: Vptr (v'0, Int.zero) :: x7 :: nil) **
         Channel_dstkport_get x3 Vnull ∘ (Int.unsigned ($ 0)) dstkportl **
         LV kport @ OS_K_Port ∗ |-> Vptr (kp_b, Int.zero) **
         kport_V_OSEventPtr (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
           (kportl1 ++
            (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2)
           dportl dpptrl **
         kportNode_P (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2)
           (kportl1 ++
            (Vint32 i2 :: Vint32 i1 :: x0 :: Vnull :: Vint32 i0 :: Vint32 i :: x4 :: nil) :: kportl2) **
         dmportp_sllseg dportlptr Vnull dportl dportmsgll OS_Port_V_nextPort **
         LV port_ptr @ OS_Port ∗ |-> Vptr (p_b, p_i) **
         LV resource_get_res @ char_t |-> res_v **
         LV semaphore @ char_t |-> Vint32 i3 **
         ChannelNode chanvl1 chanl1 chandstportll1 **
         ChannelNode chanvl2 chanl2 chandstportll2 **
         GV OSDomainPortPtrList @ OS_Port ∗ |-> dportlptr **
         LV re @ OS_Port ∗ |-> Vnull **
         GV OSRunning @ char_t |-> Vint32 Int.zero **
         PV err_l @ char_t |-> Vint32 err_v **
         LV srcPort @ OS_Port ∗ |-> srcdpr **
         LV err @ (char_t) ∗ |-> Vptr err_l **
         LV channelID @ long |-> Vint32 portchanid **
         p_local OSLInv ct init_lg **
         A_dom_lenv
           ((err, (char_t) ∗)
            :: (port_ptr, OS_Port ∗)
               :: (channelID, long)
                  :: (semaphore, char_t)
                     :: (resource_get_res, char_t)
                        :: (kport, OS_K_Port ∗)
                           :: (channel, OS_Channel ∗)
                              :: (re, OS_Port ∗) :: (flag, long) :: (srcPort, OS_Port ∗) :: nil) **
         Aie false **
         Ais nil **
         Acs (true :: nil) **
         Aisr empisr **
         A_isr_is_prop **
         Aier ier ** 
         GAarray OSChannelIDTbl (Tarray OS_Channel ∗ ∘ CHANNEL_NUMS)
(chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) **
GAarray OSKernelPortIDTbl (Tarray OS_K_Port ∗ ∘ PORT_NUMS)
(kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) **
GV ksCurDomain @ long |-> Vint32 curdomain **
GV ksDomains @ OSdomain_t ∗ |-> Vptr domainv **
Astruct (get_off_addr domainv (Int.mul ($ 34) curdomain)) OSdomain_t domainvl **
GV OSPortAttrTbl @ OSport_attr_t ∗ |-> Vptr portattrv **
Astruct (get_off_addr portattrv (Int.mul ($ 12) ($ Z.of_nat pid))) OSport_attr_t portattrvl **
LV flag @ long |-> (V$ 1) **
AOSKernelPortFreeList kportfptr kportfl **
AOSChannelFreeList chanfptr chanfl **
OtherPortPtrList otherppl otherpl othermsgll **
EvtInv ecbls p1 (tcbl1 ++ tcbcur :: tcbl2) tcbls vhold scapl mcapl qcapl **
AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls).
         pure intro.
         clear H49 H60 H61.
         (* srcPort ′ =ₑ (channel ′ → srcPort) → dmport;ₛ *)
         eapply seq_rule.
         hoare name lift (Alvarmapsto srcPort) pre.
         hoare name lift Aop pre.
         eapply assign_rule_lvar; [ 
            intro s; split; intro Hs; exact Hs|
            subst;symbolic_exe_port | apply assign_type_match_true; simpl; auto | li_sepauto li ].
         pauto. pauto. 
         clear H46. rewrite H10 in H27. inversion H27.
         rewrite H12 in H41. inversion H41. subst. clear H27. 
         eapply backward_rule1.
         { intros s Hs.
         sep lift 8%nat in Hs.
         eapply disj_star_elim_disj in Hs.
         exact Hs. 
         }
         hoare forward.
         {  pure intro.
            exfalso.
            clear - H6 H27.
            unfold DomainportNode_P, Domainport_Portt_P  in *.
            simpljoin1.
            rewrite H3 in H27.
            inversion H27. }
         pure intro.

         rename v'3 into qout. rename v'2 into qin. rename v'1 into qend. rename v'4 into qsize. rename v'5 into qentries.
         rename v'6 into invalid_msgl. rename v'0 into srckp_b.
         assert (OS_Port_V_direction dport = Some (V$ DESTINATION)).
         {  clear - H6.
            unfold DomainportNode_P,Domainport_direction_P in H6.
            simpljoin1.
            auto. 
         }
         assert (OS_Port_V_OSQEntries dport = Some (V$ 0)) as Hqentrieseq0.
         { eapply  Hqueuechan.
           2: rewrite <- Hlenchanvl1, <- H42; apply nth_error_middle.
           all: eauto.
           rewrite <- Hlenchanvl1, <- H43;apply nth_error_middle.
         }
         assert (OS_Port_V_mode srcdport = Some (Vint32 (Int.repr QUEUE))) as Hsrcportmode.
         { eapply  Hqueuechan.
           2: rewrite <- Hlenchanvl1, <- H42; apply nth_error_middle.
           all: eauto.
           rewrite <- Hlenchanvl1, <- H43;apply nth_error_middle.
           cbn. reflexivity.
         }
         eapply RL_PortPtrList_app in H as ?;eauto.
         destruct H66 as (dpptrl1 & dpptrl2 & ? & Hlendpptrl1 &  Hdpptrl1 & Hdpptrl2);subst dpptrl.
         assert (srcpid = length (dportl1) \/ srcpid < length (dportl1) \/  length (dportl1) < srcpid)%nat  as [ |   [ | ] ] by lia.
         { exfalso. subst.
           rewrite nth_error_middle in Hnthsrcdportl. inversion Hnthsrcdportl;subst.
           rewrite H41 in Hsrcdire. inversion Hsrcdire.
         }
         * (* srcpid < length (dportl1) *) 
           rewrite nth_error_app1 in Hnthsrcdportl by lia.
           hoare name lift (dmportp_sllseg dportlptr (Vptr (p_b, p_i)) dportl1) pre.
           eapply backward_rule1.
           { intros s Hs.
            eapply  dmportp_sllseg_length_frm;eauto.
           }
           pure intro.
           destruct (nth_error dportmsgll1 srcpid) as  [ srcmsgl | ] eqn:  Hnthsrcmsg.
           2: { apply nth_error_None in Hnthsrcmsg. exfalso. lia. }
           apply nth_error_split in Hnthsrcmsg as (dportmsgll11 &  dportmsgll12 & ? & Hlendportmsgll11).
           subst.
           apply nth_error_split in Hnthsrcdportl as (dportl11 &  dportl12 & ? & Hlendportl11).
           subst.
           rewrite nth_error_app1 in Hnthsrcdpptrl by lia.
           eapply backward_rule1.
           eapply dmportp_sllseg_app_tail_frm with (dpptrl :=dpptrl1);eauto.
           cbn [dmportp_sllseg].
           pure intro.
           rename v'1 into srcdpr. rename v'2 into srcqstart. rename v'0 into srcnext_v.
           eapply backward_rule1.
           { intros s Hs.
             sep  lift 2%nat in Hs.
             eapply disj_star_elim_disj in Hs.
             destruct Hs.
             exfalso. sep normal in H68.  sep split in H68. rewrite H72 in Hsrcportmode. inversion Hsrcportmode.
             exact H68.
           }
           pure intro.
           rename v'2 into srcqout. rename v'1 into srcqin. rename v'0 into srcqend. rename v'3 into srcqsize. rename v'4 into srcqentries.
           rename v'5 into srcinvalid_msgl.
           simpl (nth_val' 2 _ ).
           unfold OS_K_Port_V_dmport  in Hsrcdp.  cbn in Hsrcdp. inversion Hsrcdp;subst x1.
           
           hoare name lift p_local pre.
           hoare name lift A_dom_lenv pre.
           hoare name lift (APortStruct (p_b, p_i)) pre.
           hoare name lift (Alvarmapsto port_ptr) pre.
           hoare name lift (Alvarmapsto srcPort) pre.
           hoare name lift Aop pre.
           eapply seq_rule.
           eapply backward_rule2.
           { eapply portaddtochannelproof_while1 with (dport := dport);eauto. }
           { intros s Hs. sep normal. sep eexists. sep autocancel.
             sep pauto. sep cancel dmportp_sllseg_qport_msg.
             rewrite gjb_common.update_nth_val_eq_same.
             rewrite gjb_common.update_nth_val_eq_same.
             sep pauto.
             unfold OS_Port_V_OSQEnd in *. eapply nth_val_nth_val'_some_eq. auto.
             unfold OS_Port_V_OSQEntries in *. eapply nth_val_nth_val'_some_eq.
             port_nth_val_solve.
           }
           pure intro.
           rename srcqout into srcqout_ori. rename srcqentries into srcqentries_ori. rename srcmsgl into srcmsgl_ori.
           rename v'0 into srcqout. rename v'1 into srcqentries. rename v'2 into  srcmsgl.
           rename srcinvalid_msgl into srcinvalid_msgl_ori. rename v'3 into srcinvalid_msgl.
           clear H77.
           pure intro.
           eapply aconj_aisfalse_rule.
           symbolic_exe_port.
           { sep split in H77.
             clear - H80 H79 H70.
             destruct srcdport; simpl in *; tryfalse.
             do 18 (destruct H70 as [? H70]; split;auto;
                  destruct srcdport; simpl in *; tryfalse).
             clear - H80 H79.
             assert (Int.unsigned srcqentries <= 65535) by lia. clear - H.
             pauto. }
           { port_nth_val_solve.  }
           pure intro.
           assert (Int.ltu qsize srcqentries = false).
           { clear - H81. 
             destruct (Int.ltu qsize srcqentries);auto.
             destruct H81;tryfalse.
           }
           clear H81.
           hoare name lift Aie Ais Acs Aisr A_isr_is_prop pre.
           hoare name lift Aier pre.
           hoare lifts (7::8::9::10::11::18::19::12::13::14::15::nil)%nat pre.
           eapply forward_rule2.
           eapply backward_rule2.
           eapply portaddtochannelproof_while2 with (srcdport := (update_nth_val 17
           (update_nth_val 15 srcdport (Vptr srcqout))
           (Vint32 srcqentries)) ).
           22:{ intros s Hs.
                sep eexists.
                sep autocancel.
                sep cancel dmportp_sllseg_qport_msg.
                sep cancel dmportp_sllseg_qport_msg.
                sep cancel dmportp_sllseg_qport_msg.
                sep cancel dmportp_sllseg_qport_msg.
                sep split;eauto.
                instantiate (2:= dport).
                do 2 rewrite gjb_common.update_nth_val_eq_same.
                sep autocancel.
                do 2 rewrite gjb_common.update_nth_val_eq_same.
                exact Hs.
                eapply nth_val_nth_val'_some_eq;eauto.
                { eapply nth_val_nth_val'_some_eq.
                  port_nth_val_solve. }
                eapply nth_val_nth_val'_some_eq;eauto.
                { eapply nth_val_nth_val'_some_eq.
                  port_nth_val_solve. }
                { eapply nth_val_nth_val'_some_eq.
                  port_nth_val_solve. }
                { eapply nth_val_nth_val'_some_eq.
                  port_nth_val_solve. }
                instantiate (1:= srcqentries).
                rewrite H62 in Hqentrieseq0.
                inverts Hqentrieseq0.
                rewrite Int.unsigned_repr by (clear;mauto).
                lia. }
           all:eauto.
           { good_frm_sovler.   }
           all: port_nth_val_solve.
           { clear - H77 H79 H70.
            destruct srcdport; simpl in *; tryfalse.
            do 18 (destruct H70 as [? H70]; split; auto;
               destruct srcdport; simpl in *; tryfalse).
            assert (Int.unsigned srcqentries <= 65535) by lia.
            clear - H17. pauto. }
         
         intros s Hs. 
         sep normal in Hs. sep destruct Hs.
         rename x into srcqout'. rename x1 into srcqentries'.
         rename x6 into srcmsgl'. rename x8 into srcinvalid_msgl'.
         rename x10 into qin'. rename x11 into qentries'.
         rename x12 into msgl'. rename x13 into invalid_msgl'.
         eapply sep_aconj_r_aisfalse_to_astar in Hs.
         2:{ intros. sep_get_port_rv. sep split in H81. 
            clear - H84 H79 H70.
            destruct srcdport; simpl in *; tryfalse.
            do 18 (destruct H70 as [? H70]; split; auto;
               destruct srcdport; simpl in *; tryfalse).
            assert (Int.unsigned srcqentries' <= 65535) by lia.
            clear - H17. pauto.
         port_nth_val_solve. } 
         sep normal in Hs.
         sep name lift (Int.ltu ($ 0) srcqentries') in Hs.
         apply sep_pure_split in Hs as [? Hs].
         kport_combine kportvl3 kportvl4.
         2: { pauto. }
         sep name lift (APortStruct srcdpr) in Hs.
         rewrite update_nth_val_diff in Hs by lia.
         rewrite update_nth_val_same in Hs.
         rewrite update_nth_val_diff in Hs by lia.
         rewrite update_nth_val_same in Hs.
         exists (Vptr srcdpr) (update_nth_val 17
         (update_nth_val 14 dport (Vptr qin'))
         (Vint32 qentries'))   (((dportl11 ++ (update_nth_val 17 (update_nth_val 15 srcdport (Vptr srcqout'))
         (Vint32 srcqentries')) :: dportl12) ++ (update_nth_val 17
             (update_nth_val 14 dport (Vptr qin'))
             (Vint32 qentries')) :: dportl2)) 
             ((dportmsgll11 ++ srcmsgl' :: dportmsgll12) ++ msgl' :: dportmsgll2).
         sep name lift Channel_dstkport_get in Hs.
         apply Channel_dstkport_get_length in Hs.
         assert (∘ (Int.unsigned ($ 0)) = 0)%nat by   (clear;unfold nat_of_Z in *;mauto).
         rewrite H83 in Hs. rewrite H83.
         apply sep_pure_split in Hs as [? Hs].
         clear H83. destruct dstkportl as [ | ];[ | simpl in H84;tryfalse].
         cbn [Channel_dstkport_get] in *.
         apply sep_pure_split in Hs as [? Hs];subst x3.  clear H84.
         sep autocancel.
         rewrite Hsrckportl, Hsrckportvl.
         sep autocancel.
         sep name lift dmportp_sllseg dportlptr.
         eapply dmportp_sllseg_app'_frm;eauto.
         {  clear - H5.
            rewrite ! app_length in *.
            cbn in *.
            lia.
         }
         {  instantiate (1:= (p_b, p_i)). instantiate (1:=  (dpptrl1 ++ (p_b, p_i) :: dpptrl2)).
            clear - Hlendpptrl1  H4.
            rewrite app_length in *.
            cbn in *.
            auto.
         }
         { assert (length dpptrl1 =
            length (dportl11 ++ update_nth_val 17 (update_nth_val 15 srcdport (Vptr srcqout')) (Vint32 srcqentries') :: dportl12)).
            { rewrite app_length. cbn. rewrite Hlendpptrl1. rewrite app_length. cbn. auto. } 
           eapply RL_PortPtrList_upd with (ndstport := dport);auto.
           2: unfold OS_Port_V_nextPort;rewrite ! nth_upd_neqrev' by lia;auto.
           apply RL_PortPtrList_tail_null.
           apply RL_PortPtrList_tail_app.
           { rewrite app_length. cbn. rewrite Hlendpptrl1. rewrite app_length. cbn. auto. }
           split; [ | apply RL_PortPtrList_tail_null;auto ].
           apply nth_error_split in Hnthsrcdpptrl as (? & ? & ? & ?).
           subst dpptrl1.
           eapply RL_PortPtrList_tail_upd;eauto.
           lia.
           unfold OS_Port_V_nextPort;rewrite ! nth_upd_neqrev' by lia;auto.
         }
         cbn [dmportp_sllseg].
         sep normal.
         sep eexists.
         sep lift 6%nat.
         eapply disj_split.
         right.
         sep normal.
         sep eexists.
         sep name lift (APortStruct (p_b, p_i)) (dmportp_sllseg_qport_msg qout)  (dmportp_sllseg_qport_msg qin') in Hs.
         sep cancel dmportp_sllseg_qport_msg.
         sep cancel dmportp_sllseg_qport_msg.
         sep cancel APortStruct.
         sep split in Hs.
         sep split;eauto; try port_nth_val_solve.
         7,8: split;[port_nth_val_solve | try lia].
         { sep cancel (dmportp_sllseg dport_nextv).
         eapply dmportp_sllseg_app_tail_frm;eauto.
         { apply nth_error_split in Hnthsrcdpptrl as (? & ? & ? & ?).
         subst dpptrl1.
         eapply RL_PortPtrList_tail_upd;eauto.
         lia.
         unfold OS_Port_V_nextPort;rewrite ! nth_upd_neqrev' by lia;auto.
         }
         cbn [dmportp_sllseg].
         sep normal.
         sep eexists.
         sep lift 6%nat.
         eapply disj_split.
         right.
         sep normal.
         sep eexists.
         sep cancel dmportp_sllseg_qport_msg.
         sep cancel dmportp_sllseg_qport_msg.
         sep cancel APortStruct.
         sep split;eauto; try port_nth_val_solve.
         3,4: split;[port_nth_val_solve | try lia].
         { sep cancel (dmportp_sllseg srcnext_v).
            sep cancel dmportp_sllseg.
            rewrite <- Hsrckportvl, <-Hsrckportl.
            (* kport_V_OSEventPtr *)
            eapply kport_V_OSEventPtr_update_dport with (dport := dport).
            unfold OS_Port_V_direction. rewrite ! nth_upd_neqrev' by lia;auto.
            rewrite <- app_assoc in Hs. rewrite <- app_assoc.
            simpl ((_ :: _) ++ _) in *.
            eapply kport_V_OSEventPtr_update_dport with (dport := srcdport);eauto.
            unfold OS_Port_V_direction. rewrite ! nth_upd_neqrev' by lia;auto.
             }
             clear - H84 H79 H70.
             destruct srcdport; simpl in *; tryfalse.
             do 18 (destruct H70 as [? H70]; split; auto;
                destruct srcdport; simpl in *; tryfalse).
             assert (Int.unsigned srcqentries' <= 65535) by lia.
             clear - H17. pauto.
         }
         {  
            rewrite <- Hsrckportl, <- Hsrckportvl.
            unfold channel_V_srcdstkport_aux.
            split;auto.
            eapply channel_V_srcdstkport_update_dport with (dport := dport).
            unfold OS_Port_V_direction. rewrite ! nth_upd_neqrev' by lia;auto.
            rewrite <- app_assoc in Hportch. rewrite <- app_assoc.
            simpl ((_ :: _) ++ _) in *.
            eapply channel_V_srcdstkport_update_dport with (dport := srcdport);eauto.
            unfold OS_Port_V_direction. rewrite ! nth_upd_neqrev' by lia;auto. }
         { rewrite <- Hsrckportl, <- Hsrckportvl.
           apply R_Kernelport_DomainPort_init_app in H1 as [H1_0 H1_1]; [ | lia].
           apply R_Kernelport_DomainPort_init_app.
           { rewrite Hlendpptrl1. rewrite !app_length. cbn. reflexivity.  }
           split.
           { apply nth_error_split in Hnthsrcdpptrl as (? & ? & ? & ?).
             subst dpptrl1.
             apply R_Kernelport_DomainPort_init_app in H1_0 as [H1_01  H1_02]; [ | lia].
             apply R_Kernelport_DomainPort_init_app;[lia | ].
             split;auto.
            eapply R_Kernelport_DomainPort_init_upd_headport with (dport := srcdport);eauto.
            unfold OS_Port_V_portID. rewrite ! nth_upd_neqrev' by lia;auto.
            unfold OS_Port_V_coreNum. rewrite ! nth_upd_neqrev' by lia;auto. } 
            eapply R_Kernelport_DomainPort_init_upd_headport with (dport := dport);eauto.
            unfold OS_Port_V_portID. rewrite ! nth_upd_neqrev' by lia;auto.
            unfold OS_Port_V_coreNum. rewrite ! nth_upd_neqrev' by lia;auto. }
         { split;auto. 
         assert (length (dportl11 ++ srcdport :: dportl12) = length(dportl11 ++
         update_nth_val 17 (update_nth_val 15 srcdport (Vptr srcqout')) (Vint32 srcqentries')
         :: dportl12)).
         { rewrite ! app_length. cbn. auto. }
         rewrite H88. apply nth_error_middle. 
         port_nth_val_solve.
         }
         {  split;auto.
            eapply RL_PortPtrList_upd with (ndstport := dport);auto.
            3: unfold OS_Port_V_nextPort;rewrite ! nth_upd_neqrev' by lia;auto.
            apply RL_PortPtrList_tail_null.
            apply RL_PortPtrList_tail_app.
            { rewrite app_length. cbn. rewrite Hlendpptrl1. rewrite app_length. cbn. auto. }
            split; [ | apply RL_PortPtrList_tail_null;auto ].
            apply nth_error_split in Hnthsrcdpptrl as (? & ? & ? & ?).
            subst dpptrl1.
            eapply RL_PortPtrList_tail_upd;eauto.
            lia.
            unfold OS_Port_V_nextPort;rewrite ! nth_upd_neqrev' by lia;auto.
            rewrite app_length. cbn. rewrite Hlendpptrl1. rewrite app_length. cbn. auto.
         }
         clear - H11 H65 H86.
         destruct dport; simpl in *; tryfalse.
         do 18 (destruct H11 as [? H11]; split; auto;
            destruct dport; simpl in *; tryfalse).
         clear - H86 H65.
         assert (Int.unsigned qentries' <= 65535) by lia. clear - H.
         pauto.
        * (* length (dportl1) < srcpid *)
        rewrite nth_error_app2 in Hnthsrcdportl by lia.
        assert ((srcpid - length dportl1) = S (srcpid - length dportl1 - 1))%nat by lia.
        rewrite H67 in Hnthsrcdportl.
        cbn [nth_error] in Hnthsrcdportl.
        hoare name lift (dmportp_sllseg dport_nextv Vnull dportl2) pre.
        eapply backward_rule1.
        { intros s Hs.
          eapply dmportp_sllseg_length_frm;eauto.
        }
        pure intro.
        destruct (nth_error dportmsgll2 (srcpid - length dportl1 - 1)) as  [ srcmsgl | ] eqn:  Hnthsrcmsg.
        2: { apply nth_error_None in Hnthsrcmsg. exfalso.
             rewrite <- H68 in Hnthsrcmsg. apply nth_error_None in Hnthsrcmsg. congruence. }
        apply nth_error_split in Hnthsrcmsg as (dportmsgll21 &  dportmsgll22 & ? & Hlendportmsgll21).
        subst.
        apply nth_error_split in Hnthsrcdportl as (dportl21 &  dportl22 & ? & Hlendportl21).
        subst.
        rewrite nth_error_app2 in Hnthsrcdpptrl by lia.
        rewrite <- Hlendpptrl1 in H67.
        rewrite H67 in Hnthsrcdpptrl.
        cbn [nth_error] in Hnthsrcdpptrl. clear H67. rename H68 into H67.
        rewrite Hlendpptrl1 in Hnthsrcdpptrl.
        cbn in Hdpptrl2.
        destruct Hdpptrl2 as [_ [hd [? Hdpptrl2]]].
        rewrite H10 in H68. inversion H68;subst hd. clear H68.
        eapply backward_rule1.
        eapply dmportp_sllseg_app_tail_frm with (dpptrl :=dpptrl2);eauto.
        apply RL_PortPtrList_tail_null;auto.
        cbn [dmportp_sllseg].
        pure intro.
        rename v'1 into srcdpr. rename v'2 into srcqstart. rename v'0 into srcnext_v.
        eapply backward_rule1.
        { intros s Hs.
          sep  lift 2%nat in Hs.
          eapply disj_star_elim_disj in Hs.
          destruct Hs.
          exfalso. sep normal in H68.  sep split in H68. rewrite H72 in Hsrcportmode. inversion Hsrcportmode.
          exact H68.
        }
        pure intro.
        rename v'2 into srcqout. rename v'1 into srcqin. rename v'0 into srcqend. rename v'3 into srcqsize. rename v'4 into srcqentries.
        rename v'5 into srcinvalid_msgl.
        simpl (nth_val' 2 _ ).
        unfold OS_K_Port_V_dmport  in Hsrcdp.  cbn in Hsrcdp. inversion Hsrcdp;subst x1.
        
        hoare name lift p_local pre.
        hoare name lift A_dom_lenv pre.
        hoare name lift (APortStruct (p_b, p_i)) pre.
        hoare name lift (Alvarmapsto port_ptr) pre.
        hoare name lift (Alvarmapsto srcPort) pre.
        hoare name lift Aop pre.
        eapply seq_rule.
        eapply backward_rule2.
        { eapply portaddtochannelproof_while1 with (dport := dport);eauto. }
        { intros s Hs. sep normal. sep eexists. sep autocancel.
          sep pauto. sep cancel dmportp_sllseg_qport_msg.
          rewrite gjb_common.update_nth_val_eq_same.
          rewrite gjb_common.update_nth_val_eq_same.
          sep pauto.
          unfold OS_Port_V_OSQEnd in *. eapply nth_val_nth_val'_some_eq. auto.
          unfold OS_Port_V_OSQEntries in *. eapply nth_val_nth_val'_some_eq.
          port_nth_val_solve.
        }
        pure intro.
        rename srcqout into srcqout_ori. rename srcqentries into srcqentries_ori. rename srcmsgl into srcmsgl_ori.
        rename v'0 into srcqout. rename v'1 into srcqentries. rename v'2 into  srcmsgl.
        rename srcinvalid_msgl into srcinvalid_msgl_ori. rename v'3 into srcinvalid_msgl.
        clear H77.
        pure intro.
        eapply aconj_aisfalse_rule.
        symbolic_exe_port.
        { sep split in H77.
          clear - H80 H79 H70.
          destruct srcdport; simpl in *; tryfalse.
          do 18 (destruct H70 as [? H70]; split;auto;
               destruct srcdport; simpl in *; tryfalse).
          clear - H80 H79.
          assert (Int.unsigned srcqentries <= 65535) by lia. clear - H.
          pauto. }
        { port_nth_val_solve.  }
        pure intro.
        assert (Int.ltu qsize srcqentries = false).
        { clear - H81. 
          destruct (Int.ltu qsize srcqentries);auto.
          destruct H81;tryfalse.
        }
        clear H81.
        hoare name lift Aie Ais Acs Aisr A_isr_is_prop pre.
        hoare name lift Aier pre.
        hoare lifts (7::8::9::10::11::18::19::12::13::14::15::nil)%nat pre.
        eapply forward_rule2.
        eapply backward_rule2.
        eapply portaddtochannelproof_while2 with (srcdport := (update_nth_val 17
        (update_nth_val 15 srcdport (Vptr srcqout))
        (Vint32 srcqentries)) ).
        22:{ intros s Hs.
             sep eexists.
             sep autocancel.
             sep cancel dmportp_sllseg_qport_msg.
             sep cancel dmportp_sllseg_qport_msg.
             sep cancel dmportp_sllseg_qport_msg.
             sep cancel dmportp_sllseg_qport_msg.
             sep split;eauto.
             instantiate (2:= dport).
             do 2 rewrite gjb_common.update_nth_val_eq_same.
             sep autocancel.
             do 2 rewrite gjb_common.update_nth_val_eq_same.
             exact Hs.
             eapply nth_val_nth_val'_some_eq;eauto.
             { eapply nth_val_nth_val'_some_eq.
               port_nth_val_solve. }
             eapply nth_val_nth_val'_some_eq;eauto.
             { eapply nth_val_nth_val'_some_eq.
               port_nth_val_solve. }
             { eapply nth_val_nth_val'_some_eq.
               port_nth_val_solve. }
             { eapply nth_val_nth_val'_some_eq.
               port_nth_val_solve. }
             instantiate (1:= srcqentries).
             rewrite H62 in Hqentrieseq0.
             inverts Hqentrieseq0.
             rewrite Int.unsigned_repr by (clear;mauto).
             lia. }
        all:eauto.
        { good_frm_sovler.   }
        all: port_nth_val_solve.
        { clear - H77 H79 H70.
         destruct srcdport; simpl in *; tryfalse.
         do 18 (destruct H70 as [? H70]; split; auto;
            destruct srcdport; simpl in *; tryfalse).
         assert (Int.unsigned srcqentries <= 65535) by lia.
         clear - H17. pauto. }
      
      intros s Hs. 
      sep normal in Hs. sep destruct Hs.
      rename x into srcqout'. rename x1 into srcqentries'.
      rename x6 into srcmsgl'. rename x8 into srcinvalid_msgl'.
      rename x10 into qin'. rename x11 into qentries'.
      rename x12 into msgl'. rename x13 into invalid_msgl'.
      eapply sep_aconj_r_aisfalse_to_astar in Hs.
      2:{ intros. sep_get_port_rv. sep split in H81. 
         clear - H84 H79 H70.
         destruct srcdport; simpl in *; tryfalse.
         do 18 (destruct H70 as [? H70]; split; auto;
            destruct srcdport; simpl in *; tryfalse).
         assert (Int.unsigned srcqentries' <= 65535) by lia.
         clear - H17. pauto.
      port_nth_val_solve. } 
      sep normal in Hs.
      sep name lift (Int.ltu ($ 0) srcqentries') in Hs.
      apply sep_pure_split in Hs as [? Hs].
      kport_combine kportvl3 kportvl4.
      2: { pauto. }
      sep name lift (APortStruct srcdpr) in Hs.
      rewrite update_nth_val_diff in Hs by lia.
      rewrite update_nth_val_same in Hs.
      rewrite update_nth_val_diff in Hs by lia.
      rewrite update_nth_val_same in Hs.
      exists (Vptr srcdpr).  
      exists (update_nth_val 17 (update_nth_val 14 dport (Vptr qin'))
      (Vint32 qentries')) (dportl1 ++  (update_nth_val 17 (update_nth_val 14 dport (Vptr qin'))
      (Vint32 qentries')) :: (dportl21  ++  (update_nth_val 17 (update_nth_val 15 srcdport (Vptr srcqout'))
      (Vint32 srcqentries')) :: dportl22)).
      exists (dportmsgll1 ++ msgl' :: (dportmsgll21 ++ srcmsgl' :: dportmsgll22)).
      sep name lift Channel_dstkport_get in Hs.
      apply Channel_dstkport_get_length in Hs.
      assert (∘ (Int.unsigned ($ 0)) = 0)%nat by   (clear;unfold nat_of_Z in *;mauto).
      rewrite H83 in Hs. rewrite H83.
      apply sep_pure_split in Hs as [? Hs].
      clear H83. destruct dstkportl as [ | ];[ | simpl in H84;tryfalse].
      cbn [Channel_dstkport_get] in *.
      apply sep_pure_split in Hs as [? Hs];subst x3.  clear H84.
      sep autocancel.
      rewrite Hsrckportl, Hsrckportvl.
      sep autocancel.
      sep name lift dmportp_sllseg dportlptr.
      eapply dmportp_sllseg_app'_frm;eauto.
      { eapply RL_PortPtrList_upd with (ndstport := dport);auto.
        2: unfold OS_Port_V_nextPort;rewrite ! nth_upd_neqrev' by lia;auto.
        apply nth_error_split in Hnthsrcdpptrl as (? & ? & ? & ?).
        subst dpptrl2.
        do 2 rewrite app_comm_cons.  do  2 rewrite app_assoc.
        eapply RL_PortPtrList_upd with (ndstport := srcdport);auto.
        do 2 rewrite <- app_assoc. do 2  rewrite <- app_comm_cons. auto.
        do 2 rewrite app_length. cbn. rewrite Hlendpptrl1. lia. 
        unfold OS_Port_V_nextPort;rewrite ! nth_upd_neqrev' by lia;auto.
      }
      cbn [dmportp_sllseg].
      sep normal.
      sep eexists.
      sep lift 6%nat.
      eapply disj_split.
      right.
      sep normal.
      sep eexists.
      sep name lift (APortStruct (p_b, p_i)) (dmportp_sllseg_qport_msg qout)  (dmportp_sllseg_qport_msg qin') in Hs.
      sep cancel dmportp_sllseg_qport_msg.
      sep cancel dmportp_sllseg_qport_msg.
      sep cancel APortStruct.
      sep split in Hs.
      sep split;eauto; try port_nth_val_solve.
      7,8: split;[port_nth_val_solve | try lia].
      { 
      eapply dmportp_sllseg_app'_frm;eauto.
      { apply nth_error_split in Hnthsrcdpptrl as (? & ? & ? & ?).
      subst dpptrl2.
      eapply RL_PortPtrList_upd;eauto.
      lia.
      unfold OS_Port_V_nextPort;rewrite ! nth_upd_neqrev' by lia;auto.
      }
      cbn [dmportp_sllseg].
      sep normal.
      sep eexists.
      sep lift 6%nat.
      eapply disj_split.
      right.
      sep normal.
      sep eexists.
      sep cancel dmportp_sllseg_qport_msg.
      sep cancel dmportp_sllseg_qport_msg.
      sep cancel APortStruct.
      sep split;eauto; try port_nth_val_solve.
      3,4: split;[port_nth_val_solve | try lia].
      { sep cancel (dmportp_sllseg srcnext_v).
         do 2 sep cancel dmportp_sllseg.
         rewrite <- Hsrckportvl, <-Hsrckportl.
         (* kport_V_OSEventPtr *)
         eapply kport_V_OSEventPtr_update_dport with (dport := dport).
         unfold OS_Port_V_direction. rewrite ! nth_upd_neqrev' by lia;auto.
         rewrite app_comm_cons in Hs. rewrite  app_assoc in Hs.
         rewrite app_comm_cons. rewrite  app_assoc.
         eapply kport_V_OSEventPtr_update_dport with (dport := srcdport);eauto.
         unfold OS_Port_V_direction. rewrite ! nth_upd_neqrev' by lia;auto.
          }
          clear - H84 H79 H70.
          destruct srcdport; simpl in *; tryfalse.
          do 18 (destruct H70 as [? H70]; split; auto;
             destruct srcdport; simpl in *; tryfalse).
          assert (Int.unsigned srcqentries' <= 65535) by lia.
          clear - H17. pauto.
      }
      {  
         rewrite <- Hsrckportl, <- Hsrckportvl.
         unfold channel_V_srcdstkport_aux.
         split;auto.
         eapply channel_V_srcdstkport_update_dport with (dport := dport).
         unfold OS_Port_V_direction. rewrite ! nth_upd_neqrev' by lia;auto.
         rewrite app_comm_cons in Hportch.  rewrite app_assoc in Hportch.
         rewrite app_comm_cons. rewrite app_assoc.
         eapply channel_V_srcdstkport_update_dport with (dport := srcdport);eauto.
         unfold OS_Port_V_direction. rewrite ! nth_upd_neqrev' by lia;auto. }
      { rewrite <- Hsrckportl, <- Hsrckportvl.
        apply R_Kernelport_DomainPort_init_app in H1 as [H1_0 H1_1]; [ | lia].
        apply R_Kernelport_DomainPort_init_app. 
        lia.
        split;auto.
        eapply R_Kernelport_DomainPort_init_upd_headport with (dport := dport);eauto.
        unfold OS_Port_V_portID. rewrite ! nth_upd_neqrev' by lia;auto.
        unfold OS_Port_V_coreNum. rewrite ! nth_upd_neqrev' by lia;auto.
        destruct H1_1 as [H1_11 H1_12].
        split;auto.
        apply nth_error_split in Hnthsrcdpptrl as (? & ? & ? & ?).
        subst dpptrl2.
        apply R_Kernelport_DomainPort_init_app in H1_12 as [H1_01  H1_02]; [ | lia].
        apply R_Kernelport_DomainPort_init_app;[lia | ].
        split;auto.
        eapply R_Kernelport_DomainPort_init_upd_headport with (dport := srcdport);eauto.
        unfold OS_Port_V_portID. rewrite ! nth_upd_neqrev' by lia;auto.
        unfold OS_Port_V_coreNum. rewrite ! nth_upd_neqrev' by lia;auto. }
      { split;auto.
        apply nth_error_middle.
        port_nth_val_solve.
      }
      {  split;auto.
         eapply RL_PortPtrList_upd with (ndstport := dport);auto.
         2: unfold OS_Port_V_nextPort;rewrite ! nth_upd_neqrev' by lia;auto.
         apply nth_error_split in Hnthsrcdpptrl as (? & ? & ? & ?).
         subst dpptrl2.
         do 2 rewrite app_comm_cons.  do  2 rewrite app_assoc.
         eapply RL_PortPtrList_upd with (ndstport := srcdport);auto.
         do 2 rewrite <- app_assoc. do 2  rewrite <- app_comm_cons. auto.
         do 2 rewrite app_length. cbn. rewrite Hlendpptrl1. lia. 
         unfold OS_Port_V_nextPort;rewrite ! nth_upd_neqrev' by lia;auto.
      }
      clear - H11 H65 H86.
      destruct dport; simpl in *; tryfalse.
      do 18 (destruct H11 as [? H11]; split; auto;
         destruct dport; simpl in *; tryfalse).
      clear - H86 H65.
      assert (Int.unsigned qentries' <= 65535) by lia. clear - H.
      pauto.
      }
      intros s Hs.
      destruct Hs as [Hs | Hs].
      sep normal in Hs.
      sep destruct Hs.
      sep normal. sep eexists.
      sep autocancel.
      sep auto.
      {  exfalso.
         sep normal in Hs.
         sep destruct Hs.
         sep split in Hs.
         destruct H55 as [ | [[? ?] ?] ];subst x1.
         { rewrite Hsrckportvl in Hportch. rewrite Hsrckportl in Hportch.
         apply channel_V_srcdstkport_app in  Hportch as [Hportch1 [[ | [? [? [Hportchsrc Hportchdst]]]] Hportch2]];auto.
         { cbn in H55. simpljoin1. tryfalse. }
         inversion H55;subst x.
         unfold channel_V_src_P in Hportchsrc.
         cbn in Hportchsrc. 
         specialize (Hportchsrc _ (ltac:(reflexivity))).
         clear s H60 H61 H62 H63 H64 H65 H66 H49 Hs.
         simpljoin1.
         rewrite Hsrckportvl in Hnodupkp.
         eapply nth_error_nodup_midlle in H49;eauto.
         subst x.  rewrite <- H51 in H60. erewrite nth_error_middle in H60.
         inversion H60;subst x1.
         cbn in H62. inversion H62.  }
         clear - H49.
         cbn in H49.
         destruct H49;tryfalse.
      }
      + intros s Hs.
        destruct Hs as [Hs | Hs].
        *  sep normal in Hs.
           sep destruct Hs.
           sep normal.
           sep eexists.
           sep autocancel.
           sep split in Hs.
           sep split;eauto.
           simpljoin1.
           splits;auto.
        *  sep normal in Hs.
           sep normal.
           sep name lift Channel_dstkport_get in Hs.
           apply Channel_dstkport_get_length in Hs.
           assert (∘ (Int.unsigned ($ 0)) = 0)%nat by   (clear;unfold nat_of_Z in *;mauto).
           rewrite H49 in Hs. rewrite H49.
           apply sep_pure_split in Hs as [? Hs].
           destruct dstkportl; [ | simpl in H50;tryfalse].
           cbn [Channel_dstkport_get] in *.
           apply sep_pure_split in Hs as [? Hs].
           subst x3.
           sep eexists.
           sep autocancel.
           port_combine.
           sep split;eauto.
           sep pauto.
           clear Hs.
           unfold RLH_PortPtrINecb.
           split;auto.
           split;eauto.
           rewrite nth_error_middle;eauto.
           clear - H6.
           unfold DomainportNode_P, Domainport_direction_P in H6.
           simpljoin1. auto. 
   }
   hoare forward.
   -  subst H3.
      eapply forward_rule2.
      eapply backward_rule2.
      eapply portaddtochannelproof_incore_destionation_endpart1;[ idtac | eauto .. ].
      4:{ intros s Hs.
      sep normal in Hs. sep destruct Hs.
      sep normal. sep eexists.
      sep autocancel.
      exact Hs. }
      { can_change_aop_solver'. } 
      { erewrite nth_error_middle. eauto. }
      { clear - H6.
      unfold DomainportNode_P, Domainport_direction_P in H6.
      simpljoin1. auto. }
      intros s Hs.
      sep normal in Hs. sep normal. sep eexists.
      sep autocancel. 
      sep auto.
   -  subst H3.
      eapply forward_rule2.
      eapply backward_rule2.
      eapply portaddtochannelproof_incore_destionation_endpart2 
      with (pid := pid) (portchanid := portchanid) (kportvl1 := kportvl1);[ idtac | eauto .. ].
      2:{ intros s Hs.
      sep normal in Hs. sep destruct Hs.
      sep normal. sep eexists.
      sep autocancel.

      instantiate (1:= EX x, LV srcPort @ OS_Port ∗ |-> x **
      LV port_ptr @ OS_Port ∗ |-> Vptr (p_b, p_i) **
      LV resource_get_res @ char_t |-> res_v **
      ChannelNode chanvl1 chanl1 chandstportll1 **
      ChannelNode chanvl2 chanl2 chandstportll2 **
      GV OSDomainPortPtrList @ OS_Port ∗ |-> dportlptr **
      LV re @ OS_Port ∗ |-> Vnull **
      GV OSRunning @ char_t |-> Vint32 Int.zero **
      PV err_l @ char_t |-> Vint32 err_v **
      LV err @ (char_t) ∗ |-> Vptr err_l **
      Aie false **
      Ais nil **
      Acs (true :: nil) **
      Aisr empisr **
      A_isr_is_prop **
      Aier ier **
      GAarray OSChannelIDTbl (Tarray OS_Channel ∗ ∘ CHANNEL_NUMS) (chanvl1 ++ Vptr (v', Int.zero) :: chanvl2) **
      GAarray OSKernelPortIDTbl (Tarray OS_K_Port ∗ ∘ PORT_NUMS) (kportvl1 ++ Vptr (kp_b, Int.zero) :: kportvl2) **
      GV ksCurDomain @ long |-> Vint32 curdomain **
      GV ksDomains @ OSdomain_t ∗ |-> Vptr domainv **
      Astruct (get_off_addr domainv (Int.mul ($ 34) curdomain)) OSdomain_t domainvl **
      GV OSPortAttrTbl @ OSport_attr_t ∗ |-> Vptr portattrv **
      Astruct (get_off_addr portattrv (Int.mul ($ 12) ($ Z.of_nat pid))) OSport_attr_t portattrvl **
      LV flag @ long |-> (V$ 1) **
      AOSKernelPortFreeList kportfptr kportfl **
      AOSChannelFreeList chanfptr chanfl **
      OtherPortPtrList otherppl otherpl othermsgll **
      EvtInv ecbls p1 (tcbl1 ++ tcbcur :: tcbl2) tcbls vhold scapl mcapl qcapl **
      AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls **
      [|val_inj (notint (val_inj (if Int.eq i4 ($ 0) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)))) = Vint32 Int.zero \/
        val_inj (notint (val_inj (if Int.eq i4 ($ 0) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)))) = Vnull|]).
      sep eexists.
      exact Hs. }
      { can_change_aop_solver'. } 
      intros s Hs.
      sep normal in Hs. 
      sep destruct Hs.
      sep normal. sep eexists.
      sep autocancel. 
      sep auto.   
Qed.


