Require Import include_frm.
Require Import os_code_defs.
Require Import os_inv.
Require Import seplog_tactics.
Require Import ucos_frmaop.

Definition PartitionInv_part1 ecbls :=
  (EX dportlptr dportl dportmsgll dportls1 dpptrl
      otherppl otherpl othermsgll dportls2 dportls
      kportvl kportl kportls kportfptr kportfl
      chanvl chanl chandstkportll chanls chanfptr chanfl cportlptr cportpl,
        AOSDomainPortPtrList dportlptr dportl dportmsgll **
        Hdomainportl dportls ** 
        [| join dportls1 dportls2 dportls |] **
        [| RL_PortAttr dpptrl dportl |] **
        [| RLH_PortPtrINecb dportlptr dportl dpptrl ecbls |] **
        [| RLH_Domainportl dportlptr dportl dportmsgll dportls1|] **
        AOSKernelPortIDTbl kportvl kportl **
        Hkernelport kportls **
        [| RLH_Kernelport kportvl kportl kportls|] ** 
        AOSChannelIDTbl chanvl chanl chandstkportll**
        Hchannell chanls **
        [| RLH_Channel otherppl chanvl chanl chandstkportll chanls kportls dportls1 dportls2 |] **
        AOSKernelPortFreeList kportfptr kportfl **
        AOSChannelFreeList chanfptr chanfl **
        [| R_Kernelport_DomainPort kportvl kportl dportl dpptrl |] **
        [| R_KernelPortIDTbl_ChannelIDTbl kportvl kportl chanvl chanl chandstkportll kportls dportls1 dportls2 |] **
        OtherPortPtrList otherppl otherpl othermsgll **
        [| RLH_OtherPortPtrList otherppl otherpl othermsgll dportls2 |] **
        [| nodup_dport kportls |] **
        Hcoreportpl cportpl **
        AOSCorePortPtrList cportlptr cportpl dportls1).

Definition PartitionInv_part2 :=
  (EX rtsk_vll absrtsk ucosf absucosf dom2index absdom2index ksdomscdidx ksdomscdlen kscurd kslastd
          ksdomt ksdschedule ksdscd iscp intpmuxvl intpmux ksdom absks iscb systm ossp
          cpn partareavl partarea partid2domvl portattrls,
        ARootTaskStk rtsk_vll absrtsk **
        AMPAXs ** AXMPFR ** AMDMAER **
        AucosConf ucosf absucosf ** Hucosconf absucosf **
        Adomain2index dom2index absdom2index **
        AKsDSchdidx ksdomscdidx ** HKsDSchdidx ksdomscdidx **
        AKsDSchdlen ksdomscdlen ** HKsDSchdlen ksdomscdlen **
        AKsCurDomain kscurd ** HKsCurDomain kscurd **
        AKsLastDomain kslastd ** HKsLastDomain kslastd **
        AKsDomainTime ksdomt ** HKsDomainTime ksdomt **
        AKsDomSchedule ksdschedule ksdscd **
        AisChangePartion iscp **
        AIntPartMux intpmuxvl intpmux **
        AKsDomains ksdom absks ** HKsDomains absks **
        AisCoreBoot iscb **
        AsystemStck' systm **
        AOSSystemSP ossp **
        ACorepartnum cpn ** [| R_Cpartnum_Dom2idx_P cpn dom2index |] **
        APortnumcur **
        APartArea partareavl partarea **
        APartID2Dom partid2domvl ** AOSPortAttrTbl' portattrls).

Ltac trycancel_PartitionInv1 :=
try sep cancel AOSDomainPortPtrList;
try sep cancel AOSKernelPortIDTbl;
try sep cancel AOSChannelIDTbl;
try sep cancel AOSKernelPortFreeList;
try sep cancel AOSChannelFreeList;
try sep cancel OtherPortPtrList;
try sep cancel AOSCorePortPtrList.

Ltac trycancel_PartitionInv2 :=
try sep cancel ARootTaskStk;
try sep cancel AMPAXs;
try sep cancel AXMPFR;
try sep cancel AMDMAER;
try sep cancel AucosConf;
try sep cancel Adomain2index;
try sep cancel AKsDSchdidx;
try sep cancel AKsDSchdlen;
try sep cancel AKsCurDomain;
try sep cancel AKsLastDomain;
try sep cancel AKsDomainTime;
try sep cancel AKsDomSchedule;
try sep cancel AisChangePartion;
try sep cancel AIntPartMux;
try sep cancel AKsDomains;
try sep cancel AisCoreBoot;
try sep cancel AsystemStck';
try sep cancel AOSSystemSP;
try sep cancel ACorepartnum;
try sep cancel APortnumcur;
try sep cancel APartArea;
try sep cancel APartID2Dom;
try sep cancel AOSPortAttrTbl'.

Ltac trycancel_PartitionInv :=
trycancel_PartitionInv1; trycancel_PartitionInv2.

Lemma PartitionInv_eq:
forall ecbls,
    PartitionInv ecbls <==> PartitionInv_part1 ecbls ** PartitionInv_part2.
Proof.
unfold PartitionInv.
unfold PartitionInv_part1.
unfold PartitionInv_part2.
intros.
split; introv Hsat; sep normal in Hsat; sep destruct Hsat; sep normal; sep eexists.
trycancel_PartitionInv.
sep auto; eauto.
trycancel_PartitionInv.
sep auto; eauto.
Qed.

Lemma fold_PartitionInv_part1:
forall s P ecbls dportlptr dportl dportmsgll dportls1 dpptrl
      otherppl otherpl othermsgll dportls2 dportls
      kportvl kportl kportls kportfptr kportfl
      chanvl chanl chandstkportll chanls chanfptr chanfl cportlptr cportpl,
join dportls1 dportls2 dportls ->
RL_PortAttr dpptrl dportl ->
RLH_PortPtrINecb dportlptr dportl dpptrl ecbls ->
RLH_Domainportl dportlptr dportl dportmsgll dportls1->
RLH_Kernelport kportvl kportl kportls ->
RLH_Channel otherppl chanvl chanl chandstkportll chanls kportls dportls1 dportls2 ->
R_Kernelport_DomainPort kportvl kportl dportl dpptrl ->
R_KernelPortIDTbl_ChannelIDTbl kportvl kportl chanvl chanl chandstkportll kportls dportls1 dportls2 ->
RLH_OtherPortPtrList otherppl otherpl othermsgll dportls2 ->
nodup_dport kportls ->
s |= AOSDomainPortPtrList dportlptr dportl dportmsgll **
        Hdomainportl dportls ** 
        AOSKernelPortIDTbl kportvl kportl **
        Hkernelport kportls **
        AOSChannelIDTbl chanvl chanl chandstkportll**
        Hchannell chanls **
        AOSKernelPortFreeList kportfptr kportfl **
        AOSChannelFreeList chanfptr chanfl **
        OtherPortPtrList otherppl otherpl othermsgll **
        Hcoreportpl cportpl **
        AOSCorePortPtrList cportlptr cportpl dportls1 ** P ->
   s |= PartitionInv_part1 ecbls ** P.
Proof.
unfold PartitionInv_part1.
intros.
sep pauto; eauto.
Qed.

Lemma fold_PartitionInv_part2:
forall s P rtsk_vll absrtsk ucosf absucosf dom2index absdom2index ksdomscdidx ksdomscdlen kscurd kslastd
          ksdomt ksdschedule ksdscd iscp intpmuxvl intpmux ksdom absks iscb systm ossp
          cpn partareavl partarea partid2domvl portattrls,
   R_Cpartnum_Dom2idx_P cpn dom2index ->
   s |=ARootTaskStk rtsk_vll absrtsk **
          AMPAXs ** AXMPFR ** AMDMAER **
          AucosConf ucosf absucosf ** Hucosconf absucosf **
          Adomain2index dom2index absdom2index **
          AKsDSchdidx ksdomscdidx ** HKsDSchdidx ksdomscdidx **
          AKsDSchdlen ksdomscdlen ** HKsDSchdlen ksdomscdlen **
          AKsCurDomain kscurd ** HKsCurDomain kscurd **
          AKsLastDomain kslastd ** HKsLastDomain kslastd **
          AKsDomainTime ksdomt ** HKsDomainTime ksdomt **
          AKsDomSchedule ksdschedule ksdscd **
          AisChangePartion iscp **
          AIntPartMux intpmuxvl intpmux **
          AKsDomains ksdom absks ** HKsDomains absks **
          AisCoreBoot iscb **
          AsystemStck' systm **
          AOSSystemSP ossp **
          ACorepartnum cpn **
          APortnumcur **
          APartArea partareavl partarea **
          APartID2Dom partid2domvl ** AOSPortAttrTbl' portattrls** P ->
   s |= PartitionInv_part2 ** P.
Proof.
unfold PartitionInv_part2.
intros.
sep pauto; eauto.
Qed.

Lemma unfold_PartitionInv_frm:
forall ecbls P,
    PartitionInv ecbls ** P ==>
    PartitionInv_part1 ecbls ** PartitionInv_part2 ** P.
Proof.
unfold PartitionInv.
unfold PartitionInv_part1.
unfold PartitionInv_part2.
introv Hsat; sep normal in Hsat; sep destruct Hsat; sep normal; sep eexists.
trycancel_PartitionInv.
sep auto; eauto.
Qed.

Lemma fold_PartitionInv_frm:
forall ecbls P,
    PartitionInv_part1 ecbls ** PartitionInv_part2 ** P
    ==> PartitionInv ecbls ** P.
Proof.
unfold PartitionInv.
unfold PartitionInv_part1.
unfold PartitionInv_part2.
introv Hsat; sep normal in Hsat; sep destruct Hsat; sep normal; sep eexists.
trycancel_PartitionInv.
sep auto; eauto.
Qed.

Lemma can_change_aop_PartitionInv_part1:
  forall ecbls,
    can_change_aop (PartitionInv_part1 ecbls).
Proof.
  intros.
  unfold PartitionInv_part1.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_PartitionInv_part1: can_change_aop.

Lemma can_change_aop_PartitionInv_part2:
    can_change_aop (PartitionInv_part2). 
Proof.
  intros.
  unfold PartitionInv_part2.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_PartitionInv_part2: can_change_aop.

Lemma good_frm_PartitionInv_part1:
forall  ecbls, GoodFrm (PartitionInv_part1 ecbls).
Proof.
  intros.
  unfold PartitionInv_part1.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_PartitionInv_part1  : good_frm_lemmas.

Lemma good_frm_PartitionInv_part2:
    GoodFrm (PartitionInv_part2).
Proof.
  intros.
  unfold PartitionInv_part2.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_PartitionInv_part2  : good_frm_lemmas.

