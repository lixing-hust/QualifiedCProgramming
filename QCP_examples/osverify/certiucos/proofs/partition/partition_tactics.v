Require Import ucos_include.
Require Import Lia.


Require Import aux_pureLib.
Require Import corecommu_tactics.
Require Import partition_rules.
Require Import partition_symrules.
Require Import partition_seprules.
Require Import partinv_lemmas.

Ltac sep_get_port_rv :=
  match goal with
    | H: ?s |= _ 
      |- ?s |= Rv port_ptr ′ → coreNum @ ?t == ?v =>
        sep name lift APortStruct in H; sep name lift port_ptr in H;
        eapply port_coreNum_rv;[eauto | eauto | exact H]
    | H: ?s |= _ 
      |- ?s |= Rv port_ptr ′ → OSEventType @ ?t == ?v =>
        sep name lift APortStruct in H; sep name lift port_ptr in H;
        sep name lift EvtInv in H;
        eapply port_OSEventType_rv;[eauto | eauto | eauto | exact H]
    | H: ?s |= _ 
      |- ?s |= Rv OSTCBCur ′ → OSTCBY ==ₑ port_ptr ′ → domain @ ?t == ?v =>
        sep name lift A_dom_lenv in H;sep name lift AOSTCBList in H;
        sep name lift (Alvarmapsto port_ptr) in H;sep name lift APortStruct in H;
        eapply tcby_port_domain_rv;[eauto | eauto | eauto |  eauto |  | exact H];simpl;auto 
    | H : ?s |= _ 
      |- ?s |= Rv port_ptr ′ → os_code_defs.direction @ ?t == ?v =>
        sep name lift APortStruct in H;sep name lift (Alvarmapsto port_ptr) in H;
        eapply port_direction_rv;[eauto | eauto | exact H]
    | H : ?s |= _ 
      |- ?s |= Rv port_ptr ′ → mode @ ?t == ?v =>
        sep name lift APortStruct in H;sep name lift (Alvarmapsto port_ptr) in H;
        eapply port_mode_rv;[eauto | eauto | exact H]
    | H: ?s |= _ 
      |- ?s |= Rv port_ptr ′ → portID @ ?t == ?v =>
        sep name lift APortStruct in H; sep name lift (Alvarmapsto port_ptr) in H;
        eapply port_id_rv;[eauto | eauto | exact H]
    | H: ?s |= ?P
      |- ?s |= Rv ?x ′ → OSQEntries @ ?t == ?v =>
          match P with 
          | context [LV x @ OS_Port ∗ |-> Vptr ?pptr] =>
        sep name lift (APortStruct pptr) in H; sep name lift (Alvarmapsto x) in H;
        eapply port_QEntries_rv;[ | | exact H];eauto 
        end
    | H: ?s |= ?P 
      |- ?s |= Rv ?x ′ → OSQSize @ ?t == ?v =>
          match P with 
          | context [LV x @ OS_Port ∗ |-> Vptr ?pptr] =>
          sep name lift (APortStruct pptr) in H; sep name lift (Alvarmapsto x) in H;
          eapply port_QSize_rv;[ | | exact H];eauto 
          end
    | H: ?s |= ?P
      |- ?s |= Rv (?x ′ → OSQOut) → len @ ?t == ?v =>
        match P with 
        | context [LV x @ OS_Port ∗ |-> Vptr ?pptr] => 
        match P with 
        | context [APortStruct pptr ?dport] =>
          match goal with 
          | H0 : OS_Port_V_OSQOut dport = Some (Vptr ?qout) |- _ =>
          match P with 
          | context [dmportp_sllseg_qport_msg qout ?qin ?qstart ?qend ?n (?msg :: ?msgl)] =>
            sep name lift (dmportp_sllseg_qport_msg  qout qin) in H;
            sep name lift (APortStruct pptr dport) in H; sep name lift (Alvarmapsto x) in H;
            eapply port_OSQOut_len_rv;[ | exact H0 | exact H];eauto
          | _ => sep name lift (Aptrmapsto qout) in H;
                sep name lift (APortStruct pptr dport) in H; sep name lift (Alvarmapsto x) in H;
                eapply port_OSQOut_len_rv';[idtac | idtac | exact H0 | exact H];eauto end
        end end end 
    | H: ?s |= ?P
      |- ?s |= Rv (?x ′ → OSQOut) → data @ ?t == ?v => 
        match P with 
          | context [LV x @ OS_Port ∗ |-> Vptr ?pptr] => 
          match P with 
          | context [APortStruct pptr ?dport] =>
            match goal with 
            | H0 : OS_Port_V_OSQOut dport = Some (Vptr ?qout) |- _ =>
        match P with 
        | context [dmportp_sllseg_qport_msg qout ?qin ?qstart ?qend ?n (?msg :: ?msgl)] =>
          sep name lift (dmportp_sllseg_qport_msg qout qin) in H;
          sep name lift (APortStruct pptr dport) in H; sep name lift (Alvarmapsto x) in H;
          eapply port_OSQOut_data_rv;[ |  | exact H];eauto
        | _ => sep name lift (Aptrmapsto qout) in H;
               sep name lift (APortStruct pptr dport) in H; sep name lift (Alvarmapsto x) in H;
               eapply port_OSQOut_data_rv';[ |  | exact H];eauto end
        end end end 
    | H: ?s |= ?P 
      |- ?s |= Rv (port_ptr ′ → OSQIn) → len @ ?t == ?v =>
        match P with 
        | context [LV port_ptr @ OS_Port ∗ |-> Vptr ?pptr] => 
        match P with 
        | context [APortStruct pptr ?dport] =>
          match goal with 
          | H0 : OS_Port_V_OSQIn ?dport = Some (Vptr ?qin) |- _ =>
        match P with 
        | context [dmportp_sllseg_qport_msg qin ?qout ?qstart ?qend ?n (?msg :: ?msgl)] =>
          sep name lift (dmportp_sllseg_qport_msg qin qout) in H;
          sep name lift (APortStruct pptr dport) in H; sep name lift (Alvarmapsto port_ptr) in H;
          eapply port_OSQIn_len_rv;[ |  | exact H];eauto 
        | _ => sep name lift (Aptrmapsto qin) in H;
               sep name lift (APortStruct pptr dport) in H; sep name lift (Alvarmapsto port_ptr) in H;
               eapply port_OSQIn_len_rv';[ |  | exact H];eauto end
        end end end 
    | H: ?s |= ?P, H0 : OS_Port_V_OSQIn ?dport = Some (Vptr ?qin) 
      |- ?s |= Rv (port_ptr ′ → OSQIn) → data @ ?t == ?v => 
        match P with 
        | context [dmportp_sllseg_qport_msg qin ?qout ?qstart ?qend ?n (?msg :: ?msgl)] =>
          sep name lift dmportp_sllseg_qport_msg in H;
          sep name lift APortStruct in H; sep name lift (Alvarmapsto port_ptr) in H;
          eapply port_OSQIn_data_rv;[eauto | eauto | exact H]
        end
    | H: ?s |= ?P, H0 : OS_Channel_V_srcPort ?chan = Some (Vptr ?kpptr) 
      |- ?s |= Rv (channel ′ → srcPort) → dmport @ ?t == ?v => 
        match P with 
        | context [Astruct ?chanptr OS_Channel chan] =>
          sep name lift (Astruct' kpptr OS_K_Port_Seg_dls) in H;
          sep name lift (Astruct chanptr OS_Channel chan) in H;
          sep name lift (Alvarmapsto channel) in H;
          eapply channel_srcport_dmport_rv;[ |  | eauto | exact H];eauto
        end
    | H: ?s |= ?P 
      |- ?s |= Rv port_ptr ′ → OSQIn @ ?t == ?v =>
        match P with 
        | context [LV port_ptr @ OS_Port ∗ |-> Vptr ?pptr] => 
        match P with 
        | context [APortStruct pptr ?dport] =>
        sep name lift (APortStruct pptr dport) in H; sep name lift (Alvarmapsto port_ptr) in H;
        eapply port_QIn_rv;[ |  | exact H];eauto
        end end 
    | H: ?s |= ?P 
      |- ?s |= Rv ?x ′ → OSQOut @ ?t == ?v =>
        match P with 
        | context [LV x @ OS_Port ∗ |-> Vptr ?pptr] =>
        sep name lift (APortStruct pptr) in H; sep name lift (Alvarmapsto x) in H;
        eapply port_QOut_rv;[ |  | exact H];eauto 
        end
    | H: ?s |= ?P 
      |- ?s |= Rv ?x ′ → OSQEnd @ ?t == ?v =>
        match P with 
        | context [LV x @ OS_Port ∗ |-> Vptr ?pptr] =>
        sep name lift (APortStruct pptr) in H; sep name lift (Alvarmapsto x) in H;
        eapply port_QEnd_rv;[ |  | exact H];eauto
        end
    | H: ?s |= ?P 
      |- ?s |= Rv ?x ′ → OSQStart @ ?t == ?v =>
        match P with 
        | context [LV x @ OS_Port ∗ |-> Vptr ?pptr] =>
        sep name lift (APortStruct pptr) in H; sep name lift (Alvarmapsto x) in H;
        eapply port_QStart_rv;[ |  | exact H];eauto
        end
    | H: ?s |= ?P 
      |- ?s |= Rv os_code_defs.kport ′ → channel @ ?t == ?v => 
        match P with 
        | context [Astruct' ?kpptr OS_K_Port_Seg_dls (firstn 6 ?kport)] =>
        sep name lift (Astruct' kpptr OS_K_Port_Seg_dls (firstn 6 kport)) in H; sep name lift (Alvarmapsto os_code_defs.kport) in H;
        eapply kport_channel_rv;[eauto | exact H]
        end 
    | H: ?s |= _ 
      |- ?s |= Rv OSKernelPortIDTbl ′ [port_ptr ′ → portID] @ ?t == ?v =>
        sep name lift (GAarray OSKernelPortIDTbl) in H; sep name lift A_dom_lenv in H;
        eapply symbolic_lemmas.array_member_rv_g;[exact H | cbn;auto | cbn;auto | sep_get_port_rv | 
          eauto | eauto | clear; mauto | 
          idtac .. ]
    | |- ?s |= Rv 〈 Int16u 〉 (′ ?z) @ ?t == ?v => 
        eapply cast_rv_tint32_tint16;[sep_get_rv | simpl;auto]
    | |- _ |= Rv (ebinop ?bop ?e1 ?e2) @ _ == _ =>
      eapply symbolic_lemmas.bop_rv;
        [ sep_get_port_rv
        | sep_get_port_rv
        | simpl; auto
        | unfold val_inj; try rewrite Int.eq_true;pauto
        | simpl; auto ]
    | |- _ |= Rv (eunop ?uop ?e) @ _ == _ =>
      eapply symbolic_lemmas.uop_rv;
        [ sep_get_port_rv
        | simpl; auto
        | unfold val_inj; try rewrite Int.eq_true;pauto
        | simpl; auto ]
    | |- _ |= Rv (eaddrof (earrayelem ?e1 ?e2)) @ _ == _ =>
      eapply symbolic_lemmas.addrof_array_elem_rv; 
        [ sep_get_port_rv
        | sep_get_port_rv
        | intuition eauto 
        | intuition eauto ]
    | |- _ => (sep normal; sep eexists; sep_get_rv) ||  idtac end.
Ltac symbolic_exe_port := let s := fresh "s" in let H := fresh "H" in intros s H; sep_get_port_rv.


Ltac rename_partitionvars:=
  match goal with 
  | |- context [AOSDomainPortPtrList ?v ?v1 ?v2] => rename v into dportlptr; rename v1 into dportl; rename v2 into dportmsgll end;
  match goal with 
  | |- context [Hdomainportl ?v] => rename v into dportls  end;
  match goal with 
  | |- context [AOSKernelPortIDTbl ?v ?v'] => rename v into kportvl; rename v' into kportl end;
  match goal with 
  | |- context [Hkernelport ?v] => rename v into kportls end;
  match goal with 
  | |- context [AOSChannelIDTbl ?v ?v0 ?v1] => rename v into chanvl ; rename v0 into chanl; rename v1 into chandstportll end;
  match goal with 
  | |- context [Hchannell ?v] => rename v into chanls end;
  match goal with 
  | H: context [RL_PortAttr ?v _] |- _ => rename v into dpptrl end;
  match goal with 
  | H: context [RH_TCBList_ECBList_P ?v _ _ ] |- _ => rename v into ecbls end;
  match goal with 
  | H: context [RLH_OtherPortPtrList ?v0 ?v1 ?v2 ?v3] |- _ => 
    rename v0 into otherppl; rename v1 into otherpl; rename v2 into othermsgll; rename v3 into dportls2 end;
  match goal with 
  | H: context [RLH_OtherPortPtrList _ _ _  ?v3], H0: join ?v1 ?v3 ?v2 |- _ => rename v1 into dportls1 end.
Ltac partition_enter := hoare forward prim; pure intro; hoare name lift PartitionInv pre;
                      unfold PartitionInv;pure intro;rename_partitionvars.

Ltac partition_exit := hoare forward prim;
    match goal with 
    | H: ?s |= ?p |- ?s |= _ => 
      match p with 
      | context [ ([|OS_Port_V_mode ?dport = Some (Vint32 (ZToInt SAMPLE))|] **
      dmportp_sllseg_sampleport_msg ?v ?msgl \\// ?q)] => sep name lift ([|OS_Port_V_mode dport = Some (Vint32 (ZToInt SAMPLE))|] **
      dmportp_sllseg_sampleport_msg v msgl \\// q) in H end;
      sep name lift APortStruct in H;
      match p with 
      | context [ dmportp_sllseg ?v Vnull] => sep name lift (dmportp_sllseg v Vnull) in H end;
      match p with 
      | context [ dmportp_sllseg ?v (Vptr ?v')] => sep name lift (dmportp_sllseg v (Vptr v')) in H end;
      eapply dmportp_sllseg_compose in H;eauto;
      sep autocancel;unfold PartitionInv,AOSDomainPortPtrList;
      sep normal;sep eexists;sep pauto
    | |- _ => unfold PartitionInv;sep pauto  end;
    match goal with 
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} => idtac 
    | |- RLH_PortPtrINecb _ _ _ _ =>  solve [eauto || unfold RLH_PortPtrINecb;splits;eauto] 
    | |- RH_CurTCB ?tid ?tcbls => solve [eauto || unfold RH_CurTCB;eauto]
    | |- GoodFrm (_ ** _ ) => go  (* 为了排除 GoodFrm ?frm 还没有填的情况 *)
    | |- _ => eauto 
    end.

Ltac partition_absrulestac r :=
    hoare name lift osdomainportid pre;
    hoare abscsq;[apply noabs_oslinv | eapply r;eauto;go | ].

Ltac split_portlist := 
    match goal with 
    | H4: RL_PortPtrList ?dportlptr ?dportl ?dpptrl, 
      H5: RLH_Domainportl ?dportlptr ?dportl ?dportmsgll ?dportls,
      Hdp : get ?dportls ?p_v = Some ?port
     |- _ =>
    let n := fresh "n" in let dport := fresh "dport" in let msgl := fresh "msgl" in 
    let h1 := fresh "H" in let h2 := fresh "H" in let h3 := fresh "H" in let h4 := fresh "H" in
  assert (exists n dport msgl, nth_error dportl n = Some dport /\ nth_error dportmsgll n = Some msgl /\ 
                               nth_error dpptrl n = Some p_v /\ DomainportNode_P dport port msgl) as (n & dport & msgl & h1 & h2 & h3 & h4);
  [ clear - H4 H5 Hdp; eapply RLH_Domainportl_abs_getsome;eauto |  
    let dportl1 := fresh "dportl1" in let dportl2 := fresh "dportl2" in 
    apply nth_error_split in h1 as (dportl1 & dportl2 & ? & ?);
    let dportmsgll1 := fresh "dportmsgll1" in let dportmsgll2 := fresh "dportmsgll2" in 
    apply nth_error_split in h2 as (dportmsgll1 & dportmsgll2 & ? & ?);
    subst dportl dportmsgll ]
  end.

Ltac partition_destruct H :=
  match type of H with
  | exists (_ : ?A), _ =>  
      match A with 
      | int32 => let x := fresh "i" in destruct H as [x H];partition_destruct H
      | addrval => let x := fresh "p" in destruct H as [x H];partition_destruct H
      | vallist  => let x := fresh "l" in destruct H as [x H];partition_destruct H
      | absdomainport.B => let x := fresh "dport" in destruct H as [x H];partition_destruct H
      | port_coreNum  => let x := fresh "pcn" in destruct H as [x H];partition_destruct H
      | port_domain => let x := fresh "pd" in destruct H as [x H];partition_destruct H
      | port_id => let x := fresh "pid" in destruct H as [x H];partition_destruct H
      | direction => let x := fresh "pdir" in destruct H as [x H];partition_destruct H
      | port_status => let x := fresh "pst" in destruct H as [x H];partition_destruct H
      | port_intick  => let x := fresh "pin" in destruct H as [x H];partition_destruct H
      | port_outick  => let x := fresh "pout" in destruct H as [x H];partition_destruct H
      | Portt  => let x := fresh "pt" in destruct H as [x H];partition_destruct H
      | _ => destruct H as [? H];partition_destruct H
      end
  | _ /\ _ => let H0 := fresh "H" in 
              destruct H as [H H0];
              partition_destruct H;
              partition_destruct H0
  | _ => idtac
  end.

Ltac port_nth_val_solve:=
  unfold OS_Port_V_OSQEntries, OS_Port_V_OSQIn, OS_Port_V_OSQOut, OS_Port_V_OSQStart,
  OS_Port_V_OSQEnd, OS_Port_V_OSQSize, OS_Port_V_nextPort, OS_Port_V_maxMsgSize, 
  OS_Port_V_mode, OS_Port_V_direction, OS_Port_V_portID, OS_Port_V_domain, OS_Port_V_coreNum in *;
  repeat (eauto; match goal with
  | |- nth_val ?n (update_nth_val ?n ?l ?v) = _ => eapply update_nth
  | |- nth_val ?n (update_nth_val ?m ?l ?v) = _ => eapply nth_upd_neqrev;[lia| ]
  end
  ).

Ltac can_change_aop_solver' :=
  can_change_aop_solver;
  try (split; can_change_aop_solver).



(* 下面两个 分区临界区操作 转化了partition inv *)
Ltac partition_enter_trinv:= hoare forward prim; pure intro; hoare name lift PartitionInv pre;
  eapply backward_rule1;[ apply unfold_PartitionInv_frm | unfold PartitionInv_part1;pure intro;rename_partitionvars].

Ltac partition_exit_trinv:= 
hoare forward prim;   
match goal with 
| H: ?s |= ?p |- ?s |= _ => 
sep name lift PartitionInv; apply fold_PartitionInv_frm;
match p with 
| context [ ([|OS_Port_V_mode ?dport = Some (Vint32 (ZToInt SAMPLE))|] **
dmportp_sllseg_sampleport_msg ?v ?msgl \\// ?q)] => sep name lift ([|OS_Port_V_mode dport = Some (Vint32 (ZToInt SAMPLE))|] **
dmportp_sllseg_sampleport_msg v msgl \\// q) in H end;
sep name lift APortStruct in H;
match p with 
| context [ dmportp_sllseg ?v Vnull] => sep name lift (dmportp_sllseg v Vnull) in H end;
match p with 
| context [ dmportp_sllseg ?v (Vptr ?v')] => sep name lift (dmportp_sllseg v (Vptr v')) in H end;
eapply dmportp_sllseg_compose in H;eauto;
sep autocancel;unfold PartitionInv_part1,AOSDomainPortPtrList;
sep normal;sep eexists;sep pauto
| |- _ => try (sep name lift PartitionInv; apply fold_PartitionInv_frm; unfold PartitionInv_part1);sep pauto  end;
match goal with 
| |-  {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} => idtac 
| |- RLH_PortPtrINecb _ _ _ _ =>  solve [eauto || unfold RLH_PortPtrINecb;splits;eauto] 
| |- RH_CurTCB ?tid ?tcbls => solve [eauto || unfold RH_CurTCB;eauto]
| |- GoodFrm (_ ** _ ) => go  (* 为了排除 GoodFrm ?frm 还没有填的情况 *)
| |- _ => eauto 
end.