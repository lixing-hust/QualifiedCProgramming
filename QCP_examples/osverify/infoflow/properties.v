
Require Import memory.
Require Import if_language.
Require Import if_opsem.

Require Import spec_aux_defs. 
Require Import mq_apispecs. 
Require Import prt_apispecs.
Require Import buffer_apispecs. 
Require Import osspecs. 

Require Import if_succ_gen. 

Open Scope int_scope. 

Set Asymmetric Patterns.
Set Implicit Arguments.
Unset Strict Implicit.

  
Definition ctid_equiv (td: taskdom) (O1 O2: osabst) :=
  exists t1 t2,
    get O1 curtid = Some (oscurt t1)
    /\ get O2 curtid = Some (oscurt t2)
    /\
      forall pr1 pr2,
        task_prio_id O1 pr1 t1 -> 
        task_prio_id O2 pr2 t2 ->
        dom_for_prio pr1 = td ->
        pr1 = pr2. 
    
Definition kernel_task_equiv (td: taskdom) (O1 O2: osabst) :=
  exists tcbs1 tcbs2,
    get O1 abstcblsid = Some (abstcblist tcbs1)
    /\ get O2 abstcblsid = Some (abstcblist tcbs2)
    /\ forall pr,
      dom_for_prio pr = td ->
      (
        ((exists t, task_prio_id O1 pr t) <-> (exists t, task_prio_id O2 pr t))
        /\
          (forall t1 t2 pr1 pr2 st1 st2 msg1 msg2 sus1 sus2,
              get tcbs1 t1 = Some (pr1, st1, msg1, sus1, pr) ->
              get tcbs2 t2 = Some (pr2, st2, msg2, sus2, pr) ->
              (pr1 = pr2 /\ st1 = st2 /\ msg1 = msg2 /\ sus1 = sus2))
      ).

Definition tidls_equiv (tids1 tids2: list tid) (O1 O2: osabst) :=
  length tids1 = length tids2 /\ 
  forall pr,
    ((exists t, List.In t tids1 /\ task_prio_id O1 pr t) <->
       (exists t, List.In t tids2 /\ task_prio_id O2 pr t)). 


Definition mq_ed_equiv (ed1 ed2: edata) (O1 O2: osabst) :=
  exists ms mlen pws1 pws2,
    ed1 = absmsgq ms mlen pws1
    /\ ed2 = absmsgq ms mlen pws2
    /\ tidls_equiv pws1 pws2 O1 O2.

Definition mq_equiv (td: taskdom) (mq1 mq2: absqattrb.B) (O1 O2: osabst) :=
  exists eo1 eo2 wtp flgs mms msz cms csltidxs,
    mq1 = (eo1, wtp, flgs, mms, msz, cms, csltidxs)
    /\ mq2 = (eo2, wtp, flgs, mms, msz, cms, csltidxs)
    /\ (
        (eo1 = Null /\ eo2 = Null)
        \/ (eo1 = Holder /\ eo2 = Holder)
        \/ (
            exists (ecbs1 ecbs2: EcbMod.map) eid ed1 ed2 ws1 ws2,
              eo1 = Valid_Addr eid
              /\ eo2 = Valid_Addr eid
              /\ get O1 absecblsid = Some (absecblist ecbs1)
              /\ get O2 absecblsid = Some (absecblist ecbs2)
              /\ get ecbs1 eid = Some (ed1, ws1)
              /\ get ecbs2 eid = Some (ed2, ws2)
              /\ mq_ed_equiv ed1 ed2 O1 O2
              /\ tidls_equiv ws1 ws2 O1 O2
          )).

Definition kernel_mq_equiv (td: taskdom) (O1 O2: osabst) :=
  exists mqatts1 mqatts2,
    get O1 absmqattrid = Some (absmqattr mqatts1)
    /\ get O2 absmqattrid = Some (absmqattr mqatts2)
    /\ forall i, 
      mqidx_in_dom i td = true ->
      ((get mqatts1 i <> None <-> get mqatts2 i <> None)
       /\
         (forall mq1 mq2,
             get mqatts1 i = Some mq1 -> 
             get mqatts2 i = Some mq2 -> 
             mq_equiv td mq1 mq2 O1 O2)).

  
Definition ports_equiv (td: taskdom) (O1 O2: osabst) :=
  exists (prts1 prts2: DomainPortMod.map) (els1 els2: EcbMod.map), 
    get O1 osdomainportid = Some (osdomainport prts1)
    /\ get O2 osdomainportid = Some (osdomainport prts2)
    /\ get O1 absecblsid = Some (absecblist els1)
    /\ get O2 absecblsid = Some (absecblist els2) 
    /\ (forall a,
           addrval_in_dom a td = true ->
           (get prts1 a = get prts2 a
            /\
              ((exists tls, get els1 a = Some (absport, tls)) <-> (exists tls, get els2 a = Some (absport, tls)))
            /\
              (forall tls1 tls2, 
                  get els1 a = Some (absport, tls1) ->
                  get els2 a = Some (absport, tls2) ->
                  (* all tasks in tls1 and tls2 are supposed to be in the domain td *)
                  tidls_equiv tls1 tls2 O1 O2))). 


Definition cap_equiv (td: taskdom) (O1 O2: osabst) :=
  exists cspc1 cspc2,
    get O1 cspaceid = Some (capcspace cspc1)
    /\ get O2 cspaceid = Some (capcspace cspc2)
    /\ (forall pr,
           dom_for_prio pr = td ->
           ((forall cls cap, (has_cat_cap pr cspc1 cls cap <-> has_cat_cap pr cspc2 cls cap))
            /\ (forall idx,
                   mqidx_in_dom idx td = true ->
                   (((exists objp, mq_ptr O1 idx objp) <-> (exists objp, mq_ptr O2 idx objp))
                    /\
                      (forall objp1 objp2, 
                          mq_ptr O1 idx objp1 ->
                          mq_ptr O2 idx objp2 -> 
                          (has_obj_cap pr cspc1 objp1 <-> has_obj_cap pr cspc2 objp2)))))). 

            
Definition buffer_equiv (td: taskdom) (O1 O2: osabst) :=
  exists els1 els2,
    get O1 absecblsid = Some (absecblist els1) /\
      get O2 absecblsid = Some (absecblist els2) /\
      forall eid,
        buf_in_dom eid td = true ->
        (
          ((exists ed ws, get els1 eid = Some (ed, ws)) <->
             (exists ed ws, get els2 eid = Some (ed, ws)))
          /\
            (forall ed1 ed2 ws1 ws2, 
                get els1 eid = Some (ed1, ws1) -> 
                get els2 eid = Some (ed2, ws2) -> 
                (mq_ed_equiv ed1 ed2 O1 O2 
                 /\ tidls_equiv ws1 ws2 O1 O2))). 

Definition kernel_data_equiv (td: taskdom) (O1 O2: osabst) := 
  kernel_task_equiv td O1 O2
  /\ kernel_mq_equiv td O1 O2
  /\ ports_equiv td O1 O2
  /\ buffer_equiv td O1 O2
  /\ cap_equiv td O1 O2. 

      
Definition ibufs_equiv (td: taskdom) (O1 O2: osabst) :=
  exists ibufmp1 ibufmp2,
    get O1 ibufsid = Some (ibufs ibufmp1)
    /\ get O2 ibufsid = Some (ibufs ibufmp2)
    /\ ibufmp1 td = ibufmp2 td. 

Definition obufs_equiv (td: taskdom) (O1 O2: osabst) :=
  exists obufmp1 obufmp2,
    get O1 obufsid = Some (obufs obufmp1)
    /\ get O2 obufsid = Some (obufs obufmp2) 
    /\ obufmp1 td = obufmp2 td. 

Definition bufs_equiv (td: taskdom) (O1 O2: osabst) :=
  ibufs_equiv td O1 O2 /\ obufs_equiv td O1 O2. 
      

Definition local_envs_equiv
  (td: taskdom) (cenvs1 cenvs2: cltenvs) (O1 O2: osabst) (* (eta: addrmp) *) :=  
  forall pr,
    dom_for_prio pr = td ->
    forall t1 t2,
      task_prio_id O1 pr t1 ->
      task_prio_id O2 pr t2 ->
      get cenvs1 t1 = get cenvs2 t2. 


Definition client_data_equiv
  (td: taskdom) (cst1 cst2: clientst) (O1 O2: osabst) :=
  exists ges1 ges2 ces1 ces2 m1 m2,
    cst1 = (ges1, ces1, m1)
    /\ cst2 = (ges2, ces2, m2)
    /\ ges1 td = ges2 td
    /\ local_envs_equiv td ces1 ces2 O1 O2 
    /\ get_dom_mem m1 td = get_dom_mem m2 td. 

Fixpoint head_asrt_sat (pr: priority) (cd: spec_code) (O: osabst) := 
  match cd with
    spec_prim asrt _ _ => fst asrt O pr
  | sched asrt => fst asrt O pr
  | spec_done _ => True 
  | spec_seq cd1 cd2 => head_asrt_sat pr cd1 O 
  | spec_ifelse asrt b cd1 cd2 => fst asrt O pr
  | spec_if_else_ asrt b cd1 cd2 => fst asrt O pr
  | spec_assume asrt _ => fst asrt O pr
  | spec_assert asrt _ => fst asrt O pr
  | spec_abort => True 
  | getsem asrt _ | postsem asrt _ 
  | coreint asrt _ _ | clearipc asrt _ _
  | cslsemacc asrt _ _ | cslsemrel asrt _ => fst asrt O pr
  end.


Definition data_equiv_tskd
  (td: taskdom) (cst1 cst2: clientst) (O1 O2: osabst) :=
  ctid_equiv td O1 O2
  /\ bufs_equiv td O1 O2
  /\ kernel_data_equiv td O1 O2
  /\ client_data_equiv td cst1 cst2 O1 O2. 


(* given command is not a kernel statement *) 
Definition not_knl_stmt (c: cureval) :=   
  (exists e, c = cure e)
  \/ exists s, c = curs s /\ (~exists ss, s = hapi_code ss).


Fixpoint get_hd_vl (cd: spec_code) : option vallist :=
  match cd with
    spec_prim asrt _ _ => Some (snd asrt)
  | sched asrt => Some (snd asrt)
  | spec_done _ => None
  | spec_seq cd1 cd2 => get_hd_vl cd1
  | spec_ifelse asrt b cd1 cd2 => Some (snd asrt)
  | spec_if_else_ asrt b cd1 cd2 => Some (snd asrt)
  | spec_assume asrt _ => Some (snd asrt)
  | spec_assert asrt _ => Some (snd asrt)
  | spec_abort => None
  | getsem asrt _ | postsem asrt _
  | coreint asrt _ _ | clearipc asrt _ _
  | cslsemacc asrt _ _ | cslsemrel asrt _ => Some (snd asrt)  
  end.  


Definition mqsend_equiv (cd1 cd2: spec_code) :=
  exists (vl vl1 vl2: vallist) k,
    length vl = 4%nat /\ length vl1 = 4%nat /\ length vl2 = 4%nat
    /\ List.nth_error (get_all_succs (mqsend (vl++vl1))) k = Some cd1
    /\ List.nth_error (get_all_succs (mqsend (vl++vl2))) k = Some cd2. 

Definition mqrecv_equiv (cd1 cd2: spec_code) :=
  exists (vl vl1 vl2: vallist) k,
    length vl = 4%nat /\ length vl1 = 4%nat /\ length vl2 = 4%nat
    /\ List.nth_error (get_all_succs (mqreceive (vl++vl1))) k = Some cd1
    /\ List.nth_error (get_all_succs (mqreceive (vl++vl2))) k = Some cd2. 

Definition mqtimedrecv_equiv (cd1 cd2: spec_code) :=
  exists (vl vl1 vl2: vallist) k,
    length vl = 5%nat /\ length vl1 = 4%nat /\ length vl2 = 4%nat
    /\ List.nth_error (get_all_succs (mqtimedreceive (vl++vl1))) k = Some cd1
    /\ List.nth_error (get_all_succs (mqtimedreceive (vl++vl2))) k = Some cd2. 

Definition qprtpost_equiv (cd1 cd2: spec_code) :=
  exists (vl vl1 vl2: vallist) k,
    length vl = 1%nat /\ length vl1 = 2%nat /\ length vl2 = 2%nat 
    /\ List.nth_error (get_all_succs (qportpost (vl++vl1))) k = Some cd1
    /\ List.nth_error (get_all_succs (qportpost (vl++vl2))) k = Some cd2.

Definition qprtpend_equiv (cd1 cd2: spec_code) := 
  exists (vl vl1 vl2: vallist) k,
    length vl = 2%nat /\ length vl1 = 2%nat /\ length vl2 = 2%nat 
    /\ List.nth_error (get_all_succs (qportpend (vl++vl1))) k = Some cd1
    /\ List.nth_error (get_all_succs (qportpend (vl++vl2))) k = Some cd2.

Definition sprtpost_equiv (cd1 cd2: spec_code) :=
  exists (vl vl1 vl2: vallist) k,
    length vl = 1%nat /\ length vl1 = 2%nat /\ length vl2 = 2%nat 
    /\ List.nth_error (get_all_succs (sampleportpost (vl++vl1))) k = Some cd1
    /\ List.nth_error (get_all_succs (sampleportpost (vl++vl2))) k = Some cd2.

Definition prtaccept_equiv (cd1 cd2: spec_code) :=
  exists (vl vl1 vl2: vallist) k,
    length vl = 1%nat /\ length vl1 = 2%nat /\ length vl2 = 2%nat 
    /\ List.nth_error (get_all_succs (portaccept (vl++vl1))) k = Some cd1
    /\ List.nth_error (get_all_succs (portaccept (vl++vl2))) k = Some cd2.

Definition bufferpost_equiv (cd1 cd2: spec_code) :=
  exists (vl vl1 vl2: vallist) k,
    length vl = 2%nat /\ length vl1 = 1%nat /\ length vl2 = 1%nat 
    /\ List.nth_error (get_all_succs (bufferpost (vl++vl1))) k = Some cd1
    /\ List.nth_error (get_all_succs (bufferpost (vl++vl2))) k = Some cd2. 

Definition bufferaccept_equiv (cd1 cd2: spec_code) :=
  exists (vl vl1 vl2: vallist) k,
    length vl = 1%nat /\ length vl1 = 1%nat /\ length vl2 = 1%nat 
    /\ List.nth_error (get_all_succs (bufferaccept (vl++vl1))) k = Some cd1
    /\ List.nth_error (get_all_succs (bufferaccept (vl++vl2))) k = Some cd2. 

Definition bufferpend_equiv (cd1 cd2: spec_code) :=
  exists (vl vl1 vl2: vallist) k,
    length vl = 2%nat /\ length vl1 = 1%nat /\ length vl2 = 1%nat 
    /\ List.nth_error (get_all_succs (bufferpend (vl++vl1))) k = Some cd1
    /\ List.nth_error (get_all_succs (bufferpend (vl++vl2))) k = Some cd2. 

Require Import intspecs.

Definition intr_equiv (cd1 cd2: spec_code) :=
  (* List.In cd1 (get_all_succs tickisr) /\ cd1 = cd2.  *) 
  exists k,
    List.nth_error (get_all_succs tickisr) k = Some cd1
    /\ List.nth_error (get_all_succs tickisr) k = Some cd2. 

Definition stmt_equiv (cd1 cd2: spec_code) :=
  (exists vo, cd1 = spec_done vo /\ cd2 = spec_done vo)
  \/
    ((~(exists vo1 vo2, cd1 = spec_done vo1 /\ cd2 = spec_done vo2))
     /\ (
         mqsend_equiv cd1 cd2
         \/ mqrecv_equiv cd1 cd2
         \/ mqtimedrecv_equiv cd1 cd2
         \/ qprtpost_equiv cd1 cd2 
         \/ qprtpend_equiv cd1 cd2 
         \/ sprtpost_equiv cd1 cd2 
         \/ prtaccept_equiv cd1 cd2
         \/ bufferpost_equiv cd1 cd2
         \/ bufferaccept_equiv cd1 cd2
         \/ bufferpend_equiv cd1 cd2 
         \/ intr_equiv cd1 cd2
         \/ (cd1 = ABORT /\ cd2 = ABORT))
    ).   

Definition vl_equiv (cd1 cd2: spec_code) : Prop :=
  (forall vl1 vl2,
      get_hd_vl cd1 = Some vl1 -> get_hd_vl cd2 = Some vl2 ->
      (forall i v1 v2, nth_error vl1 i = Some v1 -> nth_error vl2 i = Some v2 -> v1 = v2)).  

      
Definition cmd_equiv pr c1 c2 O1 O2 := 
  ((not_knl_stmt c1 /\ not_knl_stmt c2) /\ c1 = c2 \/
     (exists cd1 cd2,
         c1 = curs (hapi_code cd1) /\ c2 = curs (hapi_code cd2)
         /\ head_asrt_sat pr cd1 O1 /\ head_asrt_sat pr cd2 O2 
         /\ vl_equiv cd1 cd2
         /\ stmt_equiv cd1 cd2)).


Definition cont_equiv (pr: priority) (ks1 ks2: stmtcont) (O1 O2: osabst) :=
  ((~(exists c1 ke1 ks1', ks1 = kevent c1 ke1 ks1')) /\
     (~(exists c2 ke2 ks2', ks2 = kevent c2 ke2 ks2')) /\
     ks1 = ks2)
  \/
    (exists c1 c2 ke ks',
        ks1 = kevent c1 ke ks' /\
          ks2 = kevent c2 ke ks' /\
          cmd_equiv pr c1 c2 O1 O2
    ).
    
    
Definition code_equiv_tskd
  (d: taskdom) (T1 T2: tasks) (O1 O2: osabst) :=
  forall (pr: priority) t1 t2,
    dom_for_prio pr = d ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    (exists c1 c2 ke ks1 ks2,
        get T1 t1 = Some (c1, (ke, ks1))
        /\ get T2 t2 = Some (c2, (ke, ks2))
        /\ cmd_equiv pr c1 c2 O1 O2
        /\ cont_equiv pr ks1 ks2 O1 O2).


Definition code_equiv_tskd'
  (d: taskdom) (T1 T2: tasks) (O1 O2: osabst) :=
  forall (pr: priority) t1 t2,
    dom_for_prio pr = d ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    (get T1 t1 = get T2 t2
     /\ (forall c ke ks,
            get T1 t1 = Some (c, (ke, ks)) ->
            (not_knl_stmt c
             \/ (exists cd,
                    c = curs (hapi_code cd)
                    /\ (head_asrt_sat pr cd O1 <-> head_asrt_sat pr cd O2)))
            /\ (forall c' cd' ke' ks',
                   ks = kevent c' ke' ks' ->
                   c' = curs (hapi_code cd') ->
                   (head_asrt_sat pr cd' O1 <-> head_asrt_sat pr cd' O2)))). 


Definition obsr_equiv_tskd
  (sc: ossched) (td: taskdom) (T1 T2: tasks) (cst1 cst2: clientst) (O1 O2: osabst) :=
  code_equiv_tskd td T1 T2 O1 O2
  /\ data_equiv_tskd td cst1 cst2 O1 O2.  


Definition obsr_equiv_tskd'
  (sc: ossched) (td: taskdom) (T1 T2: tasks) (cst1 cst2: clientst) (O1 O2: osabst) :=
  code_equiv_tskd' td T1 T2 O1 O2
  /\ data_equiv_tskd td cst1 cst2 O1 O2.
      
      
Definition data_equiv_schd (O1 O2: osabst) :=
  (get O1 kscurdomid <> None /\ get O1 kscurdomid = get O2 kscurdomid)
  /\ (get O1 ksdschedidxid <> None /\ get O1 ksdschedidxid = get O2 ksdschedidxid)
  /\ (get O1 ksdschedid <> None /\ get O1 ksdschedid = get O2 ksdschedid)
  /\ (get O1 ksdomtimeid <> None /\ get O1 ksdomtimeid = get O2 ksdomtimeid)  
  /\ (exists t1 t2,
         get O1 curtid = Some (oscurt t1)
         /\ get O2 curtid = Some (oscurt t2)
         /\ ((exists pr, task_prio_id O1 pr t1) <-> (exists pr, task_prio_id O2 pr t2))
         /\ (forall pr1 pr2,
                task_prio_id O1 pr1 t1 ->
                task_prio_id O2 pr2 t2 ->
                dom_for_prio pr1 = dom_for_prio pr2)).


Definition code_equiv_schd (T1 T2: tasks) (O1 O2: osabst) :=
  exists c1 c2 ke1 ke2 ks1 ks2,
    code_cur_task T1 O1 = Some (c1, (ke1, ks1))
    /\ code_cur_task T2 O2 = Some (c2, (ke2, ks2))
    /\ (absintcont ks1 <> None <-> absintcont ks2 <> None)
    /\ (absintcont ks1 <> None -> c1 = c2). 


Definition obsr_equiv_schd (T1 T2: tasks) (O1 O2: osabst) :=
  code_equiv_schd T1 T2 O1 O2 /\ data_equiv_schd O1 O2.  


(* channel state & capability state *)
Definition obsr_equiv_chnd (O1 O2: osabst) := 
  (get O1 oschannelid <> None /\ get O1 oschannelid = get O2 oschannelid) /\
    (get O1 oskportid <> None /\ get O1 oskportid = get O2 oskportid).  


Definition obsr_equiv
  (sc: ossched) (dm: dom) (T1 T2: tasks) (cst1 cst2: clientst) (O1 O2: osabst) : Prop :=  
  match dm with
    TaskDom td =>
      obsr_equiv_tskd sc td T1 T2 cst1 cst2 O1 O2
  | SchedDom =>
      obsr_equiv_schd T1 T2 O1 O2 
  | TransDom =>
      obsr_equiv_chnd O1 O2
  end.

Definition obsr_equiv'
  (sc: ossched) (dm: dom) (T1 T2: tasks) (cst1 cst2: clientst) (O1 O2: osabst) : Prop :=  
  match dm with
    TaskDom td =>
      obsr_equiv_tskd' sc td T1 T2 cst1 cst2 O1 O2
  | SchedDom =>
      obsr_equiv_schd T1 T2 O1 O2 
  | TransDom =>
      obsr_equiv_chnd O1 O2
  end.             


Local Open Scope type_scope. 

Definition sys_cfg :=
  ((tid -> option priority) 
   * CSpaceMod.map 
   * DomainPortMod.map 
   * KernelPMod.map 
   * ChannelMod.map). 

Parameter ccfg : sys_cfg. 


Definition eqdomto :=
  fun (T: tasks) (O: osabst) => 
    exists tls,
      get O abstcblsid = Some (abstcblist tls)
      /\ (forall t, (exists a, get tls t = Some a ) <-> (exists C,get T t = Some C)). 


Definition init_tsk (p:progunit) (T:tasks) (cst:clientst) (O:osabst) := 
  eqdomto T O
  /\ forall t C,
      TasksMod.get T t = Some C ->
      exists s f d1 d2 t, C = nilcont s /\ p f = Some (t, d1, d2, s). 

Definition init_cli_st (cst: clientst) :=
  exists ges ces m,
    cst = (ges, ces, m)
    /\ (forall t E x b tp,
           get ces t = Some E ->
           get E x = Some (b, tp) ->
           get m (b, 0%Z) <> None). 

Definition init_tsk_st (O: osabst) (tps: tid->option priority) := 
  exists tls,
    OSAbstMod.get O abstcblsid = Some (abstcblist tls)
    /\ (forall t st p p0 msg sus,
           TcbMod.get tls t = Some (p, st, msg, sus, p0) ->
           (st = rdy /\ tps t = Some p0))
    /\ (forall t p0,
           tps t = Some p0 ->
           exists p st msg sus, TcbMod.get tls t = Some (p, st, msg, sus, p0))
           /\ (exists t, get O curtid = Some (oscurt t)).  
             

Definition init_evt_st (O: osabst) :=
  (exists mqs, OSAbstMod.get O absmqattrid = Some (absmqattr mqs)) 
  /\ (exists els, OSAbstMod.get O absecblsid = Some (absecblist els)). 

Definition init_prt_st (O: osabst) dpl kpl chs :=
  OSAbstMod.get O oskportid = Some (oskport kpl)
  /\ OSAbstMod.get O oschannelid = Some (oschannel chs)
  /\  OSAbstMod.get O osdomainportid = Some (osdomainport dpl). 

Definition init_sch_st (O: osabst) :=
  exists schtbl,
    get O ksdschedid = Some (ksdsched schtbl) 
    /\ (forall idx d n, get schtbl idx = Some (d, n) -> Int.lt Int.zero n = true) 
    /\ (exists len,
           get O ksdschedlenid = Some (ksdschedlen len)
           /\ (forall idx, (Int.eq idx len = true \/ Int.lt len idx = true) -> get schtbl idx = None)
           /\ exists dschi, get O ksdschedidxid = Some (ksdschedidx dschi) /\ Int.lt dschi len = true).  
           
Definition init_buf_st (O: osabst) :=
  exists ibmp obmp,
    get O ibufsid = Some (ibufs ibmp) 
    /\ get O obufsid = Some (obufs obmp). 

Definition init_cap_st (O: osabst) cspc :=
    get O cspaceid = Some (capcspace cspc) /\
      (forall pr, (exists t, task_prio_id O pr t) <-> get cspc pr <> None). 
  
Definition init_st (T: tasks) (cst: clientst) (O: osabst) :=
  exists tps dpl kpl chs cspc,
    ccfg = (tps, cspc, dpl, kpl, chs) 
    /\ init_cli_st cst
    /\ init_sch_st O
    /\ init_tsk_st O tps
    /\ init_evt_st O
    /\ init_prt_st O dpl kpl chs
    /\ init_buf_st O
    /\ init_cap_st O cspc.  

Definition init (pu: progunit) (T: tasks) (cst: clientst) (O: osabst) := 
  init_tsk pu T cst O /\ init_st T cst O. 


Definition reachable (hp: hprog) (T: tasks) (cst: clientst) (O: osabst) :=
  exists pu spc,
    hp = (pu, spc)
    /\ (exists T0 cst0 O0,
           init pu T0 cst0 O0
           /\ hpstepokstar hp T0 cst0 O0 T cst O). 
  

(* there is a channel with src and dst ports in td and td', respectively *) 
Definition has_channel dpl kpl chs td td' :=
  exists a cid cdstn dstpaddrs tp,
  exists asrcdp spcn spd spid sdir spst spin spout sptt,
  exists asrckp ao spcn' spst', 
  exists adstkp dpid ao' ao'' dpcn' dpst',
  exists adstdp kpcn dpd ddir dpst dpin dpout dptt,  
    get dpl asrcdp = Some (spcn, spd, spid, sdir, spst, spin, spout, sptt) /\ 
      get kpl asrckp = Some (spid, ao, Some a, spcn', spst') /\ 
      get chs a = Some (cid, cdstn, dstpaddrs, tp) /\
      List.In adstkp dstpaddrs /\
      get kpl adstkp = Some (dpid, ao', ao'', dpcn', dpst') /\
      get dpl adstdp = Some (kpcn, dpd, dpid, ddir, dpst, dpin, dpout, dptt) /\ 
      addrval_in_dom asrcdp td = true /\
      addrval_in_dom adstdp td' = true.
    
(*********************** The Flow Policy ***********************)  
(* implicit that the only domains d satisfying "flowsTo d SchedDom" are
     SchedDom and TransDom *)
(* implicit that the only domains d satisfying "flowsTo d TransDom" are
     SchedDom and TransDom *)
Inductive flowsTo: dom -> dom -> Prop :=

  flows_to_refl: forall d, flowsTo d d

| sched_flows_to_all: forall d, flowsTo SchedDom d

| trans_flows_to_all: forall d,  flowsTo TransDom d

| comm_flows:
  forall td td' dpl kpl chs tls cspc, 
    ccfg = (tls, cspc, dpl, kpl, chs) -> 
    has_channel dpl kpl chs td td' -> 
    has_post_cap tls cspc td -> 
    flowsTo (TaskDom td) (TaskDom td'). 

(* OLD DESCRIPTION OF FLOW POLICY *)
(* Section FlowRelation.  *)
(*   Parameter flowsTo: dom -> dom -> Prop. *)
(*   Axiom flows_to_refl: forall d, flowsTo d d. *)
(*   Axiom sched_flows_to_all: forall d, flowsTo SchedDom d. *)
(*   Axiom trans_flows_to_all: forall d, flowsTo TransDom d. *)
(*   Axiom flows_to_sched: forall d, flowsTo d SchedDom -> (d = SchedDom \/ d = TransDom). *)
(*   Axiom flows_to_trans: forall d, flowsTo d TransDom -> (d = TransDom \/ d = SchedDom).  *)
(* End FlowRelation.    *)




(*********************** the unwinding conditions ***********************)  

Definition confidentiality_u (hp: hprog) :=
  forall pu apispc intspc sc
         T1 T2 cst1 cst2 O1 O2 T1' T2' cst1' cst2' O1' O2' act td dm', 
    hp = (pu, (apispc, intspc, sc)) -> 
    reachable hp T1 cst1 O1 -> 
    reachable hp T2 cst2 O2 -> 
    obsr_equiv sc (SchedDom) T1 T2 cst1 cst2 O1 O2 -> 
    obsr_equiv sc (TransDom) T1 T2 cst1 cst2 O1 O2 -> 
    obsr_equiv sc (TaskDom td) T1 T2 cst1 cst2 O1 O2 ->
    (flowsTo dm' (TaskDom td) -> obsr_equiv sc dm' T1 T2 cst1 cst2 O1 O2) ->
    hpstep_pt hp T1 cst1 O1 T1' cst1' O1' act dm' ->
    hpstep_pt hp T2 cst2 O2 T2' cst2' O2' act dm' ->
    obsr_equiv sc (TaskDom td) T1' T2' cst1' cst2' O1' O2'. 
      
Definition integrity_u (hp: hprog) :=
  forall pu apispc intspc sc T T' cst cst' O O' td dm' act,
    hp = (pu, (apispc, intspc, sc)) -> 
    reachable hp T cst O ->
    hpstep_pt hp T cst O T' cst' O' act dm' -> 
    ~(flowsTo dm' (TaskDom td)) ->
    obsr_equiv' sc (TaskDom td) T T' cst cst' O O'. 

