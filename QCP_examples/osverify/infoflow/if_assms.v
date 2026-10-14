
Require Import memory. 
Require Import if_language.
Require Import if_opsem.
Require Import properties.
Require Import spec_aux_defs. 


(* memory allocation for the local variables of a function is deterministic *) 
Axiom alloc_det: 
  forall M1 M2 d le tp x le1' le2' M1' M2', 
    get_dom_mem M1 d = get_dom_mem M2 d ->
    alloc_pt x tp le M1 le1' M1' d ->
    alloc_pt x tp le M2 le2' M2' d ->
    (le1' = le2' /\ get_dom_mem M1' d = get_dom_mem M2' d). 
       
(* no memory block violates the boundary of partitions *)  
Axiom n_block_cross_part:
  forall i1 i2 b d, addr_in_dom (b, i1) d = addr_in_dom (b, i2) d. 

(* each original priority for a task corresponds to a unique task identifier *)
Axiom tid_unique: 
  forall O pr t t', task_prio_id O pr t -> task_prio_id O pr t' -> t = t'.  

(* an address cannot be in two different domains at the same time *)
Axiom dom_disj_addrs:
  forall d1 d2 a,
    d1 <> d2 ->
    addr_in_dom a d1 = true ->
    addr_in_dom a d2 = true ->
    False.


(* an index for a gjb message queue cannot be in two different domains
   at the same time *)
Axiom mqidx_diff_dom:
  forall d1 d2 i,
    d1 <> d2 ->
    mqidx_in_dom i d1 = true ->
    mqidx_in_dom i d2 = true ->
    False. 

(* if a gjb message queue contains a valid pointer to some ECB,
 then the pointer points to the ECB of a message queue in uC/OS-II *) 
Axiom mq_ecb:
  forall O mqs idx eid a b c d e f els,
    get O absmqattrid = Some (absmqattr mqs) ->
    get mqs idx = Some (Valid_Addr eid, a, b, c, d, e, f) ->
    get O absecblsid = Some (absecblist els) -> 
    exists ms sz pwl wl,
      get els eid = Some (absmsgq ms sz pwl, wl). 

(* if two gjb message queues both contain valid ECB pointers, then the pointers are different
   (this was checked in the refinement verification performed in phase I) *)
Axiom mq_ecb_ref_distinct:
  forall i1 i2 (mqs: MqattrMod.map) ep1 ep2 x1 x2 x3 x4 x5 x6 x1' x2' x3' x4' x5' x6',
    i1 <> i2 -> 
    get mqs i1 = Some (Valid_Addr ep1, x1, x2, x3, x4, x5, x6) ->
    get mqs i2 = Some (Valid_Addr ep2, x1', x2', x3', x4', x5', x6') ->
    ep1 <> ep2. 

(* any task waiting for a gjb message queue is in the partition of the message queue *)
Axiom mq_part_consistent: 
  forall O mqs idx td eid wtp qflg mmsg msz cmsgs ecbs ms mlen wl pwl qcp,
    get O absmqattrid = Some (absmqattr mqs) ->
    mqidx_in_dom idx td = true ->
    get mqs idx = Some (Valid_Addr eid, wtp, qflg, mmsg, msz, cmsgs, qcp)  ->
    get O absecblsid = Some (absecblist ecbs) ->
    get ecbs eid = Some (absmsgq ms mlen pwl, wl) ->
    forall t,
      (In t wl \/ In t pwl) ->
      exists pr, task_prio_id O pr t /\ dom_for_prio pr = td. 

Definition distinct (ts: list tid) :=
  forall i j t1 t2,
    List.nth_error ts i = Some t1 ->
    List.nth_error ts j = Some t2 ->
    i <> j ->
    t1 <> t2. 

(* the task identifiers in the wait lists for a message queue ECB are distinct *) 
Axiom distinct_wait_tids:
  forall O ecbs eid ms mlen pwl wl, 
    get O absecblsid = Some (absecblist ecbs) ->
    get ecbs eid = Some (absmsgq ms mlen pwl, wl) ->
    (distinct wl /\ distinct pwl).


(* an ECB pointer cannot point to a gjb message queue and a partition buffer
   at the same time *)
Axiom not_both_mq_and_buffer:
  forall O mqs eid idx qwt qflg qmm qms qcms qcap td, 
    get O absmqattrid = Some (absmqattr mqs) ->
    get mqs idx = Some (Valid_Addr eid, qwt, qflg, qmm, qms, qcms, qcap) ->
    buf_in_dom eid td = true ->
    False. 


(* if a partition buffer is in a domain, then its ECB is in the domain *) 
Axiom bufadr_diff_dom :
  forall d eid, 
    buf_in_dom eid d = true -> addrval_in_dom eid d = true.

(* if an address is for some partition buffer in some domain, then there
   must be an ECB for a message queue (in uC/OS-II) at the address *)  
Axiom buffer_ecb:
  forall O els eid td,
    buf_in_dom eid td = true -> 
    get O absecblsid = Some (absecblist els) -> 
    exists ms sz pwl wl,
      get els eid = Some (absmsgq ms sz pwl, wl). 

(* any task waiting for a buffer is in the partition of the buffer *)
Axiom buffer_part_consistent:
  forall O els eid td wl pwl sz ms,
    get O absecblsid = Some (absecblist els) -> 
    buf_in_dom eid td = true -> 
    get els eid = Some (absmsgq ms sz pwl, wl) ->
    forall t,
      (In t wl \/ In t pwl) ->
      exists pr, task_prio_id O pr t /\ dom_for_prio pr = td. 


(* the task identifiers in the wait list for a port are distinct *)
Axiom distinct_wait_tids_prt:
  forall O ecbs eid wl, 
    get O absecblsid = Some (absecblist ecbs) ->
    get ecbs eid = Some (absport, wl) ->
    distinct wl. 

(* the address of a port in a partition is in the domain recorded for the port *)
Axiom prt_dom_correct:
  forall O dp a pcn pd pid dir pst pin pout ptt, 
    get O osdomainportid = Some (osdomainport dp) ->
    get dp a = Some (pcn, pd, pid, dir, pst, pin, pout, ptt) ->
    addrval_in_dom a  ($(Z_of_nat pd)) = true.  

(* there is a port if and only if there is a corresponding ECB for a port *)
Axiom prt_ecb_consistent:
  forall O dpl els, 
    get O osdomainportid = Some (osdomainport dpl) -> 
    get O absecblsid = Some (absecblist els) -> 
    forall a, 
      ((exists dp, get dpl a = Some dp) <-> (exists wl, get els a = Some (absport, wl))). 

(* each port identifier corresponds to a unique kernel port address *) 
Axiom kprt_addr_unique:
  forall O kpl pid dpa1 cha1 pcn1 pst1 dpa2 cha2 pcn2 pst2 a1 a2,
    get O oskportid = Some (oskport kpl) ->
    get kpl a1 = Some (pid, dpa1, cha1, pcn1, pst1) ->
    get kpl a2 = Some (pid, dpa2, cha2, pcn2, pst2) ->
    a1 = a2. 

(* any task waiting for a port is in the partition of the port *)
Axiom qprt_part_consistent:
  forall O els a wl t td, 
    get O absecblsid = Some (absecblist els) ->
    get els a = Some (absport, wl) ->
    In t wl ->
    ((exists pr, task_prio_id O pr t /\ dom_for_prio pr = td) <->
       addrval_in_dom a td = true). 


(* in states that are observationally equivalent wrt channels, 
   the results of getting a channel semaphore is the same *) 
Axiom chsem_res_eq:
  forall O1 O2 v1 v2, 
    obsr_equiv_chnd O1 O2 ->
    chsem_res O1 v1 ->
    chsem_res O2 v2 ->
    v1 = v2. 


(* in each reachable state, the value assertions annotated on the
   statements for the tasks are satisifed *)
Axiom rch_hasrt_sat:
  forall hp T cst O t cd ke ks pr,
     reachable hp T cst O ->
     get T t = Some (curs (hapi_code cd), (ke, ks)) ->
     task_prio_id O pr t ->
     head_asrt_sat pr cd O.


