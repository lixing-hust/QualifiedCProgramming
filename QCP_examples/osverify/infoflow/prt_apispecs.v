
Require Import memory. 
Require Import if_language.
Require Import if_opsem.

Require Import spec_aux_defs.

Definition upd_bufmp (mp: taskdom -> list msg) (td: taskdom) (ms: list msg) :=
  fun td' => if Int.eq td td' then ms else mp td'.

Definition port_indomainport v (O1: osabst) : Prop :=
  match v with 
  | Vptr v =>
      exists dpl pd pid pdir pst pin pout pt,
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (Z.to_nat DNUM, pd, pid, pdir, pst, pin, pout, pt)
  | _ => False
  end.

Definition has_port v (O: osabst) (_: priority) : Prop :=
  v = Vnull \/ port_indomainport v O.

Definition prt_indom v (O1: osabst) (pr: priority) :=
  exists a, v = Vptr a /\ addrval_in_dom a (dom_for_prio pr) = true. 
  
(* Definition prt_indom v (O1: osabst) (pr: priority) := *)
(*   v = Vnull \/ prt_indom0 v O1 pr.   *)

Definition not_port (O: osabst) (prt: val)  :=
  exists a els, 
    prt = Vptr a /\ 
      get O absecblsid = Some (absecblist els) /\
      (~exists wl, get els a = Some (absport, wl)). 
          
Definition wrong_core O prt :=
  exists a dpl pcn pd pid pdir pst pin pout pt,
    prt = Vptr a /\
      get O osdomainportid = Some (osdomainport dpl) /\ 
      get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
      pcn <> (Z.to_nat DNUM). 

Definition wrong_dom O prt :=
  exists a dpl pcn pd pid pdir pst pin pout pt,
  exists pr,
    prt = Vptr a /\ 
      get O osdomainportid = Some (osdomainport dpl) /\
      get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
      dom_cur_tsk O (dom_for_prio pr) /\ 
      Int.eq (dom_for_prio pr) (Int.repr (Z.of_nat pd)) = false. 

Definition no_channel O prt := 
  exists a dpl pcn pd pid pdir pst pin pout pt,
  exists kportl kpaddr kpst,
    prt = Vptr a /\ 
      get O osdomainportid = Some (osdomainport dpl) /\
      get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
      get O oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some a, None, pcn, kpst). 

Definition is_intercore O a :=
  exists dpl pcn pd pid pdir pst pin pout pt,
  exists kportl kpaddr kpst channaddr,
  exists chanl cid cdstn cdstkpl csem,
    (* sem = Int.repr (Z.of_nat csem) /\ *)
      get O osdomainportid = Some (osdomainport dpl) /\
      get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
      get O oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some a, Some channaddr, pcn, kpst) /\ 
      get O oschannelid = Some (oschannel chanl) /\ 
      get chanl channaddr = Some (cid, cdstn, cdstkpl, OutcoreC csem). 


(* (************************************ QPortPost  **************************************) *)

(* there is a domain port at address a *)
(* the domain port corresponds to a destination kernel port in dstkpaddrs *)  
(* the domain port is not full and has not waiting tasks *) 
Definition dst_port_not_full
  (kprtmp: KernelPMod.map) (dstkpaddrs: list addrval) (dpl: DomainPortMod.map) a : Prop := 
  (exists a' pid pcn pd pst pin pout n msgl, 
    exists a0 cha pcn' kpst,
      List.In a' dstkpaddrs /\
        get kprtmp a' = Some (pid, Some a0, Some cha, pcn', kpst) /\ 
        get dpl a = Some (pcn, pd, pid, DestinationP, pst, pin, pout, QueuePort n msgl) /\
        (List.length msgl < n)%nat). 

Definition dpl_upd
  (kprtmp: KernelPMod.map) (dstkpaddrs: list addrval) (m: msg)
  (dpl dpl': DomainPortMod.map) :=
  (forall a,
      (dst_port_not_full kprtmp dstkpaddrs dpl a
       /\ (exists pcn pd pid dir pst pin pout n msgl,
              get dpl a = Some (pcn, pd, pid, dir, pst, pin, pout, QueuePort n msgl) /\ 
              get dpl' a = Some (pcn, pd, pid, dir, pst, pin, pout, QueuePort n (msgl++(m::nil)))))
      \/
        (~dst_port_not_full kprtmp dstkpaddrs dpl a /\ get dpl' a = get dpl a)). 


Definition hwait_prt
  a kprtmp
  (dstkpaddrs: list addrval) (dpl: DomainPortMod.map)
  (els: EcbMod.map) (tls: TcbMod.map) wl t' := 
  exists a' pid pcn pd pst pin pout n msgl, 
  exists a0 cha pcn' kpst,
    List.In a' dstkpaddrs /\
      get kprtmp a' = Some (pid, Some a0, Some cha, pcn', kpst) /\
      get dpl a = Some (pcn, pd, pid, DestinationP, pst, pin, pout, QueuePort n msgl) /\
      get els a = Some (absport, wl) /\ wl <> nil /\
      GetHWait tls wl t'. 

Definition ecbl_upd
  (kprtmp: KernelPMod.map) (dstkpaddrs: list addrval)
  (dpl: DomainPortMod.map) (els els': EcbMod.map) (tls: TcbMod.map) := 
  forall a,
    ((exists t' wl,
         hwait_prt a kprtmp dstkpaddrs dpl els tls wl t'
         /\ get els' a = Some (absport, remove_tid t' wl))
     \/
       ((~(exists t' wl, hwait_prt a kprtmp dstkpaddrs dpl els tls wl t'))
        /\ get els' a = get els a) 
    ).

Definition tcbl_upd
  (kprtmp: KernelPMod.map) (dstkpaddrs: list addrval)
  (dpl: DomainPortMod.map) (els: EcbMod.map) (tls tls': TcbMod.map) := 
  forall t,
    (((exists wl a, hwait_prt a kprtmp dstkpaddrs dpl els tls wl t) 
      /\ (exists p st msg sus p0,
             get tls t = Some (p,st,msg,sus,p0) /\ 
               get tls' t = Some (p, rdy, Vint32 (Int.repr OS_PARTITION_MESSAGE_COME), sus, p0)))
     \/
       (~(exists wl a, hwait_prt a kprtmp dstkpaddrs dpl els tls wl t) /\
          get tls' t = get tls t)). 
          
Definition has_dst_ports (O: osabst) (prt: val) :=
  exists prta dpl pcn pd pid ptp pin pout pt kportl,
  exists a pcn' kpst pst kpaddr, 
  exists chanl chaddr cid cdstn cdstkpl chtp,
    prt = Vptr prta /\ 
    get O osdomainportid = Some (osdomainport dpl) /\
      get dpl prta = Some (pcn, pd, pid, ptp, pst, pin, pout, pt) /\ 
      get O oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some a, Some chaddr, pcn', kpst) /\ 
      get O oschannelid = Some (oschannel chanl) /\ 
      get chanl chaddr = Some (cid, cdstn, cdstkpl, chtp) /\
      cdstkpl <> nil. 
  
Definition q_send_to_domain 
  (vl: vallist) (O1: osabst) (act: action) (rst: option val * option osabst) :=
  match rst with
  | (opv, opo) =>
      exists v dpl pcn pd srcpid pst pin pout pt,
      exists kportl kpaddr a chaddr pcn' kpst, 
      exists chanl cid cdstn cdstkpl chtp,
      exists ibmp td msg msgl,
      exists els els' tls tls' dpl', 
        vl = Vptr v :: nil /\ (* v is addr of source port *) 
          get O1 osdomainportid = Some (osdomainport dpl) /\
          get dpl v = Some (pcn, pd, srcpid, SourceP, pst, pin, pout, pt) /\ 
          get O1 oskportid = Some (oskport kportl) /\
          get kportl kpaddr = Some (srcpid, Some a, Some chaddr, pcn', kpst) /\ 
          get O1 oschannelid = Some (oschannel chanl) /\ 
          get chanl chaddr = Some (cid, cdstn, cdstkpl, chtp) /\
          get O1 ibufsid = Some (ibufs ibmp) /\
          get O1 absecblsid = Some (absecblist els) /\
          get O1 abstcblsid = Some (abstcblist tls) /\ 
          dom_cur_tsk O1 td /\ 
          ibmp td = msg :: msgl /\ 
          dpl_upd kportl cdstkpl msg dpl dpl' /\ 
          ecbl_upd kportl cdstkpl dpl els els' tls /\
          tcbl_upd kportl cdstkpl dpl els tls tls' /\ 
          opv = None /\ 
          act = SendAct /\ 
          opo = Some
                  (set (set (set (set O1 osdomainportid (osdomainport dpl'))
                               abstcblsid (abstcblist tls'))
                          absecblsid (absecblist els'))
                     ibufsid (ibufs (upd_bufmp ibmp td msgl)))
  end.

Definition conditional_semrel vprt sem := 
  Aif |(prt_indom vprt, nil)| (fun O => exists a, vprt = Vptr a /\ is_intercore O a) {
      cslsemrel trivial_asrt (Z.to_nat (Int.unsigned sem)) 
    } else {
    spec_skip
  }. 

Definition store_msg
  (vl: vallist) (O1: osabst) (act: action) (rst: option val * option osabst) :=
  match rst with
  | (opv, opo) =>
      exists v dpl pcn pd pid pst pin pout n msgl,
      exists ibmp td m dpl', 
        vl = Vptr v :: nil /\ (* v is addr of source port *) 
          get O1 osdomainportid = Some (osdomainport dpl) /\
          get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort n msgl) /\
          get O1 ibufsid = Some (ibufs ibmp) /\          
          dom_cur_tsk O1 td /\ 
          ibmp td = m :: msgl /\
          dpl' = set dpl v (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort n (msgl ++ (m::nil))) /\
          act = SendAct /\ 
          opo = Some (set (set O1
                             osdomainportid (osdomainport dpl'))
                        ibufsid (ibufs (upd_bufmp ibmp td msgl)))
  end.


Definition has_no_cap_prtpost O :=
  exists t tls cspc pr st m pr0,
    get O curtid = Some (oscurt t) /\
      get O abstcblsid = Some (abstcblist tls) /\
      get tls t = Some (pr, st, m, pr0) /\ 
      get O cspaceid = Some (capcspace cspc) /\
      ~has_cat_cap pr0 cspc CAP_PORT_CLASS PORT_POST_CAP. 
          
Definition has_prtpost_cap O (pr: priority) :=
  exists cspc tps td,
    get O cspaceid = Some (capcspace cspc) /\
      tps_tst_corr O tps /\ 
      dom_for_prio pr = td /\ 
      has_post_cap tps cspc td. 

Definition qportpost (vl: vallist) :=
  match vl with
    vprt :: (Vint32 sem) :: vsr :: nil => 
      (* We model the msg buffer pointed to by "OSMsg *msg" in the abstract state.
           Hence, there is no message pointer v1 in the argument list. *)
      Aif (fun O => has_no_cap_prtpost O) {
          ret_val (| Vint32 (Int.repr USER_CAPABILITY_NONE) :: nil |) 
        } else {          
        ASSERT (fun O => vprt = Vnull \/ port_indomainport vprt O);;
        (
          Aif |(fun O => fun pr => has_port vprt O pr /\ has_prtpost_cap O pr, nil)|
          (fun O => vprt = Vnull) {
              ret_val (| Vint32 (Int.repr OS_PORT_ERR_NULL) :: nil |)  
            } else {
            Aif (fun O => not_port O vprt \/ wrong_core O vprt \/ wrong_dom O vprt) {
                ret_val (| Vint32 (Int.repr OS_ERR_PARTITION_UNMAPPED) :: nil |)  
              } else {
              Aif (fun O => exists a dpl pcn pd pid pdir pst pin pout pt, 
                       get O osdomainportid = Some (osdomainport dpl) /\
                         vprt = Vptr a /\ get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
                         (pdir <> SourceP \/ (exists ml, pt = SamplePort ml))) {
                  ret_val (| Vint32 (Int.repr OS_PORT_ERR_TYPE) :: nil |) 
                } else {
                Aif (fun O => exists a dpl pcn pd pid pdir pst pin pout pt,
                         get O osdomainportid = Some (osdomainport dpl) /\
                           vprt = Vptr a /\ get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
                       (Z.of_nat pid >= PORT_NUMS)%Z) {
                    ret_val (| Vint32 (Int.repr OS_PORT_ID_INVALID) :: nil |)  
                  } else {
                  spec_skip ;;
                  Aif |(fun O => fun pr => prt_indom vprt O pr /\ has_prtpost_cap O pr, nil)| 
                  (fun O => no_channel O vprt) {
                      ret_val (| Vint32 (Int.repr OS_ERR_PORT_NO_CHANNEL) :: nil |)
                    } else {
                    spec_seq 
                      (Aif (fun O => exists a, vprt = Vptr a /\ is_intercore O a) {
                           cslsemacc trivial_asrt (Z.to_nat (Int.unsigned sem)) vsr;;
                           Aif |(fun O => fun pr => prt_indom vprt O pr /\ has_prtpost_cap O pr, (vsr::nil))| 
                           (fun O => vsr = (Vint32 (Int.zero))) {
                               ret_val (| (Vint32 (Int.repr OS_CHANNEL_ERR_BEING_USED)) :: nil |)
                             } else { spec_skip } 
                         } else { spec_skip }) 
                      (Aif |(fun O => fun pr => prt_indom vprt O pr /\ has_prtpost_cap O pr, nil)| 
                        (fun O => has_dst_ports O vprt) {
                           q_send_to_domain (| vprt :: nil |);; (* might be necessary to convey that the _;;_ is atomic*)
                           conditional_semrel vprt sem;;
                           SCHED;;
                           ret_val (| Vint32 (Int.repr OS_NO_ERR)::nil |)
                         } else {
                          Aif (fun O => exists a dpl pcn pd pid pst pin pout n msgl,
                                   vprt = Vptr a /\ get O osdomainportid = Some (osdomainport dpl) /\ 
                                     get dpl a = Some (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort n msgl) /\
                                     (List.length msgl < n)%nat) {
                              store_msg (| vprt :: nil |);; (* might be necessary to convey that the _;;_ is atomic*)
                              conditional_semrel vprt sem;;
                              ret_val (| Vint32 (Int.repr OS_NO_ERR)::nil |) 
                            } else {
                            conditional_semrel vprt sem;;
                            ret_val (| Vint32 (Int.repr OS_NO_ERR)::nil |)                                       
                          }
                        }
                      ) 
                  }
                }
              }
            }
          }
        )
  }
| _ => ABORT 
end.


(* (************************************ QPortPend  **************************************) *)
  
Definition qportpend_block (vl : vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) :=  
  match rst with 
  | (opv, opo) =>
      exists v tm,
      exists dpl pcn pd pid pdir pst pin pout sz,
        vl = Vptr v :: Vint32 tm :: nil /\ 
          get O1 osdomainportid = Some (osdomainport dpl) /\
          get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout,  QueuePort sz nil) /\
          exists tls tls' p st t tskm sus t_opt p0,
            get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls) /\ 
              exists ecbls wt ecbls',
                get O1 absecblsid = Some (absecblist ecbls) /\
                  get ecbls v = Some (absport, wt)  /\ 
                  ecbls'= set ecbls v (absport, t :: wt)/\
                  get tls t = Some (p, st, tskm, sus, p0) /\
                  tls' = set tls t (p, wait (os_stat_port v) t_opt, tskm, sus, p0)/\
                  ((t_opt = Some tm /\ tm <> Int.zero) \/ (t_opt = None /\ tm = Int.zero)) /\
                  opv = None /\
                  act = TauAct /\ 
                  opo = Some (set (set O1 abstcblsid (abstcblist tls')) absecblsid (absecblist ecbls')) 
  end.

Definition msg_come O (* a *) := 
  (* exists dpl pcn pd pid pdir pst pin pout pm sz, *)
  (*   get O osdomainportid = Some (osdomainport dpl) /\ *)
  (*     get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout,  QueuePort sz pm) /\ *)
  exists tls p st t tskm sus p0,
    get O curtid = Some (oscurt t) /\
      get O abstcblsid = Some (abstcblist tls) /\ 
      get tls t = Some (p,st,tskm,sus,p0) /\
      tskm = Vint32 (Int.repr OS_PARTITION_MESSAGE_COME).

Definition qportpend_block_get_body
  (vl : vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) :=  
  match rst with 
  | (opv, opo) => 
      exists v tm,
      exists dpl pcn pd pid pdir pst pin pout sz,
      exists msg msgl,
        vl = Vptr v :: Vint32 tm :: nil /\ 
          get O1 osdomainportid = Some (osdomainport dpl) /\
          get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout, QueuePort sz (msg :: msgl)) /\
          exists tls tls' p st t sus p0,          
          exists dpl' obmp obmp', 
          get O1 curtid = Some (oscurt t) /\
          get O1 abstcblsid = Some (abstcblist tls) /\ 
          get tls t = Some (p, st, Vint32 (Int.repr OS_PARTITION_MESSAGE_COME), sus, p0) /\
          get O1 obufsid = Some (obufs obmp) /\ 
          tls' = set tls t (p, rdy, Vnull, sus,p0) /\
          dpl' = set dpl v (pcn, pd, pid, pdir, pst, pin, pout, QueuePort sz msgl) /\
          obmp' = upd_bufmp obmp (dom_for_prio p0) (obmp (dom_for_prio p0) ++ (msg::nil)) /\ 
          opv = Some (Vint32 (Int.repr OS_NO_ERR)) /\ 
          act = RecvAct /\ 
          opo = Some
                  (set
                     (set (set O1 abstcblsid (abstcblist tls')) osdomainportid (osdomainport dpl'))
                     obufsid (obufs obmp'))
  end.

Definition qportpend_block_timeout
  (vl : vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo) =>
      exists v tm,
      exists dpl pcn pd pid pdir pst pin pout pm sz,
        vl = Vptr v :: Vint32 tm :: nil /\ 
          get O1 osdomainportid = Some (osdomainport dpl) /\
          get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout, QueuePort sz pm) /\
          exists tls tls' p st t tskm sus p0,
            get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls) /\ 
              get tls t = Some (p, st, tskm, sus, p0) /\
              tskm <> Vint32 (Int.repr OS_PARTITION_MESSAGE_COME) /\
              tls' = set tls t (p, rdy, Vnull, sus, p0)/\
              exists ecbls wt ecbls',
                get O1 absecblsid = Some (absecblist ecbls) /\
                  get ecbls v = Some (absport, wt)  /\ 
                  In t wt /\ 
                  ecbls'= set ecbls v (absport, (remove_tid t wt))/\
                  opv = Some (Vint32 (Int.repr OS_TIMEOUT)) /\ 
                  act = TauAct /\ 
                  opo = Some (set (set O1 abstcblsid (abstcblist tls')) absecblsid (absecblist ecbls'))
  end.


Definition qportpend_notnil_body (vl : vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo) =>
      exists v tm,
      exists dpl pcn pd pid pdir pst pin pout sz,
      exists msg msgl,
      (* exists kportl kpaddr kpst channaddr, *)
      (* exists chanl cid cdn cdstkp ctype, *)
        exists dpl' obmp obmp' td,  
        vl = Vptr v :: tm :: nil /\ 
          get O1 osdomainportid = Some (osdomainport dpl) /\
          get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout, QueuePort sz (msg :: msgl)) /\
          (* get O1 oskportid = Some (oskport kportl) /\ *)
          (* get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) /\  *)
          (* get O1 oschannelid = Some (oschannel chanl) /\ *)
          (* get chanl channaddr = Some  (cid, cdn, cdstkp, ctype) /\  *)
          get O1 obufsid = Some (obufs obmp) /\ 
          dom_cur_tsk O1 td /\ 
          dpl' = set dpl v (pcn, pd, pid, pdir, pst, pin, pout,  QueuePort sz (msgl)) /\
          obmp' = upd_bufmp obmp td (obmp td ++ (msg::nil)) /\ 
          opv = None /\
          act = RecvAct /\ 
          opo = Some (set (set O1 osdomainportid (osdomainport dpl')) obufsid (obufs obmp'))
  end.

Definition port_not_empty O prt :=
  exists a dpl msg msgl pcn pd pid pdir pst, exists pin pout sz, 
    prt = Vptr a /\
      get O osdomainportid = Some (osdomainport dpl) /\
      get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout, QueuePort sz (msg :: msgl)). 


Definition has_no_cap_prtpend O := 
  exists t tls cspc pr st m pr0,
    get O curtid = Some (oscurt t) /\
      get O abstcblsid = Some (abstcblist tls) /\
      get tls t = Some (pr, st, m, pr0) /\ 
      get O cspaceid = Some (capcspace cspc) /\
      ~has_cat_cap pr0 cspc CAP_PORT_CLASS PORT_PEND_CAP.   


Definition qportpend (vl: vallist) :=
  match vl with
    vprt :: v0 (* tm *) :: (Vint32 sem) :: vsr :: nil => 
      (* We model the msg buffer pointed to by "OSMsg *msg" in the abstract state.
           Hence, there is no message pointer v1 in the argument list. *)
      Aif (fun O => has_no_cap_prtpend O) {
          ret_val (| Vint32 (Int.repr USER_CAPABILITY_NONE) :: nil |)  
        } else {
      ASSERT (fun O => vprt = Vnull \/ port_indomainport vprt O);; 
      (
        Aif |(has_port vprt, nil)| (fun O => vprt = Vnull) {
            ret_val (| Vint32 (Int.repr OS_PORT_ERR_NULL) :: nil |)  
          } else {                      
          Aif (fun O => not_port O vprt \/ wrong_core O vprt \/ wrong_dom O vprt) { 
              ret_val (| Vint32 (Int.repr OS_ERR_PARTITION_UNMAPPED) :: nil |)  
            } else {
            Aif (fun O => exists a dpl pcn pd pid pst pin pout pt,
                     vprt = Vptr a /\ 
                       get O osdomainportid = Some (osdomainport dpl) /\
                       get dpl a = Some (pcn, pd, pid, SourceP, pst, pin, pout, pt)) { 
                ret_val (| Vint32 (Int.repr OS_PORT_ERR_DIRECTION_TYPE) :: nil |) 
              } else {
              Aif (fun O => exists a dpl pcn pd pid pst pin pout msg, 
                       vprt = Vptr a /\ 
                         get O osdomainportid = Some (osdomainport dpl) /\
                         get dpl a = Some (pcn, pd, pid, DestinationP, pst, pin, pout, SamplePort msg)) {
                  ret_val (| Vint32 (Int.repr OS_PORT_ERR_TYPE) :: nil |) 
                } else {
                spec_skip (* preemption possible after ensuring port type is correct *) ;;
                Aif |(prt_indom vprt, nil)| (fun O => no_channel O vprt) {
                    ret_val (| Vint32 (Int.repr OS_ERR_PORT_NO_CHANNEL) :: nil |) 
                  } else {
                  spec_seq 
                    (Aif (fun O => exists a, vprt = Vptr a /\ is_intercore O a) {
                      cslsemacc trivial_asrt (Z.to_nat (Int.unsigned sem)) vsr;;
                      Aif |(prt_indom vprt, (vsr::nil))| (fun O => vsr = (Vint32 (Int.zero))) {
                            ret_val (| (Vint32 (Int.repr OS_CHANNEL_ERR_BEING_USED)) :: nil |)
                       } else { spec_skip }  
                     } else { spec_skip } )
                    (Aif |(prt_indom vprt, nil)| (fun O => port_not_empty O vprt) {
                          qportpend_notnil_body (| vprt :: v0 :: nil |) ;;
                          conditional_semrel vprt sem;; 
                          ret_val (| (Vint32 (Int.repr OS_NO_ERR)) :: nil |)
                       } else {
                          conditional_semrel vprt sem;; 
                          (prt_indom vprt, nil) # qportpend_block [| vprt :: v0 :: nil |] ;;
                          (sched (prt_indom vprt, nil)) ;;
                          Aif |(prt_indom vprt, nil)| (fun O => msg_come O) {
                              qportpend_block_get_body (| vprt :: v0 :: nil |) 
                            } else {
                            qportpend_block_timeout (| vprt :: v0 :: nil |) 
                          }                        
                      }
                    )
                }
              }
            }
          }
        }
      )
  }
  | _ => ABORT
  end.


(* (************************************ SamplePortPost  **************************************) *)

Definition sdpl_upd
  (kprtmp: KernelPMod.map) (dstkpaddrs: list addrval) (m: msg)
  (dpl dpl': DomainPortMod.map) pin :=
  (forall a,
      (exists a' cha pcn' kpst pid a0, 
          List.In a' dstkpaddrs /\
            get kprtmp a' = Some (pid, Some a0, Some cha, pcn', kpst) /\
            exists pcn pd pst pin0 pout mopt, 
              get dpl a = Some (pcn, pd, pid, DestinationP, pst, pin0, pout, SamplePort mopt)
              /\ get dpl' a = Some (pcn, pd, pid, DestinationP, pst, pin, pout, SamplePort (Some m)))
      \/
        (~(exists a' cha pcn' kpst pid a0,
               List.In a' dstkpaddrs /\
                 get kprtmp a' = Some (pid, Some a0, Some cha, pcn', kpst) /\
                 exists pcn pd pst pin0 pout mopt, 
                   get dpl a = Some (pcn, pd, pid, DestinationP, pst, pin0, pout, SamplePort mopt)
           ) /\
           get dpl' a = get dpl a)
  ). 

Definition sample_send_to_domain 
  (vl: vallist) (O1: osabst) (act: action) (rst: option val * option osabst) :=
  match rst with
  | (opv, opo) =>
      exists v dpl pcn pd srcpid pst pin pout pt,
      exists kportl kpaddr a chaddr pcn' kpst, 
      exists chanl cid cdstn cdstkpl chtp,
      exists ibmp td msg msgl,
      exists dpl', 
        vl = Vptr v :: nil /\ (* v is addr of source port *) 
          get O1 osdomainportid = Some (osdomainport dpl) /\
          get dpl v = Some (pcn, pd, srcpid, SourceP, pst, pin, pout, pt) /\ 
          get O1 oskportid = Some (oskport kportl) /\
          get kportl kpaddr = Some (srcpid, Some a, Some chaddr, pcn', kpst) /\ 
          get O1 oschannelid = Some (oschannel chanl) /\ 
          get chanl chaddr = Some (cid, cdstn, cdstkpl, chtp) /\
          get O1 ibufsid = Some (ibufs ibmp) /\
          dom_cur_tsk O1 td /\ 
          ibmp td = msg :: msgl /\ 
          sdpl_upd kportl cdstkpl msg dpl dpl' pin /\ 
          opv = None /\ 
          act = SendAct /\ 
          opo = Some
                  (set (set O1
                          osdomainportid (osdomainport dpl'))
                     ibufsid (ibufs (upd_bufmp ibmp td msgl)))
  end.

Definition sampleportpost (vl: vallist) :=
  match vl with
    vprt :: (Vint32 sem) :: vsr :: nil => 
      (* We model the msg buffer pointed to by "OSMsg *msg" in the abstract state.
           Hence, there is no message pointer v1 in the argument list. *)
      Aif (fun O => has_no_cap_prtpost O) {
          ret_val (| Vint32 (Int.repr USER_CAPABILITY_NONE) :: nil |) 
        } else {          
        ASSERT (fun O => vprt = Vnull \/ port_indomainport vprt O);;
        (
          Aif |(fun O => fun pr => has_port vprt O pr /\ has_prtpost_cap O pr, nil)|
          (fun O => vprt = Vnull) {
              ret_val (| Vint32 (Int.repr OS_PORT_ERR_NULL) :: nil |)  
            } else {
            Aif (fun O => not_port O vprt \/ wrong_core O vprt \/ wrong_dom O vprt) {
                ret_val (| Vint32 (Int.repr OS_ERR_PARTITION_UNMAPPED) :: nil |)  
              } else {
              Aif (fun O => exists a dpl pcn pd pid pdir pst pin pout pt, 
                       get O osdomainportid = Some (osdomainport dpl) /\
                         vprt = Vptr a /\ get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
                         (pdir <> SourceP \/ (exists n msgl, pt = QueuePort n msgl))) { 
                  ret_val (| Vint32 (Int.repr OS_PORT_ERR_TYPE) :: nil |) 
                } else {
                Aif (fun O => exists a dpl pcn pd pid pdir pst pin pout pt,
                         get O osdomainportid = Some (osdomainport dpl) /\
                           vprt = Vptr a /\ get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
                           (Z.of_nat pid >= PORT_NUMS)%Z) {
                    ret_val (| Vint32 (Int.repr OS_PORT_ID_INVALID) :: nil |)  
                  } else {
                  spec_skip ;;
                  Aif |(fun O => fun pr => prt_indom vprt O pr /\ has_prtpost_cap O pr, nil)| 
                  (fun O => no_channel O vprt) {
                      ret_val (| Vint32 (Int.repr OS_ERR_PORT_NO_CHANNEL) :: nil |)
                    } else {
                    spec_seq 
                      (Aif (fun O => exists a, vprt = Vptr a /\ is_intercore O a) {
                           cslsemacc trivial_asrt (Z.to_nat (Int.unsigned sem)) vsr;;
                           Aif |(fun O => fun pr => prt_indom vprt O pr /\ has_prtpost_cap O pr, (vsr::nil))| 
                           (fun O => vsr = (Vint32 (Int.zero))) {
                               ret_val (| (Vint32 (Int.repr OS_CHANNEL_ERR_BEING_USED)) :: nil |)
                             } else { spec_skip } 
                         } else { spec_skip }) 
                      (
                        (fun O => fun pr => prt_indom vprt O pr /\ has_prtpost_cap O pr, nil)
                          # sample_send_to_domain [| vprt :: nil |];; 
                        conditional_semrel vprt sem;;
                        ret_val (| Vint32 (Int.repr OS_NO_ERR)::nil |) 
                      )
                  }
                }
              }
            }
          }
        )
  }
| _ => ABORT
end. 

(* (************************************ PortAccept  **************************************) *)

Definition has_no_cap_prtaccept O := 
  exists t tls cspc pr st m pr0,
    get O curtid = Some (oscurt t) /\
      get O abstcblsid = Some (abstcblist tls) /\
      get tls t = Some (pr, st, m, pr0) /\ 
      get O cspaceid = Some (capcspace cspc) /\
      ~has_cat_cap pr0 cspc CAP_PORT_CLASS PORT_ACCEPT_CAP.   

Definition receive_port_msg 
  (vl: vallist) (O1: osabst) (act: action) (rst: option val * option osabst) :=
  match rst with
  | (opv, opo) =>
      exists v dpl pcn pd srcpid pst pin pout pt,
      exists msg obmp td,
      exists dpl' obmp', 
        vl = Vptr v :: nil /\ (* v is addr of source port *) 
          get O1 osdomainportid = Some (osdomainport dpl) /\
          get O1 obufsid = Some (obufs obmp) /\ 
          get dpl v = Some (pcn, pd, srcpid, DestinationP, pst, pin, pout, pt) /\ 
          ((exists msgl n,
               pt = QueuePort n (msg::msgl)
               /\ dpl' = set dpl v (pcn, pd, srcpid, DestinationP, pst, pin, pout, QueuePort n msgl))
           \/
             pt = SamplePort (Some msg)
             /\ dpl' = dpl 
          )
        /\ dom_cur_tsk O1 td 
        /\ obmp' = upd_bufmp obmp td (obmp td ++ (msg::nil))
        /\ act = RecvAct
        /\ opo = Some (set (set O1 osdomainportid (osdomainport dpl')) obufsid (obufs obmp'))
  end. 

Definition portaccept (vl: vallist) :=
  match vl with
    vprt :: (Vint32 sem) :: vsr :: nil => 
      (* We model the msg buffer pointed to by "OSMsg *msg" in the abstract state.
           Hence, there is no message pointer v1 in the argument list. *)
      Aif (fun O => has_no_cap_prtaccept O) {
          ret_val (| Vint32 (Int.repr USER_CAPABILITY_NONE) :: nil |)  
        } else {
      ASSERT (fun O => vprt = Vnull \/ port_indomainport vprt O);; 
      (
        Aif |(has_port vprt, nil)| (fun O => vprt = Vnull) {
            ret_val (| Vint32 (Int.repr OS_PORT_ERR_NULL) :: nil |)  
          } else {                      
          Aif (fun O => not_port O vprt \/ wrong_core O vprt \/ wrong_dom O vprt) { 
              ret_val (| Vint32 (Int.repr OS_ERR_PARTITION_UNMAPPED) :: nil |)  
            } else {
            Aif (fun O => exists a dpl pcn pd pid pst pin pout pt,
                     vprt = Vptr a /\ 
                       get O osdomainportid = Some (osdomainport dpl) /\
                       get dpl a = Some (pcn, pd, pid, SourceP, pst, pin, pout, pt)) { 
                ret_val (| Vint32 (Int.repr OS_PORT_ERR_DIRECTION_TYPE) :: nil |) 
              } else {
              spec_skip (* preemption possible after ensuring port type is correct *) ;;
              Aif |(prt_indom vprt, nil)| (fun O => no_channel O vprt) {
                   ret_val (| Vint32 (Int.repr OS_ERR_PORT_NO_CHANNEL) :: nil |) 
               } else {
                spec_seq 
                  (Aif (fun O => exists a, vprt = Vptr a /\ is_intercore O a) {
                       cslsemacc trivial_asrt (Z.to_nat (Int.unsigned sem)) vsr;;
                       Aif |(prt_indom vprt, (vsr::nil))| (fun O => vsr = (Vint32 (Int.zero))) {
                           ret_val (| (Vint32 (Int.repr OS_CHANNEL_ERR_BEING_USED)) :: nil |)
                       } else { spec_skip }  
                     } else { spec_skip })
                  (
                    (fun O => fun pr => prt_indom vprt O pr, nil)
                      # receive_port_msg [| vprt :: nil |];; 
                    conditional_semrel vprt sem;;
                    ret_val (| Vint32 (Int.repr OS_NO_ERR)::nil |) 
                  )
              }
            }
          }
        }
      )
  }
| _ => ABORT
end. 
                  
              
