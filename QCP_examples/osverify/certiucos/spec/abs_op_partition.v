Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import abs_op.
Require Import abs_op_corecommu.
Require Import abs_op_tmr.
Require Import os_inv.

(* 这些函数参数中的 port ptr 应该要求是在OSDOMAINPORT 里面的 *)
(*************************************************************************************************************************************************)
(******************************************************************  Common Error   **************************************************************)
(*************************************************************************************************************************************************)
Definition err_pendisr (vl: vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) => vl =  nil /\ opv = Some (Vint32 (Int.repr OS_ERR_PEND_ISR)) /\
      opo = Some O1 
  end.

Definition err_portnull (port: vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) => port = Vnull :: nil /\ opv = Some (Vint32 (Int.repr OS_PORT_ERR_NULL)) /\
      opo = Some O1 
  end.

Definition err_unmapped (port: vallist)  (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
     exists v dpl,
     exists pcn pd pid pdir pst pin pout pt,
     exists tid tcbl pri st msg sus,
      port = Vptr v :: nil /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
      get O1 curtid = Some (oscurt tid) /\
      get O1 abstcblsid = Some (abstcblist tcbl) /\
      get tcbl tid = Some (pri, st, msg, sus) /\ 
      (* (Z.of_nat pcn <> DNUM \/  Int.eq (Int.shru pri (Int.repr 3)) (Int.repr (Z.of_nat pd)) = false) /\ *)
      Int.eq (Int.shru pri (Int.repr 3)) (Int.repr (Z.of_nat pd)) = false /\
      opv = Some (Vint32 (Int.repr OS_ERR_PARTITION_UNMAPPED)) /\
      opo = Some O1 
  end.

Definition err_msgnull (err: Z)  (msg: vallist)  (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) => msg = Vnull :: nil /\ opv = Some (Vint32 (Int.repr err)) /\
      opo = Some O1 
  end.

Definition err_idinvalid (port: vallist)  (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
     exists v dpl,
     exists pcn pd pid pdir pst pin pout pt,
      port = Vptr v :: nil /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
      (Z.of_nat pid >= PORT_NUMS)%Z /\
      opv = Some (Vint32 (Int.repr OS_PORT_ID_INVALID)) /\
      opo = Some O1 
  end.

Definition err_unbind (port: vallist)  (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
     exists v dpl,
     exists pcn pd pid pdir pst pin pout pt,
     exists kportl,
      port = Vptr v :: nil /\
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
      get O1 oskportid = Some (oskport kportl) /\
      (~ exists kpaddr kpchan kpst, get kportl kpaddr = Some (pid, Some v, kpchan, pcn, kpst)) /\ 
      opv = Some (Vint32 (Int.repr OS_ERR_PORT_UNBIND)) /\
      opo = Some O1 
  end.

Definition err_nochannel (port: vallist)  (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
     exists v dpl,
     exists pcn pd pid pdir pst pin pout pt,
     exists kportl kpaddr kpst,
      port = Vptr v :: nil /\
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
      get O1 oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some v, None, pcn, kpst) /\ 
      opv = Some (Vint32 (Int.repr OS_ERR_PORT_NO_CHANNEL)) /\
      opo = Some O1 
  end.

Definition Semacc_err  sem :=
  match sem with
  | Vint32 semn => cslsemacc (Z.to_nat (Int.unsigned semn)) (Vint32 (Int.zero))
  | _ => spec_abort
  end.

Definition Semacc_succ  sem :=
  match sem with
  | Vint32 semn => cslsemacc (Z.to_nat (Int.unsigned semn)) (Vint32 (Int.one))
  | _ => spec_abort
  end.

Definition Semrelease  sem :=
  match sem with
  | Vint32 semn => cslsemrel (Z.to_nat (Int.unsigned semn)) 
  | _ => spec_abort
  end.

(****************************************************************** SamplePortPost  **************************************************************)
(* if (port->direction != SOURCE || port->mode != SAMPLE ) {    return (INT8U)(OS_PORT_ERR_TYPE); } *)
Definition err_porttype (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
    exists v,
     exists dpl pcn pd pid pdir pst pin pout pt,
      vl = Vptr v :: nil /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
      (pdir <> SourceP \/ (exists sz ml, pt = QueuePort sz ml)) /\ 
      opv = Some (Vint32 (Int.repr OS_PORT_ERR_TYPE)) /\
      opo = Some O1 
  end.

Definition samplepost_msg (vl : vallist) (O1: osabst) : Prop :=
  exists mdata mlen cHeapl cHeape cHeapt,
        vl = Vint32 mlen :: Vptr mdata :: nil /\
        get O1 oscoreheapid = Some (oscoreheap (cHeapl,cHeape, cHeapt )) /\ 
        In_heapl_addrval cHeapl mdata (Z.to_nat (Int.unsigned mlen)).

Definition update_dstp_msg (dstp : Port) (msg : list val) (dstp' : Port) :=
  match dstp with 
  | (pcn, pd, pid, pdir, pst, pin, pout, SamplePort _) => dstp' = (pcn, pd, pid, pdir, pst, pin, pout, SamplePort (Some msg))
  | _ => False 
  end.

Definition samplepost_memcpy (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
    exists v m,
    exists dpl pcn pd pid pst pin pout pm,
      vl = Vptr v :: Vptr m ::  nil /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, SamplePort pm) /\
      exists intick, get O1 ostmid = Some (ostm intick) /\
      exists cHeapl cHeape cHeapt,
        get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\
      exists mlen msg, 
      (* OS_Msg 这个结构体的起始地址开始存了 [length] ++ msg 这个vallist *)
        Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
      exists dpl', 
        dpl' = set dpl v (pcn, pd, pid, SourceP, pst, Z.to_nat (Int.unsigned intick), pout, SamplePort (Some msg))/\
        opv = None /\ 
        opo = Some (set O1 osdomainportid (osdomainport dpl') )
  end.

Definition samplepost_dstplength_coresem (vl : vallist) (O1: osabst) : Prop :=
  exists v m vsem vsdstcl,
    exists dpl pcn pd pid pst pin pout pm,
     exists kportl kpaddr kpst channaddr,
     exists chanl cid cdn cdstkp,
      vl = Vptr v :: Vptr m :: Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: vsem :: vsdstcl  /\ 
      (length vsdstcl = length cdstkp)%nat /\
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, SamplePort pm) /\
      get O1 oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) /\ 
      get O1 oschannelid = Some (oschannel chanl) /\
      ( ( exists csemid,
          vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\
          Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstcl /\
          get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/ 
        vsem = Vnull /\ 
        Forall (fun (v:val) => v = Vnull) vsdstcl /\  
        get chanl channaddr = Some  (cid, cdn, cdstkp, IncoreC) ) /\
      ( forall n, (n < (length cdstkp))%nat -> 
        exists dstpaddr dstpcn dstpd dstpid dstpst dstpin dstpout dstpm,
        exists dstkpaddr dstkpst nextdst,
        nth_error cdstkp n = Some dstkpaddr /\ 
        get kportl dstkpaddr = Some (dstpid, Some dstpaddr, Some channaddr, dstpcn, dstkpst) /\ 
        get dpl dstpaddr = Some (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, SamplePort dstpm) /\
        ((Z.of_nat dstpcn) <> DNUM -> nth_error vsdstcl n = Some (Vint32 (Int.repr (Z.of_nat dstpcn)))) ).

Definition samplepost_sendmemcpy_one (n: nat) (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
    exists v m vsem vsdstcl,
    exists dpl pcn pd pid pst pin pout pm,
     exists kportl kpaddr kpst channaddr,
     exists chanl cid cdn cdstkp,
      vl = Vptr v :: Vptr m :: Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: vsem :: vsdstcl /\
      (length cdstkp = length vsdstcl)%nat /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, SamplePort pm) /\
      get O1 oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) /\ 
      get O1 oschannelid = Some (oschannel chanl) /\
      ( ( exists csemid,
          vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\
          Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstcl /\
          get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/ 
        vsem = Vnull /\  
        Forall (fun (v:val) => v = Vnull) vsdstcl /\  
        get chanl channaddr = Some  (cid, cdn, cdstkp, IncoreC)) /\
      exists cHeapl cHeape cHeapt,
        get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\
      ( ~ ( exists mlen msg,
              Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
              (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ) /\ opo = None \/
      exists mlen msg,
        Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
        (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z /\
      (* OS_Msg 这个结构体的起始地址开始存了 [length] ++ msg 这个vallist *)
      exists dstpaddr dstpcn dstpd dstpid dstpst dstpin dstpout dstpm,
      exists dstkpaddr dstkpst nextdst,
      exists dpl' tm,
        nth_error cdstkp ((length cdstkp) - n)%nat = Some dstkpaddr /\ 
        get O1 ostmid = Some (ostm tm) /\
        get kportl dstkpaddr = Some (dstpid, Some dstpaddr, Some channaddr, dstpcn, dstkpst) /\ 
        get dpl dstpaddr = Some (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, SamplePort dstpm) /\ 
        ((Z.of_nat dstpcn) <> DNUM ->
          nth_error vsdstcl ((length cdstkp) - n)%nat =
              Some (Vint32 (Int.repr (Z.of_nat dstpcn)))) /\ 
        dpl' = set dpl dstpaddr (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, pin, Z.to_nat (Int.unsigned tm), SamplePort (Some msg))/\
        opv = None /\ 
        opo = Some (set O1 osdomainportid (osdomainport dpl') ))
  end.

Fixpoint samplepost_sendmemcpy_aux_Incore (n : nat) (vl: vallist ) : spec_code :=
  match n with 
  | O => END None
  | S n' =>  (samplepost_sendmemcpy_one (S n')) (|vl|) ;; 
             samplepost_sendmemcpy_aux_Incore n' vl 
  end.

Definition samplepost_generateipc (n: nat) (vl : vallist) : spec_code :=
  match vl with 
  | Vptr v :: Vptr m :: Vint32 vlen :: Vint32 csemid :: vdstcl =>
    match (nth_error vdstcl ((length vdstcl) - n)%nat) with
    | Some (Vint32 dstn) =>
        coreint (Z.to_nat (Int.unsigned dstn)) (Vint32 (Int.repr GET_PORT_MESSAGE)) 
    | _ => spec_abort 
    end
  | _ => spec_abort 
  end.

Fixpoint samplepost_sendmemcpy_aux_Outcore (n : nat) (vl: vallist ) : spec_code :=
  match n with 
  | O => END None
  | S n' =>  (samplepost_sendmemcpy_one (S n')) (|vl|) ;; 
             samplepost_generateipc (S n') vl ;;
             samplepost_sendmemcpy_aux_Outcore n' vl 
  end.

Definition samplepost_sendmemcpy_aux (vl: vallist ) : spec_code :=
  match vl with 
  | Vptr v :: Vptr m :: Vint32 vlen :: Vnull :: vdstcl => 
        let dtsl := Z.to_nat (Int.unsigned vlen) in 
          spec_code_cons
            (samplepost_sendmemcpy_aux_Incore dtsl vl)
            (END (Some (Vint32 (Int.repr OS_NO_ERR ))))
  | Vptr v :: Vptr m :: Vint32 vlen :: Vint32 sem :: vdstcl => 
        let dtsl := Z.to_nat (Int.unsigned vlen) in 
          Semacc_err (Vint32 sem ) ;; END (Some (Vint32 (Int.repr OS_CHANNEL_ERR_BEING_USED))) ?? 
          Semacc_succ (Vint32 sem ) ;;
          spec_code_cons
            (samplepost_sendmemcpy_aux_Outcore dtsl vl)
            ( Semrelease (Vint32 sem ) ;;
              END (Some (Vint32 (Int.repr OS_NO_ERR ))))
  | _ => spec_abort
 end.

Definition samplepost_sendmemcpy vl: spec_code :=
  ASSERT (samplepost_dstplength_coresem vl) ;; samplepost_sendmemcpy_aux vl.


Definition port_indomainport v (O1: osabst) : Prop :=
  match v with 
  | Vptr v =>
      exists dpl pd pid pdir pst pin pout pt,
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (Z.to_nat DNUM, pd, pid, pdir, pst, pin, pout, pt)
  | _ => False
  end.

Definition valid_port v (O1:osabst): Prop :=
   v = Vnull \/ port_indomainport v O1. 

Definition samplepostcode (vl : vallist) :=
  match vl with
  | nil => spec_abort
  | v :: nil => spec_abort
  | _ :: _ :: nil => spec_abort 
  | v0 :: v1 :: v2 :: nil => spec_abort
  | v0 :: v1 :: v2 :: v3:: nil => spec_abort
  | v0 :: v1 :: v2 :: v3:: v4 :: vl' => 
                    ASSERT (port_indomainport v0) ;;
                    ( err_unmapped (|v0::nil|) ??
                      err_msgnull (OS_ERR_POST_NULL_PTR) (|v1::nil|) ??
                      err_porttype (|v0::nil|) ??
                      err_nochannel (|v0::nil|) ??
                      samplepost_sendmemcpy vl  )
  end.

Definition samplepostapi := (samplepostcode, (Tint8, Tptr OS_Port :: Tptr OSMsg_t :: nil)).

(******************************************************************  PortAccept  **************************************************************)

Definition portacc_err_dire (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
     exists v,
     exists dpl pcn pd pid pst pin pout pt,
      vl = Vptr v :: nil /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, pt) /\
      opv = None /\
      opo = Some O1 
  end.

Definition portacc_err_msgnull (msg: vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) => msg = Vnull :: nil /\ opv = None /\ opo = Some O1 
  end.

Definition portacc_err_nochannel (port: vallist)  (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
     exists v dpl,
     exists pcn pd pid pdir pst pin pout pt,
     exists kportl kpaddr kpst,
      port = Vptr v :: nil /\
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
      get O1 oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some v, None, pcn, kpst) /\ 
      opv = None /\
      opo = Some O1 
  end.

Definition corecommu_ (port: val) (sem: val) (O1: osabst) : Prop :=
  match port with 
  | Vptr v =>   exists v dpl,
                exists pcn pd pid pdir pst pin pout pt,
                exists kportl kpaddr kpst channaddr,
                exists chanl cid cdstn cdstkpl csem,
                port = Vptr v /\ sem = Vint32 (Int.repr (Z.of_nat csem)) /\
                get O1 osdomainportid = Some (osdomainport dpl) /\
                get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
                get O1 oskportid = Some (oskport kportl) /\
                get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) /\ 
                get O1 oschannelid = Some (oschannel chanl) /\ 
                get chanl channaddr = Some (cid, cdstn, cdstkpl, OutcoreC csem)
  | _ => False
  end.

Definition portacc_queue_nil (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
     exists v m,
     exists dpl pcn pd pid pdir pst pin pout sz,
     (* exists kportl kpaddr kpst channaddr, *)
     (* exists chanl cid cdn cdstkp, *)
      vl = Vptr v :: Vptr m :: nil /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout,  QueuePort sz nil) /\
      (* get O1 oskportid = Some (oskport kportl) /\ *)
      (* get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) /\  *)
      (* get O1 oschannelid = Some (oschannel chanl) /\ *)
      (* ((exists csemid, get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/  *)
      (* get chanl channaddr = Some  (cid, cdn, cdstkp, IncoreC))/\  *)
      (* exists cHeapl cHeape cHeapt reshl, *)
      (* get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\  *)
      (* update_heapl_addrval cHeapl m 1%nat (Vint32 Int.zero :: nil) reshl /\  *)
      opv = None /\
      opo = Some O1
  end.

Definition portacc_queue_notnil (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
    exists v m dpl,
    exists pcn pd pid pdir pst pin pout sz,
     exists msg msgl,
     exists kportl kpaddr kpst channaddr,
     exists chanl cid cdn cdstkp ct,
      vl = Vptr v :: Vptr m :: nil /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout, QueuePort sz (msg :: msgl)) /\
      get O1 oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) /\ 
      get O1 oschannelid = Some (oschannel chanl) /\
      get chanl channaddr = Some  (cid, cdn, cdstkp, ct) /\ 
      exists cHeapl cHeape cHeapt,
        get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\ 
        (~ In_heapl_addrval cHeapl m (S (length msg)) /\ opo = None \/
        exists reshl portl',
          update_heapl_addrval cHeapl m (S (length msg)) (Vint32 (Int.repr (Z.of_nat (length msg))) :: msg) reshl /\
          portl' = set dpl v (pcn, pd, pid, pdir, pst, pin, pout,  QueuePort sz (msgl)) /\ 
          opv = None /\
          opo = Some (set (set O1 oscoreheapid (oscoreheap (reshl, cHeape, cHeapt))) osdomainportid (osdomainport portl')))
  end.

Definition portacc_sample (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo) =>
     exists v m dpl,
     exists pcn pd pid pdir pst pin pout,
     exists msg,
     exists kportl kpaddr kpst channaddr,
     exists chanl cid cdn cdstkp ct,
      vl = Vptr v :: Vptr m :: nil /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout, SamplePort (Some msg)) /\
      get O1 oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) /\ 
      get O1 oschannelid = Some (oschannel chanl) /\
      get chanl channaddr = Some  (cid, cdn, cdstkp, ct) /\ 
      exists cHeapl cHeape cHeapt,
        get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\ 
        ( ~ In_heapl_addrval cHeapl m (S (length msg)) /\ opo = None \/
        exists reshl,
          update_heapl_addrval cHeapl m (S (length msg)) (Vint32 (Int.repr (Z.of_nat (length msg))) :: msg) reshl /\
          opv = None /\
          opo = Some (set O1 oscoreheapid (oscoreheap (reshl, cHeape, cHeapt))))
  end.

Definition port_acc_without_chk (vl : vallist) :=
  match vl with
  | nil => spec_abort
  | v :: nil => spec_abort
  | v0 :: v1 :: nil => spec_abort
  | v0 :: v1 :: v2 :: vl' => 
                  ASSERT (port_indomainport v0) ;;
                  ( portacc_err_dire (|(v0::nil)|) ??
                    portacc_err_msgnull (|v1::nil|) ??
                    portacc_err_nochannel (|v0::nil|) ??
                    (* 核间通信 *)
                    ( ASSERT (corecommu_ v0 v2) ;;
                      ( Semacc_err v2 ??
                        ( Semacc_succ v2 ;;
                          ( portacc_queue_nil (|(v0::v1::nil)|) ??
                            portacc_queue_notnil (|(v0::v1::nil)|) ??
                            portacc_sample (|(v0::v1::nil)|) ) ;;
                          Semrelease v2 ) ) ) ??
                    (* 核内通信 *)
                    ( portacc_queue_nil (|(v0::v1::nil)|) ??
                      portacc_queue_notnil (|(v0::v1::nil)|) ??
                      portacc_sample (|(v0::v1::nil)|) ) )
  end.

Definition portacccode (vl : vallist) :=
  match vl with
  | nil => spec_abort
  | v :: nil => spec_abort
  | v0 :: v1 :: nil => spec_abort
  | v0 :: v1 :: v2 :: vl' => 
                  ( ASSERT (port_indomainport v0) ;;
                    err_unmapped (|v0::nil|)  ) ??
                  spec_code_cons
                  ( port_acc_without_chk vl )
                  ( END (Some (Vint32 (Int.repr OS_PORT_ERR_DIRECTION_TYPE))) ??
                    END (Some (Vint32 (Int.repr OS_PORT_MSG_ARG_NULL))) ??
                    END (Some (Vint32 (Int.repr OS_ERR_PORT_NO_CHANNEL))) ??
                    END (Some (Vint32 (Int.repr OS_CHANNEL_ERR_BEING_USED))) ??
                    END (Some (Vint32 (Int.repr OS_NO_ERR)))  )
  end.

Definition portaccapi := (portacccode, (Tint8, Tptr OS_Port :: Tptr OSMsg_t :: nil)).

(******************************************************************  PortFlush  **************************************************************)
(* OS_EVENT_TYPE_PORT 在OSINV中要求 *)

Definition portflush_succ (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo) =>
     exists v dpl,
     exists pcn pd pid pdir pst pin pout pt,
     exists kportl kpaddr kpst chan,
      vl = Vptr v :: nil /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
      get O1 oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some v, chan, pcn, kpst) /\ 
      exists pt', ((exists msg, pt = SamplePort msg /\ pt' = SamplePort (Some (@nil val))) \/
                   (exists sz msg, pt = QueuePort sz msg /\ pt' = QueuePort sz (nil))) /\
      opv = None /\
      opo = Some (set O1 osdomainportid (osdomainport (set dpl v (pcn, pd, pid, pdir, pst, pin, pout, pt'))))
  end. 

Definition portflushcode (vl : vallist) :=
  match vl with
  | nil => spec_abort
  | v :: nil => spec_abort
  | v0 :: v1 :: vl' => 
                  ASSERT (port_indomainport v0) ;;
                  ( err_unmapped (|v0::nil|) ??
                    ( ASSERT (corecommu_ v0 v1) ;; 
                      ( ( Semacc_err v1 ;;
                          END (Some (Vint32 (Int.repr OS_CHANNEL_ERR_BEING_USED))) ) ??
                        ( Semacc_succ v1 ;;
                          portflush_succ (|v0 :: nil |) ;;
                          Semrelease v1 ;;
                          END (Some (Vint32 (Int.repr OS_NO_ERR ))) ) ) ) ??
                    ( portflush_succ (|v0 :: nil |) ;;
                      END (Some (Vint32 (Int.repr OS_NO_ERR ))) ) )
  end.

Definition portflushapi := (portflushcode, (Tint8, Tptr OS_Port:: nil)).

  
(******************************************************************  qportpost_port_kport_channel_map  **************************************************************)
Definition err_porttype_queue (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
    exists v,
     exists dpl pcn pd pid pdir pst pin pout pt,
      vl = Vptr v :: nil /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
      (pdir <> SourceP \/ (exists ml, pt = SamplePort ml)) /\ 
      opv = Some (Vint32 (Int.repr OS_PORT_ERR_TYPE)) /\
      opo = Some O1 
  end.

(* 用户端口 内核端口 通道地址对应*)
Definition qportpost_port_kport_channel_map (vl : vallist) (O1: osabst) : Prop :=
  exists v m vsem vsdstcl,
    exists dpl pcn pd pid pst pin pout pm sz,
      exists kportl kpaddr kpst channaddr,
      exists chanl cid cdn cdstkp,
      vl = Vptr v :: Vptr m :: Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: vsem :: vsdstcl  /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz pm) /\
      get O1 oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) /\ 
      get O1 oschannelid = Some (oschannel chanl) /\
      ((exists csemid, vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\ 
                        get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/ 
        vsem = Vnull /\  get chanl channaddr = Some  (cid, cdn, cdstkp, IncoreC)).

(*待发送的Msg存在heapl中*)
Definition qportpost_msg_in_heapl(vl: vallist)(O1: osabst): Prop:=
  exists v m vl',
  (vl = v :: Vptr m :: vl')  /\ 
  (exists cHeapl cHeape cHeapt,
  get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\
  (exists mlen msg, 
(* OS_Msg 这个结构体的起始地址开始存了 [length] ++ msg 这个vallist *)
  Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\ (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z)).

(*vsdstcl对应通道目的端口链表相应的核号*)
Definition qportpost_dstplength_coresem_Outcore (vl : vallist) (O1: osabst) : Prop :=
  exists v m csemid vsem vlen vsdstcl,
    exists dpl pcn pd pid pst pin pout sz pm,
      exists kportl kpaddr kpst channaddr,
      exists chanl cid cdn cdstkp,
      vl = Vptr v :: Vptr m :: vlen :: vsem :: vsdstcl  /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz pm) /\
      get O1 oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) /\ 
      get O1 oschannelid = Some (oschannel chanl) /\
      get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid) /\
      (length vsdstcl = length cdstkp)%nat /\
      Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstcl /\
      ( forall n, (n < (length cdstkp))%nat -> 
        exists dstpaddr dstpcn dstpd dstpid dstpst dstpin dstpout dstsz dstpm,
        exists dstkpaddr dstkpst nextdst,
        nth_error cdstkp n = Some dstkpaddr /\ 
        get kportl dstkpaddr = Some (dstpid, Some dstpaddr, Some channaddr, dstpcn, dstkpst) /\ 
        get dpl dstpaddr = Some (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz dstpm) /\
        ((Z.of_nat dstpcn) <> DNUM -> nth_error vsdstcl n = Some (Vint32 (Int.repr (Z.of_nat dstpcn)))) ).


(*核间通信，将消息存入一个目的端口*)
Definition qportpost_send_one_Outcore (n: nat) (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
    exists v m  csemid vsdstcl,
    exists dpl pcn  pid,
      exists kportl kpaddr kpst channaddr,
      exists chanl cid cdn cdstkp,
      vl = Vptr v :: Vptr m :: Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: Vint32 (Int.repr (Z.of_nat csemid)) :: vsdstcl /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get O1 oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) /\ 
      get O1 oschannelid = Some (oschannel chanl) /\
      get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid) /\
      exists cHeapl cHeape cHeapt,
        get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\
      exists mlen msg, 
      (* OS_Msg 这个结构体的起始地址开始存了 [length] ++ msg 这个vallist *)
        Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\ (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z /\
      exists dstpaddr dstpcn dstpd dstpid dstpst dstpin dstpout dstpm dstsz,
      exists nextdst dstkpaddr dstkpst,
      exists dpl',
        nth_error cdstkp ((length cdstkp) - n)%nat = Some dstkpaddr /\ 
        get kportl dstkpaddr = Some (dstpid, Some dstpaddr, Some channaddr, dstpcn, dstkpst) /\ 
        get dpl dstpaddr = Some (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz dstpm) /\ 
        ((Z.of_nat dstpcn) <> DNUM ->
          nth_error vsdstcl ((length cdstkp) - n)%nat =
              Some (Vint32 (Int.repr (Z.of_nat dstpcn)))) /\ 
        dpl' = set dpl dstpaddr (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz (dstpm++(msg::nil)))/\
        opv = None /\ 
        opo = Some (set O1 osdomainportid (osdomainport dpl')  )
  end.

Definition qportpost_generateipc (n: nat) (vl : vallist) : spec_code :=
  match vl with 
  | Vptr v :: Vptr m :: Vint32 vlen :: Vint32 csemid :: vdstcl =>
    match (nth_error vdstcl ((length vdstcl) - n)%nat) with
    | Some (Vint32 dstn) =>
        coreint (Z.to_nat (Int.unsigned dstn)) (Vint32 (Int.repr GET_PORT_MESSAGE)) 
    | _ => spec_abort 
    end
  | _ => spec_abort 
  end.

Fixpoint qportpost_send_Outcore (n : nat) (vl: vallist ) : spec_code :=
  match n with 
  | O => END None
  | S n' =>   qportpost_generateipc n vl ;; qportpost_send_Outcore n' vl 
              ??
              (qportpost_send_one_Outcore n) (|vl|);; qportpost_generateipc n vl;; qportpost_send_Outcore n' vl 
              
  end.

(*有任务在等待这个目的端口*)
Definition qportpost_send_one_Incore_taskwait (n: nat) (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
    exists v m vsdstcl,
    exists dpl pcn  pid,
     exists kportl kpaddr kpst channaddr,
     exists chanl cid cdn cdstkp,
      vl = Vptr v :: Vptr m :: Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: Vnull :: vsdstcl /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get O1 oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) /\ 
      get O1 oschannelid = Some (oschannel chanl) /\
      get chanl channaddr = Some  (cid, cdn, cdstkp, IncoreC) /\
      exists dstpaddr dstpcn dstpid,
      exists dstkpaddr dstkpst,
        nth_error cdstkp ((length cdstkp) - n)%nat = Some dstkpaddr /\ 
        get kportl dstkpaddr = Some (dstpid, Some dstpaddr, Some channaddr, dstpcn, dstkpst)  /\ 
        exists ecbls wt,
        get O1 absecblsid = Some (absecblist ecbls) /\
        get ecbls dstpaddr = Some (absport, wt)  /\ 
        wt <> nil /\
        opv = None /\ 
        opo = Some O1
  end.

Definition qportpost_send_one_Incore_porttskrdy (n: nat) (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
    exists v m vsdstcl,
    exists dpl pcn pid,
     exists kportl kpaddr kpst channaddr,
     exists chanl cid cdn cdstkp,
      vl = Vptr v :: Vptr m :: Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: Vnull :: vsdstcl /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get O1 oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) /\ 
      get O1 oschannelid = Some (oschannel chanl) /\
      get chanl channaddr = Some  (cid, cdn, cdstkp, IncoreC) /\
      exists dstpaddr dstpcn  dstpid,
      exists dstkpaddr dstkpst,
        nth_error cdstkp ((length cdstkp) - n)%nat = Some dstkpaddr /\ 
        get kportl dstkpaddr = Some (dstpid, Some dstpaddr, Some channaddr, dstpcn, dstkpst) /\ 
      exists ecbls wt,
        get O1 absecblsid = Some (absecblist ecbls) /\
        get ecbls dstpaddr = Some (absport, wt)  /\ 
        wt <> nil /\
      exists tls t' p st tskm sus, 
        get O1 abtcblsid = Some (abstcblist tls) /\
        (GetHWait tls wt t') /\
        get tls t' = Some (p, st, tskm, sus) /\
        ( sus = true /\ opo = None \/
        exists tls' ecbls',
        tls' = set tls t' (p, rdy, Vptr OS_PARTITION_MESSAGE_COME_ptr, sus) /\ 
        ecbls' = set ecbls' dstpaddr (absport, (remove_tid t' wt)) /\
        sus = false /\ opv = None /\
        opo = Some (set (set O1 abtcblsid (abstcblist tls')) 
                              absecblsid (absecblist ecbls')))
  end.  

(*核内通信，将消息存入一个目的端口*)
Definition qportpost_send_one_Incore (n: nat) (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
    exists v m vsdstcl,
    exists dpl pcn  pid,
      exists kportl kpaddr kpst channaddr,
      exists chanl cid cdn cdstkp,
      vl = Vptr v :: Vptr m :: Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: Vnull :: vsdstcl /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get O1 oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) /\ 
      get O1 oschannelid = Some (oschannel chanl) /\
      get chanl channaddr = Some (cid, cdn, cdstkp, IncoreC) /\
      exists cHeapl cHeape cHeapt,
        get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\
      exists mlen msg, 
      (* OS_Msg 这个结构体的起始地址开始存了 [length] ++ msg 这个vallist *)
        Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\ (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z /\
      exists dstpaddr dstpcn dstpd dstpid dstpst dstpin dstpout dstpm dstsz,
      exists nextdst dstkpaddr dstkpst,
      exists dpl',
        nth_error cdstkp ((length cdstkp) - n)%nat = Some dstkpaddr /\ 
        get kportl dstkpaddr = Some (dstpid, Some dstpaddr, Some channaddr, dstpcn, dstkpst) /\ 
        get dpl dstpaddr = Some (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz dstpm) /\ 
        dpl' = set dpl dstpaddr (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz (dstpm++(msg::nil)))/\
        opv = None /\ 
        opo = Some (set O1 osdomainportid (osdomainport dpl')  )
  end.

Fixpoint qportpost_send_Incore (n : nat) (vl: vallist ) : spec_code :=
  match n with 
  | O => END None
  | S n' =>  (*有任务在等待该目的端口*)
              (*(qportpost_send_one_Incore_taskwait n) (|vl|) ;;*) (qportpost_send_one_Incore_porttskrdy n) (|vl|);;
              qportpost_send_Incore n' vl  
              ??
              (*(qportpost_send_one_Incore_taskwait n) (|vl|) ;;*) (qportpost_send_one_Incore_porttskrdy n) (|vl|);;
              (qportpost_send_one_Incore n) (|vl|);; qportpost_send_Incore n' vl  
              ??
              (*没有任务等待且队列没有满*)
              (qportpost_send_one_Incore n) (|vl|);; qportpost_send_Incore n' vl  
              ??
              (*没有任务等待且队列满了*)
              qportpost_send_Incore n' vl 
  end.

(*当通道没有目的端口(无论核内/核间)，都将消息先存入源端口中*)
Definition qportpost_store_one (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
    exists v m vsem vsdstcl,
    exists dpl pcn pd pid pst pin pout pm sz,
      exists kportl kpaddr kpst channaddr,
      (* exists chanl cid cdn vsem channelmode, *)
      vl = Vptr v :: Vptr m :: Vint32 Int.zero :: vsem :: vsdstcl /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz pm) /\
      get O1 oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) /\ 
      exists cHeapl cHeape cHeapt,
        get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\
      ((exists mlen msg, 
      (* OS_Msg 这个结构体的起始地址开始存了 [length] ++ msg 这个vallist *)
        Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
        (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z /\
      exists dpl',
        dpl' = set dpl v (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz (pm ++ (msg :: nil)))/\
        opv = None /\ 
        opo = Some (set O1 osdomainportid (osdomainport dpl') )))
  end.

(*
Definition qportpost_send (vl: vallist ) : spec_code :=
  match vl with 
  | Vptr v :: Vptr m :: Vint32 vlen :: Vnull :: Vnull :: nil => 
        let dtsl := Z.to_nat (Int.unsigned vlen) in 
          qportpost_send_Incore dtsl vl
  | Vptr v :: Vptr m :: Vint32 vlen :: Vint32 sem :: vdstcore :: nil => 
        let dtsl := Z.to_nat (Int.unsigned vlen) in 
          Semacc_err (Vint32 sem ) ?? 
          Semacc_succ (Vint32 sem ) ;;
          qportpost_send_Outcore dtsl vl;;
          Semrelease (Vint32 sem ) ;;
          (END (Some (Vint32 (Int.repr OS_NO_ERR ))) ?? 
           END (Some (Vint32 (Int.repr OS_ERR_DSTPORT_FULL ))))
  | _ => spec_abort
  end.

Definition qportpost_store (vl: vallist): spec_code:=
  match vl with
  | Vptr v :: Vptr m :: (Vint32 vlen) :: Vnull :: Vnull :: nil => 
      END (Some (Vint32 (Int.repr OS_Q_FULL))) ??
      (qportpost_store_one) (|vl|)
  | Vptr v :: Vptr m :: (Vint32 vlen) :: Vint32 sem :: vdstcore :: nil => 
      Semacc_err (Vint32 sem ) ?? 
      Semacc_succ (Vint32 sem ) ;;
      (
        Semrelease (Vint32 sem ) ;;
        END (Some (Vint32 (Int.repr OS_Q_FULL))) ??
        (qportpost_store_one) (|vl|) ;;
        Semrelease (Vint32 sem ) ;;
        END (Some (Vint32 (Int.repr OS_NO_ERR )))
      )
  | _ => spec_abort
  end.
*)
 
Definition qportpost_aux (vl: vallist): spec_code:=
  match vl with
  | Vptr v :: Vptr m :: (Vint32 vlen) :: Vnull :: vdstcl => 
      END (Some (Vint32 (Int.repr OS_Q_FULL)))
      ??
      ASSERT (qportpost_msg_in_heapl vl);;
      (
        (let dtsl := Z.to_nat (Int.unsigned vlen) in 
          spec_code_cons (qportpost_send_Incore dtsl vl) 
          (isched;;
          (END (Some (Vint32 (Int.repr OS_NO_ERR ))) ?? END (Some (Vint32 (Int.repr OS_ERR_DSTPORT_FULL ))))))
        ??
        qportpost_store_one (|vl|) ;; END (Some (Vint32 (Int.repr OS_NO_ERR )))
      ) 
       
  | Vptr v :: Vptr m :: (Vint32 vlen) :: Vint32 sem :: vdstcl => 
      Semacc_err (Vint32 sem );; END (Some (Vint32 (Int.repr OS_CHANNEL_ERR_BEING_USED)))
      ?? 
      Semacc_succ (Vint32 sem );;
      (
        Semrelease (Vint32 sem ) ;; END (Some (Vint32 (Int.repr OS_Q_FULL)))
        ??
        ASSERT (qportpost_msg_in_heapl vl);;
          (
            qportpost_store_one (|vl|) ;;
              Semrelease (Vint32 sem ) ;;
              END (Some (Vint32 (Int.repr OS_NO_ERR )))
            ??
            ASSERT (qportpost_dstplength_coresem_Outcore vl);; 
            (let dtsl := Z.to_nat (Int.unsigned vlen) in 
              spec_code_cons (qportpost_send_Outcore dtsl vl) 
              (Semrelease (Vint32 sem );; isched;;  
              (END (Some (Vint32 (Int.repr OS_NO_ERR ))) ?? END (Some (Vint32 (Int.repr OS_ERR_DSTPORT_FULL ))))))
          )
      )
  | _ => spec_abort
  end. 


Definition qportpostcode (vl : vallist) :=
  match vl with
  | nil => spec_abort
  | v :: nil => spec_abort
  | _ :: _ :: nil => spec_abort 
  | v0 :: v1 :: v2 :: nil => spec_abort
  | v0 :: v1 :: v2 :: v3:: nil => spec_abort
  | v0 :: v1 :: v2 :: v3:: v4 :: vl' => 
                    ASSERT (valid_port v0) ;;(
                    err_portnull (|v0::nil|) ??
                    err_unmapped (|v0::nil|) ??
                    err_msgnull (OS_ERR_POST_NULL_PTR) (|v1::nil|) ??
                    err_porttype_queue (|v0::nil|) ??
                    err_idinvalid (|v0::nil|) ??
                    (*err_unbind (|v0::nil|) ??*)
                    err_nochannel (|v0::nil|) ??
                    (ASSERT (qportpost_port_kport_channel_map vl) ;;
                    qportpost_aux vl))
  end.
  
Definition qportpostapi := (qportpostcode, (Tint8, Tptr OS_Port:: Tptr OSMsg_t ::nil)).


(******************************************************************  QPortPend  **************************************************************)

Definition portpend_err_dire (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
     exists v tm m,
     exists dpl pcn pd pid pst pin pout pt,
      vl = Vptr v :: tm :: m :: nil /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, pt) /\
      opv = Some (Vint32 (Int.repr OS_PORT_ERR_DIRECTION_TYPE)) /\
      opo = Some O1 
  end.

Definition portpend_err_type (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
     exists v tm m,
     exists dpl pcn pd pid pst pin pout msg nextdst,
      vl = Vptr v :: tm :: m :: nil /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, DestinationP nextdst, pst, pin, pout, SamplePort msg) /\
      opv = Some (Vint32 (Int.repr OS_PORT_ERR_TYPE)) /\
      opo = Some O1 
  end.

Definition qportpend_notnil (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
    exists v tm m,
     exists dpl pcn pd pid pdir pst pin pout sz,
     exists msg msgl,
     exists kportl kpaddr kpst channaddr,
     exists chanl cid cdn cdstkp ctype,
      vl = Vptr v :: tm :: Vptr m :: nil /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout,  QueuePort sz (msg :: msgl)) /\
      get O1 oskportid = Some (oskport kportl) /\
      get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) /\ 
      get O1 oschannelid = Some (oschannel chanl) /\
      get chanl channaddr = Some  (cid, cdn, cdstkp, ctype) /\ 
      exists cHeapl cHeape cHeapt,
        get O1 oscoreheapid = Some (oscoreheap (cHeapl, cHeape, cHeapt)) /\ 
        (~ In_heapl_addrval cHeapl m (S (length msg)) /\ opo = None \/
        exists reshl portl',
        update_heapl_addrval cHeapl m (S (length msg)) (Vint32 (Int.repr (Z.of_nat (length msg))) :: msg) reshl /\
        portl' = set dpl v (pcn, pd, pid, pdir, pst, pin, pout,  QueuePort sz (msgl)) /\ 
        opv = Some (Vint32 (Int.repr  OS_NO_ERR)) /\
        opo = Some (set (set O1 oscoreheapid (oscoreheap (reshl, cHeape, cHeapt))) osdomainportid (osdomainport portl')))
  end.

Definition qportpend_nil (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
  | (opv, opo) =>
    exists v tm m,
      exists dpl pcn pd pid pdir pst pin pout sz,
      vl = Vptr v :: tm :: Vptr m :: nil /\ 
      get O1 osdomainportid = Some (osdomainport dpl) /\
      get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout,  QueuePort sz nil) /\
      opv = None /\ 
      opo = Some O1
  end.

Definition qportpend_idle_err (vl: vallist) (O1: osabst) (rst: option val * option osabst):=
  match rst with
  | (rv, O_opt) =>
    ( exists v tm m,
        vl = Vptr v :: tm :: Vptr m :: nil /\ 
        exists tls st msg t sus,
          get O1 curtid = Some (oscurt t) /\
          get O1 abstcblsid = Some (abstcblist tls) /\
          get tls t = Some (Int.repr OS_IDLE_PRIO, st, msg, sus) /\ 
          rv = None /\
          O_opt = None
    )
  end.

Definition qportpend_not_ready_err (vl: vallist) (O1: osabst) (rst: option val * option osabst):=
  match rst with
  | (rv, O_opt) =>
    (exists v tm m,
        vl = Vptr v :: tm :: Vptr m :: nil /\
        exists tls st msg prio t sus,
          get O1 curtid = Some (oscurt t) /\
          get O1 abstcblsid = Some (abstcblist tls) /\
          get tls t = Some (prio,st,msg,sus) /\
          ~ (st = rdy /\ sus = false) /\
          rv = None /\ 
          O_opt = None
    )
  end.


Definition qportpend_block (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
    exists v tm m,
      exists dpl pcn pd pid pdir pst pin pout sz,
        vl = Vptr v :: Vint32 tm:: Vptr m :: nil /\ 
        get O1 osdomainportid = Some (osdomainport dpl) /\
        get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout,  QueuePort sz nil) /\
        exists tls tls' p st t tskm sus t_opt,
          get O1 curtid = Some (oscurt t) /\
          get O1 abstcblsid = Some (abstcblist tls) /\ 
        exists ecbls wt ecbls',
          get O1 absecblsid = Some (absecblist ecbls) /\
          get ecbls v = Some (absport, wt)  /\ 
          ecbls'= set ecbls v (absport, t :: wt)/\
          get tls t = Some (p,st,tskm,sus) /\
          tls' = set tls t (p, wait (os_stat_port v) t_opt,tskm,sus)/\
          ((t_opt = Some tm /\ tm <> Int.zero) \/ (t_opt = None /\ tm = Int.zero)) /\
          opv = None /\ 
          opo = Some (set ( set O1 abstcblsid (abstcblist tls') ) 
                          absecblsid (absecblist ecbls')) 
  end.

Definition qportpend_after_sched (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid tls prio st msg sus t,
      vl = (Vptr qid :: nil) /\
             get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
            get tls t = Some (prio,st,msg,sus) /\ 
           opv = None /\ 
           ( ((st = rdy /\ msg = (Vptr OS_PARTITION_MESSAGE_COME_ptr) /\ sus = false \/ st = wait (os_stat_port qid) (Some Int.zero) /\ msg = Vnull /\ sus = false)
             /\ O_opt = Some O1) \/ 
             (~(st = rdy /\ msg = (Vptr OS_PARTITION_MESSAGE_COME_ptr) /\ sus = false \/ st = wait (os_stat_port qid) (Some Int.zero)  /\ msg = Vnull /\ sus = false)
             /\ O_opt = None )    )
  end.


Definition qportpend_block_get (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
    exists v tm m,
      (* exists dpl pcn pd pid pdir pst pin pout pm sz, *)
        vl = Vptr v :: Vint32 tm:: Vptr m :: nil /\ 
        (* get O1 osdomainportid = Some (osdomainport dpl) /\
        get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout,  QueuePort sz pm) /\ *)
        exists tls tls' p st t tskm sus,
          get O1 curtid = Some (oscurt t) /\
          get O1 abstcblsid = Some (abstcblist tls) /\ 
          get tls t = Some (p,st,tskm,sus) /\
          tskm <> Vnull /\
          tls' = set tls t (p, rdy, Vnull, sus)/\
          opv = None /\ 
          opo = Some ( set O1 abstcblsid (abstcblist tls') ) 
  end.

Definition qportpend_block_timeout (vl : vallist) (O1 : osabst) (rst : option val * option osabst) := 
  match rst with 
  | (opv, opo ) =>
    exists v tm m,
      exists dpl pcn pd pid pdir pst pin pout pm sz,
        vl = Vptr v :: Vint32 tm:: Vptr m :: nil /\ 
        get O1 osdomainportid = Some (osdomainport dpl) /\
        get dpl v = Some (pcn, pd, pid, pdir, pst, pin, pout, QueuePort sz pm) /\
        exists tls tls' p st t tskm sus,
          get O1 curtid = Some (oscurt t) /\
          get O1 abstcblsid = Some (abstcblist tls) /\ 
          get tls t = Some (p,st,tskm,sus) /\
          tskm = Vnull /\
          tls' = set tls t (p, rdy, Vnull, false)/\
        exists ecbls wt ecbls',
          get O1 absecblsid = Some (absecblist ecbls) /\
          get ecbls v = Some (absport, wt)  /\ 
          ecbls'= set ecbls v (absport, (remove_tid t wt))/\
          opv = Some (Vint32 (Int.repr OS_TIMEOUT)) /\ 
          opo = Some (set ( set O1 abstcblsid (abstcblist tls') ) 
                           absecblsid (absecblist ecbls')) 
  end.

Definition err_msg v m : absexpr := 
   (fun O =>
  match v with 
  | Vint32 errm => errm = m 
  | _ => False
  end).

Definition portpend_accwithoutcheck (vl : vallist) :=
  match vl with
  | nil => spec_abort
  | v :: nil => spec_abort
  | v0 :: v1 :: nil => spec_abort
  | v0 :: v1 :: v2 :: nil => spec_abort
  | v :: v0 :: v1 :: errv :: vl' => 
                    portacc_err_nochannel (|v::nil|) ;; ASSERT (err_msg errv  (Int.repr OS_ERR_PORT_NO_CHANNEL)) ??
                    (* 核间通信 *)
                    ( ASSERT (corecommu_ v v1) ;;
                      ( Semacc_err v1 ;; ASSERT (err_msg errv (Int.repr OS_CHANNEL_ERR_BEING_USED)) ??
                        ( Semacc_succ v1 ;;
                          ( portacc_queue_nil (|(v::v0::nil)|)   ??
                            portacc_queue_notnil (|(v::v0::nil)|)) ;; 
                          Semrelease v1 ;; ASSERT (err_msg errv (Int.repr OS_NO_ERR)) ) )) ??
                    (* 核内通信 *)
                    ( portacc_queue_nil (|(v::v0::nil)|) ;; ASSERT (err_msg errv (Int.repr OS_NO_ERR)) ??
                            portacc_queue_notnil (|(v::v0::nil)|);; ASSERT (err_msg errv (Int.repr OS_NO_ERR)) ) 
  end.  


Definition portpendcode (vl : vallist) :=
  match vl with
  | nil => spec_abort
  | v :: nil => spec_abort
  | v :: v0:: nil => spec_abort
  | v :: v0 :: v1 :: nil => spec_abort 
  | v :: v0 :: v1 :: v2 :: nil => spec_abort 
  | v :: v0 :: v1 :: semv :: errv :: vl' => 
                  err_pendisr (|nil|) ??
                  ASSERT (port_indomainport v) ;;
                  ( (* err_portnull (|v::nil|) ?? *)
                    err_unmapped (|v::nil|) ??
                    portpend_err_dire (|v :: v0 :: v1 :: nil |) ?? 
                    portpend_err_type (|v :: v0 :: v1 :: nil |) ??
                    err_msgnull OS_PORT_MSG_ARG_NULL (|v1::nil|) ??
                    (* err_unbind (|v::nil|) ?? *)
                    err_nochannel (|v::nil|) ??
                    (* 核间通信 *)
                    ( ASSERT (corecommu_ v semv) ;;
                      (* 核间通信但信号量获取失败*)
                      ( Semacc_err semv ;; END (Some (Vint32 (Int.repr OS_CHANNEL_ERR_BEING_USED)))  ??
                       Semacc_succ semv ;; 
                      ( (*qport 不为空*)
                       qportpend_notnil (|v :: v0 :: v1 :: nil |) ;;  (Semrelease semv) ;; END (Some (Vint32 (Int.repr OS_NO_ERR))) ??
                       (*qport 为空*)
                       qportpend_nil (|v :: v0 :: v1 :: nil |) ;;  (Semrelease semv) ;;
                       (qportpend_idle_err (|v :: v0 :: v1 :: nil |) ?? qportpend_not_ready_err (|v :: v0 :: v1 :: nil |) ?? 
                       qportpend_block (|v :: v0 :: v1 :: nil |) ;;  isched ;; 
                       ASSERT (port_indomainport v) ;; qportpend_after_sched (|v::nil|);;
                       ( (spec_code_cons (portpend_accwithoutcheck (v ::  v1 :: semv :: errv ::nil)) 
                                         (qportpend_block_get (|v::v0::v1::nil|) ;; END Some (errv))) ??
                         qportpend_block_timeout  (|v::v0::v1::nil|) ))
                      ))) ?? 
                    (* 核内通信 *)
                    ( ( (*qport 不为空*)
                       qportpend_notnil (|v :: v0 :: v1 :: nil |)  ??
                       (*qport 为空*)
                       qportpend_nil (|v :: v0 :: v1 :: nil |) ;;
                       (qportpend_idle_err (|v :: v0 :: v1 :: nil |) ?? qportpend_not_ready_err (|v :: v0 :: v1 :: nil |) ?? 
                       qportpend_block (|v :: v0 :: v1 :: nil |) ;;  isched ;; 
                       ASSERT (port_indomainport v) ;; qportpend_after_sched (|v::nil|);;
                       ( (spec_code_cons (portpend_accwithoutcheck (v ::  v1 :: semv :: errv ::nil)) 
                                          (qportpend_block_get (|v::v0::v1::nil|) ;; END Some (errv)))  ??
                         qportpend_block_timeout  (|v::v0::v1::nil|) ))
                      ))
                  )
  end.

Definition qportpendapi := (portpendcode, (Tint8, Tptr OS_Port:: Tint32 ::  Tptr OSMsg_t ::nil)).