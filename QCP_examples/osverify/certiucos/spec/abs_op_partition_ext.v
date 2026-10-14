Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import os_inv.

(* partitionSysInit *)

Definition partitionSysInit_succ
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
     exists idx cd ld kscd,
     exists dom kscd_len cd' dt' ,
     exists O1'  O1'' O1'''  O1'''' ,
      (vl = nil) /\
      get O1 ksdschedidxid = Some (ksdschedidx idx) /\
      get O1 kscurdomid = Some (kscurdom cd) /\
      get O1 kslastdomid = Some (kslastdom ld) /\
      get O1 ksdschedid = Some (ksdsched kscd) /\
      KsDScdMod.get kscd Int.zero = Some (dom, kscd_len)  /\
      cd' = dom /\
      dt' = kscd_len /\
      O1' = set O1 ksdschedidxid (ksdschedidx Int.zero) /\
      O1'' = set O1' kscurdomid (kscurdom cd')  /\ 
      O1''' = set O1'' ksdomtimeid (ksdomtime dt') /\
     O1'''' = set O1''' kslastdomid (kslastdom Int.mone) /\
      O_opt = Some O1'''' /\
      opv = None
  end.

Definition partitionSys (vl:vallist) := partitionSysInit_succ (| vl |).

(* nextDomain *)

Definition nextDomain_succ
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
     exists idx len cd ld kscd idx' ld',
     exists dom kscd_len cd' dt',
     exists O1' O1'' O1''' O1'''',
      (vl = nil) /\
      get O1 ksdschedidxid = Some (ksdschedidx idx) /\
      get O1 ksdschedlenid = Some (ksdschedlen len) /\
      get O1 kscurdomid = Some (kscurdom cd) /\
      get O1 kslastdomid = Some (kslastdom ld) /\
      get O1 ksdschedid = Some (ksdsched kscd) /\
      idx' = (if (Int.ltu (Int.add idx Int.one) len) then (Int.add idx Int.one) else Int.zero) /\
      ld' = cd /\
      KsDScdMod.get kscd idx' = Some (dom, kscd_len) /\
      cd' = dom /\
      dt' = kscd_len /\
      O1' = set O1 ksdschedidxid (ksdschedidx idx') /\
      O1'' = set O1' kslastdomid (kslastdom ld') /\
      O1''' = set O1'' kscurdomid (kscurdom cd') /\
      O1'''' = set O1''' ksdomtimeid (ksdomtime dt') /\
      O_opt = Some O1'''' /\
      opv = None
  end.

Definition nextdom (vl:vallist) := nextDomain_succ (| vl |).

(* getPartitionID *)

Definition ksize_abt 
(vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) => 
    exists  v cd,
    (vl =  v  :: nil) /\
     get O1 kscurdomid = Some (kscurdom cd)   /\ 
    ((v = Vint32 cd /\ O_opt = Some O1) \/
      (v <> Vint32 cd /\ O_opt = None ))
end.

Definition cd_abt
(vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O_opt) => 
       exists v,
       (vl= v :: nil) /\
        v=Vint32 Int.mone /\
        opv=None /\
       O_opt =None
  end.

Definition get_ksdid_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) => 
        exists v cd domt ksdid1 v1,
        exists cr ksDSL  ksDL  dRdy  Dsch  Domc g h j ks,
        (vl =  v  :: v1 :: nil) /\
        (v = Vint32 cd /\0 <= Int.unsigned cd < DOMAIN_SIZE)%Z  /\
        get O1 ksdomsid = Some (ksdoms domt)   /\
        KsDomsMod.get  domt cd = Some ks /\
        ks = (g, cr, ksDSL,  ksDL,  dRdy,  Dsch, Domc,  h, j) /\
         ksdid1 = cr/\
       opv = Some (Vint32 ksdid1) /\
       (v1 = Vint32 ksdid1 /\ O_opt = Some O1
         \/ v1 <> Vint32 ksdid1 /\ O_opt = None)
  end.

Definition getPartitionID_pos (vl: vallist) :=
  match vl with
        v  :: v1 ::nil =>  
                ksize_abt (|v:: nil|) ;; (cd_abt(| v :: nil |)  ?? get_ksdid_yes(| v :: v1 :: nil |) )
  | _ => spec_abort
  end.

Definition getPartitionIDapi :=(getPartitionID_pos , (Tint8, (nil: list type))).

(* switchDomain *)

Definition ksLastDomain_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists cd,
      get O1 kscurdomid = Some (kscurdom cd) /\
      get O1 kslastdomid = Some (kslastdom cd) /\
      opv = None  /\ O_opt = Some O1
  end.

Definition ksCurDomain_valid (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists cd,
      get O1 kscurdomid = Some (kscurdom cd) /\
      cd <> Int.mone /\
      opv = None  /\ O_opt = Some O1
  end.

Definition ksCurDomain_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists cd,
      (get O1 kscurdomid = Some (kscurdom cd) /\ cd=Int.mone) /\
      opv = None  /\ O_opt = Some O1
  end.

Definition set_mpaxh (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists q vsize vbaddr evheap t l l',
    vl = ((Vptr q) :: vbaddr ::  vsize :: nil) /\
    get O1 evstructheapid = Some (evstructheap evheap) /\
    Get_struct evheap q = Some (q, t, l) /\
    l' = (vbaddr :: vsize :: nil) /\
    O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct evheap q t l'))) /\
    opv = None
end.

Definition set_mpaxl (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists q vraddr vsr vsw vsx vur vuw vux,
    exists evheap t l l',
    vl = ((Vptr q) :: vraddr :: vsr :: vsw :: vsx :: vur :: vuw :: vux :: nil) /\
    get O1 evstructheapid = Some (evstructheap evheap) /\
    Get_struct evheap q = Some (q, t, l) /\
    l' = (vraddr :: vsr :: vsw :: vsx :: vur :: vuw :: vux :: nil) /\
    O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct evheap q t l'))) /\
    opv = None
end.

Definition get_rtsk_baddr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists rv_baddr cur ksdom_vl vdom vid vperiod vpaddr vaddr,
    exists vlen vsize vstatus vintst b i type i' voff,
    vl = (rv_baddr :: nil) /\
    get O1 kscurdomid = Some (kscurdom cur) /\
    get O1 ksdomsid = Some (ksdoms ksdom_vl) /\
    KsDomsMod.get ksdom_vl cur = Some (vdom, vid, vperiod, vpaddr, vaddr, vlen,
 vsize, vstatus, vintst) /\
    RootTaskStk_head = (b,i) /\ 
    type = (Tarray Tint32 (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) /\
    i' = Int.add i (Int.repr (Z.of_nat((Z.to_nat(Int.unsigned vid)) * (typelen type)))) /\
    voff = Int.shru (ptr_to_int32 (b, i')) (Int.repr 12) /\
    (rv_baddr = Vint32 voff /\ O_opt = Some O1
     \/ (rv_baddr <> Vint32 voff /\ O_opt = None)) /\
    opv = None
end.

Definition get_rtsk_raddr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists rv_raddr cur ksdom_vl vdom vid vperiod vpaddr vaddr,
    exists vlen vsize vstatus vintst b i type i' voff voff',
    vl = (rv_raddr :: nil) /\
    get O1 kscurdomid = Some (kscurdom cur) /\
    get O1 ksdomsid = Some (ksdoms ksdom_vl) /\
    KsDomsMod.get ksdom_vl cur = Some (vdom, vid, vperiod, vpaddr, vaddr, vlen,
 vsize, vstatus, vintst) /\
    RootTaskStk_head = (b,i) /\ 
    type = (Tarray Tint32 (nat_of_Z (2 * PTHREAD_STACK_MIN/4 ))) /\
    i' = Int.add i (Int.repr (Z.of_nat((Z.to_nat(Int.unsigned vid)) * (typelen type)))) /\
    voff = ptr_to_int32 (b, i') /\
    voff' = (if Int.ltu voff (Int.repr (0x80000000))
             then Int.shru voff (Int.repr 12)
             else Int.or (Int.shru (Int.sub voff (Int.repr (0x80000000)))
                                   (Int.repr 12))
                         (Int.repr (0x800000))) /\
    (rv_raddr = Vint32 voff' /\ O_opt = Some O1
     \/ (rv_raddr <> Vint32 voff' /\ O_opt = None)) /\
    opv = None
end.

Definition get_ksdom_size_vaddr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists rv_size rv_vaddr cur ksdom_vl vdom vid vperiod vpaddr vaddr,
    exists vlen vsize vstatus vintst voff,
    vl = (rv_size :: rv_vaddr :: nil) /\
    get O1 kscurdomid = Some (kscurdom cur) /\
    get O1 ksdomsid = Some (ksdoms ksdom_vl) /\
    KsDomsMod.get ksdom_vl cur = Some (vdom, vid, vperiod, vpaddr, vaddr, vlen,
 vsize, vstatus, vintst) /\
    voff = Int.shru vaddr (Int.repr 12) /\
    ( (rv_size = Vint32 vsize /\ rv_vaddr = Vint32 voff) /\ O_opt = Some O1
     \/ (~(rv_size = Vint32 vsize /\ rv_vaddr = Vint32 voff) /\ O_opt = None)) /\
    opv = None
end.

Definition get_ksdom_paddr_if (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists rv_paddr cur ksdom_vl vdom vid vperiod vpaddr vaddr,
    exists vlen vsize vstatus vintst voff,
    vl = (rv_paddr :: nil) /\
    get O1 kscurdomid = Some (kscurdom cur) /\
    get O1 ksdomsid = Some (ksdoms ksdom_vl) /\
    KsDomsMod.get ksdom_vl cur = Some (vdom, vid, vperiod, vpaddr, vaddr, vlen,
 vsize, vstatus, vintst) /\
    voff = (if Int.ltu vpaddr (Int.repr (0x80000000))
             then Int.shru vpaddr (Int.repr 12)
             else Int.or (Int.shru (Int.sub vpaddr (Int.repr (0x80000000)))
                                   (Int.repr 12))
                         (Int.repr (0x800000))) /\
    ( rv_paddr = Vint32 voff /\ O_opt = Some O1
     \/ (rv_paddr <> Vint32 voff /\ O_opt = None)) /\
    opv = None
end.

(* SUPERVISOR_MODE_EN > 0 *)
Definition switchDom (vl: vallist) :=
  match vl with
      (Vptr lmpaxh) :: (Vptr lmpaxl) :: (Vptr lses_mpaxh) ::
      (Vptr lses_mpaxl) :: (Vptr lsms_mpaxh) :: (Vptr lsms_mpaxl) :: 
      rv_baddr :: rv_raddr :: rv_size :: rv_vaddr :: rv_paddr :: nil =>
      ksLastDomain_err (| nil |) ??
      (ksCurDomain_valid (| nil |) ;;
        (*index = MPAXSHIPARTIONSTKCUR *)
        get_rtsk_baddr (|rv_baddr :: nil|) ;;
        set_mpaxh (|(Vptr lmpaxh) :: rv_baddr :: (Vint32 (Int.repr 12)) :: nil|) ;;
        csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lmpaxh ;;
        set_mpaxh (|(Vptr lsms_mpaxh) :: rv_baddr :: (Vint32 (Int.repr 12)) :: nil|) ;;
        csl_msmc_setSMSMPAXH (Z.to_nat DNUM)
                                                           (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lsms_mpaxh ;;
        set_mpaxh (|(Vptr lses_mpaxh) :: rv_baddr :: (Vint32 (Int.repr 12)) :: nil|) ;;
        csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                                                          (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lses_mpaxh ;;
        get_rtsk_raddr (|rv_raddr :: nil|) ;;
        set_mpaxl (|(Vptr lmpaxl) :: rv_raddr ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                                nil|) ;;
        csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lmpaxl ;;
        set_mpaxl (|(Vptr lsms_mpaxl) :: rv_raddr ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                                nil|) ;;
        csl_msmc_setSMSMPAXL (Z.to_nat DNUM) 
                                                           (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lsms_mpaxl ;;
        set_mpaxl (|(Vptr lses_mpaxl) :: rv_raddr ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                                nil|) ;;
        csl_msmc_setSESMPAXL (Z.to_nat DNUM) 
                                                          (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lses_mpaxl ;;
        (*index = MPAXSHIPARTIONCUR *)
        get_ksdom_size_vaddr (| rv_size :: rv_vaddr :: nil |) ;;
        set_mpaxh (|(Vptr lmpaxh) :: rv_vaddr :: rv_size :: nil|) ;;
        csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lmpaxh ;;
        set_mpaxh (|(Vptr lsms_mpaxh) :: rv_vaddr :: rv_size :: nil|) ;;
        csl_msmc_setSMSMPAXH (Z.to_nat DNUM) 
                                                            (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lsms_mpaxh ;;
        set_mpaxh (|(Vptr lses_mpaxh) :: rv_vaddr :: rv_size :: nil|) ;;
        csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                                                          (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lses_mpaxh ;;
        get_ksdom_paddr_if (| rv_paddr :: nil |) ;;
        set_mpaxl (|(Vptr lmpaxl) :: rv_paddr ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                                nil|) ;;
        csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lmpaxl ;;
        set_mpaxl (|(Vptr lsms_mpaxl) :: rv_paddr ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                                nil|) ;;
        csl_msmc_setSMSMPAXL (Z.to_nat DNUM) 
                                                           (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lsms_mpaxl ;;
        set_mpaxl (|(Vptr lses_mpaxl) :: rv_paddr ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                                nil|) ;;
        csl_msmc_setSESMPAXL (Z.to_nat DNUM) 
                                                          (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lses_mpaxl) ??
       (* end of ksCurDomain <> -1*)
      ( ksCurDomain_err (|nil|) ;; (* ksCurDomain = -1*)
         (* index = MPAXSHIPARTIONCUR *)
        set_mpaxh (|(Vptr lmpaxh) :: (Vint32 Int.zero) :: (Vint32 Int.zero) :: nil|) ;;
        csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lmpaxh ;;
        set_mpaxh (|(Vptr lsms_mpaxh) :: (Vint32 Int.zero) :: (Vint32 Int.zero) ::  nil|) ;;
        csl_msmc_setSMSMPAXH (Z.to_nat DNUM) 
                                                            (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lsms_mpaxh ;;
        set_mpaxh (|(Vptr lses_mpaxh) :: (Vint32 Int.zero) :: (Vint32 Int.zero) ::  nil|) ;;
        csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                                                          (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lses_mpaxh ;;
        set_mpaxl (|(Vptr lmpaxl) :: (Vint32 (Int.shru Int.zero (Int.repr 12))) ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                                (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) ::
                                nil|) ;;
        csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lmpaxl ;;
        set_mpaxl (|(Vptr lsms_mpaxl) :: (Vint32 (Int.shru Int.zero (Int.repr 12))) ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                                (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) ::
                                nil|) ;;
        csl_msmc_setSMSMPAXL (Z.to_nat DNUM) 
                                                           (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lsms_mpaxl ;;
        set_mpaxl (|(Vptr lses_mpaxl) :: (Vint32 (Int.shru Int.zero (Int.repr 12))) ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                                (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) ::
                                nil|) ;;
        csl_msmc_setSESMPAXL (Z.to_nat DNUM) 
                                                          (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lses_mpaxl
        ) (*end of ksCurDomain = -1*)
  | _ => spec_abort
  end.

(* SUPERVISOR_MODE_EN = 0 *)
Definition switchDom' (vl: vallist) :=
  match vl with
      (Vptr lmpaxh) :: (Vptr lmpaxl) :: (Vptr lses_mpaxh) ::
      (Vptr lses_mpaxl) :: (Vptr lsms_mpaxh) :: (Vptr lsms_mpaxl) :: 
      rv_baddr :: rv_raddr :: rv_size :: rv_vaddr :: rv_paddr :: nil =>
      ksLastDomain_err (| nil |) ??
      (ksCurDomain_valid (| nil |) ;;
        (*index = MPAXSHIPARTIONSTKCUR *)
        get_rtsk_baddr (|rv_baddr :: nil|) ;;
        set_mpaxh (|(Vptr lmpaxh) :: rv_baddr :: (Vint32 (Int.repr 12)) :: nil|) ;;
        csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lmpaxh ;;
        set_mpaxh (|(Vptr lsms_mpaxh) :: rv_baddr :: (Vint32 (Int.repr 12)) :: nil|) ;;
        csl_msmc_setSMSMPAXH (Z.to_nat DNUM)
                                                           (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lsms_mpaxh ;;
        set_mpaxh (|(Vptr lses_mpaxh) :: rv_baddr :: (Vint32 (Int.repr 12)) :: nil|) ;;
        csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                                                          (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lses_mpaxh ;;
        get_rtsk_raddr (|rv_raddr :: nil|) ;;
        set_mpaxl (|(Vptr lmpaxl) :: rv_raddr ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                                nil|) ;;
        csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lmpaxl ;;
        set_mpaxl (|(Vptr lsms_mpaxl) :: rv_raddr ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                                nil|) ;;
        csl_msmc_setSMSMPAXL (Z.to_nat DNUM) 
                                                           (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lsms_mpaxl ;;
        set_mpaxl (|(Vptr lses_mpaxl) :: rv_raddr ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                                nil|) ;;
        csl_msmc_setSESMPAXL (Z.to_nat DNUM) 
                                                          (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lses_mpaxl ;;
        (*index = MPAXSHIPARTIONCUR *)
        get_ksdom_size_vaddr (| rv_size :: rv_vaddr :: nil |) ;;
        set_mpaxh (|(Vptr lmpaxh) :: rv_vaddr :: rv_size :: nil|) ;;
        csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lmpaxh ;;
        set_mpaxh (|(Vptr lsms_mpaxh) :: rv_vaddr :: rv_size :: nil|) ;;
        csl_msmc_setSMSMPAXH (Z.to_nat DNUM) 
                                                            (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lsms_mpaxh ;;
        set_mpaxh (|(Vptr lses_mpaxh) :: rv_vaddr :: rv_size :: nil|) ;;
        csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                                                          (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lses_mpaxh ;;
        get_ksdom_paddr_if (| rv_paddr :: nil |) ;;
        set_mpaxl (|(Vptr lmpaxl) :: rv_paddr ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                                nil|) ;;
        csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lmpaxl ;;
        set_mpaxl (|(Vptr lsms_mpaxl) :: rv_paddr ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                                nil|) ;;
        csl_msmc_setSMSMPAXL (Z.to_nat DNUM) 
                                                           (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lsms_mpaxl ;;
        set_mpaxl (|(Vptr lses_mpaxl) :: rv_paddr ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                                (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                                nil|) ;;
        csl_msmc_setSESMPAXL (Z.to_nat DNUM) 
                                                          (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lses_mpaxl) ??
       (* end of ksCurDomain <> -1*)
      ( ksCurDomain_err (|nil|) ;; (* ksCurDomain = -1*)
         (* index = MPAXSHIPARTIONCUR *)
        set_mpaxh (|(Vptr lmpaxh) :: (Vint32 Int.zero) :: (Vint32 Int.zero) :: nil|) ;;
        csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lmpaxh ;;
        set_mpaxh (|(Vptr lsms_mpaxh) :: (Vint32 Int.zero) :: (Vint32 Int.zero) ::  nil|) ;;
        csl_msmc_setSMSMPAXH (Z.to_nat DNUM) 
                                                            (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lsms_mpaxh ;;
        set_mpaxh (|(Vptr lses_mpaxh) :: (Vint32 Int.zero) :: (Vint32 Int.zero) ::  nil|) ;;
        csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                                                          (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lses_mpaxh ;;
        set_mpaxl (|(Vptr lmpaxl) :: (Vint32 (Int.shru Int.zero (Int.repr 12))) ::
                               (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) ::
                                (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) ::
                                nil|) ;;
        csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lmpaxl ;;
        set_mpaxl (|(Vptr lsms_mpaxl) :: (Vint32 (Int.shru Int.zero (Int.repr 12))) ::
                                (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) ::
                                (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) ::
                                nil|) ;;
        csl_msmc_setSMSMPAXL (Z.to_nat DNUM) 
                                                           (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lsms_mpaxl ;;
        set_mpaxl (|(Vptr lses_mpaxl) :: (Vint32 (Int.shru Int.zero (Int.repr 12))) ::
                                (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) ::
                                (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) ::
                                nil|) ;;
        csl_msmc_setSESMPAXL (Z.to_nat DNUM) 
                                                          (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lses_mpaxl
        ) (*end of ksCurDomain = -1*)
  | _ => spec_abort
  end.

(* initDefaultMPAX *)

Definition mpaxl_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists q evheap t l l',
    exists v v0 v1 v2 v3 v4 v5,
    vl = ((Vptr q) :: nil) /\
    get O1 evstructheapid = Some (evstructheap evheap) /\
    opv = None /\
    l = (v :: v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: nil) /\
    l'  = (v :: Vint32 Int.one :: Vint32 Int.one :: Vint32 Int.one :: Vint32 Int.zero :: Vint32 Int.zero :: Vint32 Int.zero :: nil) /\
    Get_struct evheap q = Some (q, t, l) /\
    O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct evheap q t l')))
end.

Definition initDefaultMPAX' (vl: vallist) :=
  match vl with
     ((Vptr q0) :: (Vptr q1) :: (Vptr q2) :: nil) =>
      csl_xmc_getXMPAXL (Vint32 Int.zero) q0 ;;
      mpaxl_succ (|Vptr q0 :: nil|) ;;
      csl_xmc_setXMPAXL (Vint32 Int.zero) q0  ;;
      csl_xmc_getXMPAXL (Vint32 Int.one) q0 ;;
      mpaxl_succ (|Vptr q0 :: nil|);;
      csl_xmc_setXMPAXL (Vint32 Int.one) q0 ;;
      csl_msmc_getSMSMPAXL (Z.to_nat DNUM) (Vint32 Int.zero) q1 ;;
      mpaxl_succ (|Vptr q1 :: nil|) ;;
      csl_msmc_setSMSMPAXL (Z.to_nat DNUM) (Vint32 Int.zero) q1 ;;
      csl_msmc_getSESMPAXL (Z.to_nat DNUM) (Vint32 Int.zero) q2 ;;
      mpaxl_succ (|Vptr q2 :: nil|) ;;
      csl_msmc_setSESMPAXL (Z.to_nat DNUM) (Vint32 Int.zero) q2
  | _ => spec_abort
  end.

(* initMPAX *)

Definition get_ksdom_paddr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists rv_paddr cur ksdom_vl vdom vid vperiod vpaddr vaddr,
    exists vlen vsize vstatus vintst voff,
    vl = (rv_paddr :: nil) /\
    get O1 kscurdomid = Some (kscurdom cur) /\
    get O1 ksdomsid = Some (ksdoms ksdom_vl) /\
    KsDomsMod.get ksdom_vl cur = Some (vdom, vid, vperiod, vpaddr, vaddr, vlen,
 vsize, vstatus, vintst) /\
    voff = Int.shru vpaddr (Int.repr 12) /\
    ( rv_paddr = Vint32 voff /\ O_opt = Some O1
     \/ (rv_paddr <> Vint32 voff /\ O_opt = None)) /\
    opv = None
end.

Fixpoint spec_code_cons' (s1:spec_code) (s2:spec_code) :=
  match s1 with
  | sp1 ?? sp2 => (spec_code_cons' sp1 s2) ?? (spec_code_cons' sp2 s2)
  | sp1 ;; sp2 => spec_code_cons' sp1 (spec_code_cons' sp2 s2)
  | _ => s1 ;; s2
  end.

Definition initMPAX' (vl: vallist) :=
  match vl with
      (Vptr lmpaxh) :: (Vptr lmpaxl) :: (Vptr lses_mpaxh) ::
      (Vptr lses_mpaxl) :: (Vptr lsms_mpaxh) :: (Vptr lsms_mpaxl) :: 
      rv_baddr :: rv_raddr :: rv_size :: rv_vaddr :: rv_paddr :: nil =>
      spec_code_cons' (initDefaultMPAX' (Vptr lmpaxl :: Vptr lsms_mpaxl :: Vptr lses_mpaxl :: nil))
      (( ksCurDomain_err (|nil|) ??
       ((*index = MPAXSHIPARTIONSTKCUR *)
        get_rtsk_baddr (|rv_baddr :: nil|) ;;
        set_mpaxh (|(Vptr lmpaxh) :: rv_baddr :: (Vint32 (Int.repr 12)) :: nil|) ;;
        csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lmpaxh ;;
        set_mpaxh (|(Vptr lsms_mpaxh) :: rv_baddr :: (Vint32 (Int.repr 12)) :: nil|) ;;
        csl_msmc_setSMSMPAXH (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lsms_mpaxh ;;

        set_mpaxh (|(Vptr lses_mpaxh) :: rv_baddr :: (Vint32 (Int.repr 12)) :: nil|) ;;
        csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lses_mpaxh ;;
        get_rtsk_raddr (|rv_raddr :: nil|) ;;
        set_mpaxl (|(Vptr lmpaxl) :: rv_raddr ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                    nil|) ;;
        csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lmpaxl ;;
        set_mpaxl (|(Vptr lsms_mpaxl) :: rv_raddr ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                    nil|) ;;
        csl_msmc_setSMSMPAXL (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lsms_mpaxl ;;
        set_mpaxl (|(Vptr lses_mpaxl) :: rv_raddr ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                    nil|) ;;
        csl_msmc_setSESMPAXL (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONSTKCUR)) lses_mpaxl ;;
        (*index = MPAXSHIPARTIONCUR *)
        get_ksdom_size_vaddr (| rv_size :: rv_vaddr :: nil |) ;;
        set_mpaxh (|(Vptr lmpaxh) :: rv_vaddr :: rv_size :: nil|) ;;
        csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lmpaxh ;;
        set_mpaxh (|(Vptr lsms_mpaxh) :: rv_vaddr :: rv_size :: nil|) ;;
        csl_msmc_setSMSMPAXH (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lsms_mpaxh ;;
      
        set_mpaxh (|(Vptr lses_mpaxh) :: rv_vaddr :: rv_size :: nil|) ;;
        csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lses_mpaxh ;;
        get_ksdom_paddr (| rv_paddr :: nil |) ;;
        set_mpaxl (|(Vptr lmpaxl) :: rv_paddr ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                    nil|) ;;
        csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lmpaxl ;;
        set_mpaxl (|(Vptr lsms_mpaxl) :: rv_paddr ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                    nil|) ;;
        csl_msmc_setSMSMPAXL (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lsms_mpaxl ;;
        set_mpaxl (|(Vptr lses_mpaxl) :: rv_paddr ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) :: 
                    nil|) ;;
        csl_msmc_setSESMPAXL (Z.to_nat DNUM) 
                             (Vint32 (Int.repr MPAXSHIPARTIONCUR)) lses_mpaxl)
       );; (* end of ksCurDomain <> -1*)
       (* index = MPAXSHAREDAREA *)
       set_mpaxh (|(Vptr lmpaxh) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x13) :: nil|) ;;
       csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXSHAREDAREA)) lmpaxh ;;
       set_mpaxh (|(Vptr lsms_mpaxh) ::  
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x13) :: nil|) ;;
       csl_msmc_setSMSMPAXH (Z.to_nat DNUM) 
                            (Vint32 (Int.repr MPAXSHAREDAREA)) lsms_mpaxh ;;
       set_mpaxh (|(Vptr lses_mpaxh) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x13) :: nil|) ;;
       csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                            (Vint32 (Int.repr MPAXSHAREDAREA)) lses_mpaxh ;;
       set_mpaxl (|(Vptr lmpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.zero) :: (Vint32 Int.one) :: 
                    nil|) ;;
       csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXSHAREDAREA)) lmpaxl ;;
       set_mpaxl (|(Vptr lsms_mpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.zero) :: (Vint32 Int.one) :: 
                    nil|) ;;
       csl_msmc_setSMSMPAXL (Z.to_nat DNUM)
                            (Vint32 (Int.repr MPAXSHAREDAREA)) lsms_mpaxl ;;
       set_mpaxl (|(Vptr lses_mpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.one) :: (Vint32 Int.zero) :: (Vint32 Int.one) :: 
                    nil|) ;;
       csl_msmc_setSESMPAXL (Z.to_nat DNUM)
                            (Vint32 (Int.repr MPAXSHAREDAREA)) lses_mpaxl ;;
       (* index = MPAXALLAREA *)
       set_mpaxh (|(Vptr lmpaxh) ::  
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x15) :: nil|) ;;
       csl_xmc_setXMPAXH (Vint32 (Int.repr MPAXALLAREA))lmpaxh ;;
       set_mpaxh (|(Vptr lsms_mpaxh) ::  
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x15) :: nil|) ;;
       csl_msmc_setSMSMPAXH (Z.to_nat DNUM) 
                            (Vint32 (Int.repr MPAXALLAREA)) lsms_mpaxh ;;
       set_mpaxh (|(Vptr lses_mpaxh) ::  
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) :: 
                    Vint32 (Int.repr 0x15) :: nil|) ;;
       csl_msmc_setSESMPAXH (Z.to_nat DNUM) 
                            (Vint32 (Int.repr MPAXALLAREA)) lses_mpaxh ;;
       set_mpaxl (|(Vptr lmpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) :: 
                    nil|) ;;
       csl_xmc_setXMPAXL (Vint32 (Int.repr MPAXALLAREA)) lmpaxl ;;
       set_mpaxl (|(Vptr lsms_mpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) :: 
                    nil|) ;;
       csl_msmc_setSMSMPAXL (Z.to_nat DNUM)
                            (Vint32 (Int.repr MPAXALLAREA)) lsms_mpaxl ;;
       set_mpaxl (|(Vptr lses_mpaxl) :: 
                    Vint32 (Int.shru (Int.repr 0x0C000000) (Int.repr 12)) ::
                    (Vint32 Int.one) :: (Vint32 Int.one) :: (Vint32 Int.one) ::
                    (Vint32 Int.zero) :: (Vint32 Int.zero) :: (Vint32 Int.zero) :: 
                    nil|) ;;
       csl_msmc_setSESMPAXL (Z.to_nat DNUM)
                            (Vint32 (Int.repr MPAXALLAREA)) lses_mpaxl) ;;
       csl_xmc_clearFault ;;
       csl_cgem_clearMDMAError
  | _ => spec_abort
  end.

(* IntPartitionMuxInit *)

Fixpoint set_idm_to_ipm (cnum: nat) (idm: IntrDomMod.map) (ipm: IntPMuxMod.map) : IntPMuxMod.map :=
  match cnum with
  | 0%nat => match IntrDomMod.get idm (Int.repr (Z.of_nat cnum)) with
              | None => ipm
              | Some idmv => (set ipm (Int.repr (Z.of_nat cnum)) idmv)
              end
  | (S cnum') => match IntrDomMod.get idm (Int.repr (Z.of_nat cnum)) with
                  | None => set_idm_to_ipm cnum' idm ipm
                  | Some idmv => set (set_idm_to_ipm cnum' idm ipm) 
                                     (Int.repr (Z.of_nat cnum)) idmv
                  end
  end.

Definition intpartmux_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      exists uconf mgf fv fn fps fccs fnps idm a cpus,
      exists ccf ptrg ptrt pt mgl ipm ipm',
      vl = nil /\
      get O1 uconfid = Some (absuconf uconf) /\
      uconf = (mgf, fv, fn, fps, fccs, fnps, idm, a, cpus, ccf, ptrg, ptrt, pt, mgl) /\
      get O1 intpmuxid = Some (intparmux ipm) /\
      ipm' = set_idm_to_ipm (Z.to_nat (USER_INT_MAX_N - 1)%Z) idm ipm /\
      opv = None /\
      O_opt = Some (set O1 intpmuxid (intparmux ipm'))
  end.

Definition intpartmux (vl: vallist) := intpartmux_succ (|vl|).

