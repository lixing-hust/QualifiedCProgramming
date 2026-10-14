Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import include_frm.

Open Scope list_scope.
Open Scope code_scope.

Definition kscurdom_ext
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists curd,
      (vl = nil) /\
      get O1 kscurdomid = Some (kscurdom curd) /\
     opv = None /\
     ( curd <> Int.mone /\ O_opt = Some O1
       \/ (curd = Int.mone /\ O_opt = None))
  end.

Definition get_temp_dom
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists  vr_temp_dom curd domls idx,
      (vl =  (vr_temp_dom)  :: nil) /\
      get O1 kscurdomid = Some (kscurdom curd) /\
      get O1 dom2indexid = Some (domindexlist domls) /\
      get domls curd = Some idx /\
     opv = None /\
     ( vr_temp_dom = Vint32 idx /\ O_opt = Some O1
       \/ (vr_temp_dom <> Vint32 idx /\ O_opt = None))
  end.

Definition get_temp_num
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists  vr_temp_num cpn,
      (vl =  (vr_temp_num)  :: nil) /\
      get O1 cpartnumid = Some (cpartnum cpn) /\
     opv = None /\
     ( vr_temp_num = Vint32 cpn /\ O_opt = Some O1
       \/ (vr_temp_num <> Vint32 cpn /\ O_opt = None))
  end.

Definition pos_lt_rgn_err
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists  pos vr_temp_dom vr_temp_num evt,
      (vl =  Vint32 pos :: (Vint32 vr_temp_dom)  :: (Vint32 vr_temp_num) :: nil) /\
       evt = (Int.repr (OS_USER_MAX_EVENTS / 3)) /\
      Int.ltu pos (Int.mul (Int.divs evt vr_temp_num) vr_temp_dom) = true /\
     opv =  Some (Vint32 (Int.mone)) /\
     O_opt = Some O1
  end.

Definition pos_ge_rgn_err
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists  pos vr_temp_dom vr_temp_num evt,
      (vl =  Vint32 pos :: (Vint32 vr_temp_dom)  :: (Vint32 vr_temp_num) :: nil) /\
       evt = (Int.repr (OS_USER_MAX_EVENTS / 3)) /\
      Int.ltu pos (Int.mul (Int.divs evt vr_temp_num) (Int.add vr_temp_dom Int.one)) = false /\
     opv =  Some (Vint32 (Int.mone)) /\
     O_opt = Some O1
  end.

Definition partition_pos_rgn (vl: vallist) s :=
match vl with
posv :: vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil =>
             kscurdom_ext (| nil |) ;;
             get_temp_dom (| vr_temp_dom :: nil |) ;;
             get_temp_num (| vr_temp_num :: nil |) ;;
             (pos_lt_rgn_err (| posv ::  vr_temp_dom :: vr_temp_num :: nil |) ??
               (kscurdom_ext (| nil |) ;; 
                 get_temp_dom (| vr_temp_dom' :: nil |) ;;
                 get_temp_num (| vr_temp_num' :: nil |) ;;
                 (pos_ge_rgn_err (| posv ::  vr_temp_dom' :: vr_temp_num' :: nil |) ??
                   s)))
| _ => spec_abort
end.

Definition partition_pos_out_of_rgn_err
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a pbls posv evt curd domls idx cpn,
      vl = (Vptr a) :: nil /\
      opv = Some (Vint32 (Int.mone)) /\ 
      cmpaddr Clt userAddrStart a = true /\
      cmpaddr Cle a userAddrEnd = true /\
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a = Some posv /\
      get O1 kscurdomid = Some (kscurdom curd) /\
      get O1 dom2indexid = Some (domindexlist domls) /\
      get domls curd = Some idx /\
      get O1 cpartnumid = Some (cpartnum cpn) /\
      evt = (Int.repr (OS_USER_MAX_EVENTS / 3)) /\
      (Int.ltu posv (Int.mul (Int.divs evt cpn) idx) = true \/
        Int.ltu posv (Int.mul (Int.divs evt cpn) (Int.add idx Int.one)) = false) /\
       O_opt = Some O1
  end.


