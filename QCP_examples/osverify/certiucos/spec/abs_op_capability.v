Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import ios_int.
Require Import int_lock.
Require Import evt_spec_defs. 
Require Import ios_cap_defs.
Require Import Lia.
Require Import os_inv. 
Require Import abs_op.
 
Definition EINVAL := 30%Z.

(* High-level specification *)

(* Obtain list of child tasks of a task.

  The arguments are: prio, childs, map.
*)
Inductive child_abs: int32 -> list int32 -> CSpaceMod.map -> Prop :=
  |child_abs_rule:
  forall i slots childs map prio,
    CSpaceMod.get map i = Some (slots, childs, prio) ->
    child_abs i childs map
  |child_abs_rule_none:
    forall i map,
    CSpaceMod.get map i = None ->
    child_abs i nil map.

    (*
    Inductive child_rel: CSpaceMod.map -> int32 -> int32 -> Prop :=
  child_rel_rule:
  forall acspace slots childs i j prio,
    CSpaceMod.get acspace i = Some (slots, childs, prio) ->
    List.In j childs ->
    child_rel acspace j i.*)

Inductive child_rel: CSpaceMod.map -> int32 -> int32 -> Prop :=
  child_rel_rule:
  forall acspace slots childs i j parent,
    CSpaceMod.get acspace j = Some (slots, childs, parent) ->
    parent = i ->
    child_rel acspace j i.

Fixpoint nth_slots (n: nat) (vl: list slot_val_type) :=
  match vl with 
  |nil => None 
  |v :: vl' =>
      match n with 
      | 0%nat => Some v 
      | S n' => nth_slots n' vl' 
      end 
  end.

Fixpoint update_nth_slots (n: nat) (vl : list slot_val_type) (v : slot_val_type) :=
  match vl with
    | nil => nil
    | v'::vl' => match n with
                  | 0%nat => v::vl'
                  | S n' => v'::(update_nth_slots n' vl' v)
                end
  end.

Fixpoint update_nth_list (t: Type) (n : nat) (vl : list t) (v : t){struct vl} :=
  match vl with
    | nil => nil
    | v'::vl' => match n with
                  | 0%nat => v::vl'
                  | S n' => v'::(update_nth_list t n' vl' v)
                end
  end.

  
Definition check_cap_type_spec (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
    exists  capability captype prior v',
    vl = ((Vint32 capability) :: (Vint32 captype) :: (Vint32 prior) :: v') /\
    O2 = Some O1 /\
    ((opv = Some (Vint32 (Int.repr SLOT_NUM))) \/
      (exists idx, opv = Some (Vint32 (Int.repr idx)) /\ (Z.to_nat idx) < 255))
  end. 
(* High-level specification of Get_Obj_Slot function.

  The function accepts an object and looks up capability to that
  object. If it is found, return the corresponding index. Otherwise
  return SLOT_NULL_CAP.

  The arguments are: prio, obj, O1, return value
*)
Inductive get_obj_slot_rel: int32 -> addrval -> CSpaceMod.map -> int32 -> Prop :=
  get_obj_slot_rel_found:
  forall prio obj acspace slots childs prio' idx slot_type cap_type cap_content cap_right,
    CSpaceMod.get acspace prio = Some (slots, childs, prio') ->
    nth_slots (Z.to_nat idx) slots =
      Some (slot_type, (cap_type, (cap_content, cap_right, Vptr obj))) ->
    get_obj_slot_rel prio obj acspace (Int.repr idx)
| get_obj_slot_rel_not_found:
  forall prio obj acspace slots childs prio',
    CSpaceMod.get acspace prio = Some (slots, childs, prio') ->
    (~exists idx slot_type cap_type cap_content cap_right,
      nth_slots (Z.to_nat idx) slots =
        Some (slot_type, (cap_type, (cap_content, cap_right, Vptr obj)))) ->
    get_obj_slot_rel prio obj acspace (Int.repr SLOT_NULL_CAP).

(* High-level specification of Check_Cap_Type.

  This function accepts three parameters: capability, capType, and prio.
  Depending on the value of capType, it performs the following:

  - if capType = CAP_FUNCTION_TYPE, the function verifies that capability
    is less than OBJ_POSITION, and returns capability.

  - if capType = CAP_SEM_TYPE, capability is index within Sem_info, return
    the corresponding pointer to semaphore.

  - if capType = CAP_MUTEX_TYPE, capability is index within Pthread_Mutex,
    return the corresponding pointer to mutex.

  - if capType = CAP_Q_TYPE, capability is index within Mq_Attr, return
    the corresponding pointer to queue.

  - if capType = CAP_TASK_TYPE, capability is priority, return the
    corresponding pointer to TCB.

  The arguments are: capability, capType, prio, O1, return value
*)
Inductive check_cap_type_rel: int32 -> int32 -> int32 -> osabst -> int32 -> Prop :=
  check_cap_type_rel_function_succ:
  forall capability capType prio O1,
    Int.eq capType (Int.repr CAP_FUNCTION_TYPE) = true ->
    Int.lt prio (Int.repr OBJ_POSITION) = true ->
    check_cap_type_rel capability capType prio O1 capability
| check_cap_type_rel_function_fail:
  forall capability capType prio O1,
    Int.eq capType (Int.repr CAP_FUNCTION_TYPE) = true ->
    Int.lt prio (Int.repr OBJ_POSITION) = false ->
    check_cap_type_rel capability capType prio O1 (Int.repr SLOT_NUM)
| check_cap_type_rel_sem_null:
  forall capability capType prio O1 semifo,
    Int.eq capType (Int.repr CAP_SEM_TYPE) = true ->
    get O1 seminfoid = Some (seminfo semifo) ->
    (exists bin sc,
      get semifo capability = Some (infonull, bin, sc)) ->
    check_cap_type_rel capability capType prio O1 (Int.repr SLOT_NUM)
| check_cap_type_rel_sem:
  forall capability capType prio O1 acspace semifo ptr,
    Int.eq capType (Int.repr CAP_SEM_TYPE) = true ->
    get O1 cspaceid = Some (capcspace acspace) ->
    get O1 seminfoid = Some (seminfo semifo) ->
    (exists bin sc,
      get semifo capability = Some (infotid ptr, bin, sc)) ->
    get_obj_slot_rel prio ptr acspace (Int.repr idx) ->
    check_cap_type_rel capability capType prio O1 (Int.repr idx)
| check_cap_type_rel_sem_not_found:
  forall capability capType prio O1 acspace semifo ptr,
    Int.eq capType (Int.repr CAP_SEM_TYPE) = true ->
    get O1 cspaceid = Some (capcspace acspace) ->
    get O1 seminfoid = Some (seminfo semifo) ->
    (exists bin sc,
      get semifo capability = Some (infotid ptr, bin, sc)) ->
    get_obj_slot_rel prio ptr acspace (Int.repr SLOT_NULL_CAP) ->
    check_cap_type_rel capability capType prio O1 (Int.repr SLOT_NUM)
| check_cap_type_rel_mutex_null:
  forall capability capType prio O1 mls,
    Int.eq capType (Int.repr CAP_MUTEX_TYPE) = true ->
    get O1 absmutinfoid = Some (absmutinfo mls) ->
    (exists o x n pro pi w c mc,
      get mls capability = Some (Null, o, x, n, pro, pi, w, c, mc)) ->
    check_cap_type_rel capability capType prio O1 (Int.repr SLOT_NUM)
| check_cap_type_rel_mutex:
  forall capability capType prio O1 acspace mls ptr,
    Int.eq capType (Int.repr CAP_MUTEX_TYPE) = true ->
    get O1 cspaceid = Some (capcspace acspace) ->
    get O1 absmutinfoid = Some (absmutinfo mls) ->
    (exists o x n pro pi w c mc,
      get mls capability = Some (Valid_Addr ptr, o, x, n, pro, pi, w, c, mc)) ->
    get_obj_slot_rel prio ptr acspace (Int.repr idx) ->
    check_cap_type_rel capability capType prio O1 (Int.repr idx)
| check_cap_type_rel_mutex_not_found:
  forall capability capType prio O1 acspace mls ptr,
    Int.eq capType (Int.repr CAP_MUTEX_TYPE) = true ->
    get O1 cspaceid = Some (capcspace acspace) ->
    get O1 absmutinfoid = Some (absmutinfo mls) ->
    (exists o x n pro pi w c mc,
      get mls capability = Some (Valid_Addr ptr, o, x, n, pro, pi, w, c, mc)) ->
    get_obj_slot_rel prio ptr acspace (Int.repr SLOT_NULL_CAP) ->
    check_cap_type_rel capability capType prio O1 (Int.repr SLOT_NUM)
| check_cap_type_rel_q_null:
  forall capability capType prio O1 qtls,
    Int.eq capType (Int.repr CAP_Q_TYPE) = true ->
    get O1 absmqattrid = Some (absmqattr qtls) ->
    (exists wtype flag maxm msize curm mqc,
      get qtls capability = Some (Null, wtype, flag, maxm, msize, curm, mqc)) ->
    check_cap_type_rel capability capType prio O1 (Int.repr SLOT_NUM)
| check_cap_type_rel_q:
  forall capability capType prio acspace O1 qtls ptr,
    Int.eq capType (Int.repr CAP_Q_TYPE) = true ->
    get O1 cspaceid = Some (capcspace acspace) ->
    get O1 absmqattrid = Some (absmqattr qtls) ->
    (exists wtype flag maxm msize curm mqc,
      get qtls capability = Some (Valid_Addr ptr, wtype, flag, maxm, msize, curm, mqc)) ->
    get_obj_slot_rel prio ptr acspace (Int.repr idx) ->
    check_cap_type_rel capability capType prio O1 (Int.repr idx)
| check_cap_type_rel_q_not_found:
  forall capability capType prio O1 acspace qtls ptr,
    Int.eq capType (Int.repr CAP_Q_TYPE) = true ->
    get O1 cspaceid = Some (capcspace acspace) ->
    get O1 absmqattrid = Some (absmqattr qtls) ->
    (exists wtype flag maxm msize curm mqc,
      get qtls capability = Some (Valid_Addr ptr, wtype, flag, maxm, msize, curm, mqc)) ->
    get_obj_slot_rel prio ptr acspace (Int.repr SLOT_NULL_CAP) ->
    check_cap_type_rel capability capType prio O1 (Int.repr SLOT_NUM).

(* Obtain list of descendent tasks of a task or a list of tasks.

  - For wellform_descendents_abs, the arguments are:
    prio, descendents, map.
  - For wellform_descendents_list_abs, the arguments are:
    prio list, descendents, map.
*)

 

Inductive wellform_descendents_abs: int32 -> list int32 -> CSpaceMod.map -> Prop :=
| wellform_descendents_abs_rule:
  forall node childs map descs,
    child_abs node childs map ->
    wellform_descendents_list_abs childs descs map ->
    (contains descs node = false) ->
    wellform_descendents_abs node (node :: descs) map
with
  wellform_descendents_list_abs: list int32 -> list int32 -> CSpaceMod.map -> Prop :=
| wellform_descendents_list_abs_nil:
  forall map,
    wellform_descendents_list_abs nil nil map
| wellform_descendents_list_abs_cons:
  forall node desc1 rest desc2 map,
    wellform_descendents_abs node desc1 map ->
    wellform_descendents_list_abs rest desc2 map ->
    intersection desc1 desc2 = false ->
    wellform_descendents_list_abs (node :: rest) (desc1 ++ desc2) map.

(* Reset a single slot, inner abstract version.

  The arguments are: prio, cap, O1, O2.

  There are two cases: the capability to the reset has either category
  or object type.
*)
Inductive reset_nth_cspace_slot_ucos:
    int32 -> int32 -> CSpaceMod.map -> CSpaceMod.map -> Prop :=
| reset_nth_cspace_slot_ucos_none_cspace:
  forall i cap acspace,
  CSpaceMod.get acspace i = None->
  reset_nth_cspace_slot_ucos i cap acspace acspace
| reset_nth_cspace_slot_ucos_none_slots:
  forall i cap acspace slots childs prio,
    CSpaceMod.get acspace i = Some (slots, childs, prio) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) slots = None ->
    reset_nth_cspace_slot_ucos i cap acspace acspace
| reset_nth_cspace_slot_ucos_category:
  forall i cap acspace slots childs prio,
  forall slot_type cap_type cap_content cap_right object_t,
    CSpaceMod.get acspace i = Some (slots, childs, prio) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) slots =
      Some (slot_type, (cap_type, (cap_content, cap_right, object_t))) ->
    Int.eq cap_type (Int.repr CAP_CATEGORY_TYPE) = true ->
    reset_nth_cspace_slot_ucos i cap acspace
        (CSpaceMod.set (
          CSpaceMod.set acspace i
          (update_nth_list slot_val_type (Z.to_nat (Int.unsigned cap)) slots
            (slot_type, (Int.zero, (Int.zero, Int.zero, object_t))),
          childs, prio)
          ) i
          (update_nth_list slot_val_type (Z.to_nat (Int.unsigned cap)) (update_nth_list slot_val_type (Z.to_nat (Int.unsigned cap)) slots
            (slot_type, (Int.zero, (Int.zero, Int.zero, object_t))))
            (Int.repr SLOT_NULL_CAP, (Int.zero, (Int.zero, Int.zero, object_t))),
          childs, prio))
| reset_nth_cspace_slot_ucos_object:
  forall i cap  acspace slots childs prio,
  forall slot_type cap_type cap_content cap_right object_t,
    CSpaceMod.get acspace i = Some (slots, childs, prio) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) slots =
      Some (slot_type, (cap_type, (cap_content, cap_right, object_t))) ->
    Int.eq cap_type (Int.repr CAP_OBJECT_TYPE) = true ->
    reset_nth_cspace_slot_ucos i cap acspace
        (CSpaceMod.set (
          CSpaceMod.set acspace i
          (update_nth_list slot_val_type (Z.to_nat (Int.unsigned cap)) slots
            (slot_type, (Int.zero, (Int.zero, cap_right, Vnull))),
          childs, prio)
          ) i
          (update_nth_list slot_val_type (Z.to_nat (Int.unsigned cap)) (update_nth_list slot_val_type (Z.to_nat (Int.unsigned cap)) slots
          (slot_type, (Int.zero, (Int.zero, cap_right, Vnull))))
            (Int.repr SLOT_NULL_CAP, (Int.zero, (Int.zero, cap_right, Vnull))),
          childs, prio))
| reset_nth_cspace_slot_ucos_nocapobj:
  forall i cap  acspace slots childs prio,
  forall slot_type cap_type cap_content cap_right object_t,
    CSpaceMod.get acspace i = Some (slots, childs, prio) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) slots =
      Some (slot_type, (cap_type, (cap_content, cap_right, object_t))) ->
    Int.eq cap_type (Int.repr CAP_CATEGORY_TYPE) = false ->
    Int.eq cap_type (Int.repr CAP_OBJECT_TYPE) = false ->
    reset_nth_cspace_slot_ucos i cap acspace (CSpaceMod.set (
      CSpaceMod.set acspace i
      (update_nth_list slot_val_type (Z.to_nat (Int.unsigned cap)) slots
        (slot_type, (cap_type, (cap_content, cap_right, object_t))),
      childs, prio)
      ) i
      (update_nth_list slot_val_type (Z.to_nat (Int.unsigned cap)) (update_nth_list slot_val_type (Z.to_nat (Int.unsigned cap)) slots
      (slot_type, (cap_type, (cap_content, cap_right, object_t))))
        (Int.repr SLOT_NULL_CAP, (cap_type, (cap_content, cap_right, object_t))),
      childs, prio)).

(* wsl: user_cnode_delete_impl?
  Reset a single slot, outer abstract version.

  The arguments are: prio, capType, capability, O1, O2.

  First call Check_Cap_Type to obtain the correct index into slots,
  then depending on capType, possibly clear the corresponding value
  in sem_cap, etc.
*)
(* Inductive reset_nth_cspace_slot_user:
    int32 -> int32 -> int32 -> osabst -> osabst -> Prop :=
| reset_nth_cspace_slot_user_not_found:
  forall prio capType capability O1,
    (* Check_Cap_Type returns not found: do nothing *)
    check_cap_type_rel capability capType prio O1 (Int.repr SLOT_NUM) ->
    reset_nth_cspace_slot_user prio capType capability O1 O1
| reset_nth_cspace_slot_user_sem:
  forall prio capType capability O1 O2,
    (* First step: call reset_nth_cspace_slot_ucos *)
    check_cap_type_rel capability capType prio O1 (Int.repr index) ->
    reset_nth_cspace_slot_ucos prio (Int.repr index) O1 O2 ->
    Int.eq capType (Int.repr CAP_SEM_TYPE) = true ->
    (* Second step: update Sem_info's sem_cap *)
    forall acspace semifo ptr bin sc,
      get O2 cspaceid = Some (capcspace acspace) ->
      get O2 seminfoid = Some (seminfo semifo) ->
      get semifo capability = Some (infotid ptr, bin, sc) ->
      reset_nth_cspace_slot_user prio capType capability O1
        (set O2 seminfoid (seminfo (EmbMod.set semifo capability
          (infotid ptr, bin,
           update_nth_list int32 (Z.to_nat (Int.signed (Int.sub prio Int.one)))
            sc Int.zero))))
| reset_nth_cspace_slot_user_mutex:
  forall prio capType capability O1 O2,
    (* First step: call reset_nth_cspace_slot_ucos *)
    check_cap_type_rel capability capType prio O1 (Int.repr index) ->
    reset_nth_cspace_slot_ucos prio (Int.repr index) O1 O2 ->
    Int.eq capType (Int.repr CAP_MUTEX_TYPE) = true ->
    (* Second step: update Pthread_Mutex's mutex_cap *)
    forall acspace mls ptr o x n pro pi w c mc,
      get O2 cspaceid = Some (capcspace acspace) ->
      get O2 absmutinfoid = Some (absmutinfo mls) ->
      get mls capability = Some (Valid_Addr ptr, o, x, n, pro, pi, w, c, mc) ->
      reset_nth_cspace_slot_user prio capType capability O1
        (set O2 absmutinfoid (absmutinfo (MibMod.set mls capability
          (Valid_Addr ptr, o, x, n, pro, pi, w, c,
           update_nth_list int32 (Z.to_nat (Int.signed (Int.sub prio Int.one)))
            mc Int.zero))))
| reset_nth_cspace_slot_user_q:
  forall prio capType capability O1 O2,
    (* First step: call reset_nth_cspace_slot_ucos *)
    check_cap_type_rel capability capType prio O1 (Int.repr index) ->
    reset_nth_cspace_slot_ucos prio (Int.repr index) O1 O2 ->
    Int.eq capType (Int.repr CAP_Q_TYPE) = true ->
    (* Second step: update Mq_attr's mq_cap *)
    forall acspace qtls ptr wtype flag maxm msize curm mqc,
      get O2 cspaceid = Some (capcspace acspace) ->
      get O2 absmqattrid = Some (absmqattr qtls) ->
      get qtls capability = Some (Valid_Addr ptr, wtype, flag, maxm, msize, curm, mqc) ->
      reset_nth_cspace_slot_user prio capType capability O1
        (set O2 absmqattrid (absmqattr (MqattrMod.set qtls capability
          (Valid_Addr ptr, wtype, flag, maxm, msize, curm,
           update_nth_list int32 (Z.to_nat (Int.signed (Int.sub prio Int.one)))
            mqc Int.zero))))
| reset_nth_cspace_slot_user_category:
  forall prio capType capability O1 O2,
    (* Call reset_nth_cspace_slot_ucos *)
    check_cap_type_rel capability capType prio O1 (Int.repr index) ->
    reset_nth_cspace_slot_ucos prio (Int.repr index) O1 O2 ->
    Int.eq capType (Int.repr CAP_FUNCTION_TYPE) = true ->
    reset_nth_cspace_slot_user prio capType capability O1 O2. *)



(* Reset capability for all descendents

  - For reset_descendents_cspace_slot_abs, the arguments are:
    prio, capType, capability, O1, O2
  - For reset_descendents_cspace_list_slot_abs, the arguments are:
    prio list, capType, capability, O1, O2
*)
Definition Check_Cap_Type_WeakRet v:=
  (v = Z.to_nat SLOT_NUM)%nat \/ (0%nat <= v < Z.to_nat SLOT_NUM)%nat.


Definition reset_nth_cspace_slot_ucos_option prio (capability: int32) n_class acspace1 acspace2:=
  Check_Cap_Type_WeakRet n_class/\
  if((0 <=? n_class)%nat && (n_class <? Z.to_nat SLOT_NUM)%nat )
  then reset_nth_cspace_slot_ucos prio  (Int.repr (Z.of_nat n_class)) acspace1 acspace2
  else acspace2 = acspace1.
Inductive reset_descendents_cspace_slot_abs:
    int32-> int32 -> CSpaceMod.map -> CSpaceMod.map -> Prop :=
| reset_descendents_cspace_slot_abs_rule:
  forall prio  capability acspace childs acspace1 acspace2,
    child_abs prio childs acspace ->
    (exists n_class, reset_nth_cspace_slot_ucos_option prio  capability n_class acspace acspace1 )->
    reset_descendents_cspace_list_slot_abs childs capability acspace1 acspace2 ->
    reset_descendents_cspace_slot_abs prio capability acspace acspace2
with
  reset_descendents_cspace_list_slot_abs:
    list int32 -> int32 -> CSpaceMod.map -> CSpaceMod.map -> Prop :=
| reset_descendents_cspace_list_slot_abs_nil:
  forall capability acspace,
    reset_descendents_cspace_list_slot_abs nil capability acspace acspace
| reset_descendents_cspace_list_slot_abs_cons:
  forall node rest capability acspace1 acspace2 acspace3,
    reset_descendents_cspace_slot_abs node  capability acspace1 acspace2 ->
    reset_descendents_cspace_list_slot_abs rest capability acspace2 acspace3 ->
    reset_descendents_cspace_list_slot_abs (node :: rest)  capability acspace1 acspace3.

(* High-level specification of ucos_CNode_Mint.

  The arguments are: dest, src, capability, rights, acspace1, return value, acspace2.
  Here capability must be index into category type (less than OBJ_POSITION).
*)


Inductive ucos_cnode_mint_rel:
    int32 -> int32 -> int32 -> int32 -> CSpaceMod.map -> int32 -> CSpaceMod.map -> Prop :=
  ucos_cnode_mint_rel_err:
  forall dest src cap rights,
  forall acspace src_slots src_childs src_prio,
  forall src_slot_type src_cap_type src_cap_content src_cap_right src_object_t,
    CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
      Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, src_object_t))) ->
    ~(Int.eq src_cap_type (Int.repr CAP_CATEGORY_TYPE) = true /\
      Int.eq (Int.and (Int.not src_cap_right) rights) Int.zero = false /\
      Int.eq rights src_cap_right = false) ->
    ucos_cnode_mint_rel dest src cap rights acspace
      (Int.repr CNODE_MINT_FAILURE) acspace
| ucos_cnode_mint_rel_succ:
  forall dest src cap rights O1,
  forall acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
  forall src_slot_type src_cap_type src_cap_content src_cap_right src_object_t,
  forall dest_slot_type dest_cap_type dest_cap_content dest_cap_right dest_object_t,
    get O1 cspaceid = Some (capcspace acspace) ->
    CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) ->
    CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
      Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, src_object_t))) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) dest_slots =
      Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t))) ->
    Int.eq src_cap_type (Int.repr CAP_CATEGORY_TYPE) = true ->
    Int.eq (Int.and (Int.not src_cap_right) rights) Int.zero = true ->
    Int.eq rights src_cap_right = false ->
    ucos_cnode_mint_rel dest src cap rights acspace
      (Int.repr CNODE_NONE_FAULT)
      (CSpaceMod.set acspace dest
        (update_nth_slots (Z.to_nat (Int.unsigned cap)) dest_slots
          (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, rights, dest_object_t))), dest_childs, dest_prio)).

(* High-level specification of user_CNode_mint.

  We make the specification in two stages: first assume both src and dest
  priorities are in valid range (and not OS_PRIO_SELF), then consider the
  general case.

  The arguments are: dest, src, capability, rights, O1, return value, O2.
  
  There are the following cases:
  - the current task does not have capability to perform function.
  - dest is not child of src in CapParent.
  - ucos_CNode_Mint is performed.
*)
Inductive user_cnode_mint_rel':
    int32 -> int32 -> int32 -> int32 -> osabst -> int32 -> osabst -> Prop :=
  user_cnode_mint_rel_no_cap:
  forall dest src cap rights O1,
  forall acspace t tls p st m sus curt_slots curt_childs curt_prio,
  forall curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t,
    get O1 cspaceid = Some (capcspace acspace) ->
    get O1 curtid = Some (oscurt t) ->
    get O1 abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, st, m, sus) ->
    CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_prio) ->
    nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
      Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) ->
    Int.eq (Int.and curt_cap_right (Int.repr CNODE_MINT_CAP)) Int.zero = true ->
    user_cnode_mint_rel' dest src cap rights O1
      (Int.repr USER_CAPABILITY_NONE) O1
| user_cnode_mint_rel_not_parent:
  forall dest src cap rights O1,
  forall acspace src_slots src_childs src_prio,
    get O1 cspaceid = Some (capcspace acspace) ->
    CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) ->
    ~List.In dest src_childs ->
    user_cnode_mint_rel' dest src cap rights O1
      (Int.repr USER_CAPABILITY_NONE) O1
| user_cnode_mint_rel_fail:
  forall dest src cap rights O1 acspace1 rv acspace2,
    (* Call ucos_cnode_mint_rel results in failure *)
    Int.lt cap (Int.repr OBJ_POSITION) = true ->
    get O1 cspaceid = Some (capcspace acspace1) ->
    child_rel acspace1 dest src ->
    ucos_cnode_mint_rel dest src cap rights acspace1 rv acspace2 ->
    Int.eq rv (Int.repr CNODE_NONE_FAULT) = false ->
    user_cnode_mint_rel' dest src cap rights O1
      (Int.repr CNODE_MINT_FAILURE)
      (set O1 cspaceid (capcspace acspace2))
| user_cnode_mint_rel_succ:
  forall dest src cap rights O1 acspace1 acspace2,
    (* Call ucos_cnode_mint_rel results in success *)
    Int.lt cap (Int.repr OBJ_POSITION) = true ->
    get O1 cspaceid = Some (capcspace acspace1) ->
    child_rel acspace1 dest src ->
    ucos_cnode_mint_rel dest src cap rights acspace1
      (Int.repr CNODE_NONE_FAULT) acspace2 ->
    user_cnode_mint_rel' dest src cap rights O1
      (Int.repr CNODE_MINT_SUCCESS)
      (set O1 cspaceid (capcspace acspace2)).

(* In the second stage, we check for validity of dest and src,
   and replace OS_PRIO_SELF with the current priority.

  The arguments are: dest, src, capability, rights, O1, return value, O2.

  There are the following cases:
  - src is invalid
  - dest is invalid
  - src is OS_PRIO_SELF
  - dest is OS_PRIO_SELF
  - both src and dest are in valid range 
*)
Inductive user_cnode_mint_rel:
    int32 -> int32 -> int32 -> int32 -> osabst -> int32 -> osabst -> Prop :=
  user_cnode_mint_rel_src_invalid:
  forall dest src capType capability O1,
    Int.lt src (Int.repr OS_LOWEST_PRIO) = false ->
    Int.eq src (Int.repr OS_PRIO_SELF) = false ->
    user_cnode_mint_rel dest src capType capability O1
      (Int.repr OS_PRIO_INVALID) O1
| user_cnode_mint_rel_dest_invalid:
  forall dest src capType capability O1,
    Int.lt dest (Int.repr OS_LOWEST_PRIO) = false ->
    Int.eq dest (Int.repr OS_PRIO_SELF) = false ->
    user_cnode_mint_rel dest src capType capability O1
      (Int.repr OS_PRIO_INVALID) O1
| user_cnode_mint_rel_src_self:
  forall dest src capType capability O1,
    Int.lt dest (Int.repr OS_LOWEST_PRIO) = true ->
    Int.eq src (Int.repr OS_PRIO_SELF) = true ->
    forall t tls p st m sus rv O2,
      get O1 curtid = Some (oscurt t) ->
      get O1 abstcblsid = Some (abstcblist tls) ->
      get tls t = Some (p, st, m, sus) ->
      user_cnode_mint_rel' dest p capType capability O1 rv O2 ->
      user_cnode_mint_rel dest src capType capability O1 rv O2
| user_cnode_mint_rel_dest_self:
  forall dest src capType capability O1,
    Int.lt src (Int.repr OS_LOWEST_PRIO) = true ->
    Int.eq dest (Int.repr OS_PRIO_SELF) = true ->
    forall t tls p st m sus rv O2,
      get O1 curtid = Some (oscurt t) ->
      get O1 abstcblsid = Some (abstcblist tls) ->
      get tls t = Some (p, st, m, sus) ->
      user_cnode_mint_rel' p src capType capability O1 rv O2 ->
      user_cnode_mint_rel dest src capType capability O1 rv O2
| user_cnode_mint_rel_normal:
  forall dest src capType capability O1 rv O2,
    Int.lt dest (Int.repr OS_LOWEST_PRIO) = true ->
    Int.lt src (Int.repr OS_LOWEST_PRIO) = true ->
    user_cnode_mint_rel' dest src capType capability O1 rv O2 ->
    user_cnode_mint_rel dest src capType capability O1 rv O2.

(* High-level specification of ucos_CNode_Copy.

  The arguments are: dest, src, capability, O1, return value, O2.
  Here capability is index into slots array in src.

  There are three cases:
  - if capability is category type (less than OBJ_POSITION), just copy
    to the same position.
  
  - if capability is object type, and the object is found in dest,
    copy to the corresponding location in dest.

  - if capability is object type, and the object is not found in dest,
    append to the end of slots in dest.
*)
Inductive ucos_cnode_copy_rel:
    int32 -> int32 -> int32 -> CSpaceMod.map -> int32 -> CSpaceMod.map -> Prop :=
  ucos_cnode_copy_rel_category:
  forall dest src cap,
  forall acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
  forall src_slot_type src_cap_type src_cap_content src_cap_right src_object_t,
  forall dest_slot_type dest_cap_type dest_cap_content dest_cap_right dest_object_t,
    CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) ->
    CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
      Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, src_object_t))) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) dest_slots =
      Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t))) ->
    Int.eq src_cap_type (Int.repr CAP_CATEGORY_TYPE) = true ->
    ucos_cnode_copy_rel dest src cap acspace
      (Int.repr CNODE_NONE_FAULT)
      (CSpaceMod.set acspace dest
        (update_nth_slots (Z.to_nat (Int.unsigned cap)) dest_slots
          (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, src_cap_right, dest_object_t))), dest_childs, dest_prio))
| ucos_cnode_copy_rel_object_found:
  forall dest src cap,
  forall acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
  forall src_slot_type src_cap_type src_cap_content src_cap_right object_t,
  forall dest_idx dest_slot_type dest_cap_type dest_cap_content dest_cap_right,
    CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) ->
    CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
      Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, object_t))) ->
    nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots =
      Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, object_t))) ->
    Int.eq src_cap_type (Int.repr CAP_OBJECT_TYPE) = true ->
    ucos_cnode_copy_rel dest src cap acspace
      (Int.repr CNODE_NONE_FAULT)
      (CSpaceMod.set acspace dest
        (update_nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots
          (dest_slot_type, (Int.repr CAP_OBJECT_TYPE, (dest_cap_content, src_cap_right, object_t))), dest_childs, dest_prio))
| ucos_cnode_copy_rel_object_not_found:
  forall dest src cap,
  forall acspace src_slots src_childs dest_slots dest_childs src_prio dest_prio,
  forall src_slot_type src_cap_type src_cap_content src_cap_right object_t,
    CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) ->
    CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
      Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, object_t))) ->
    (~exists dest_idx dest_slot_type dest_cap_type dest_cap_content dest_cap_right,
      nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots =
        Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, object_t)))) ->
    Int.eq src_cap_type (Int.repr CAP_OBJECT_TYPE) = true ->
    ucos_cnode_copy_rel dest src cap acspace
      (Int.repr CNODE_NONE_FAULT)
      (CSpaceMod.set acspace dest
        (dest_slots ++ ((src_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_cap_content, src_cap_right, object_t))) :: nil), dest_childs, dest_prio)).

Definition ucos_cnode_copy_failure (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr CNODE_COPY_FAILURE)) /\
        O2 = Some O1
  end. 

Definition ucos_cnode_copy_category (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        exists dest src cap v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: v')  /\ 
  exists acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
  exists src_slot_type src_cap_type src_cap_content src_cap_right src_object_t,
  exists dest_slot_type dest_cap_type dest_cap_content dest_cap_right dest_object_t,
    CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) /\
    CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) /\
    nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
      Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, src_object_t))) /\
    nth_slots (Z.to_nat (Int.unsigned cap)) dest_slots =
      Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t))) /\
      (opv = Some (Vint32 (Int.repr CNODE_NONE_FAULT)) /\
        O2 = Some (set O1 cspaceid (capcspace
        ((CSpaceMod.set acspace dest
        (update_nth_slots (Z.to_nat (Int.unsigned cap)) dest_slots
          (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, src_cap_right, dest_object_t))), dest_childs, dest_prio)))))
      )
  end. 

Definition ucos_cnode_copy_object_found (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        exists dest src cap v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: v')  /\ 
        exists acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
        exists src_slot_type src_cap_type src_cap_content src_cap_right object_t,
        exists dest_idx dest_slot_type dest_cap_type dest_cap_content dest_cap_right,
          CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) /\ 
          CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) /\ 
          nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
            Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, object_t))) /\ 
          nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots =
            Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, object_t))) /\ 
            (opv = Some (Vint32 (Int.repr CNODE_NONE_FAULT)) /\
            O2 = Some (set O1 cspaceid (capcspace
            ((CSpaceMod.set acspace dest
            (update_nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots
          (dest_slot_type, (Int.repr CAP_OBJECT_TYPE, (dest_cap_content, src_cap_right, object_t))), dest_childs, dest_prio)))))
          )
      end. 
      
       
Definition ucos_cnode_copy_object_notfound (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        exists dest src cap v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: v')  /\ 
        exists acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
        exists src_slot_type src_cap_type src_cap_content src_cap_right object_t,
          CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) /\ 
          CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) /\ 
          nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
            Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, object_t))) /\ 
            (~exists dest_idx dest_slot_type dest_cap_type dest_cap_content dest_cap_right,
            nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots =
              Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, object_t)))) /\ 
            (opv = Some (Vint32 (Int.repr CNODE_NONE_FAULT)) /\
            O2 = Some (set O1 cspaceid (capcspace
            ( (CSpaceMod.set acspace dest
            (dest_slots ++ ((src_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_cap_content, src_cap_right, object_t))) :: nil), dest_childs, dest_prio))
    ))))
end. 

(*the top spec of ucos copy*)
Definition ucos_cnode_copy_spec  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (exists O1', 
      ucos_cnode_copy_category vl O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1') \/
      ucos_cnode_copy_object_found vl O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1') \/
      ucos_cnode_copy_object_notfound vl O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1') /\
      opv = Some (Vint32 (Int.repr CNODE_NONE_FAULT)) /\ O2 = Some O1') \/
      ucos_cnode_copy_failure vl O1 (Some (Vint32 (Int.repr CNODE_COPY_FAILURE)), Some O1)
end. 
     


(* High-level specification of user_CNode_Copy.

  We make the specification in two stages: first assume both src and dest
  priorities are in valid range (and not OS_PRIO_SELF), then consider the
  general case.

  The arguments are: dest, src, capType, capability, O1, return value, O2.
  Here capability is input into Check_Cap_Type.

  There are the following cases:
  - input capType is not in valid range.
  - Check_Cap_Type returns invalid.
  - the current task does not have capability to perform function.
  - dest is not child of src in CapParent.
  - ucos_CNode_Copy is performed, and depending on capType, update
    the corresponding info arrays.
*)
Inductive user_cnode_copy_rel':
    int32 -> int32 -> int32 -> int32 -> osabst -> int32 -> osabst -> Prop :=
  user_cnode_copy_rel_capType:
  forall dest src capType capability O1,
    Int.lt (Int.repr CAP_TASK_TYPE) capType = true ->
    user_cnode_copy_rel' dest src capType capability O1
      (Int.repr EINVAL) O1
| user_cnode_copy_rel_check_cap_type:
  forall dest src capType capability O1,
    Int.lt (Int.repr CAP_TASK_TYPE) capType = false ->
    check_cap_type_rel capability capType src O1 (Int.repr SLOT_NUM) ->
    user_cnode_copy_rel' dest src capType capability O1
      (Int.repr EINVAL) O1
| user_cnode_copy_rel_no_cap:
  forall dest src capType capability O1,
  forall acspace t tls p st m sus curt_slots curt_childs curt_prio,
  forall curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t,
    get O1 cspaceid = Some (capcspace acspace) ->
    get O1 curtid = Some (oscurt t) ->
    get O1 abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, st, m, sus) ->
    CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_prio) ->
    nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
      Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) ->
    Int.eq (Int.and curt_cap_right (Int.repr CNODE_COPY_CAP)) Int.zero = true ->
    user_cnode_copy_rel' dest src capType capability O1
      (Int.repr USER_CAPABILITY_NONE) O1
| user_cnode_copy_rel_not_parent:
  forall dest src capType capability O1 acspace,
    get O1 cspaceid = Some (capcspace acspace) ->
    ~child_rel acspace dest src ->
    user_cnode_copy_rel' dest src capType capability O1
      (Int.repr USER_CAPABILITY_NONE) O1
| user_cnode_copy_rel_copy_sem:
  forall dest src capType capability O1 acspace O2 acspace2,
    get O1 cspaceid = Some (capcspace acspace) ->
    child_rel acspace dest src ->
    (* First step: call ucos_cnode_copy_rel *)
    check_cap_type_rel capability capType src O1 (Int.repr index) ->
    ucos_cnode_copy_rel dest src (Int.repr index) acspace
      (Int.repr CNODE_NONE_FAULT) acspace2 ->
    Int.eq capType (Int.repr CAP_SEM_TYPE) = true ->
    (* Second step: update Sem_info's sem_cap *)
    forall acspace semifo ptr bin sc idx,
      get O2 cspaceid = Some (capcspace acspace) ->
      get O2 seminfoid = Some (seminfo semifo) ->
      get semifo capability = Some (infotid ptr, bin, sc) ->
      get_obj_slot_rel dest ptr acspace (Int.repr idx) ->
      user_cnode_copy_rel' dest src capType capability O1
        (Int.repr CNODE_COPY_SUCCESS)
        (set (set O1 cspaceid (capcspace acspace2)) seminfoid (seminfo (EmbMod.set semifo capability
          (infotid ptr, bin,
           update_nth_list int32 (Z.to_nat (Int.signed (Int.sub dest Int.one)))
            sc (Int.repr idx)))))
| user_cnode_copy_rel_copy_mutex:
  forall dest src capType capability O1 acspace O2 acspace2,
    get O1 cspaceid = Some (capcspace acspace) ->
    child_rel acspace dest src ->
    (* First step: call ucos_cnode_copy_rel *)
    check_cap_type_rel capability capType src O1 (Int.repr index) ->
    ucos_cnode_copy_rel dest src (Int.repr index) acspace
      (Int.repr CNODE_NONE_FAULT) acspace2 ->
    Int.eq capType (Int.repr CAP_MUTEX_TYPE) = true ->
    (* Second step: update Pthread_Mutex's mutex_cap *)
    forall acspace mls ptr o x n pro pi w c mc idx,
      get O2 cspaceid = Some (capcspace acspace) ->
      get O2 absmutinfoid = Some (absmutinfo mls) ->
      get mls capability = Some (Valid_Addr ptr, o, x, n, pro, pi, w, c, mc) ->
      get_obj_slot_rel dest ptr acspace (Int.repr idx) ->
      user_cnode_copy_rel' dest src capType capability O1
        (Int.repr CNODE_COPY_SUCCESS)
        (set (set O1 cspaceid (capcspace acspace2)) absmutinfoid (absmutinfo (MibMod.set mls capability
          (Valid_Addr ptr, o, x, n, pro, pi, w, c,
           update_nth_list int32 (Z.to_nat (Int.signed (Int.sub dest Int.one)))
            mc (Int.repr idx)))))
| user_cnode_copy_rel_copy_q:
  forall dest src capType capability O1 acspace O2 acspace2,
    get O1 cspaceid = Some (capcspace acspace) ->
    child_rel acspace dest src ->
    (* First step: call ucos_cnode_copy_rel *)
    check_cap_type_rel capability capType src O1 (Int.repr index) ->
    ucos_cnode_copy_rel dest src (Int.repr index) acspace
      (Int.repr CNODE_NONE_FAULT) acspace2 ->
    Int.eq capType (Int.repr CAP_Q_TYPE) = true ->
    (* Second step: update Mq_attr's mq_cap *)
    forall acspace qtls ptr wtype flag maxm msize curm mqc idx,
      get O2 cspaceid = Some (capcspace acspace) ->
      get O2 absmqattrid = Some (absmqattr qtls) ->
      get qtls capability = Some (Valid_Addr ptr, wtype, flag, maxm, msize, curm, mqc) ->
      get_obj_slot_rel dest ptr acspace (Int.repr idx) ->
      user_cnode_copy_rel' dest src capType capability O1
        (Int.repr CNODE_COPY_SUCCESS)
        (set (set O1 cspaceid (capcspace acspace2)) absmqattrid (absmqattr (MqattrMod.set qtls capability
          (Valid_Addr ptr, wtype, flag, maxm, msize, curm,
           update_nth_list int32 (Z.to_nat (Int.signed (Int.sub dest Int.one)))
           mqc (Int.repr idx)))))
| user_cnode_copy_rel_copy_category:
  forall dest src capType capability O1 acspace acspace2,
    get O1 cspaceid = Some (capcspace acspace) ->
    child_rel acspace dest src ->
    (* Call ucos_cnode_copy_rel *)
    check_cap_type_rel capability capType src O1 (Int.repr index) ->
    ucos_cnode_copy_rel dest src (Int.repr index) acspace
      (Int.repr CNODE_NONE_FAULT) acspace2 ->
    Int.eq capType (Int.repr CAP_FUNCTION_TYPE) = true ->
    user_cnode_copy_rel' dest src capType capability O1
      (Int.repr CNODE_COPY_SUCCESS)
      (set O1 cspaceid (capcspace acspace2)).

(* In the second stage, we check for validity of dest and src,
   and replace OS_PRIO_SELF with the current priority.

  The arguments are: dest, src, capType, capability, O1, return value, O2.
  Here capability is input into Check_Cap_Type.

  There are the following cases:
  - src is invalid
  - dest is invalid
  - src is OS_PRIO_SELF
  - dest is OS_PRIO_SELF
  - both src and dest are in valid range
*)
Inductive user_cnode_copy_rel:
    int32 -> int32 -> int32 -> int32 -> osabst -> int32 -> osabst -> Prop :=
  user_cnode_copy_rel_src_invalid:
  forall dest src capType capability O1,
    Int.lt src (Int.repr OS_LOWEST_PRIO) = false ->
    Int.eq src (Int.repr OS_PRIO_SELF) = false ->
    user_cnode_copy_rel dest src capType capability O1
      (Int.repr OS_PRIO_INVALID) O1
| user_cnode_copy_rel_dest_invalid:
  forall dest src capType capability O1,
    Int.lt dest (Int.repr OS_LOWEST_PRIO) = false ->
    Int.eq dest (Int.repr OS_PRIO_SELF) = false ->
    user_cnode_copy_rel dest src capType capability O1
      (Int.repr OS_PRIO_INVALID) O1
| user_cnode_copy_rel_src_self:
  forall dest src capType capability O1,
    Int.lt dest (Int.repr OS_LOWEST_PRIO) = true ->
    Int.eq src (Int.repr OS_PRIO_SELF) = true ->
    forall t tls p st m sus rv O2,
      get O1 curtid = Some (oscurt t) ->
      get O1 abstcblsid = Some (abstcblist tls) ->
      get tls t = Some (p, st, m, sus) ->
      user_cnode_copy_rel' dest p capType capability O1 rv O2 ->
      user_cnode_copy_rel dest src capType capability O1 rv O2
| user_cnode_copy_rel_dest_self:
  forall dest src capType capability O1,
    Int.lt src (Int.repr OS_LOWEST_PRIO) = true ->
    Int.eq dest (Int.repr OS_PRIO_SELF) = true ->
    forall t tls p st m sus rv O2,
      get O1 curtid = Some (oscurt t) ->
      get O1 abstcblsid = Some (abstcblist tls) ->
      get tls t = Some (p, st, m, sus) ->
      user_cnode_copy_rel' p src capType capability O1 rv O2 ->
      user_cnode_copy_rel dest src capType capability O1 rv O2
| user_cnode_copy_rel_normal:
  forall dest src capType capability O1 rv O2,
    Int.lt dest (Int.repr OS_LOWEST_PRIO) = true ->
    Int.lt src (Int.repr OS_LOWEST_PRIO) = true ->
    user_cnode_copy_rel' dest src capType capability O1 rv O2 ->
    user_cnode_copy_rel dest src capType capability O1 rv O2.


Definition user_cnode_copy_invalid (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      opv = Some (Vint32 (Int.repr OS_PRIO_INVALID)) /\
      O2 = Some O1 /\
      (exists dest src captype capability v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 captype) :: (Vint32 capability) :: v') /\
        ((Int.ltu  (Int.repr OS_LOWEST_PRIO) dest = true \/ Int.eq dest (Int.repr OS_LOWEST_PRIO) = true) \/
         (Int.ltu  (Int.repr OS_LOWEST_PRIO) src = true \/ Int.eq src (Int.repr OS_LOWEST_PRIO) = true))
      )
end. 

Definition user_cnode_copy_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        O2 = Some O1 /\
        (exists dest src captype capability v',
          vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
          Int.ltu (Int.repr CAP_TASK_TYPE) captype = true
        )
  end. 

Definition user_cnode_copy_slotnum (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        O2 = Some O1 /\
        (exists dest src captype capability v',
          vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
          Int.ltu (Int.repr CAP_TASK_TYPE) captype = false 
        )
  end. 

Definition user_cnode_copy_failure (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr CNODE_COPY_FAILURE)) /\
        O2 = Some O1 
  end. 

(*Definition user_cnode_copy_nocap (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE)) /\
      O2 = Some O1 /\
      (exists dest src captype capability v',
        vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
       exists acspace t tls p st m sus curt_slots curt_childs curt_prio,
       exists curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t,
       exists  dest_slots dest_childs dest_parent,
        get O1 cspaceid = Some (capcspace acspace) /\
        get O1 curtid = Some (oscurt t) /\
        get O1 abstcblsid = Some (abstcblist tls) /\
        get tls t = Some (p, st, m, sus) /\
        CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_prio) /\
        nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
          Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) /\
        CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) /\
        (Int.eq (Int.and curt_cap_right (Int.repr CNODE_COPY_CAP)) Int.zero = true \/
         not (dest_parent = src))        )
end. *)

Definition user_cnode_copy_nocap (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
| (opv, O2) => 
  exists dest captype capability v',
      vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
      (opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE)) /\ O2 = Some O1)           
end.

Definition user_cnode_copy_sem (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      opv = Some (Vint32 (Int.repr CNODE_COPY_SUCCESS)) /\
      (exists dest src captype capability v',
        vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        exists index O1',
        check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\
        ucos_cnode_copy_spec vl O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1') /\
        Int.eq captype (Int.repr CAP_SEM_TYPE) = true /\
       exists acspace semifo ptr bin sc idx,
        get O1' cspaceid = Some (capcspace acspace) /\
        get O1' seminfoid = Some (seminfo semifo) /\
        get semifo capability = Some (infotid ptr, bin, sc) /\
        get_obj_slot_rel dest ptr acspace (Int.repr idx) /\
        O2 = Some (set O1' seminfoid (seminfo (EmbMod.set semifo capability
            (infotid ptr, bin,
            update_nth_list int32 (Z.to_nat (Int.signed (Int.sub dest Int.one)))
              sc (Int.repr idx)))))
      )
end. 


Definition user_cnode_copy_mutex (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      opv = Some (Vint32 (Int.repr CNODE_COPY_SUCCESS)) /\
      (exists dest src captype capability v',
        vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        exists index O1',
        check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\
        ucos_cnode_copy_spec vl O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1') /\
        Int.eq captype (Int.repr CAP_MUTEX_TYPE) = true /\
       exists acspace mls,
       exists ptr o x n pro pi w c mc idx,
       get O1' cspaceid = Some (capcspace acspace) /\
       get O1' absmutinfoid = Some (absmutinfo mls) /\
       get mls capability = Some (Valid_Addr ptr, o, x, n, pro, pi, w, c, mc) /\
       get_obj_slot_rel dest ptr acspace (Int.repr idx) /\
        O2 = Some (set O1' absmutinfoid (absmutinfo (MibMod.set mls capability
        (Valid_Addr ptr, o, x, n, pro, pi, w, c,
         update_nth_list int32 (Z.to_nat (Int.signed (Int.sub dest Int.one)))
          mc (Int.repr idx)))))
      )
end. 

Definition user_cnode_copy_q (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      opv = Some (Vint32 (Int.repr CNODE_COPY_SUCCESS)) /\
      (exists dest src captype capability v',
        vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        exists index O1',
        check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\
        ucos_cnode_copy_spec vl O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1') /\
        Int.eq captype (Int.repr CAP_Q_TYPE) = true /\
       exists acspace qtls,
       exists ptr wtype flag maxm msize curm mqc idx,
        get O1' cspaceid = Some (capcspace acspace) /\
        get O1' absmqattrid = Some (absmqattr qtls) /\
        get qtls capability = Some (Valid_Addr ptr, wtype, flag, maxm, msize, curm, mqc) /\
        get_obj_slot_rel dest ptr acspace (Int.repr idx)  /\
          O2 = Some (set O1' absmqattrid (absmqattr (MqattrMod.set qtls capability
          (Valid_Addr ptr, wtype, flag, maxm, msize, curm,
           update_nth_list int32 (Z.to_nat (Int.signed (Int.sub dest Int.one)))
           mqc (Int.repr idx)))))
        )
end. 

Definition user_cnode_copy_category (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      opv = Some (Vint32 (Int.repr CNODE_COPY_SUCCESS)) /\
      (exists dest src captype capability v',
        vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        exists index O1',
        check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\
        ucos_cnode_copy_spec vl O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1') /\
        Int.eq captype (Int.repr CAP_FUNCTION_TYPE) = true /\
        O2 = Some O1')
  end. 

(*Definition user_cnode_copy_succ_category (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      opv = Some (Vint32 (Int.repr CNODE_COPY_SUCCESS)) /\
      (exists dest src captype capability v',
        vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        exists acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
        exists src_slot_type src_cap_type src_cap_content src_cap_right src_object_t,
        exists dest_slot_type dest_cap_type dest_cap_content dest_cap_right dest_object_t index,
          CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) /\
          CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) /\
          nth_slots (Z.to_nat index) src_slots =
            Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, src_object_t))) /\
          nth_slots (Z.to_nat index) dest_slots =
            Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t))) /\
            (* (opv = Some (Vint32 (Int.repr CNODE_NONE_FAULT)) /\ *)
            ( exists cs cs' cs'',
              cs = CSpaceMod.set acspace dest
                  (update_nth_slots (Z.to_nat index) dest_slots
                    (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, src_cap_right, dest_object_t))), dest_childs, dest_prio) /\
              cs' = CSpaceMod.set cs src 
                  (update_nth_slots (Z.to_nat index) src_slots 
                    (src_slot_type, (Int.repr 0, (Int.repr 0, Int.repr 0, src_object_t))), src_childs, src_prio) /\
              cs'' = CSpaceMod.set cs' src 
                  (update_nth_slots (Z.to_nat index) (update_nth_slots (Z.to_nat index) src_slots 
                  (src_slot_type, (Int.repr 0, (Int.repr 0, Int.repr 0, src_object_t))))
                    ((Int.repr SLOT_NULL_CAP), (Int.repr 0, (Int.repr 0, Int.repr 0, src_object_t))), src_childs, src_prio) /\
              O2 = Some (set O1 cspaceid (capcspace cs''))))
  end. 

Definition user_cnode_copy_succ_object (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr CNODE_COPY_SUCCESS)) /\
        (exists dest src captype capability v',
          vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
          exists acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
          exists src_slot_type src_cap_type src_obj_right src_dummy src_object_t,
          exists dest_idx dest_slot_type dest_cap_type dest_obj_right dest_dummy index some_dummy,
            CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) /\ 
            CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) /\ 
            nth_slots (Z.to_nat index) src_slots =
              Some (src_slot_type, (src_cap_type, (src_obj_right, src_dummy, src_object_t))) /\ 
            nth_slots (Z.to_nat dest_idx) dest_slots =
              Some (dest_slot_type, (dest_cap_type, (dest_obj_right, dest_dummy, src_object_t))) /\ 
              ( exists cs cs' cs'',
                cs = CSpaceMod.set acspace dest
                    (update_nth_slots (Z.to_nat dest_idx) dest_slots
                      (dest_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, some_dummy, src_object_t))), dest_childs, dest_prio) /\
                cs' = CSpaceMod.set cs src 
                    (update_nth_slots (Z.to_nat index) src_slots 
                      (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) /\
                cs'' = CSpaceMod.set cs' src 
                    (update_nth_slots (Z.to_nat index) (update_nth_slots (Z.to_nat index) src_slots 
                    (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull))))
                      ((Int.repr SLOT_NULL_CAP), (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) /\
               O2 = Some (set O1 cspaceid (capcspace cs''))
              (* O2 = Some (set O1 cspaceid (capcspace
              ((CSpaceMod.set (CSpaceMod.set acspace dest
              (update_nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots
                (dest_slot_type, (Int.repr CAP_OBJECT_TYPE, (dest_obj_right, src_dummy, object_t))), dest_childs, dest_prio))
                src
                (update_nth_slots (Z.to_nat (Int.unsigned captype)) src_slots ((Int.repr SLOT_NULL_CAP),
                  (Int.repr 0, (src_cap_content, Int.repr 0, Vnull))), src_childs, src_prio))) *)
            (* /\
          Int.eq captype (Int.repr CAP_FUNCTION_TYPE) = true ) *) ))
    end. 
    

Definition user_cnode_copy_succ_objectnot (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr CNODE_COPY_SUCCESS)) /\
        (exists dest src captype capability v',
          vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
          exists acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
          exists src_slot_type src_cap_type object_t index ranindex src_obj_right src_dummy some_dummy some_slot_type,
          exists slots_vll11 slots_vll12 slots_vll21 endPtr,
            CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) /\ 
            CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) /\ 
            nth_slots (Z.to_nat index) src_slots =
              Some (src_slot_type, (src_cap_type, (src_obj_right, src_dummy, object_t))) /\ 
              ( dest_slots = (slots_vll11 ++ slots_vll12 ++ slots_vll21) /\
                length slots_vll11 = Z.to_nat(OBJ_POSITION) /\
                length (slots_vll11 ++ slots_vll12) = Z.to_nat(Int.unsigned endPtr) /\
                ~exists dest_idx dest_slot_type dest_cap_type dest_obj_right dest_dummy,
                    (0 <= dest_idx < Z.of_nat (length slots_vll12))%Z /\
                    nth_slots (Z.to_nat dest_idx) slots_vll12 =
                        Some (dest_slot_type, (dest_cap_type, (dest_obj_right, dest_dummy, object_t)))) /\ 
                ( exists cs cs' cs'',
                  cs = CSpaceMod.set acspace dest
                      (update_nth_slots (Z.to_nat ranindex) dest_slots
                      (some_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, some_dummy, object_t))), dest_childs, dest_prio) /\
                  cs' = CSpaceMod.set cs src
                      (update_nth_slots (Z.to_nat index) src_slots 
                      (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) /\
                  cs'' = CSpaceMod.set cs' src 
                      (update_nth_slots (Z.to_nat index) (update_nth_slots (Z.to_nat index) src_slots 
                      (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull))))
                        ((Int.repr SLOT_NULL_CAP), (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) /\
                  O2 = Some (set O1 cspaceid (capcspace cs''))
          ))
    end.    *)

Definition user_cnode_copy_succ_category (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      opv = Some (Vint32 (Int.repr CNODE_COPY_SUCCESS)) /\
      (exists dest src captype capability v',
        vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        exists acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
        exists src_slot_type src_cap_type src_cap_content src_cap_right src_object_t,
        exists dest_slot_type dest_cap_type dest_cap_content dest_cap_right dest_object_t index object_t,
          CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) /\
          CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) /\
          nth_slots (Z.to_nat index) src_slots =
            Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, src_object_t))) /\
          nth_slots (Z.to_nat index) dest_slots =
            Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t))) /\
            (* (opv = Some (Vint32 (Int.repr CNODE_NONE_FAULT)) /\ *)
            (*( exists cs cs' cs'',
              cs = CSpaceMod.set acspace dest
                  (update_nth_slots (Z.to_nat index) dest_slots
                    (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, src_cap_right, dest_object_t))), dest_childs, dest_prio) /\
              cs' = CSpaceMod.set cs src 
                  (update_nth_slots (Z.to_nat index) src_slots 
                    (src_slot_type, (Int.repr 0, (Int.repr 0, Int.repr 0, src_object_t))), src_childs, src_prio) /\
              cs'' = CSpaceMod.set cs' src 
                  (update_nth_slots (Z.to_nat index) (update_nth_slots (Z.to_nat index) src_slots 
                  (src_slot_type, (Int.repr 0, (Int.repr 0, Int.repr 0, src_object_t))))
                    ((Int.repr SLOT_NULL_CAP), (Int.repr 0, (Int.repr 0, Int.repr 0, src_object_t))), src_childs, src_prio) /\
              O2 = Some (set O1 cspaceid (capcspace cs''))) *)
              ( exists cs,
                cs = CSpaceMod.set acspace dest
                (update_nth_slots (Z.to_nat index) dest_slots
                  (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, src_cap_right, object_t))), dest_childs, dest_prio) /\
                O2 = Some (set O1 cspaceid (capcspace cs))
              )
            ) 
  end. 

Definition user_cnode_copy_succ_object (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr CNODE_COPY_SUCCESS)) /\
        (exists dest src captype capability v',
          vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
          exists acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
          exists src_slot_type src_cap_type src_obj_right src_dummy src_object_t dest_object_t,
          exists dest_idx dest_slot_type dest_cap_type dest_obj_right dest_dummy index some_dummy,
            CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) /\ 
            CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) /\ 
            nth_slots (Z.to_nat index) src_slots =
              Some (src_slot_type, (src_cap_type, (src_obj_right, src_dummy, src_object_t))) /\ 
            nth_slots (Z.to_nat dest_idx) dest_slots =
              Some (dest_slot_type, (dest_cap_type, (dest_obj_right, dest_dummy, dest_object_t))) /\ 
              (*( exists cs cs' cs'',
                cs = CSpaceMod.set acspace dest
                    (update_nth_slots (Z.to_nat dest_idx) dest_slots
                      (dest_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, some_dummy, src_object_t))), dest_childs, dest_prio) /\
                cs' = CSpaceMod.set cs src 
                    (update_nth_slots (Z.to_nat index) src_slots 
                      (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) /\
                cs'' = CSpaceMod.set cs' src 
                    (update_nth_slots (Z.to_nat index) (update_nth_slots (Z.to_nat index) src_slots 
                    (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull))))
                      ((Int.repr SLOT_NULL_CAP), (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) /\
               O2 = Some (set O1 cspaceid (capcspace cs'')) *)
              ( exists cs,
                cs = CSpaceMod.set acspace dest
                (update_nth_slots (Z.to_nat dest_idx) dest_slots
                  (dest_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, some_dummy, src_object_t))), dest_childs, dest_prio) /\
                O2 = Some (set O1 cspaceid (capcspace cs)
              )
              (* O2 = Some (set O1 cspaceid (capcspace
              ((CSpaceMod.set (CSpaceMod.set acspace dest
              (update_nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots
                (dest_slot_type, (Int.repr CAP_OBJECT_TYPE, (dest_obj_right, src_dummy, object_t))), dest_childs, dest_prio))
                src
                (update_nth_slots (Z.to_nat (Int.unsigned captype)) src_slots ((Int.repr SLOT_NULL_CAP),
                  (Int.repr 0, (src_cap_content, Int.repr 0, Vnull))), src_childs, src_prio))) *)
            (* /\
          Int.eq captype (Int.repr CAP_FUNCTION_TYPE) = true ) *) ))
    end. 
    

Definition user_cnode_copy_succ_objectnot (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr CNODE_COPY_SUCCESS)) /\
        (exists dest src captype capability v',
          vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
          exists acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
          exists src_slot_type src_cap_type object_t index ranindex src_obj_right src_dummy some_dummy some_slot_type,
          exists slots_vll11 slots_vll12 slots_vll21 endPtr,
            CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) /\ 
            CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) /\ 
            nth_slots (Z.to_nat index) src_slots =
              Some (src_slot_type, (src_cap_type, (src_obj_right, src_dummy, object_t))) /\ 
              ( dest_slots = (slots_vll11 ++ slots_vll12 ++ slots_vll21) /\
                length slots_vll11 = Z.to_nat(OBJ_POSITION) /\
                length (slots_vll11 ++ slots_vll12) = Z.to_nat(Int.unsigned endPtr) /\
                ~exists dest_idx dest_slot_type dest_cap_type dest_obj_right dest_dummy,
                    (0 <= dest_idx < Z.of_nat (length slots_vll12))%Z /\
                    nth_slots (Z.to_nat dest_idx) slots_vll12 =
                        Some (dest_slot_type, (dest_cap_type, (dest_obj_right, dest_dummy, object_t)))) /\ 
                (*( exists cs cs' cs'',
                  cs = CSpaceMod.set acspace dest
                      (update_nth_slots (Z.to_nat ranindex) dest_slots
                      (some_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, some_dummy, object_t))), dest_childs, dest_prio) /\
                  cs' = CSpaceMod.set cs src
                      (update_nth_slots (Z.to_nat index) src_slots 
                      (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) /\
                  cs'' = CSpaceMod.set cs' src 
                      (update_nth_slots (Z.to_nat index) (update_nth_slots (Z.to_nat index) src_slots 
                      (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull))))
                        ((Int.repr SLOT_NULL_CAP), (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) /\
                  O2 = Some (set O1 cspaceid (capcspace cs''))*)
                ( exists cs,
                  cs = CSpaceMod.set acspace dest
                  (update_nth_slots (Z.to_nat ranindex) dest_slots
                    (some_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, some_dummy, object_t))), dest_childs, dest_prio) /\
                  O2 = Some (set O1 cspaceid (capcspace cs)
                )
          ))
    end.    

Definition user_cnode_copy_code (vl: vallist) :=
  user_cnode_copy_invalid (|vl|) ??
  user_cnode_copy_err (|vl|)??
  user_cnode_copy_slotnum (|vl|)??
  user_cnode_copy_failure (|vl|)??
  user_cnode_copy_nocap (|vl|)??
  user_cnode_copy_category (|vl|)??
  user_cnode_copy_sem (|vl|)??
  user_cnode_copy_mutex (|vl|)??
  user_cnode_copy_q (|vl|)??
  user_cnode_copy_succ_category(|vl|)??
  user_cnode_copy_succ_object(|vl|)??
  user_cnode_copy_succ_objectnot(|vl|).

 
 
(*grant*)
Fixpoint Child_In_PrioChildList (x: int) (lv: list int) : Prop :=
  match lv with
    | nil => False
    | a::lv' => if Int.eq x a then True else (Child_In_PrioChildList x lv')
  end.


Definition grant_cspace_cap_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
       opv = Some (Vint32 (Int.repr OS_PRIO_INVALID)) /\
       O2 = Some O1 /\
       (exists dest class rights v',
         vl = ((Vint32 dest) :: (Vint32 class) :: (Vint32 rights) :: v') /\
         ((Int.ltu (Int.repr OS_LOWEST_PRIO) dest  = true \/ Int.eq dest (Int.repr OS_LOWEST_PRIO) = true) 
         ))
  end.
Open Scope int_scope.
  Definition grant_cspace_cap_succ_nonfault (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
    match rst with
      | (opv, O2) => 
         (exists dest class rights v',
           vl = ((Vint32 dest) :: (Vint32 class) :: (Vint32 rights) :: v') /\
           ((Int.ltu dest (Int.repr OS_LOWEST_PRIO) = true)) /\
            (exists tls p ready msg t sus,
             get O1 curtid = Some (oscurt t) /\ 
             get O1 abtcblsid = Some (abstcblist tls) /\  
             get tls t = Some (p,ready,msg,sus) /\
               (exists acspace cur_slots cur_childs cur_parent
                 cur_slot_type cur_cap_type cur_cap_content cur_cap_right cur_object_t,
                 get O1 cspaceid = Some (capcspace acspace) /\
                 CSpaceMod.get acspace p = Some (cur_slots, cur_childs, cur_parent) /\
                 nth_slots (Z.to_nat (Int.unsigned (Int.repr SLOT_CNODE_CAP))) cur_slots =
                   Some (cur_slot_type, (cur_cap_type, (cur_cap_content, cur_cap_right, cur_object_t))) /\
                   exists  dest_slots dest_childs dest_parent
                   dest_slot_type dest_cap_type dest_cap_content dest_cap_right dest_object_t,
                   CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) /\
                   nth_slots (Z.to_nat (Int.unsigned class)) dest_slots =
                     Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t))) /\
                   ((Int.eq (Int.and cur_cap_right ((Int.repr CNODE_GRANT_CAP))) (Int.repr 0) = false /\ 
                  Int.eq p dest_parent = true /\ 
                   opv = Some (Vint32 (Int.repr CSPACE_NONE_FAULT)) /\
                   O2 = Some (set O1 cspaceid (capcspace (CSpaceMod.set acspace dest
                     (update_nth_slots (Z.to_nat (Int.unsigned class)) dest_slots
                       (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (class, Int.or (Int.and dest_cap_right ($4095)) rights, dest_object_t))),
                        dest_childs, dest_parent)))) )) 
                 )
                )
            )
    end.  

Definition grant_cspace_cap_succ_fault (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        O2 = Some O1 /\ opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE))
  end.  
  
Definition grant_cspace_cap_curpspace_null (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        (O2 = Some O1 /\ opv = Some (Vint32 (Int.repr CNODE_GRANT_FAILURE))) 
          
  end. 

Definition grant_cspace_cap_succ_fail (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
    O2 = Some O1 /\ opv = Some (Vint32 (Int.repr CNODE_GRANT_FAILURE))
  end.  

Definition grant_cspace_cap_spec (vl: vallist) :=
  grant_cspace_cap_err (|vl|) ??
  grant_cspace_cap_curpspace_null (|vl|)??
  grant_cspace_cap_succ_fail (|vl|)??
  grant_cspace_cap_succ_nonfault (|vl|)??
  grant_cspace_cap_succ_fault (|vl|).

Definition grant_cspace_cap_api :=
  (grant_cspace_cap_spec, (Tint8, Tint8 :: Tint32 :: Tint32 :: nil)).



(* CNode Mint *)

Definition user_cnode_mint_invalid_with_self (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
       opv = Some (Vint32 (Int.repr OS_PRIO_INVALID)) /\
       O2 = Some O1 /\
       (exists dest src cap rights v,
         vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: (Vint32 rights) :: v) /\
         ((((Int.ltu (Int.repr OS_LOWEST_PRIO) src = true) \/ (Int.eq src (Int.repr OS_LOWEST_PRIO) = true)) /\ (Int.eq src (Int.repr OS_PRIO_SELF) = false)) \/
          (((Int.ltu (Int.repr OS_LOWEST_PRIO) dest = true) \/ (Int.eq dest (Int.repr OS_LOWEST_PRIO) = true)) /\ (Int.eq dest (Int.repr OS_PRIO_SELF) = false))))
  end. 

(* w/o OS_PRIO_SELF *)
Definition user_cnode_mint_invalid (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
     opv = Some (Vint32 (Int.repr OS_PRIO_INVALID)) /\
     O2 = Some O1 /\
     (exists dest src cap rights v,
       vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: (Vint32 rights) :: v) /\
       ((((Int.ltu (Int.repr OS_LOWEST_PRIO) src = true) \/ (Int.eq src (Int.repr OS_LOWEST_PRIO) = true))) \/
        (((Int.ltu (Int.repr OS_LOWEST_PRIO) dest = true) \/ (Int.eq dest (Int.repr OS_LOWEST_PRIO) = true)))))
end. 

Definition user_cnode_mint_null_cspace (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      (O2 = Some O1 /\ opv = Some (Vint32 (Int.repr CNODE_MINT_FAILURE)))         
end. 

Definition user_cnode_mint_non_cap (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      (O2 = Some O1 /\ opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE)))
end. 

Definition user_cnode_mint_fail (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      (O2 = Some O1 /\ opv = Some (Vint32 (Int.repr CNODE_MINT_FAILURE)))         
end. 
Definition user_cnode_mint_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
       opv = Some (Vint32 (Int.repr CNODE_MINT_SUCCESS)) /\ 
       (exists dest src cap rights v,
         vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: (Vint32 rights) :: v) /\
         (exists cs, get O1 cspaceid = Some (capcspace cs) /\ 
          exists src_slots src_childs src_parent src_slot_type src_cap_type src_cap_content src_cap_right src_object_t,
            CSpaceMod.get cs src = Some (src_slots, src_childs, src_parent) /\
            nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
              Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, src_object_t))) /\
          exists dest_slots dest_childs dest_parent dest_slot_type dest_cap_type dest_cap_content dest_cap_right dest_object_t,
            CSpaceMod.get cs dest = Some (dest_slots, dest_childs, dest_parent) /\
            nth_slots (Z.to_nat (Int.unsigned cap)) dest_slots =
              Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t))) /\
           Int.eq src_cap_type (Int.repr CAP_CATEGORY_TYPE) = true /\
           Int.eq (Int.and (Int.not src_cap_right) rights) (Int.repr (Z.of_nat 0)) = true /\
           Int.eq rights src_cap_right = false /\
          exists cs', cs' = (CSpaceMod.set cs dest
            (update_nth_slots (Z.to_nat (Int.unsigned cap)) dest_slots
              (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, rights, dest_object_t))), dest_childs, dest_parent)) /\
           O2 = Some (set O1 cspaceid (capcspace cs'))
         )
       )
  end.

Definition user_cnode_mint_code (vl: vallist) :=
  user_cnode_mint_invalid (|vl|) ??
  user_cnode_mint_null_cspace (|vl|) ??
  user_cnode_mint_non_cap (|vl|) ??
  user_cnode_mint_succ (|vl|) ??
  user_cnode_mint_fail (|vl|).

Definition user_cnode_mint_api :=
  (user_cnode_mint_code, (Tint8, Tint32 :: Tint32 :: Tint32 :: Tint32 :: nil)).

(* CNode Move *)

(* High-level specification of ucos_CNode_Move.

  The arguments are: dest, src, capability, O1, return value, O2.
  Here capability is index into slots array in src.

  There are three cases:
  - if capability is category type (less than OBJ_POSITION), just move
    to the same position.
  
  - if capability is object type, and the object is found in dest,
    move to the corresponding location in dest.

  - if capability is object type, and the object is not found in dest,
    append to the end of slots in dest.
*)
Inductive ucos_cnode_move_rel:
    int32 -> int32 -> int32 -> CSpaceMod.map -> int32 -> CSpaceMod.map -> Prop :=
  ucos_cnode_move_rel_category:
  forall dest src cap,
  forall acspace src_slots src_childs src_parent dest_slots dest_childs dest_parent,
  forall src_slot_type src_cap_type src_cap_content src_cap_right src_object_t,
  forall dest_slot_type dest_cap_type dest_cap_content dest_cap_right dest_object_t,
    CSpaceMod.get acspace src = Some (src_slots, src_childs, src_parent) ->
    CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
      Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, src_object_t))) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) dest_slots =
      Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t))) ->
    Int.eq src_cap_type (Int.repr CAP_CATEGORY_TYPE) = true ->
    ucos_cnode_move_rel dest src cap acspace
      (Int.repr CNODE_NONE_FAULT)
      (CSpaceMod.set (CSpaceMod.set acspace dest
        (update_nth_slots (Z.to_nat (Int.unsigned cap)) dest_slots
          (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, src_cap_right, dest_object_t))), dest_childs, dest_parent))
           src 
           (update_nth_slots (Z.to_nat (Int.unsigned cap)) src_slots ((Int.repr SLOT_NULL_CAP),
            (Int.repr 0, (Int.repr 0, Int.repr 0, src_object_t))), src_childs, src_parent))
| ucos_cnode_move_rel_object_found:
  forall dest src cap,
  forall acspace src_slots src_childs src_parent dest_slots dest_childs dest_parent,
  forall src_slot_type src_cap_type src_cap_content src_cap_right object_t,
  forall dest_idx dest_slot_type dest_cap_type dest_cap_content dest_cap_right,
    CSpaceMod.get acspace src = Some (src_slots, src_childs, src_parent) ->
    CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
      Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, object_t))) ->
    nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots =
      Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, object_t))) ->
    Int.eq src_cap_type (Int.repr CAP_OBJECT_TYPE) = true ->
    ucos_cnode_move_rel dest src cap acspace
      (Int.repr CNODE_NONE_FAULT)
      (CSpaceMod.set (CSpaceMod.set acspace dest
        (update_nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots
          (dest_slot_type, (Int.repr CAP_OBJECT_TYPE, (dest_cap_content, src_cap_right, object_t))), dest_childs, dest_parent))
          src
          (update_nth_slots (Z.to_nat (Int.unsigned cap)) src_slots ((Int.repr SLOT_NULL_CAP),
            (Int.repr 0, (src_cap_content, Int.repr 0, Vnull))), src_childs, src_parent))
| ucos_cnode_move_rel_object_not_found:
  forall dest src cap,
  forall acspace src_slots src_childs dest_slots dest_childs src_parent dest_parent,
  forall src_slot_type src_cap_type src_cap_content src_cap_right object_t,
    CSpaceMod.get acspace src = Some (src_slots, src_childs, src_parent) ->
    CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
      Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, object_t))) ->
    (~exists dest_idx dest_slot_type dest_cap_type dest_cap_content dest_cap_right,
      nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots =
        Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, object_t)))) ->
    Int.eq src_cap_type (Int.repr CAP_OBJECT_TYPE) = true ->
    ucos_cnode_move_rel dest src cap acspace
      (Int.repr CNODE_NONE_FAULT)
      (CSpaceMod.set (CSpaceMod.set acspace dest
        (dest_slots ++ ((src_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_cap_content, src_cap_right, object_t))) :: nil), dest_childs, dest_parent))
        src
        (update_nth_slots (Z.to_nat (Int.unsigned cap)) src_slots ((Int.repr SLOT_NULL_CAP),
          (Int.repr 0, (src_cap_content, Int.repr 0, Vnull))), src_childs, src_parent))
   | ucos_cnode_move_rel_not_object_and_category:
   forall dest src cap,
   forall acspace src_slots src_childs  src_parent,
  forall src_slot_type src_cap_type src_cap_content src_cap_right object_t,
    CSpaceMod.get acspace src = Some (src_slots, src_childs, src_parent) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
      Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, object_t))) ->
    Int.eq src_cap_type (Int.repr CAP_OBJECT_TYPE) = false ->
    Int.eq src_cap_type (Int.repr CAP_CATEGORY_TYPE) = false ->
    ucos_cnode_move_rel dest src cap acspace
      (Int.repr CNODE_MOVE_FAILURE) acspace.


Definition ucos_cnode_move_failure (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr CNODE_MOVE_FAILURE)) /\
        O2 = Some O1
  end. 

Definition ucos_cnode_move_category (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        exists dest src cap v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: v')  /\ 
  exists acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
  exists src_slot_type src_cap_type src_cap_content src_cap_right src_object_t,
  exists dest_slot_type dest_cap_type dest_cap_content dest_cap_right dest_object_t,
    CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) /\
    CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) /\
    nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
      Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, src_object_t))) /\
    nth_slots (Z.to_nat (Int.unsigned cap)) dest_slots =
      Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t))) /\
      (opv = Some (Vint32 (Int.repr CNODE_NONE_FAULT)) /\
        O2 = Some (set O1 cspaceid (capcspace
        ((CSpaceMod.set (CSpaceMod.set acspace dest
        (update_nth_slots (Z.to_nat (Int.unsigned cap)) dest_slots
          (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, src_cap_right, dest_object_t))), dest_childs, dest_prio))
           src 
           (update_nth_slots (Z.to_nat (Int.unsigned cap)) src_slots ((Int.repr SLOT_NULL_CAP),
            (Int.repr 0, (Int.repr 0, Int.repr 0, src_object_t))), src_childs, src_prio)))))
      )
  end. 

Definition ucos_cnode_move_object_found (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        exists dest src cap v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: v')  /\ 
        exists acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
        exists src_slot_type src_cap_type src_obj_right src_dummy src_object_t dummy_d1 dummy_d2,
        exists dest_idx dest_slot_type dest_cap_type dest_obj_right ,
          CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) /\ 
          CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) /\ 
          nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
            Some (src_slot_type, (src_cap_type, (src_obj_right, src_dummy, src_object_t))) /\ 
          nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots =
            Some (dest_slot_type, (dest_cap_type, (dest_obj_right, dummy_d1, src_object_t))) /\ 
            (opv = Some (Vint32 (Int.repr CNODE_NONE_FAULT)) /\
            O2 = Some (set O1 cspaceid (capcspace
            ((CSpaceMod.set (CSpaceMod.set acspace dest
            (update_nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots
              (dest_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, dummy_d2, src_object_t))), dest_childs, dest_prio))
              src
              (update_nth_slots (Z.to_nat (Int.unsigned cap)) src_slots ((Int.repr SLOT_NULL_CAP),
                (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio)))))
          )
      end. 
      
       
Definition ucos_cnode_move_object_notfound (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        exists dest src cap v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 cap) :: v')  /\ 
        exists acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
        exists src_slot_type src_cap_type src_obj_right src_dummy object_t index ,
          CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) /\ 
          CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) /\ 
          nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
            Some (src_slot_type, (src_cap_type, (src_obj_right, src_dummy, object_t))) /\ 
            (~exists dest_idx dest_slot_type dest_cap_type dest_obj_right dest_dummy,
            nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots =
              Some (dest_slot_type, (dest_cap_type, (dest_obj_right, dest_dummy, object_t)))) /\ 
            (opv = Some (Vint32 (Int.repr CNODE_NONE_FAULT)) /\
            O2 = Some (set O1 cspaceid (capcspace
            ( (CSpaceMod.set (CSpaceMod.set acspace dest
            (update_nth_slots (Z.to_nat (Int.unsigned index)) dest_slots 
            (src_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, src_dummy, object_t))), dest_childs, dest_prio))
            (* (dest_slots ++ ((src_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, src_dummy, object_t))) :: nil), dest_childs, dest_prio)) *)
            src
            (update_nth_slots (Z.to_nat (Int.unsigned cap)) src_slots ((Int.repr SLOT_NULL_CAP),
              (Int.repr 0, (src_obj_right, Int.repr 0, Vnull))), src_childs, src_prio)))
    )))
end.

(*the top spec of ucos copy*)
Definition ucos_cnode_move_spec  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (exists O1', 
      ucos_cnode_move_category vl O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1') \/
      ucos_cnode_move_object_found vl O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1') \/
      ucos_cnode_move_object_notfound vl O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1') /\
      opv = Some (Vint32 (Int.repr CNODE_NONE_FAULT)) /\ O2 = Some O1') \/
      ucos_cnode_move_failure vl O1 (Some (Vint32 (Int.repr CNODE_COPY_FAILURE)), Some O1)
end. 


(* High-level specification of user_CNode_Move.

  We make the specification in two stages: first assume both src and dest
  priorities are in valid range (and not OS_PRIO_SELF), then consider the
  general case.

  The arguments are: dest, src, capType, capability, O1, return value, O2.
  Here capability is input into Check_Cap_Type.

  There are the following cases:
  - input capType is not in valid range.
  - Check_Cap_Type returns invalid.
  - the current task does not have capability to perform function.
  - dest is not child of src in CapParent.
  - ucos_CNode_Move is performed, and depending on capType, update
    the corresponding info arrays.
*)
Inductive user_cnode_move_rel':
    int32 -> int32 -> int32 -> int32 -> osabst -> int32 -> osabst -> Prop :=
  user_cnode_move_rel_capType:
  forall dest src capType capability O1,
    Int.ltu (Int.repr CAP_TASK_TYPE) capType = true ->
    user_cnode_move_rel' dest src capType capability O1
      (Int.repr EINVAL) O1
| user_cnode_move_rel_check_cap_type:
  forall dest src capType capability O1,
    Int.ltu (Int.repr CAP_TASK_TYPE) capType = false ->
    check_cap_type_rel capability capType src O1 (Int.repr SLOT_NUM) ->
    user_cnode_move_rel' dest src capType capability O1
      (Int.repr EINVAL) O1
| user_cnode_move_rel_no_cap:
  forall dest src capType capability O1,
  forall acspace t tls p st m sus curt_slots curt_childs curt_parent,
  forall curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t,
    get O1 cspaceid = Some (capcspace acspace) ->
    get O1 curtid = Some (oscurt t) ->
    get O1 abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, st, m, sus) ->
    CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) ->
    nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
      Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) ->
    Int.eq (Int.and curt_cap_right (Int.repr CNODE_MOVE_CAP)) Int.zero = true ->
    user_cnode_move_rel' dest src capType capability O1
      (Int.repr USER_CAPABILITY_NONE) O1
| user_cnode_move_rel_not_parent:
  forall dest src capType capability O1 acspace,
    get O1 cspaceid = Some (capcspace acspace) ->
    ~child_rel acspace dest src ->
    user_cnode_move_rel' dest src capType capability O1
      (Int.repr USER_CAPABILITY_NONE) O1
| user_cnode_move_rel_move_sem:
  forall dest src capType capability O1 acspace O2 acspace2,
    get O1 cspaceid = Some (capcspace acspace) ->
    child_rel acspace dest src ->
    (*added by wsl*)
    forall t tls p st m sus curt_slots curt_childs curt_parent,
    forall curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t,
    get O1 curtid = Some (oscurt t) ->
    get O1 abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, st, m, sus) ->
    CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) ->
    nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
      Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) ->
    Int.eq (Int.and curt_cap_right (Int.repr CNODE_MOVE_CAP)) Int.zero = false ->
     (* First step: call ucos_cnode_move_rel *)
    check_cap_type_rel capability capType src O1 (Int.repr index) ->
    ucos_cnode_move_rel dest src (Int.repr index) acspace
      (Int.repr CNODE_NONE_FAULT) acspace2 ->
    Int.eq capType (Int.repr CAP_SEM_TYPE) = true ->
    (* Second step: update Sem_info's sem_cap *)
    forall acspace semifo ptr bin sc idx,
      get O2 cspaceid = Some (capcspace acspace) ->
      get O2 seminfoid = Some (seminfo semifo) ->
      get semifo capability = Some (infotid ptr, bin, sc) ->
      get_obj_slot_rel dest ptr acspace (Int.repr idx) ->
      user_cnode_move_rel' dest src capType capability O1
        (Int.repr CNODE_MOVE_SUCCESS)
        (set (set O1 cspaceid (capcspace acspace2)) seminfoid (seminfo (EmbMod.set semifo capability
          (infotid ptr, bin,
           update_nth_list int32 (Z.to_nat (Int.signed (Int.sub dest Int.one)))
            sc (Int.repr idx)))))
| user_cnode_move_rel_move_mutex:
  forall dest src capType capability O1 acspace O2 acspace2,
    get O1 cspaceid = Some (capcspace acspace) ->
    child_rel acspace dest src ->
    (*added by wsl*)
    forall t tls p st m sus curt_slots curt_childs curt_parent,
    forall curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t,
    get O1 curtid = Some (oscurt t) ->
    get O1 abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, st, m, sus) ->
    CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) ->
    nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
      Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) ->
    Int.eq (Int.and curt_cap_right (Int.repr CNODE_MOVE_CAP)) Int.zero = false ->
    (* First step: call ucos_cnode_move_rel *)
    check_cap_type_rel capability capType src O1 (Int.repr index) ->
    ucos_cnode_move_rel dest src (Int.repr index) acspace
      (Int.repr CNODE_NONE_FAULT) acspace2 ->
    Int.eq capType (Int.repr CAP_MUTEX_TYPE) = true ->
    (* Second step: update Pthread_Mutex's mutex_cap *)
    forall acspace mls ptr o x n pro pi w c mc idx,
      get O2 cspaceid = Some (capcspace acspace) ->
      get O2 absmutinfoid = Some (absmutinfo mls) ->
      get mls capability = Some (Valid_Addr ptr, o, x, n, pro, pi, w, c, mc) ->
      get_obj_slot_rel dest ptr acspace (Int.repr idx) ->
      user_cnode_move_rel' dest src capType capability O1
        (Int.repr CNODE_MOVE_SUCCESS)
        (set (set O1 cspaceid (capcspace acspace2)) absmutinfoid (absmutinfo (MibMod.set mls capability
          (Valid_Addr ptr, o, x, n, pro, pi, w, c,
           update_nth_list int32 (Z.to_nat (Int.signed (Int.sub dest Int.one)))
            mc (Int.repr idx)))))
| user_cnode_move_rel_move_q:
  forall dest src capType capability O1 acspace O2 acspace2,
    get O1 cspaceid = Some (capcspace acspace) ->
    child_rel acspace dest src ->
    (*added by wsl*)
    forall t tls p st m sus curt_slots curt_childs curt_parent,
    forall curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t,
    get O1 curtid = Some (oscurt t) ->
    get O1 abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, st, m, sus) ->
    CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) ->
    nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
      Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) ->
    Int.eq (Int.and curt_cap_right (Int.repr CNODE_MOVE_CAP)) Int.zero = false ->
    (* First step: call ucos_cnode_move_rel *)
    check_cap_type_rel capability capType src O1 (Int.repr index) ->
    ucos_cnode_move_rel dest src (Int.repr index) acspace
      (Int.repr CNODE_NONE_FAULT) acspace2 ->
    Int.eq capType (Int.repr CAP_Q_TYPE) = true ->
    (* Second step: update Mq_attr's mq_cap *)
    forall acspace qtls ptr wtype flag maxm msize curm mqc idx,
      get O2 cspaceid = Some (capcspace acspace) ->
      get O2 absmqattrid = Some (absmqattr qtls) ->
      get qtls capability = Some (Valid_Addr ptr, wtype, flag, maxm, msize, curm, mqc) ->
      get_obj_slot_rel dest ptr acspace (Int.repr idx) ->
      user_cnode_move_rel' dest src capType capability O1
        (Int.repr CNODE_MOVE_SUCCESS)
        (set (set O1 cspaceid (capcspace acspace2)) absmqattrid (absmqattr (MqattrMod.set qtls capability
          (Valid_Addr ptr, wtype, flag, maxm, msize, curm,
           update_nth_list int32 (Z.to_nat (Int.signed (Int.sub dest Int.one)))
           mqc (Int.repr idx)))))
| user_cnode_move_rel_move_category:
  forall dest src capType capability O1 acspace acspace2,
    get O1 cspaceid = Some (capcspace acspace) ->
    child_rel acspace dest src ->
    (*added by wsl*)
    forall t tls p st m sus curt_slots curt_childs curt_parent,
    forall curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t,
    get O1 curtid = Some (oscurt t) ->
    get O1 abstcblsid = Some (abstcblist tls) ->
    get tls t = Some (p, st, m, sus) ->
    CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) ->
    nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
      Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) ->
    Int.eq (Int.and curt_cap_right (Int.repr CNODE_MOVE_CAP)) Int.zero = false ->
    (* Call ucos_cnode_move_rel *)
    check_cap_type_rel capability capType src O1 (Int.repr index) ->
    ucos_cnode_move_rel dest src (Int.repr index) acspace
      (Int.repr CNODE_NONE_FAULT) acspace2 ->
    Int.eq capType (Int.repr CAP_FUNCTION_TYPE) = true ->
    user_cnode_move_rel' dest src capType capability O1
      (Int.repr CNODE_MOVE_SUCCESS)
      (set O1 cspaceid (capcspace acspace2)).
(*do not consider the case for failure*)

(* In the second stage, we check for validity of dest and src,
   and replace OS_PRIO_SELF with the current priority.

  The arguments are: dest, src, capType, capability, O1, return value, O2.
  Here capability is input into Check_Cap_Type.

  There are the following cases:
  - src is invalid
  - dest is invalid
  - src is OS_PRIO_SELF
  - dest is OS_PRIO_SELF
  - both src and dest are in valid range
*)
Inductive user_cnode_move_rel:
    int32 -> int32 -> int32 -> int32 -> osabst -> int32 -> osabst -> Prop :=
  user_cnode_move_rel_src_invalid:
  forall dest src capType capability O1,
    Int.ltu src (Int.repr OS_LOWEST_PRIO) = false ->
    Int.eq src (Int.repr OS_PRIO_SELF) = false ->
    user_cnode_move_rel dest src capType capability O1
      (Int.repr OS_PRIO_INVALID) O1
| user_cnode_move_rel_dest_invalid:
  forall dest src capType capability O1,
    Int.lt dest (Int.repr OS_LOWEST_PRIO) = false ->
    Int.eq dest (Int.repr OS_PRIO_SELF) = false ->
    user_cnode_move_rel dest src capType capability O1
      (Int.repr OS_PRIO_INVALID) O1
| user_cnode_move_rel_src_self:
  forall dest src capType capability O1,
    Int.lt dest (Int.repr OS_LOWEST_PRIO) = true ->
    Int.eq src (Int.repr OS_PRIO_SELF) = true ->
    forall t tls p st m sus rv O2,
      get O1 curtid = Some (oscurt t) ->
      get O1 abstcblsid = Some (abstcblist tls) ->
      get tls t = Some (p, st, m, sus) ->
      user_cnode_move_rel' dest p capType capability O1 rv O2 ->
      user_cnode_move_rel dest src capType capability O1 rv O2
| user_cnode_move_rel_dest_self:
  forall dest src capType capability O1,
    Int.lt src (Int.repr OS_LOWEST_PRIO) = true ->
    Int.eq dest (Int.repr OS_PRIO_SELF) = true ->
    forall t tls p st m sus rv O2,
      get O1 curtid = Some (oscurt t) ->
      get O1 abstcblsid = Some (abstcblist tls) ->
      get tls t = Some (p, st, m, sus) ->
      user_cnode_move_rel' p src capType capability O1 rv O2 ->
      user_cnode_move_rel dest src capType capability O1 rv O2
| user_cnode_move_rel_normal:
  forall dest src capType capability O1 rv O2,
    Int.lt dest (Int.repr OS_LOWEST_PRIO) = true ->
    Int.lt src (Int.repr OS_LOWEST_PRIO) = true ->
    user_cnode_move_rel' dest src capType capability O1 rv O2 ->
    user_cnode_move_rel dest src capType capability O1 rv O2.
(*do not consider the case that dest=src=self*)

Definition user_cnode_move_invalid (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      opv = Some (Vint32 (Int.repr OS_PRIO_INVALID)) /\
      O2 = Some O1 /\
      (exists dest src captype capability v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 captype) :: (Vint32 capability) :: v') /\
        ((Int.ltu  (Int.repr OS_LOWEST_PRIO) dest = true \/ Int.eq dest (Int.repr OS_LOWEST_PRIO) = true) \/
         (Int.ltu  (Int.repr OS_LOWEST_PRIO) src = true \/ Int.eq src (Int.repr OS_LOWEST_PRIO) = true))
      )
end. 

Definition user_cnode_move_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        O2 = Some O1 /\
        (exists dest src captype capability v',
          vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
          Int.ltu (Int.repr CAP_TASK_TYPE) captype = true
        )
  end. 

Definition user_cnode_move_slotnum (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        O2 = Some O1 /\
        (exists dest src captype capability v',
          vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
          Int.ltu (Int.repr CAP_TASK_TYPE) captype = false 
        )
  end. 

Definition user_cnode_move_failure (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr CNODE_MOVE_FAILURE)) /\
        O2 = Some O1 
  end. 

(* Definition user_cnode_move_nocap (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE)) /\
      O2 = Some O1 /\
      (exists dest src captype capability v',
        vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
       exists acspace t tls p st m sus curt_slots curt_childs curt_prio,
       exists curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t,
       exists  dest_slots dest_childs dest_parent,
        get O1 cspaceid = Some (capcspace acspace) /\
        get O1 curtid = Some (oscurt t) /\
        get O1 abstcblsid = Some (abstcblist tls) /\
        get tls t = Some (p, st, m, sus) /\
        CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_prio) /\
        nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
          Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) /\
        CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) /\
        (Int.eq (Int.and curt_cap_right (Int.repr CNODE_MOVE_CAP)) Int.zero = true \/
         not (dest_parent = src))        )
end.  *)

Definition user_cnode_move_nocap (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
| (opv, O2) => 
  exists dest captype capability v',
      vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
      (opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE)) /\ O2 = Some O1)           
end.

Definition user_cnode_move_sem (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      opv = Some (Vint32 (Int.repr CNODE_MOVE_SUCCESS)) /\
      (exists dest src captype capability v',
        vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        exists index O1',
        (* check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\ *)
        ucos_cnode_move_spec ((Vint32 dest) :: (Vint32 src) ::  (Vint32 index) :: nil) O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1') /\
        (* Int.eq captype (Int.repr CAP_SEM_TYPE) = true /\ *)
       exists acspace semifo ptr bin sc idx,
        get O1' cspaceid = Some (capcspace acspace) /\
        get O1' seminfoid = Some (seminfo semifo) /\
        get semifo capability = Some (infotid ptr, bin, sc) /\
        (* get_obj_slot_rel dest ptr acspace (Int.repr idx) /\ *)
        O2 = Some (set O1' seminfoid (seminfo (EmbMod.set semifo capability
            (infotid ptr, bin,
            update_nth_list int32 (Z.to_nat (Int.signed (Int.sub dest Int.one)))
              sc (Int.repr idx)))))
      )
end. 


Definition user_cnode_move_mutex (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      opv = Some (Vint32 (Int.repr CNODE_MOVE_SUCCESS)) /\
      (exists dest src captype capability v',
        vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        exists index O1',
        check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\
        ucos_cnode_move_spec vl O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1') /\
        Int.eq captype (Int.repr CAP_MUTEX_TYPE) = true /\
       exists acspace mls,
       exists ptr o x n pro pi w c mc idx,
       get O1' cspaceid = Some (capcspace acspace) /\
       get O1' absmutinfoid = Some (absmutinfo mls) /\
       get mls capability = Some (Valid_Addr ptr, o, x, n, pro, pi, w, c, mc) /\
       get_obj_slot_rel dest ptr acspace (Int.repr idx) /\
        O2 = Some (set O1' absmutinfoid (absmutinfo (MibMod.set mls capability
        (Valid_Addr ptr, o, x, n, pro, pi, w, c,
         update_nth_list int32 (Z.to_nat (Int.signed (Int.sub dest Int.one)))
          mc (Int.repr idx)))))
      )
end. 

Definition user_cnode_move_q (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      opv = Some (Vint32 (Int.repr CNODE_MOVE_SUCCESS)) /\
      (exists dest src captype capability v',
        vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        exists index O1',
        check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\
        ucos_cnode_move_spec vl O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1') /\
        Int.eq captype (Int.repr CAP_Q_TYPE) = true /\
       exists acspace qtls,
       exists ptr wtype flag maxm msize curm mqc idx,
        get O1' cspaceid = Some (capcspace acspace) /\
        get O1' absmqattrid = Some (absmqattr qtls) /\
        get qtls capability = Some (Valid_Addr ptr, wtype, flag, maxm, msize, curm, mqc) /\
        get_obj_slot_rel dest ptr acspace (Int.repr idx)  /\
          O2 = Some (set O1' absmqattrid (absmqattr (MqattrMod.set qtls capability
          (Valid_Addr ptr, wtype, flag, maxm, msize, curm,
           update_nth_list int32 (Z.to_nat (Int.signed (Int.sub dest Int.one)))
           mqc (Int.repr idx)))))
        )
end. 

Definition user_cnode_move_category (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      opv = Some (Vint32 (Int.repr CNODE_MOVE_SUCCESS)) /\
      (exists dest src captype capability v',
        vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        exists index O1',
        check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\
        ucos_cnode_copy_spec vl O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1') /\
        Int.eq captype (Int.repr CAP_FUNCTION_TYPE) = true /\
        O2 = Some O1')
  end. 

Definition user_cnode_move_succ_category (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      opv = Some (Vint32 (Int.repr CNODE_MOVE_SUCCESS)) /\
      (exists dest src captype capability v',
        vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        exists acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
        exists src_slot_type src_cap_type src_cap_content src_cap_right src_object_t,
        exists dest_slot_type dest_cap_type dest_cap_content dest_cap_right dest_object_t index,
          CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) /\
          CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) /\
          nth_slots (Z.to_nat index) src_slots =
            Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, src_object_t))) /\
          nth_slots (Z.to_nat index) dest_slots =
            Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t))) /\
            (* (opv = Some (Vint32 (Int.repr CNODE_NONE_FAULT)) /\ *)
            ( exists cs cs' cs'',
              cs = CSpaceMod.set acspace dest
                  (update_nth_slots (Z.to_nat index) dest_slots
                    (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, src_cap_right, dest_object_t))), dest_childs, dest_prio) /\
              cs' = CSpaceMod.set cs src 
                  (update_nth_slots (Z.to_nat index) src_slots 
                    (src_slot_type, (Int.repr 0, (Int.repr 0, Int.repr 0, src_object_t))), src_childs, src_prio) /\
              cs'' = CSpaceMod.set cs' src 
                  (update_nth_slots (Z.to_nat index) (update_nth_slots (Z.to_nat index) src_slots 
                  (src_slot_type, (Int.repr 0, (Int.repr 0, Int.repr 0, src_object_t))))
                    ((Int.repr SLOT_NULL_CAP), (Int.repr 0, (Int.repr 0, Int.repr 0, src_object_t))), src_childs, src_prio) /\
              O2 = Some (set O1 cspaceid (capcspace cs''))))
  end. 

Definition user_cnode_move_succ_object (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr CNODE_MOVE_SUCCESS)) /\
        (exists dest src captype capability v',
          vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
          exists acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
          exists src_slot_type src_cap_type src_obj_right src_dummy src_object_t,
          exists dest_idx dest_slot_type dest_cap_type dest_obj_right dest_dummy index some_dummy,
            CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) /\ 
            CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) /\ 
            nth_slots (Z.to_nat index) src_slots =
              Some (src_slot_type, (src_cap_type, (src_obj_right, src_dummy, src_object_t))) /\ 
            nth_slots (Z.to_nat dest_idx) dest_slots =
              Some (dest_slot_type, (dest_cap_type, (dest_obj_right, dest_dummy, src_object_t))) /\ 
              ( exists cs cs' cs'',
                cs = CSpaceMod.set acspace dest
                    (update_nth_slots (Z.to_nat dest_idx) dest_slots
                      (dest_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, some_dummy, src_object_t))), dest_childs, dest_prio) /\
                cs' = CSpaceMod.set cs src 
                    (update_nth_slots (Z.to_nat index) src_slots 
                      (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) /\
                cs'' = CSpaceMod.set cs' src 
                    (update_nth_slots (Z.to_nat index) (update_nth_slots (Z.to_nat index) src_slots 
                    (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull))))
                      ((Int.repr SLOT_NULL_CAP), (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) /\
               O2 = Some (set O1 cspaceid (capcspace cs''))
              (* O2 = Some (set O1 cspaceid (capcspace
              ((CSpaceMod.set (CSpaceMod.set acspace dest
              (update_nth_slots (Z.to_nat (Int.unsigned dest_idx)) dest_slots
                (dest_slot_type, (Int.repr CAP_OBJECT_TYPE, (dest_obj_right, src_dummy, object_t))), dest_childs, dest_prio))
                src
                (update_nth_slots (Z.to_nat (Int.unsigned captype)) src_slots ((Int.repr SLOT_NULL_CAP),
                  (Int.repr 0, (src_cap_content, Int.repr 0, Vnull))), src_childs, src_prio))) *)
            (* /\
          Int.eq captype (Int.repr CAP_FUNCTION_TYPE) = true ) *) ))
    end. 
    

Definition user_cnode_move_succ_objectnot (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr CNODE_MOVE_SUCCESS)) /\
        (exists dest src captype capability v',
          vl = ((Vint32 dest) :: (Vint32 src) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
          exists acspace src_slots src_childs src_prio dest_slots dest_childs dest_prio,
          exists src_slot_type src_cap_type object_t index ranindex src_obj_right src_dummy some_dummy some_slot_type,
          exists slots_vll11 slots_vll12 slots_vll21 endPtr,
            CSpaceMod.get acspace src = Some (src_slots, src_childs, src_prio) /\ 
            CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_prio) /\ 
            nth_slots (Z.to_nat index) src_slots =
              Some (src_slot_type, (src_cap_type, (src_obj_right, src_dummy, object_t))) /\ 
              ( dest_slots = (slots_vll11 ++ slots_vll12 ++ slots_vll21) /\
                length slots_vll11 = Z.to_nat(OBJ_POSITION) /\
                length (slots_vll11 ++ slots_vll12) = Z.to_nat(Int.unsigned endPtr) /\
                ~exists dest_idx dest_slot_type dest_cap_type dest_obj_right dest_dummy,
                    (0 <= dest_idx < Z.of_nat (length slots_vll12))%Z /\
                    nth_slots (Z.to_nat dest_idx) slots_vll12 =
                        Some (dest_slot_type, (dest_cap_type, (dest_obj_right, dest_dummy, object_t)))) /\ 
                ( exists cs cs' cs'',
                  cs = CSpaceMod.set acspace dest
                      (update_nth_slots (Z.to_nat ranindex) dest_slots
                      (some_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, some_dummy, object_t))), dest_childs, dest_prio) /\
                  cs' = CSpaceMod.set cs src
                      (update_nth_slots (Z.to_nat index) src_slots 
                      (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) /\
                  cs'' = CSpaceMod.set cs' src 
                      (update_nth_slots (Z.to_nat index) (update_nth_slots (Z.to_nat index) src_slots 
                      (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull))))
                        ((Int.repr SLOT_NULL_CAP), (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) /\
                  O2 = Some (set O1 cspaceid (capcspace cs''))
          ))
                (* O2 = Some (set O1 cspaceid (capcspace
                ( (CSpaceMod.set (CSpaceMod.set acspace dest
                (update_nth_slots (Z.to_nat (Int.unsigned index)) dest_slots 
                (src_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, src_dummy, object_t))), dest_childs, dest_prio))
                (* (dest_slots ++ ((src_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, src_dummy, object_t))) :: nil), dest_childs, dest_prio)) *)
                src
                (update_nth_slots (Z.to_nat (Int.unsigned cap)) src_slots ((Int.repr SLOT_NULL_CAP),
                  (Int.repr 0, (src_obj_right, Int.repr 0, Vnull))), src_childs, src_prio)))
        )) /\
          Int.eq captype (Int.repr CAP_FUNCTION_TYPE) = true ) *)
    end.     



Definition user_cnode_move_code (vl: vallist) :=
  user_cnode_move_invalid (|vl|) ??
  user_cnode_move_err (|vl|)??
  user_cnode_move_slotnum (|vl|)??
  user_cnode_move_failure (|vl|)??
  user_cnode_move_nocap (|vl|)??
  user_cnode_move_category (|vl|)??
  user_cnode_move_sem (|vl|)??
  user_cnode_move_mutex (|vl|)??
  user_cnode_move_q (|vl|)??
  user_cnode_move_succ_category(|vl|)??
  user_cnode_move_succ_object(|vl|)??
  user_cnode_move_succ_objectnot(|vl|).
 
(*
Definition user_cnode_move_spec' (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (exists dest src capType capability v',
          vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 capType) :: (Vint32 capability) :: v') /\
            exists r O2', 
              (opv = (Some (Vint32 r)) /\ O2 = Some O2' /\
            user_cnode_move_rel dest src capType capability O1 r O2')
        )
  end.  
    
Definition user_cnode_move_code (vl: vallist) :=
  user_cnode_move_spec' (|vl|).


Definition user_cnode_move_api :=
  (user_cnode_move_code, (Tint8, Tint8 :: Tint8 :: Tint32 :: Tint32 :: nil)).

Definition user_cnode_copy_spec' (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (exists dest src capType capability v',
         vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 capType) :: (Vint32 capability) :: v') /\
          exists r O2', 
            (opv = (Some (Vint32 r)) /\ O2 = Some O2' /\
              user_cnode_copy_rel dest src capType capability O1 r O2')
      )
end.  
*)

(*Definition user_cnode_copy_code (vl: vallist) :=
  user_cnode_copy_spec' (|vl|).*)        


Definition user_cnode_copy_api :=
  (user_cnode_copy_code, (Tint8, Tint8 :: Tint8 :: Tint32 :: Tint32 :: nil)).
Definition user_cnode_move_api :=
(user_cnode_move_code, (Tint8, Tint8 :: Tint8 :: Tint32 :: Tint32 :: nil)).


(*mutate*)
Definition ucos_cnode_mutate_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (exists dest src funcap rights v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 funcap) :: (Vint32 rights) ::v')  /\
        (exists acspace,
          get O1 cspaceid = Some (capcspace acspace) /\
          (exists dest_slots dest_childs dest_parent
             dest_slot_type dest_cap_type dest_cap_content dest_cap_right dest_object_t,
               CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) /\
               nth_slots (Z.to_nat (Int.unsigned funcap)) dest_slots =
               Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t)))/\
               exists  src_slots src_childs src_parent
                 src_slot_type src_cap_type src_cap_content src_cap_right src_object_t,
                 CSpaceMod.get acspace src = Some (src_slots, src_childs, src_parent) /\
                 nth_slots (Z.to_nat (Int.unsigned funcap)) src_slots =
                 Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, src_object_t)))/\
                 src_cap_type = Int.repr CAP_CATEGORY_TYPE /\ 
                   (exists O1', 
                    (O1' = set O1 cspaceid (capcspace (CSpaceMod.set acspace dest
         (update_nth_slots (Z.to_nat (Int.unsigned funcap)) dest_slots
           (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, rights, dest_object_t))), dest_childs, dest_parent)))/\
           O2 = Some (set O1' cspaceid (capcspace (CSpaceMod.set acspace src
           (update_nth_slots (Z.to_nat (Int.unsigned funcap)) src_slots
             (Int.repr SLOT_NULL_CAP, (src_cap_type, (src_cap_content, (Int.and src_cap_right (Int.not rights)), src_object_t))), src_childs, src_parent)))) )/\ 
         opv = Some (Vint32 (Int.repr CNODE_NONE_FAULT))
          )
       )))
 end. 

 Definition ucos_cnode_mutate_fail(vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (exists dest src funcap rights v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 funcap) :: (Vint32 rights) :: v')  /\
        (exists acspace,
          get O1 cspaceid = Some (capcspace acspace) /\
          (exists  src_slots src_childs src_parent
             src_slot_type src_cap_type src_cap_content src_cap_right src_object_t,
            CSpaceMod.get acspace src = Some (src_slots, src_childs, src_parent) /\
            nth_slots (Z.to_nat (Int.unsigned funcap)) src_slots =
            Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, src_object_t))) /\ 
             (O2 = Some O1 /\ opv = Some (Vint32 (Int.repr CNODE_MUTATE_FAILURE)))   
       )))
 end. 


 Definition ucos_cnode_mutate_spec (vl: vallist) :=
    ucos_cnode_mutate_succ (|vl|) ??
    ucos_cnode_mutate_fail (|vl|).


(* user mutate *)

Definition user_cnode_mutate_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
       opv = Some (Vint32 (Int.repr OS_PRIO_INVALID)) /\
       O2 = Some O1 /\
       (exists dest src funcap rights v',
         vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 funcap) :: (Vint32 rights) :: v') /\
         (((Int.ltu dest (Int.repr OS_LOWEST_PRIO) = false) )
         \/ ((Int.ltu src (Int.repr OS_LOWEST_PRIO) = false))))
  end. 
Definition user_cnode_mutate_curpspace_null (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
      (O2 = Some O1 /\ opv = Some (Vint32 (Int.repr CNODE_MUTATE_FAILURE))) 
        
end. 



Definition user_cnode_mutate_none (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
         O2 = Some O1 /\ opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE))
 end. 

 Definition user_cnode_mutate_destself_none (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (exists dest src funcap rights v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 funcap) :: (Vint32 rights) :: v')  /\
        Int.eq dest (Int.repr OS_PRIO_SELF) = true  /\ Int.eq src (Int.repr OS_PRIO_SELF) = false /\
        (exists acspace,
        get O1 cspaceid = Some (capcspace acspace) /\
          (exists tls p msg t sus,
            get O1 curtid = Some (oscurt t) /\ 
            get O1 abtcblsid = Some (abstcblist tls) /\  
            get tls t = Some (p,rdy,msg,sus) /\
          (exists cur_slots cur_childs cur_parent cur_slot_type cur_cap_type cur_cap_content cur_cap_right cur_object_t,
              CSpaceMod.get acspace p = Some (cur_slots, cur_childs, cur_parent) /\
              nth_slots (Z.to_nat (Int.unsigned (Int.repr SLOT_CNODE_CAP))) cur_slots =
               Some (cur_slot_type, (cur_cap_type, (cur_cap_content, cur_cap_right, cur_object_t))) /\
               exists src_slots src_childs src_parent,
                CSpaceMod.get acspace src = Some (src_slots, src_childs, src_parent) /\
                (Int.eq (Int.and cur_cap_right ((Int.repr CNODE_MUTATE_CAP))) (Int.repr 0) = true
                  \/(not (cur_parent = src) /\ not (src_parent = p)))))) /\ 
         O2 = Some O1 /\ opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE))
          )
 end. 

 Definition user_cnode_mutate_srcself_none (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (exists dest src funcap rights v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 funcap) :: (Vint32 rights) :: v')  /\
        (exists acspace,
        get O1 cspaceid = Some (capcspace acspace) /\
          (exists tls p ready msg t sus,
            get O1 curtid = Some (oscurt t) /\ 
            get O1 abtcblsid = Some (abstcblist tls) /\  
            get tls t = Some (p,ready,msg,sus) /\
            Int.eq src p = true  /\ Int.eq dest p = false /\ 
          (exists cur_slots cur_childs cur_parent cur_slot_type cur_cap_type cur_cap_content cur_cap_right cur_object_t,
              CSpaceMod.get acspace p = Some (cur_slots, cur_childs, cur_parent) /\
              nth_slots (Z.to_nat (Int.unsigned (Int.repr SLOT_CNODE_CAP))) cur_slots =
               Some (cur_slot_type, (cur_cap_type, (cur_cap_content, cur_cap_right, cur_object_t))) /\
               exists dest_slots dest_childs dest_parent,
                 CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) /\
                 (Int.eq (Int.and cur_cap_right ((Int.repr CNODE_MUTATE_CAP))) (Int.repr 0) = true
                  \/ (not (dest_parent = p)))))) /\ 
        O2 = Some O1 /\ opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE))
          )
 end. 

 Definition user_cnode_mutate_destsrcself_none (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (exists dest src funcap rights v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 funcap) :: (Vint32 rights) :: v')  /\
        Int.eq src (Int.repr OS_PRIO_SELF) = true  /\ Int.eq dest (Int.repr OS_PRIO_SELF) = true /\ 
        (exists acspace,
        get O1 cspaceid = Some (capcspace acspace) /\
          (exists tls p ready msg t sus,
            get O1 curtid = Some (oscurt t) /\ 
            get O1 abtcblsid = Some (abstcblist tls) /\  
            get tls t = Some (p,ready,msg,sus) /\
          (exists cur_slots cur_childs cur_parent cur_slot_type cur_cap_type cur_cap_content cur_cap_right cur_object_t,
              CSpaceMod.get acspace p = Some (cur_slots, cur_childs, cur_parent) /\
              nth_slots (Z.to_nat (Int.unsigned (Int.repr SLOT_CNODE_CAP))) cur_slots =
               Some (cur_slot_type, (cur_cap_type, (cur_cap_content, cur_cap_right, cur_object_t))) /\
               (Int.eq (Int.and cur_cap_right ((Int.repr CNODE_MUTATE_CAP))) (Int.repr 0) = true
                  \/ (not (p = cur_parent) ))))) /\ 
        O2 = Some O1 /\ opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE))
          )
 end. 
 Definition user_cnode_mutate_succ_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (exists dest src funcap rights v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 funcap) :: (Vint32 rights) :: v')  /\
        (exists acspace,
           get O1 cspaceid = Some (capcspace acspace) /\
            (exists dest_slots dest_childs dest_parent
            dest_slot_type dest_cap_type dest_cap_content dest_cap_right dest_object_t,
               CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) /\
               nth_slots (Z.to_nat (Int.unsigned funcap)) dest_slots =
               Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t)))/\
               (exists src_slots src_childs src_parent
               src_slot_type src_cap_content src_cap_right src_object_t,
               CSpaceMod.get acspace src = Some (src_slots, src_childs, src_parent) /\
               nth_slots (Z.to_nat (Int.unsigned funcap)) src_slots =
                 Some (src_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, src_cap_right, src_object_t)))/\
               (exists cs cs' cs'', 
                  (cs = CSpaceMod.set acspace dest
                     (update_nth_slots (Z.to_nat (Int.unsigned funcap)) dest_slots
                         (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, rights, dest_object_t))), dest_childs, dest_parent))/\
                  cs' = CSpaceMod.set cs src
                     (update_nth_slots (Z.to_nat (Int.unsigned funcap)) src_slots
                          (src_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, (Int.and src_cap_right (Int.not rights)), src_object_t))), src_childs, src_parent) /\
                  cs'' = CSpaceMod.set cs' src
                     (update_nth_slots (Z.to_nat (Int.unsigned funcap)) ((update_nth_slots (Z.to_nat (Int.unsigned funcap)) src_slots
                     (src_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, (Int.and src_cap_right (Int.not rights)), src_object_t)))))
                          ($SLOT_NULL_CAP, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, (Int.and src_cap_right (Int.not rights)), src_object_t))), src_childs, src_parent) /\
                  O2 = Some (set O1 cspaceid (capcspace cs''))))) /\ (opv = Some (Vint32 (Int.repr CNODE_MUTATE_SUCCESS)))))  
       
 end. 

 Definition user_cnode_mutate_succ_fail (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
    O2 = Some O1 /\ opv = Some (Vint32 (Int.repr CNODE_MUTATE_FAILURE))
 end.  

 Definition user_cnode_mutate_destself_succ_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (exists dest src funcap rights,
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 funcap) :: (Vint32 rights) :: nil)  /\
        (exists acspace,
        get O1 cspaceid = Some (capcspace acspace) /\
          (exists tls p msg t sus ready,
            get O1 curtid = Some (oscurt t) /\ 
            get O1 abstcblsid = Some (abstcblist tls) /\  
            get tls t = Some (p,ready,msg,sus) /\
          (exists cur_slots cur_childs cur_parent cur_slot_type cur_cap_type cur_cap_content cur_cap_right cur_object_t,
              CSpaceMod.get acspace p = Some (cur_slots, cur_childs, cur_parent) /\
              nth_slots (Z.to_nat (Int.unsigned (Int.repr SLOT_CNODE_CAP))) cur_slots =
               Some (cur_slot_type, (cur_cap_type, (cur_cap_content, cur_cap_right, cur_object_t))) /\
               exists  src_slots src_childs src_parent,
               CSpaceMod.get acspace src = Some (src_slots, src_childs, src_parent) /\
                (Int.eq (Int.and cur_cap_right ((Int.repr CNODE_MUTATE_CAP))) (Int.repr 0) = false
                  /\ ((cur_parent = src)))  /\ 
                  ((exists opv', ucos_cnode_mutate_succ vl O1 (opv', O2) /\ opv = Some (Vint32 (Int.repr CNODE_MUTATE_SUCCESS)))
                  )     
       ))) )
 end. 

 Definition user_cnode_mutate_destself_succ_fail (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (exists dest src funcap rights,
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 funcap) :: (Vint32 rights) :: nil)  /\
        (exists acspace,
        get O1 cspaceid = Some (capcspace acspace) /\
          (exists tls p msg t sus ready,
            get O1 curtid = Some (oscurt t) /\ 
            get O1 abstcblsid = Some (abstcblist tls) /\  
            get tls t = Some (p,ready,msg,sus) /\
          (exists cur_slots cur_childs cur_parent cur_slot_type cur_cap_type cur_cap_content cur_cap_right cur_object_t,
              CSpaceMod.get acspace p = Some (cur_slots, cur_childs, cur_parent) /\
              nth_slots (Z.to_nat (Int.unsigned (Int.repr SLOT_CNODE_CAP))) cur_slots =
               Some (cur_slot_type, (cur_cap_type, (cur_cap_content, cur_cap_right, cur_object_t))) /\
               exists  src_slots src_childs src_parent,
               CSpaceMod.get acspace src = Some (src_slots, src_childs, src_parent) /\
                (Int.eq (Int.and cur_cap_right ((Int.repr CNODE_MUTATE_CAP))) (Int.repr 0) = false
                  /\ ((cur_parent = src)))  /\ 
                  (ucos_cnode_mutate_fail vl O1 (opv, O2))     
       ))) )
 end. 

 Definition user_cnode_mutate_srcself_succ_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (exists dest src funcap rights v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 funcap) :: (Vint32 rights) :: v')  /\
        Int.eq src (Int.repr OS_PRIO_SELF) = true /\ Int.eq dest (Int.repr OS_PRIO_SELF) = false /\
        (exists acspace,
        get O1 cspaceid = Some (capcspace acspace) /\
          (exists tls p msg t sus ready,
            get O1 curtid = Some (oscurt t) /\ 
            get O1 abstcblsid = Some (abstcblist tls) /\  
            get tls t = Some (p,ready,msg,sus) /\
          (exists cur_slots cur_childs cur_parent cur_slot_type cur_cap_type cur_cap_content cur_cap_right cur_object_t,
              CSpaceMod.get acspace p = Some (cur_slots, cur_childs, cur_parent) /\
              nth_slots (Z.to_nat (Int.unsigned (Int.repr SLOT_CNODE_CAP))) cur_slots =
               Some (cur_slot_type, (cur_cap_type, (cur_cap_content, cur_cap_right, cur_object_t))) /\
               exists  dest_slots dest_childs dest_parent,
               CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) /\
                (Int.eq (Int.and cur_cap_right ((Int.repr CNODE_MUTATE_CAP))) (Int.repr 0) = false
                  /\ ((dest_parent = p)))  /\ 
               ((exists opv', ucos_cnode_mutate_succ vl O1 (opv', O2) /\ opv = Some (Vint32 (Int.repr CNODE_MUTATE_SUCCESS)))
              )     
       ))) )
 end. 

 Definition user_cnode_mutate_srcself_succ_fail (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (exists dest src funcap rights v',
        vl = ((Vint32 dest) :: (Vint32 src) :: (Vint32 funcap) :: (Vint32 rights) :: v')  /\
        
        (exists acspace,
        get O1 cspaceid = Some (capcspace acspace) /\
          (exists tls p msg t sus ready,
            get O1 curtid = Some (oscurt t) /\ 
            get O1 abstcblsid = Some (abstcblist tls) /\  
            get tls t = Some (p,ready,msg,sus) /\
            Int.eq src p = true /\ Int.eq dest p = false /\
          (exists cur_slots cur_childs cur_parent cur_slot_type cur_cap_type cur_cap_content cur_cap_right cur_object_t,
              CSpaceMod.get acspace p = Some (cur_slots, cur_childs, cur_parent) /\
              nth_slots (Z.to_nat (Int.unsigned (Int.repr SLOT_CNODE_CAP))) cur_slots =
               Some (cur_slot_type, (cur_cap_type, (cur_cap_content, cur_cap_right, cur_object_t))) /\
               exists  dest_slots dest_childs dest_parent,
               CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) /\
                (Int.eq (Int.and cur_cap_right ((Int.repr CNODE_MUTATE_CAP))) (Int.repr 0) = false
                  /\ ((dest_parent = p)))  /\ 
               (ucos_cnode_mutate_fail vl O1 (opv, O2))     
       ))) )
 end. 


Definition user_cnode_mutate_spec (vl: vallist) :=
    user_cnode_mutate_err (|vl|) ??
    user_cnode_mutate_curpspace_null (|vl|)??
    user_cnode_mutate_none (|vl|)??
    user_cnode_mutate_succ_succ (|vl|)??    
    user_cnode_mutate_succ_fail (|vl|).


Definition user_cnode_mutate_api :=
  (user_cnode_mutate_spec, (Tint8, Tint8 :: Tint8 :: Tint32 :: Tint32 :: nil)).
(*delete*)



Inductive ucos_cnode_delete_rel:
    int32 -> int32 -> osabst -> int32 -> osabst -> Prop :=
| ucos_cnode_delete_rel_category:
  forall i cap O1 acspace slots childs prio,
  forall slot_type cap_type cap_content cap_right object_t,
    get O1 cspaceid = Some (capcspace acspace) /\
    CSpaceMod.get acspace i = Some (slots, childs, prio) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) slots =
      Some (slot_type, (cap_type, (cap_content, cap_right, object_t))) ->
    Int.eq cap_type (Int.repr CAP_CATEGORY_TYPE) = true ->
    ucos_cnode_delete_rel i cap O1 (Int.repr CNODE_NONE_FAULT)
      (set O1 cspaceid (capcspace
        (CSpaceMod.set acspace i
          (update_nth_list slot_val_type (Z.to_nat (Int.unsigned cap)) slots
            (Int.repr SLOT_NULL_CAP, (Int.zero, (Int.zero, Int.zero, object_t))),
          childs, prio))))
| ucos_cnode_delete_rel_object:
  forall i cap O1 acspace slots childs prio,
  forall slot_type cap_type cap_content cap_right object_t,
    get O1 cspaceid = Some (capcspace acspace) /\
    CSpaceMod.get acspace i = Some (slots, childs, prio) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) slots =
      Some (slot_type, (cap_type, (cap_content, cap_right, object_t))) ->
    Int.eq cap_type (Int.repr CAP_OBJECT_TYPE) = true ->
    ucos_cnode_delete_rel i cap O1 (Int.repr CNODE_NONE_FAULT)
      (set O1 cspaceid (capcspace
        (CSpaceMod.set acspace i
          (update_nth_list slot_val_type (Z.to_nat (Int.unsigned cap)) slots
            (Int.repr SLOT_NULL_CAP, (Int.zero, (Int.zero, cap_right, Vnull))),
          childs, prio))))
| ucos_cnode_delete_rel_failure:
  forall i cap O1 acspace slots childs prio,
  forall slot_type cap_type cap_content cap_right object_t,
    get O1 cspaceid = Some (capcspace acspace) /\
    CSpaceMod.get acspace i = Some (slots, childs, prio) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) slots =
      Some (slot_type, (cap_type, (cap_content, cap_right, object_t))) ->
    Int.eq cap_type (Int.repr CAP_OBJECT_TYPE) = false ->
    Int.eq cap_type (Int.repr CAP_CATEGORY_TYPE) = false -> 
    ucos_cnode_delete_rel i cap O1 (Int.repr CNODE_DELETE_FAILURE) O1.




Definition ucos_cnode_delete_category (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        exists dest funcap v',
        vl = ((Vint32 dest) :: (Vint32 funcap) :: v')  /\       
       exists acspace slots childs prio 
          slot_type cap_type cap_content cap_right object_t,
          get O1 cspaceid = Some (capcspace acspace) /\
          CSpaceMod.get acspace dest = Some (slots, childs, prio) ->
          nth_slots (Z.to_nat (Int.unsigned funcap)) slots =
            Some (slot_type, (cap_type, (cap_content, cap_right, object_t))) ->
          Int.eq cap_type (Int.repr CAP_CATEGORY_TYPE) = true ->
          (opv = Some (Vint32 (Int.repr CNODE_NONE_FAULT)) /\
           O2 = Some (set O1 cspaceid (capcspace
           (CSpaceMod.set acspace dest
             (update_nth_list slot_val_type (Z.to_nat (Int.unsigned funcap)) slots
               (Int.repr SLOT_NULL_CAP, (Int.zero, (Int.zero, Int.zero, object_t))),
             childs, prio)))))
  end. 

  Definition ucos_cnode_delete_object (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
    match rst with
      | (opv, O2) => 
          exists dest funcap v',
          vl = ((Vint32 dest) :: (Vint32 funcap) :: v')  /\       
         exists acspace slots childs prio 
            slot_type cap_type cap_content cap_right object_t,
            get O1 cspaceid = Some (capcspace acspace) /\
            CSpaceMod.get acspace dest = Some (slots, childs, prio) ->
            nth_slots (Z.to_nat (Int.unsigned funcap)) slots =
              Some (slot_type, (cap_type, (cap_content, cap_right, object_t))) ->
         Int.eq cap_type (Int.repr CAP_OBJECT_TYPE) = true -> 
            (opv = Some (Vint32 (Int.repr CNODE_NONE_FAULT)) /\
           O2 = Some (set O1 cspaceid (capcspace
           (CSpaceMod.set acspace dest
             (update_nth_list slot_val_type (Z.to_nat (Int.unsigned funcap)) slots
               (Int.repr SLOT_NULL_CAP, (Int.zero, (Int.zero, cap_right, Vnull))),
             childs, prio)))))
    end.
    
Definition ucos_cnode_delete_failure (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (*  exists dest funcap v',
        vl = ((Vint32 dest) :: (Vint32 funcap) :: v')  /\       
        exists acspace slots childs prio 
          slot_type cap_type cap_content cap_right object_t,
          get O1 cspaceid = Some (capcspace acspace) /\
          CSpaceMod.get acspace dest = Some (slots, childs, prio) ->
          nth_slots (Z.to_nat (Int.unsigned funcap)) slots =
            Some (slot_type, (cap_type, (cap_content, cap_right, object_t))) ->
            Int.eq cap_type (Int.repr CAP_OBJECT_TYPE) = false ->
            Int.eq cap_type (Int.repr CAP_CATEGORY_TYPE) = false -> *)
            (opv = Some (Vint32 (Int.repr CNODE_DELETE_FAILURE)) /\
           O2 = Some O1)
  end.

(*the top spec of ucos delete*)
Definition ucos_cnode_delete_spec  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      (exists O1', 
      ucos_cnode_delete_category vl O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1') \/
      ucos_cnode_delete_object vl O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), Some O1')  /\
      opv = Some (Vint32 (Int.repr CNODE_NONE_FAULT)) /\ O2 = Some O1') \/
      ucos_cnode_delete_failure vl O1 (Some (Vint32 (Int.repr CNODE_DELETE_FAILURE)), Some O1)
end. 
  
  

Inductive user_cnode_delete_rel':
    int32 -> int32 -> int32 -> osabst -> int32 -> osabst -> Prop :=
| user_cnode_delete_rel'_not_found:
  forall dest capType capability O1,
    (* Check_Cap_Type returns not found: do nothing *)
    check_cap_type_rel capability capType dest O1 (Int.repr SLOT_NUM) ->
    user_cnode_delete_rel' dest capType capability O1 (Int.repr EINVAL) O1
| user_cnode_delete_rel'_succ_succ:
  forall dest capType capability O1 acspace dest_slots dest_childs dest_parent O2,
    check_cap_type_rel capability capType dest O1 (Int.repr index) ->
    get O1 cspaceid = Some (capcspace acspace) ->
    CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) ->  
   forall t tls p st m sus curt_slots curt_childs curt_parent,
   forall curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t,
     get O1 curtid = Some (oscurt t) ->
     get O1 abstcblsid = Some (abstcblist tls) ->
     get tls t = Some (p, st, m, sus) ->
     CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) ->
     dest_parent = p \/ dest = p -> 
     nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
       Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) ->
     Int.eq (Int.and curt_cap_right (Int.repr CNODE_DELETE_CAP)) Int.zero = false ->
     ucos_cnode_delete_rel dest (Int.repr index) O1 (Int.repr CNODE_NONE_FAULT) O2 ->
     user_cnode_delete_rel' dest capType capability O1 (Int.repr CNODE_DELETE_SUCCESS) O2
| user_cnode_delete_rel'_succ_failure:
     forall dest capType capability O1 acspace dest_slots dest_childs dest_parent O2,
       check_cap_type_rel capability capType dest O1 (Int.repr index) ->
       get O1 cspaceid = Some (capcspace acspace) ->
       CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) ->  
      forall t tls p st m sus curt_slots curt_childs curt_parent,
      forall curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t,
        get O1 curtid = Some (oscurt t) ->
        get O1 abstcblsid = Some (abstcblist tls) ->
        get tls t = Some (p, st, m, sus) ->
        CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) ->
        dest_parent = p \/ dest = p -> 
        nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
          Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) ->
        Int.eq (Int.and curt_cap_right (Int.repr CNODE_DELETE_CAP)) Int.zero = false ->
        ucos_cnode_delete_rel dest (Int.repr index) O1 (Int.repr CNODE_NONE_FAULT) O2 ->
        user_cnode_delete_rel' dest capType capability O1 (Int.repr CNODE_DELETE_FAILURE) O2
| user_cnode_delete_rel'_capability_none:
    forall dest capType capability O1 acspace dest_slots dest_childs dest_parent,
       check_cap_type_rel capability capType dest O1 (Int.repr index) ->
       get O1 cspaceid = Some (capcspace acspace) ->
       CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) ->  
      forall t tls p st m sus curt_slots curt_childs curt_parent,
      forall curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t,
        get O1 curtid = Some (oscurt t) ->
        get O1 abstcblsid = Some (abstcblist tls) ->
        get tls t = Some (p, st, m, sus) ->
        CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) ->
        nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
          Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) ->
        Int.eq (Int.and curt_cap_right (Int.repr CNODE_DELETE_CAP)) Int.zero = true \/
        not (dest_parent = p \/ dest = p) ->
        user_cnode_delete_rel' dest capType capability O1 (Int.repr USER_CAPABILITY_NONE) O1.


Inductive user_cnode_delete_rel:
        int32 -> int32 -> int32 -> osabst -> int32 -> osabst -> Prop :=
      user_cnode_delete_rel_dest_invalid:
      forall dest capType capability O1,
        Int.ltu dest (Int.repr OS_LOWEST_PRIO) = false ->
        Int.eq dest (Int.repr OS_PRIO_SELF) = false ->
        user_cnode_delete_rel dest capType capability O1
          (Int.repr OS_PRIO_INVALID) O1
    | user_cnode_delete_real_wrong_funcap:
      forall dest capType capability O1,
         Int.ltu (Int.repr CAP_TASK_TYPE) capType = true ->
         user_cnode_delete_rel dest capType capability O1 (Int.repr EINVAL) O1 
    | user_cnode_delete_rel_dest_self:
      forall dest capType capability O1,
          Int.eq dest (Int.repr OS_PRIO_SELF) = true ->
        forall t tls p st m sus rv O2,
          get O1 curtid = Some (oscurt t) ->
          get O1 abstcblsid = Some (abstcblist tls) ->
          get tls t = Some (p, st, m, sus) ->
          user_cnode_delete_rel' p capType capability O1 rv O2 ->
          user_cnode_delete_rel dest capType capability O1 rv O2
    | user_cnode_delete_rel_normal:
      forall dest capType capability O1 rv O2,
        Int.ltu dest (Int.repr OS_LOWEST_PRIO) = true ->
        Int.eq dest (Int.repr OS_PRIO_SELF) = false ->
        user_cnode_delete_rel' dest capType capability O1 rv O2 ->
        user_cnode_delete_rel dest capType capability O1 rv O2. 

  Definition user_cnode_delete_invalid (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
    match rst with
      | (opv, O2) => 
         opv = Some (Vint32 (Int.repr OS_PRIO_INVALID)) /\
         O2 = Some O1 /\
         (exists dest captype capability v',
           vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
           ((Int.ltu  (Int.repr OS_LOWEST_PRIO) dest = true \/ Int.eq dest (Int.repr OS_LOWEST_PRIO) = true))
         )
    end. 

  Definition user_cnode_delete_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
    match rst with
      | (opv, O2) => 
         opv = Some (Vint32 (Int.repr EINVAL)) /\
         O2 = Some O1 /\
         (exists dest captype capability v',
           vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
           Int.ltu (Int.repr CAP_TASK_TYPE) captype = true
         )
    end. 

Definition user_cnode_delete_failure (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr CNODE_DELETE_FAILURE)) /\
        O2 = Some O1 
  end. 
(*
  Definition user_cnode_delete_dest_self_wrong (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
    match rst with
      | (opv, O2) => 
        exists dest captype capability v',
           vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
           Int.ltu (Int.repr CAP_TASK_TYPE) captype = false /\
           Int.eq dest (Int.repr OS_PRIO_SELF) = true/\
           exists t tls p st m sus,
             get O1 curtid = Some (oscurt t) /\
             get O1 abstcblsid = Some (abstcblist tls) /\
             get tls t = Some (p, st, m, sus) /\
             check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr SLOT_NUM)), Some O1) /\
             opv = Some (Vint32 (Int.repr EINVAL)) /\
           O2 = Some O1         
    end. 

Definition user_cnode_delete_dest_self_succ_category (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
    exists dest captype capability v',
        vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        Int.ltu (Int.repr CAP_TASK_TYPE) captype = false /\
           Int.eq dest (Int.repr OS_PRIO_SELF) = true/\
           exists acspace index,
             (check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\
              Z.to_nat index < 255 /\ get O1 cspaceid = Some (capcspace acspace) /\
              exists t tls p st m sus curt_slots curt_childs curt_parent,
              (exists curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t O2',
                get O1 curtid = Some (oscurt t) /\
                get O1 abstcblsid = Some (abstcblist tls) /\
                get tls t = Some (p, st, m, sus) /\
                CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) /\
                (curt_parent = p \/ p = p) /\ 
                nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
                  Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) /\
                Int.eq (Int.and curt_cap_right (Int.repr CNODE_DELETE_CAP)) Int.zero = false /\
                ucos_cnode_delete_category ((Vint32 dest) :: (Vint32 (Int.repr index)) :: v') O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), O2') /\
                opv = Some (Vint32 (Int.repr CNODE_DELETE_SUCCESS)) /\ O2 = O2'))
end. 

Definition user_cnode_delete_dest_self_succ_object (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
    exists dest captype capability v',
        vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        Int.ltu (Int.repr CAP_TASK_TYPE) captype = false /\
           Int.eq dest (Int.repr OS_PRIO_SELF) = true/\
           exists acspace index,
             (check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\
             Z.to_nat index < 255 /\
              get O1 cspaceid = Some (capcspace acspace) /\
              exists t tls p st m sus curt_slots curt_childs curt_parent,
              exists curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t O2',
                get O1 curtid = Some (oscurt t) /\
                get O1 abstcblsid = Some (abstcblist tls) /\
                get tls t = Some (p, st, m, sus) /\
                CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) /\
                (curt_parent = p \/ p = p) /\ 
                nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
                  Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) /\
                Int.eq (Int.and curt_cap_right (Int.repr CNODE_DELETE_CAP)) Int.zero = false /\
                ucos_cnode_delete_object ((Vint32 dest) :: (Vint32 (Int.repr index)) :: v') O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), O2') /\
                opv = Some (Vint32 (Int.repr CNODE_DELETE_SUCCESS)) /\ O2 = O2')
end. 

Definition user_cnode_delete_dest_self_succ_object_fail (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
    exists dest captype capability v',
        vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        Int.ltu (Int.repr CAP_TASK_TYPE) captype = false /\
           Int.eq dest (Int.repr OS_PRIO_SELF) = true/\
           exists acspace index,
             (check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\
             Z.to_nat index < 255 /\  get O1 cspaceid = Some (capcspace acspace) /\
              exists t tls p st m sus curt_slots curt_childs curt_parent,
              exists curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t O2',
                get O1 curtid = Some (oscurt t) /\
                get O1 abstcblsid = Some (abstcblist tls) /\
                get tls t = Some (p, st, m, sus) /\
                CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) /\
                (curt_parent = p \/ p = p) /\ 
                nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
                  Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) /\
                Int.eq (Int.and curt_cap_right (Int.repr CNODE_DELETE_CAP)) Int.zero = false /\
                ucos_cnode_delete_failure ((Vint32 dest) :: (Vint32 (Int.repr index)) :: v') O1 (Some (Vint32 (Int.repr CNODE_DELETE_FAILURE)), O2') /\
                opv = Some (Vint32 (Int.repr CNODE_DELETE_FAILURE)) /\ O2 = O2')
end.

Definition user_cnode_delete_dest_self_succ_fail (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
    exists dest captype capability v',
        vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        Int.ltu (Int.repr CAP_TASK_TYPE) captype = false /\
           Int.eq dest (Int.repr OS_PRIO_SELF) = true/\
           exists acspace index,
             (check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\
             Z.to_nat index < 255 /\ get O1 cspaceid = Some (capcspace acspace) /\
              exists t tls p st m sus curt_slots curt_childs curt_parent,
              exists curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t,
                get O1 curtid = Some (oscurt t) /\
                get O1 abstcblsid = Some (abstcblist tls) /\
                get tls t = Some (p, st, m, sus) /\
                CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) /\
                nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
                  Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) /\
                (Int.eq (Int.and curt_cap_right (Int.repr CNODE_DELETE_CAP)) Int.zero = true \/
                 (not(curt_parent = p \/ p = p)))/\
                 opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE)) /\ O2 = Some O1)           
end.
*)

Definition user_cnode_delete_slotnum (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      exists dest captype capability v',
          vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
          (Int.ltu (Int.repr CAP_TASK_TYPE) captype = false) /\
          (not((Int.ltu  (Int.repr OS_LOWEST_PRIO) dest = true \/ Int.eq dest (Int.repr OS_LOWEST_PRIO) = true))) /\
          (* check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr SLOT_NUM)), Some O1) /\*)
          opv = Some (Vint32 (Int.repr EINVAL)) /\
          O2 = Some O1         
  end. 

(*
Definition user_cnode_delete_nocap (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
| (opv, O2) => 
  exists dest captype capability v',
      vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
      Int.ltu (Int.repr CAP_TASK_TYPE) captype = false /\
      Int.ltu dest (Int.repr OS_LOWEST_PRIO) = true /\
        exists acspace dest_slots dest_childs dest_parent,
          ( get O1 cspaceid = Some (capcspace acspace) /\
            CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) /\
             (*check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\*)
            exists t tls p st m sus curt_slots curt_childs curt_parent,
            exists curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t,
              get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get tls t = Some (p, st, m, sus) /\
              CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) /\
              nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
                Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) /\
              (Int.eq (Int.and curt_cap_right (Int.repr CNODE_DELETE_CAP)) Int.zero = true \/
                (not(dest_parent = p \/ dest = p)))/\
                opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE)) /\ O2 = Some O1)           
end.
*)

Definition user_cnode_delete_nocap (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
| (opv, O2) => 
  exists dest captype capability v',
      vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
      (opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE)) /\ O2 = Some O1)           
end.


Definition user_cnode_delete_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
    exists dest captype capability v',
        vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
    Int.ltu (Int.repr CAP_TASK_TYPE) captype = false /\
        Int.ltu dest (Int.repr OS_LOWEST_PRIO) = true /\
        Int.eq dest (Int.repr OS_PRIO_SELF) = false /\ 
           exists acspace dest_slots dest_childs dest_parent index,
             (
              check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\
              get O1 cspaceid = Some (capcspace acspace) /\
              CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) /\
              exists t tls p st m sus curt_slots curt_childs curt_parent,
              exists curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t O2',
                get O1 curtid = Some (oscurt t) /\
                get O1 abstcblsid = Some (abstcblist tls) /\
                get tls t = Some (p, st, m, sus) /\
                CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) /\
                nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
                  Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) /\
                (Int.eq (Int.and curt_cap_right (Int.repr CNODE_DELETE_CAP)) Int.zero = false /\
                  (dest_parent = p \/ dest = p)) /\
                ucos_cnode_delete_spec ((Vint32 dest) :: (Vint32 (Int.repr index)) :: v') O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), O2') /\
                opv = Some (Vint32 (Int.repr CNODE_DELETE_SUCCESS)) /\ O2 = O2')
end. 


Definition user_cnode_delete_succ_category (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
    exists dest captype capability v',
        vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        exists acspace slots childs prio 
          slot_type cap_type cap_content cap_right object_t index,
             get O1 cspaceid = Some (capcspace acspace) /\
             CSpaceMod.get acspace dest = Some (slots, childs, prio) /\
             nth_slots (Z.to_nat (Int.unsigned index)) slots =
               Some (slot_type, (cap_type, (cap_content, cap_right, object_t))) /\
               exists acspace' acspace'',
                 acspace' = (CSpaceMod.set acspace dest
                 (update_nth_list slot_val_type (Z.to_nat (Int.unsigned index)) slots
                   (Int.repr SLOT_NULL_CAP, (cap_type, (cap_content, cap_right, object_t))),
                 childs, prio)) /\
                 acspace'' = (CSpaceMod.set acspace' dest
                 (update_nth_list slot_val_type (Z.to_nat (Int.unsigned index)) 
                 (update_nth_list slot_val_type (Z.to_nat (Int.unsigned index)) slots
                 (Int.repr SLOT_NULL_CAP, (cap_type, (cap_content, cap_right, object_t))))
                 (Int.repr SLOT_NULL_CAP, (Int.zero, (Int.zero, Int.zero, object_t))),
                 childs, prio)) /\
               (opv = Some (Vint32 (Int.repr CNODE_DELETE_SUCCESS)) /\
                O2 = Some (set O1 cspaceid (capcspace acspace'')))          
end. 

Definition user_cnode_delete_succ_object (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
    exists dest captype capability v',
        vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        exists acspace slots childs prio 
          slot_type cap_type cap_content cap_right object_t index,
             get O1 cspaceid = Some (capcspace acspace) /\
             CSpaceMod.get acspace dest = Some (slots, childs, prio) /\
             nth_slots (Z.to_nat (Int.unsigned index)) slots =
               Some (slot_type, (cap_type, (cap_content, cap_right, object_t))) /\
               exists acspace' acspace'',
                 acspace' = (CSpaceMod.set acspace dest
                 (update_nth_list slot_val_type (Z.to_nat (Int.unsigned index)) slots
                   (Int.repr SLOT_NULL_CAP, (cap_type, (cap_content, cap_right, object_t))),
                 childs, prio)) /\
                 acspace'' = (CSpaceMod.set acspace' dest
                 (update_nth_list slot_val_type (Z.to_nat (Int.unsigned index)) 
                 (update_nth_list slot_val_type (Z.to_nat (Int.unsigned index)) slots
                 (Int.repr SLOT_NULL_CAP, (cap_type, (cap_content, cap_right, object_t))))
                 (Int.repr SLOT_NULL_CAP, (Int.zero, (Int.zero, cap_right, Vnull))),
                 childs, prio))/\
               (opv = Some (Vint32 (Int.repr CNODE_DELETE_SUCCESS)) /\
                O2 = Some (set O1 cspaceid (capcspace acspace'')))        
end. 
 

(*
Definition user_cnode_delete_dest_noself_succ_object (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
    exists dest captype capability v',
        vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        Int.ltu (Int.repr CAP_TASK_TYPE) captype = false /\
        Int.ltu dest (Int.repr OS_LOWEST_PRIO) = true /\
        Int.eq dest (Int.repr OS_PRIO_SELF) = false /\
           exists acspace dest_slots dest_childs dest_parent index,
             (check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\
             Z.to_nat index < 255 /\  get O1 cspaceid = Some (capcspace acspace) /\
              CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) /\
              exists t tls p st m sus curt_slots curt_childs curt_parent,
              exists curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t O2',
                get O1 curtid = Some (oscurt t) /\
                get O1 abstcblsid = Some (abstcblist tls) /\
                get tls t = Some (p, st, m, sus) /\
                CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) /\
                (dest_parent = p \/ dest = p) /\ 
                nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
                  Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) /\
                Int.eq (Int.and curt_cap_right (Int.repr CNODE_DELETE_CAP)) Int.zero = false /\
                ucos_cnode_delete_object ((Vint32 dest) :: (Vint32 (Int.repr index)) :: v') O1 (Some (Vint32 (Int.repr CNODE_NONE_FAULT)), O2') /\
                opv = Some (Vint32 (Int.repr CNODE_DELETE_SUCCESS)) /\ O2 = O2')
end. 
*)

(*
Definition user_cnode_delete_dest_noself_succ_object_fail (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
match rst with
  | (opv, O2) => 
    exists dest captype capability v',
        vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        Int.ltu (Int.repr CAP_TASK_TYPE) captype = false /\
        Int.ltu dest (Int.repr OS_LOWEST_PRIO) = true /\
        Int.eq dest (Int.repr OS_PRIO_SELF) = false /\
           exists acspace dest_slots dest_childs dest_parent index,
             (check_cap_type_spec ((Vint32 capability) :: (Vint32 captype) :: (Vint32 dest) :: v') O1 (Some (Vint32 (Int.repr index)), Some O1) /\
             Z.to_nat index < 255 /\ get O1 cspaceid = Some (capcspace acspace) /\
              CSpaceMod.get acspace dest = Some (dest_slots, dest_childs, dest_parent) /\
              exists t tls p st m sus curt_slots curt_childs curt_parent,
              exists curt_slot_type curt_cap_type curt_cap_content curt_cap_right curt_object_t O2',
                get O1 curtid = Some (oscurt t) /\
                get O1 abstcblsid = Some (abstcblist tls) /\
                get tls t = Some (p, st, m, sus) /\
                CSpaceMod.get acspace p = Some (curt_slots, curt_childs, curt_parent) /\
                (dest_parent = p \/ dest = p) /\ 
                nth_slots (Z.to_nat SLOT_CNODE_CAP) curt_slots =
                  Some (curt_slot_type, (curt_cap_type, (curt_cap_content, curt_cap_right, curt_object_t))) /\
                Int.eq (Int.and curt_cap_right (Int.repr CNODE_DELETE_CAP)) Int.zero = false /\
                ucos_cnode_delete_failure ((Vint32 dest) :: (Vint32 (Int.repr index)) :: v') O1 (Some (Vint32 (Int.repr CNODE_DELETE_FAILURE)), O2') /\
                opv = Some (Vint32 (Int.repr CNODE_DELETE_FAILURE)) /\ O2 = O2')
end.
*)


Definition user_cnode_delete_spec (vl: vallist) :=
    user_cnode_delete_invalid  (|vl|) ??
    user_cnode_delete_err (|vl|) ??
    user_cnode_delete_failure (|vl|)??
    user_cnode_delete_slotnum (|vl|)??
    user_cnode_delete_nocap (|vl|)??     
    user_cnode_delete_succ_category (|vl|)??
    user_cnode_delete_succ_object (|vl|).

Definition user_cnode_delete_spec' (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
    match rst with
      | (opv, O2) => 
        (exists dest capType capability v',
           vl = ((Vint32 dest) :: (Vint32 capType) :: (Vint32 capability) :: v') /\
            exists r O2', 
              (opv = (Some (Vint32 r)) /\ O2 = Some O2' /\
              user_cnode_delete_rel dest capType capability O1 r O2')
        )
  end.

  
  Definition user_cnode_delete_api :=
  (user_cnode_delete_spec, (Tint8, Tint8 :: Tint8 :: Tint32 :: nil)).

(*user_cnode_revoke*)

Definition user_cnode_revoke_invalid (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
    match rst with
      | (opv, O2) => 
         opv = Some (Vint32 (Int.repr OS_PRIO_INVALID)) /\
         O2 = Some O1 /\
         (exists dest captype capability v',
           vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
           ((Int.ltu  (Int.repr OS_LOWEST_PRIO) dest = true \/ Int.eq dest (Int.repr OS_LOWEST_PRIO) = true))
         )
    end. 

Definition user_cnode_revoke_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        O2 = Some O1 /\
        (exists dest captype capability v',
          vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
          Int.ltu (Int.repr CAP_TASK_TYPE) captype = true
        )
  end. 

Definition user_cnode_revoke_failure (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
    (*这个是没有OSPrioCur这个变量*)
        opv = Some (Vint32 (Int.repr CNODE_REVOKE_FAILURE)) /\
        O2 = Some O1 
end. 
Definition user_cnode_revoke_slotnum (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      exists dest captype capability v',
          vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
          (Int.ltu (Int.repr CAP_TASK_TYPE) captype = false) /\
          (not((Int.ltu  (Int.repr OS_LOWEST_PRIO) dest = true \/ Int.eq dest (Int.repr OS_LOWEST_PRIO) = true))) /\
          O2 = Some O1         
  end.
Definition user_cnode_revoke_nocap (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O2) => 
    exists dest captype capability v',
        vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        (opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE)) /\ O2 = Some O1)           
  end.
  
Definition user_cnode_revoke_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O2) => 
    exists dest captype capability v',
        vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        (opv = Some (Vint32 (Int.repr CNODE_REVOKE_SUCCESS)) /\
        (exists acspace acspace' n_capability,
        get O1 cspaceid = Some(capcspace acspace) /\
        reset_descendents_cspace_slot_abs dest n_capability acspace acspace' /\
        O2 = Some (set O1 cspaceid (capcspace acspace'))) 
        )
  end.


Definition user_cnode_revoke_spec (vl: vallist) :=
  user_cnode_revoke_invalid  (|vl|) ??
  user_cnode_revoke_err (|vl|) ??
  user_cnode_revoke_failure (|vl|)??
  user_cnode_revoke_slotnum (|vl|) ?? 
  user_cnode_revoke_nocap(|vl|) ??
  user_cnode_revoke_succ(|vl|).
Definition user_cnode_revoke_api :=
(user_cnode_revoke_spec, (Tint8, Tint8 :: Tint8 :: Tint32 :: nil)).




