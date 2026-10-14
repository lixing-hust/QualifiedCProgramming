Require Import os_code_defs.
Require Import code_notations.
Require Import os_inv.
Require Import inv_prop.
Require Import pure_lib.
Require Import OSTimeTickPure.
Require Import seplog_tactics.
Require Import evauxvar_lemmas.
Require Import join_lib. 

Open Scope int_scope. 
Open Scope code_scope.

Definition tsk_loc_ev locmp ptrmp t vloc sid :=
  get locmp t = Some (V$ vloc) /\
  exists muxp semp qp,
    get ptrmp t = Some (muxp, semp, qp) /\ 
    (muxp = Vptr sid \/ semp = Vptr sid \/ qp = Vptr sid).


Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by (clear; tauto); 
  destruct h as [Ht | Hf].


Lemma mux_ecb_cre1: 
  forall t locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs eptr semp qp,
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    get locmp t = Some (V$ __EvLoc_ecbcre1) ->
    get ptrmp t = Some (Vptr eptr, semp, qp) ->
    (~ ptr_in_ecblist (Vptr eptr) fecbh fecbvl /\
     ~ eib_ref semeibs muxeibs qeibs eptr /\ get ecbls eptr = None). 
Proof. 
  introv Hmep Hgetl Hgetp.
  unfold MUX_ECB_P in Hmep.
  lets H00: Hmep Hgetp. clear Hmep.
  destruct H00.
  destructs H.
  splits; auto.
  destruct H.
  destructs H. rewrite Hgetl in H. inverts H.
  destructs H. rewrite Hgetl in H. inverts H.
Qed.     

Lemma sem_ecb_cre1: 
  forall t locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs eptr muxp qp, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    get locmp t = Some (V$ __EvLoc_ecbcre1) ->
    get ptrmp t = Some (muxp, Vptr eptr, qp) ->
    (~ ptr_in_ecblist (Vptr eptr) fecbh fecbvl /\
     ~ eib_ref semeibs muxeibs qeibs eptr /\ get ecbls eptr = None). 
Proof. 
  introv Hmep Hgetl Hgetp.
  unfold SEM_ECB_P in Hmep.
  lets H00: Hmep Hgetp. clear Hmep.
  destruct H00.
  destructs H.
  splits; auto.
  destruct H.
  destructs H. rewrite Hgetl in H. inverts H.
  destructs H. rewrite Hgetl in H. inverts H.
Qed.

Lemma q_ecb_cre1:
  forall t locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs eptr muxp semp,  
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    get locmp t = Some (V$ __EvLoc_ecbcre1) ->
    get ptrmp t = Some (muxp, semp, Vptr eptr) ->
    (~ ptr_in_ecblist (Vptr eptr) fecbh fecbvl /\
     ~ eib_ref semeibs muxeibs qeibs eptr /\ get ecbls eptr = None). 
Proof. 
  introv Hmep Hgetl Hgetp.
  unfold Q_ECB_P in Hmep.
  lets H00: Hmep Hgetp. clear Hmep.
  destruct H00.
  clear H0.
  destruct H. 
  destructs H.
  splits; auto.
  destruct H.
  destructs H. rewrite Hgetl in H. inverts H.
  destructs H. 
  destruct H. rewrite Hgetl in H. inverts H. rewrite Hgetl in H. inverts H. 
Qed.  

Lemma mux_ecb_cre2: 
  forall t locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs eptr semp qp,
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    get locmp t = Some (V$ __EvLoc_ecbcre2) -> 
    get ptrmp t = Some (Vptr eptr, semp, qp) ->
    (~ eib_ref semeibs muxeibs qeibs eptr /\ is_mux ecbls eptr).  
Proof.
  introv Hmp Hgetl Hgetp.
  unfold MUX_ECB_P in Hmp.
  lets H00: Hmp Hgetp. clear Hmp.
  destruct H00.
  destructs H. rewrite Hgetl in H. inverts H.
  destruct H. destructs H. splits; auto.
  destruct H. rewrite Hgetl in H. inverts H. 
Qed.

Lemma sem_ecb_cre2:  
  forall t locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs eptr muxp qp, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    get locmp t = Some (V$ __EvLoc_ecbcre2) -> 
    get ptrmp t = Some (muxp, Vptr eptr, qp) ->
    (~ eib_ref semeibs muxeibs qeibs eptr /\ is_sem ecbls eptr).  
Proof.
  introv Hsp Hgetl Hgetp.
  unfold SEM_ECB_P in Hsp.
  lets H00: Hsp Hgetp. clear Hsp.
  destruct H00.
  destructs H. rewrite Hgetl in H. inverts H.
  destruct H. destructs H. splits; auto.
  destruct H. rewrite Hgetl in H. inverts H. 
Qed.

Lemma q_ecb_cre2:  
  forall t locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs eptr muxp semp,   
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    get locmp t = Some (V$ __EvLoc_ecbcre2) -> 
    get ptrmp t = Some (muxp, semp, Vptr eptr) ->
    (~ eib_ref semeibs muxeibs qeibs eptr /\ is_que ecbls eptr).  
Proof.
  introv Hqp Hgetl Hgetp.
  unfold Q_ECB_P in Hqp.
  lets H00: Hqp Hgetp. clear Hqp.
  destruct H00. clear H0.
  destruct H.
  destructs H. rewrite Hgetl in H. inverts H.
  destruct H. destructs H. splits; auto.
  destruct H. destruct H; (rewrite Hgetl in H; tryfalse). 
Qed.

Lemma sem_ecb_nml: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs muxp qp eid ct, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get ptrmp ct = Some (muxp, Vptr eid, qp) ->
    get locmp ct = Some (V$ os_code_defs.__EvLoc_normal) ->
    (is_evt els eid \/ ptr_in_ecblist (Vptr eid) fecbh fecbvl).
Proof.
  introv Hsep Hgetp Hgetl.
  unfold SEM_ECB_P in Hsep.
  lets H00: Hsep Hgetp.
  clear Hsep.
  destruct H00 as [Hcre1 | [Hcre2 | Hdel]]; simpljoin1.
  rewrite Hgetl in H.
  tryfalse.
  rewrite Hgetl in H.
  tryfalse.
  auto.
Qed.   

Lemma ecb_del: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs t eid, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->    
    tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel eid ->
    (is_que ecbls eid /\
     ~ (exists t0,
           (get locmp t0 = Some (V$ __EvLoc_ecbcre1) \/
            get locmp t0 = Some (V$ __EvLoc_ecbcre2)) /\
           evptr_of_tsk t0 ptrmp eid) /\
     ~ eib_ref semeibs muxeibs mqeibs eid). 
Proof.
  introv Hsep Hmep Hqep Htle.
  unfold tsk_loc_ev in Htle. 
  destruct Htle as (Hgetl & mp & sp & qp & Hgetp & Hor3).
  destruct Hor3 as [Hmp | [Hsp | Hqp]]; subst.
  - 
    unfold MUX_ECB_P in Hmep.
    lets H00: Hmep Hgetp.
    rewrite Hgetl in H00.
    destruct H00.
    simpljoin1. tryfalse.  
    destruct H. 
    simpljoin1. tryfalse.
    simpljoin1. tryfalse.
  -
    unfold SEM_ECB_P in Hsep.
    lets H00: Hsep Hgetp.
    rewrite Hgetl in H00.
    destruct H00.
    simpljoin1. tryfalse.  
    destruct H. 
    simpljoin1. tryfalse.
    simpljoin1. tryfalse.
  -
    unfold Q_ECB_P in Hqep.
    lets H00: Hqep Hgetp.
    destruct H00.
    clear -H0 Hgetl.
    apply H0; auto.
Qed.   

Lemma n_ptr_in_ecblist_tail: 
  forall eptr sid p vl vll, 
    ~ ptr_in_ecblist (Vptr eptr) (Vptr sid) (vl :: vll) ->
    V_OSEventListPtr vl = Some (Vptr p) -> 
    ~ ptr_in_ecblist (Vptr eptr) (Vptr p) vll. 
Proof.
  introv Hnin Hnxtp Hin.
  apply Hnin.
  unfold ptr_in_ecblist.
  unfold ptr_in_ecblist in Hin.
  unfold ptr_in_ecbsllseg; fold ptr_in_ecbsllseg.
  destruct (beq_val (Vptr eptr) (Vptr sid)) eqn: E.
  auto.
  rewrite Hnxtp.
  auto.
Qed.   

Lemma ptr_in_ecblist_tail: 
  forall eptr sid hd' vl vll, 
    ptr_in_ecblist (Vptr eptr) (Vptr sid) (vl :: vll) ->
    eptr <> sid ->
    V_OSEventListPtr vl = Some hd' -> 
    isptr hd' -> 
    ptr_in_ecblist (Vptr eptr) hd' vll. 
Proof.
  introv Hin Hneq Hnxt Hisptr.
  unfold ptr_in_ecblist in *.
  unfold ptr_in_ecbsllseg in Hin.
  fold ptr_in_ecbsllseg in Hin.
  assert (Hfalse: beq_val (Vptr eptr) (Vptr sid) = false).
  {
    unfold beq_val. unfold os_inv.beq_addrval.
    destruct eptr. destruct sid.
    destruct (beq_pos b b0) eqn: E1;
      destruct (Int.eq i i0) eqn: E2;
      simpl; auto.
    assert (b = b0). 
    { rewrite beq_pos_Pos_eqb_eq in E1. rewrite Pos.eqb_eq in E1. auto. }
    assert (i = i0).
    {
      lets H00: Int.eq_spec.
      specialize (H00 i i0).
      rewrite E2 in H00.
      auto.
    }
    subst.
    false.
  } 
  rewrite Hfalse in Hin.
  rewrite Hnxt in Hin.
  auto.
Qed.     

Lemma ptr_in_freelist_notcre1_: 
  forall locmp ptrmp ecbls fhp fecbvl semeibs muxeibs qeibs t muxp semp qp a, 
    SEM_ECB_P locmp ptrmp ecbls (Vptr fhp) fecbvl semeibs muxeibs qeibs ->
    MUX_ECB_P locmp ptrmp ecbls (Vptr fhp) fecbvl semeibs muxeibs qeibs ->
    Q_ECB_P locmp ptrmp ecbls (Vptr fhp) fecbvl semeibs muxeibs qeibs ->
    ptr_in_ecblist (Vptr a) (Vptr fhp) fecbvl -> 
    get locmp t = Some (Vint32 (Int.repr __EvLoc_ecbcre1)) ->
    get ptrmp t = Some (muxp, semp, qp) ->
    (muxp <> Vptr a /\ semp <>  Vptr a /\ qp <> Vptr a). 
Proof. 
  introv Hsp Hmp Hqp Hin Hgetl Hgetp.
  splits. 
  - introv Hf. subst muxp.
    lets H00: mux_ecb_cre1 Hmp Hgetl Hgetp.
    destructs H00. apply H in Hin. tryfalse.
  - introv Hf. subst semp.
    lets H00: sem_ecb_cre1 Hsp Hgetl Hgetp. 
    destructs H00. apply H in Hin. tryfalse. 
  - introv Hf. subst qp. 
    lets H00: q_ecb_cre1 Hqp Hgetl Hgetp.
    destructs H00. apply H in Hin. tryfalse. 
Qed.   

Lemma ptr_in_freelist_notcre1:
  forall locmp ptrmp ecbls fhp fecbvl semeibs muxeibs qeibs a, 
    SEM_ECB_P locmp ptrmp ecbls (Vptr fhp) fecbvl semeibs muxeibs qeibs ->
    MUX_ECB_P locmp ptrmp ecbls (Vptr fhp) fecbvl semeibs muxeibs qeibs ->
    Q_ECB_P locmp ptrmp ecbls (Vptr fhp) fecbvl semeibs muxeibs qeibs ->
    ptr_in_ecblist (Vptr a) (Vptr fhp) fecbvl -> 
    ~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 a.
Proof.
  introv Hsp Hmp Hqp Hin Hex.
  destruct Hex as (t & Htle).
  unfold tsk_loc_ev in Htle.
  destruct Htle.
  destruct H0 as (muxp & semp & qp & (Hptr & Hor)).
  lets H00: ptr_in_freelist_notcre1_ Hsp Hmp Hqp Hin H.
  lets H0: H00 Hptr. clear H00.
  intuition.
Qed.


Lemma not_in_els_notcre2_:
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs a muxp semp qp t,
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get ecbls a = None ->
    get locmp t = Some (Vint32 (Int.repr __EvLoc_ecbcre2)) ->
    get ptrmp t = Some (muxp, semp, qp) ->
    (muxp <> Vptr a /\ semp <> Vptr a /\ qp <> Vptr a).
Proof.
  introv Hsep Hmep Hqep Hnone Hgetl Hgetp.
  splits.
  intro Hf.
  subst muxp.
  lets H00: mux_ecb_cre2 Hmep Hgetl Hgetp.
  destruct H00. unfold is_mux in H0.
  simpljoin1.
  unfold get in Hnone. destruct EcbMap.
  unfold Maps.get in H0.
  rewrite Hnone in H0. inverts H0.
  intro Hf.
  subst semp.
  lets H00: sem_ecb_cre2 Hsep Hgetl Hgetp.
  destruct H00. unfold is_sem in H0.
  simpljoin1.
  unfold get in Hnone. destruct EcbMap.
  unfold Maps.get in H0.
  rewrite Hnone in H0. inverts H0.
  introv Hf.
  subst qp.
  lets H00: q_ecb_cre2 Hqep Hgetl Hgetp.
  destruct H00. unfold is_que in H0.
  simpljoin1.
  unfold get in Hnone. destruct EcbMap.
  unfold Maps.get in H0.
  rewrite Hnone in H0. inverts H0.
Qed.

Lemma not_in_els_notcre2:
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs a, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs -> 
    get ecbls a = None -> 
    ~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 a. 
Proof.
  introv Hsep Hmep Hqep Hnone Hex.
  destruct Hex as (t & Htle).
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hcre2 & Hptr).
  destruct Hptr as (mp & sp & qp & (Hget & Hor)).
  lets H00: not_in_els_notcre2_ Hsep Hmep Hqep Hnone Hcre2.
  lets H0: H00 Hget. clear H00.
  intuition.
Qed.   

Lemma not_in_els_notdel: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs a, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs -> 
    get ecbls a = None -> 
    ~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel a.
Proof.
  introv Hsep Hmep Hqep Hnone Hex.
  destruct Hex as (t & Htle).
  (* unfold MUX_ECB_P in Hmep. *)
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hdel & (mp & sp & qp & Hptr & Hor)).
  destruct Hor as [Hmptr | [Hsptr | Hqptr]].
  -
    subst.
    lets H00: Hmep Hptr.
    rewrite Hdel in H00.
    inverts H00.
    simpljoin1. inverts H.
    inverts H. simpljoin1. inverts H.
    simpljoin1.  inverts H.
  -
    subst.
    lets H00: Hsep Hptr.
    rewrite Hdel in H00.
    inverts H00.
    simpljoin1. inverts H.
    inverts H. simpljoin1. inverts H.
    simpljoin1.  inverts H.
  -
    subst.
    lets H00: Hqep Hptr. 
    simpljoin1.
    lets H00: H0 Hdel. clear H0.
    destruct H00 as (Hisque & _ & _).
    unfold is_que in Hisque.
    simpljoin1.
    unfold get in Hnone, H0.
    unfold EcbMap in Hnone, H0. 
    rewrite Hnone in H0.
    inverts H0.
Qed.   

Lemma inactive_ecb_no_eib_ref: 
  forall eptr ecbls semeibs muxeibs qeibs, 
    get ecbls eptr = None -> 
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    ~ eib_ref semeibs muxeibs qeibs eptr.  
Proof. 
  introv Hnone Hsem Hmux Hque Heibref.
  unfold eib_ref in Heibref.
  destruct Heibref as [Hseibref | [Hmeibref | Hqeibref]].
  + unfold RH_SEM_EINFO_ECB_P in Hsem.
    unfold semeib_ref in Hseibref.
    destruct Hseibref as (pos & tp & sc & Hget).
    apply Hsem in Hget.
    rewrite Hnone in Hget. simpljoin1. tryfalse.
  + unfold RH_ECBlk_EIBlk_Mux_P in Hmux.
    unfold muxeib_ref in Hmeibref.
    destruct Hmeibref as (pos & owr & tp & cnt & ptr & ptc & wq0 & cs & mc & Hget).
    lets H00: Hmux Hget.
    specialize (H00 (eq_refl _)).
    simpljoin1.
    unfold get in Hnone. unfold EcbMap in Hnone.
    unfold get in H. unfold EcbMap in H.
    rewrite Hnone in H.
    tryfalse.
  + unfold RH_EIBlk_ECBlk_Q_P in Hque.
    unfold mqeib_ref in Hqeibref.
    destruct Hqeibref as (pos0 & tp & flgs & mms & msz & cms & mqc & Hget).
    apply Hque in Hget. 
    unfold get in Hnone. unfold EcbMap in Hnone.
    unfold get in Hget. unfold EcbMap in Hget.
    rewrite Hnone in Hget.
    simpljoin1. tryfalse. 
Qed.   

Lemma eibref_distinct_semref_nmuxref:
  forall semeibs muxeibs mqeibs eid, 
    eibref_distinct semeibs muxeibs mqeibs ->
    semeib_ref semeibs eid ->
    ~muxeib_ref muxeibs eid. 
Proof.
  introv Hd Hsr Hmr.
  unfold eibref_distinct in Hd.
  lets H00: Hd eid.
  clear Hd.
  destruct H00 as (Hst & Hsd & Hmd & Hqd).
  unfold evref_same_type in Hst.
  simpljoin1.
  apply H in Hsr.
  simpljoin1.
  tryfalse.
Qed.

Lemma eibref_distinct_semref_nmqref:
  forall semeibs muxeibs mqeibs eid, 
    eibref_distinct semeibs muxeibs mqeibs ->
    semeib_ref semeibs eid ->
    ~mqeib_ref mqeibs eid. 
Proof.
  introv Hd Hsr Hmr.
  unfold eibref_distinct in Hd.
  lets H00: Hd eid.
  clear Hd.
  destruct H00 as (Hst & Hsd & Hmd & Hqd).
  unfold evref_same_type in Hst.
  simpljoin1.
  apply H in Hsr.
  simpljoin1.
  tryfalse.
Qed.
  

(*************** lemmas for  the use of semaphores *****************)

Lemma evdel_nodup_normal_semptr_preserve: 
  forall locmp ptrmp tid sid, 
    evdel_nodup locmp ptrmp ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    evdel_nodup locmp (set ptrmp tid (Vnull, Vptr sid, Vnull)). 
Proof.
  introv Hnd Hgetl Hgetp.
  unfold evdel_nodup in *.
  introv Hneq Hgetl1 Hgetl2 Hptr1 Hptr2.
  casetac t1 tid Ht Hf.
  subst.
  rewrite Hgetl in Hgetl1. tryfalse.
  unfold evptr_of_tsk in Hptr1. 
  rewrite set_a_get_a' in Hptr1; eauto.
  casetac t2 tid Ht' Hf'.
  subst.
  rewrite Hgetl in Hgetl2. tryfalse.
  unfold evptr_of_tsk in Hptr2.
  rewrite set_a_get_a' in Hptr2; eauto.
Qed.    

Lemma evcre_nodup_normal_semptr_preserve: 
  forall locmp ptrmp tid sid, 
    evcre_nodup locmp ptrmp ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    evcre_nodup locmp (set ptrmp tid (Vnull, Vptr sid, Vnull)). 
Proof.
  introv Hnd Hgetl Hgetp.
  unfold evcre_nodup in *.
  introv Hneq Hgetl1 Hgetl2 Hptr1 Hptr2.
  casetac t1 tid Ht Hf.
  subst.
  rewrite Hgetl in Hgetl1. destruct Hgetl1; tryfalse.
  unfold evptr_of_tsk in Hptr1. 
  rewrite set_a_get_a' in Hptr1; eauto.
  casetac t2 tid Ht' Hf'.
  subst.
  rewrite Hgetl in Hgetl2. destruct Hgetl2; tryfalse.
  unfold evptr_of_tsk in Hptr2.
  rewrite set_a_get_a' in Hptr2; eauto.
Qed.    

Lemma sem_ecb_p_semptr_normal_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs eid tid, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) ->
    is_sem els eid ->
    SEM_ECB_P locmp (set ptrmp tid (Vnull, Vptr eid, Vnull)) els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hsep Hgetl Hgetp Hsem.
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
    right. right.
    splits; auto.
    left. unfold is_evt. left; auto.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
Qed.   

Lemma mux_ecb_p_semptr_normal_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs eid tid, 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) ->
    is_sem els eid ->
    MUX_ECB_P locmp (set ptrmp tid (Vnull, Vptr eid, Vnull)) els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hmep Hgetl Hgetp Hsem.
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
Qed.   

Lemma mq_ecb_p_semptr_normal_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs eid tid, 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) ->
    is_sem els eid ->
    Q_ECB_P locmp (set ptrmp tid (Vnull, Vptr eid, Vnull)) els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hqep Hgetl Hgetp Hsem.
  unfold Q_ECB_P in *.
  introv Hgetp'.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    destruct H00 as (Hor3 & Hdel).
    split.
    auto. 
    introv Hdel'.
    apply Hdel in Hdel'.
    simpljoin.
    splits; auto.
    introv Hex.
    apply H0.
    simpljoin1.
    casetac x tid Ht' Hf'.
    subst.
    rewrite Hgetl in H2. destruct H2; tryfalse. 
    unfold evptr_of_tsk in H3. 
    rewrite set_a_get_a' in H3; eauto.
Qed.

Lemma evdel_nodup_set_null3_preserve:  
  forall locmp ptrmp tid, 
    evdel_nodup locmp ptrmp ->
    evdel_nodup locmp (set ptrmp tid (Vnull, Vnull, Vnull)). 
Proof.
  introv Hnd.
  unfold evdel_nodup in *.
  introv Hne Hgetl1 Hgetl2 Het1 Het2.
  unfold evptr_of_tsk in Het1.
  unfold evptr_of_tsk in Het2. 
  casetac t1 tid Ht Hf.
  subst.
  rewrite set_a_get_a in Het1.
  destruct Het1. simpljoin1; tryfalse.
  destruct H. simpljoin1. tryfalse.
  simpljoin1. tryfalse.
  rewrite set_a_get_a' in Het1; eauto.
  casetac t2 tid Ht' Hf'.
  subst.
  rewrite set_a_get_a in Het2. 
  destruct Het2.
  simpljoin1; tryfalse.
  destruct H.
  simpljoin1; tryfalse.
  simpljoin1; tryfalse.
  rewrite set_a_get_a' in Het2; eauto.
Qed. 

Lemma evcre_nodup_set_null3_preserve:   
  forall locmp ptrmp tid, 
    evcre_nodup locmp ptrmp ->
    evcre_nodup locmp (set ptrmp tid (Vnull, Vnull, Vnull)). 
Proof.
  introv Hnd.
  unfold evcre_nodup in *.
  introv Hne Hgetl1 Hgetl2 Het1 Het2.
  unfold evptr_of_tsk in Het1.
  unfold evptr_of_tsk in Het2. 
  casetac t1 tid Ht Hf.
  subst.
  rewrite set_a_get_a in Het1.
  destruct Het1. simpljoin1; tryfalse.
  destruct H. simpljoin1. tryfalse.
  simpljoin1. tryfalse.
  rewrite set_a_get_a' in Het1; eauto.
  casetac t2 tid Ht' Hf'.
  subst.
  rewrite set_a_get_a in Het2. 
  destruct Het2.
  simpljoin1; tryfalse.
  destruct H.
  simpljoin1; tryfalse.
  simpljoin1; tryfalse.
  rewrite set_a_get_a' in Het2; eauto.
Qed. 

Lemma sem_ecb_p_set_null3_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs tid, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    SEM_ECB_P locmp (set ptrmp tid (Vnull, Vnull, Vnull)) els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hsep.
  unfold SEM_ECB_P in *.
  introv Hgetp.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp.
    inverts Hgetp.
  -
    rewrite set_a_get_a' in Hgetp; eauto.
Qed.    

Lemma mux_ecb_p_set_null3_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs tid, 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    MUX_ECB_P locmp (set ptrmp tid (Vnull, Vnull, Vnull)) els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hmep.
  unfold MUX_ECB_P in *.
  introv Hgetp.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp.
    inverts Hgetp.
  -
    rewrite set_a_get_a' in Hgetp; eauto.
Qed.

Lemma mq_ecb_p_set_null3_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs tid, 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    Q_ECB_P locmp (set ptrmp tid (Vnull, Vnull, Vnull)) els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hqep.
  unfold Q_ECB_P in *. 
  introv Hgetp.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp.
    inverts Hgetp.
  -
    rewrite set_a_get_a' in Hgetp; eauto.
    lets H00: Hqep Hgetp.
    clear Hqep.
    destruct H00 as (Hor3 & Hdel).
    split; eauto.
    introv Hgetl.
    apply Hdel in Hgetl.
    clear Hdel.
    simpljoin1.
    splits; auto.
    introv Hex. apply H0.
    simpljoin1.
    unfold evptr_of_tsk in H3.
    casetac x tid Heq Hneq.
    subst.
    rewrite set_a_get_a in H3.
    destruct H3.
    simpljoin1; tryfalse.
    destruct H3. simpljoin1; tryfalse. simpljoin1; tryfalse.
    rewrite set_a_get_a' in H3; eauto. 
Qed.      


(*************** preservation for OSSemAccept/OSSemPend *****************) 

Lemma sem_ecb_p_sem_minus_one_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs n wls sid, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    get els sid = Some (abssem n, wls) -> 
    SEM_ECB_P locmp ptrmp (set els sid (abssem (n -ᵢ Int.one), wls)) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hsep Hget.
  unfold SEM_ECB_P in *.
  introv Hgetp.
  lets H00: Hsep Hgetp.
  clear Hsep.
  destruct H00 as [Hcre1 | [Hcre2 | Hnm]].
  -
    simpljoin1.
    left. splits; auto. 
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    unfold is_sem.
    casetac sid eptr Ht Hf.
    subst.
    rewrite set_a_get_a.
    do 2 eexists; eauto.
    rewrite set_a_get_a'; eauto. 
  -
    right; right.
    simpljoin1.
    splits; auto.
    destruct H0.
    2: { right. auto. }
    left.
    unfold is_evt.
    casetac sid eptr Ht' Hf'.
    subst.
    left. unfold is_sem. rewrite set_a_get_a.
    do 2 eexists; eauto.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a'; eauto.
Qed. 

Lemma mux_ecb_p_sem_minus_one_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs n wls sid, 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    get els sid = Some (abssem n, wls) -> 
    MUX_ECB_P locmp ptrmp (set els sid (abssem (n -ᵢ Int.one), wls)) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hmep Hget.
  unfold MUX_ECB_P in *.
  introv Hgetp.
  lets H00: Hmep Hgetp.
  clear Hmep.
  destruct H00 as [Hcre1 | [Hcre2 | Hnm]].
  - 
    simpljoin1.
    left. splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    casetac sid eptr Ht hf.
    subst.
    unfold is_mux in H1.
    simpljoin1.
    rewrite Hget in H1.
    inverts H1.
    unfold is_mux.
    rewrite set_a_get_a'; eauto.
  -
    right; right.
    simpljoin1.
    splits; auto.
    destruct H0.
    2: { right; auto. }
    left.
    unfold is_evt.
    casetac sid eptr Ht Hf.
    subst.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a; eauto.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a'; eauto.
Qed.   

Lemma mq_ecb_p_sem_minus_one_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs n wls sid, 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    get els sid = Some (abssem n, wls) -> 
    Q_ECB_P locmp ptrmp (set els sid (abssem (n -ᵢ Int.one), wls)) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hqep Hget.
  unfold Q_ECB_P in *.
  introv Hgetp.
  lets H00: Hqep Hgetp.
  clear Hqep.
  destruct H00 as (Hor3 & Hdel).
  split. 
  destruct Hor3 as [Hcre1 | [Hcre2 | Hnm]].
  - 
    simpljoin1.
    left. splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    casetac sid eptr Ht hf.
    subst.
    unfold is_que in H1.
    simpljoin1.
    rewrite Hget in H1.
    inverts H1.
    unfold is_que.
    rewrite set_a_get_a'; eauto.
  -
    right; right.
    simpljoin1.
    splits; auto.
    destruct H0.
    2: { right; auto. }
    left.
    unfold is_evt.
    casetac sid eptr Ht Hf.
    subst.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a; eauto.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a'; eauto.
  -
    introv Hdel'.
    specialize (Hdel Hdel').
    simpljoin1.
    splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold is_que in H.
    simpljoin1.
    rewrite Hget in H.
    inverts H.
    unfold is_que.
    rewrite set_a_get_a'; eauto.
Qed.   



Lemma sem_ecb_p_sem_set_wls'_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs n wls wls' sid, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    get els sid = Some (abssem n, wls) -> 
    SEM_ECB_P locmp ptrmp (set els sid (abssem n, wls')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hsep Hget.
  unfold SEM_ECB_P in *.
  introv Hgetp.
  lets H00: Hsep Hgetp.
  clear Hsep.
  destruct H00 as [Hcre1 | [Hcre2 | Hnm]].
  -
    simpljoin1.
    left. splits; auto. 
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    unfold is_sem.
    casetac sid eptr Ht Hf.
    subst.
    rewrite set_a_get_a.
    do 2 eexists; eauto.
    rewrite set_a_get_a'; eauto. 
  -
    right; right.
    simpljoin1.
    splits; auto.
    destruct H0.
    2: { right. auto. }
    left.
    unfold is_evt.
    casetac sid eptr Ht' Hf'.
    subst.
    left. unfold is_sem. rewrite set_a_get_a.
    do 2 eexists; eauto.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a'; eauto.
Qed. 

Lemma mux_ecb_p_sem_set_wls'_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs n wls wls' sid,  
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    get els sid = Some (abssem n, wls) -> 
    MUX_ECB_P locmp ptrmp (set els sid (abssem n, wls')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hmep Hget.
  unfold MUX_ECB_P in *.
  introv Hgetp.
  lets H00: Hmep Hgetp.
  clear Hmep.
  destruct H00 as [Hcre1 | [Hcre2 | Hnm]].
  - 
    simpljoin1.
    left. splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    casetac sid eptr Ht hf.
    subst.
    unfold is_mux in H1.
    simpljoin1.
    rewrite Hget in H1.
    inverts H1.
    unfold is_mux.
    rewrite set_a_get_a'; eauto.
  -
    right; right.
    simpljoin1.
    splits; auto.
    destruct H0.
    2: { right; auto. }
    left.
    unfold is_evt.
    casetac sid eptr Ht Hf.
    subst.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a; eauto.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a'; eauto.
Qed.   

Lemma mq_ecb_p_sem_set_wls'_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs n wls wls' sid,  
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    get els sid = Some (abssem n, wls) -> 
    Q_ECB_P locmp ptrmp (set els sid (abssem n, wls')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hqep Hget.
  unfold Q_ECB_P in *.
  introv Hgetp.
  lets H00: Hqep Hgetp.
  clear Hqep.
  destruct H00 as (Hor3 & Hdel).
  split. 
  destruct Hor3 as [Hcre1 | [Hcre2 | Hnm]].
  - 
    simpljoin1.
    left. splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    casetac sid eptr Ht hf.
    subst.
    unfold is_que in H1.
    simpljoin1.
    rewrite Hget in H1.
    inverts H1.
    unfold is_que.
    rewrite set_a_get_a'; eauto.
  -
    right; right.
    simpljoin1.
    splits; auto.
    destruct H0.
    2: { right; auto. }
    left.
    unfold is_evt.
    casetac sid eptr Ht Hf.
    subst.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a; eauto.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a'; eauto.
  -
    introv Hdel'.
    specialize (Hdel Hdel').
    simpljoin1.
    splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold is_que in H.
    simpljoin1.
    rewrite Hget in H.
    inverts H.
    unfold is_que.
    rewrite set_a_get_a'; eauto.
Qed.



(*************** preservation for OSSemPost *****************) 

Lemma sem_ecb_p_sem_inc_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs n wls sid, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    get els sid = Some (abssem n, wls) -> 
    SEM_ECB_P locmp ptrmp (set els sid (abssem (n +ᵢ Int.one), wls)) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hsep Hget.
  unfold SEM_ECB_P in *.
  introv Hgetp.
  lets H00: Hsep Hgetp.
  clear Hsep.
  destruct H00 as [Hcre1 | [Hcre2 | Hnm]].
  -
    simpljoin1.
    left. splits; auto. 
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    unfold is_sem.
    casetac sid eptr Ht Hf.
    subst.
    rewrite set_a_get_a.
    do 2 eexists; eauto.
    rewrite set_a_get_a'; eauto. 
  -
    right; right.
    simpljoin1.
    splits; auto.
    destruct H0.
    2: { right. auto. }
    left.
    unfold is_evt.
    casetac sid eptr Ht' Hf'.
    subst.
    left. unfold is_sem. rewrite set_a_get_a.
    do 2 eexists; eauto.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a'; eauto.
Qed. 

Lemma mux_ecb_p_sem_inc_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs n wls sid, 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    get els sid = Some (abssem n, wls) -> 
    MUX_ECB_P locmp ptrmp (set els sid (abssem (n +ᵢ Int.one), wls)) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hmep Hget.
  unfold MUX_ECB_P in *.
  introv Hgetp.
  lets H00: Hmep Hgetp.
  clear Hmep.
  destruct H00 as [Hcre1 | [Hcre2 | Hnm]].
  - 
    simpljoin1.
    left. splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    casetac sid eptr Ht hf.
    subst.
    unfold is_mux in H1.
    simpljoin1.
    rewrite Hget in H1.
    inverts H1.
    unfold is_mux.
    rewrite set_a_get_a'; eauto.
  -
    right; right.
    simpljoin1.
    splits; auto.
    destruct H0.
    2: { right; auto. }
    left.
    unfold is_evt.
    casetac sid eptr Ht Hf.
    subst.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a; eauto.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a'; eauto.
Qed.   

Lemma mq_ecb_p_sem_inc_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs n wls sid, 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    get els sid = Some (abssem n, wls) -> 
    Q_ECB_P locmp ptrmp (set els sid (abssem (n +ᵢ Int.one), wls)) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hqep Hget.
  unfold Q_ECB_P in *.
  introv Hgetp.
  lets H00: Hqep Hgetp.
  clear Hqep.
  destruct H00 as (Hor3 & Hdel).
  split. 
  destruct Hor3 as [Hcre1 | [Hcre2 | Hnm]].
  - 
    simpljoin1.
    left. splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    casetac sid eptr Ht hf.
    subst.
    unfold is_que in H1.
    simpljoin1.
    rewrite Hget in H1.
    inverts H1.
    unfold is_que.
    rewrite set_a_get_a'; eauto.
  -
    right; right.
    simpljoin1.
    splits; auto.
    destruct H0.
    2: { right; auto. }
    left.
    unfold is_evt.
    casetac sid eptr Ht Hf.
    subst.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a; eauto.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a'; eauto.
  -
    introv Hdel'.
    specialize (Hdel Hdel').
    simpljoin1.
    splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold is_que in H.
    simpljoin1.
    rewrite Hget in H.
    inverts H.
    unfold is_que.
    rewrite set_a_get_a'; eauto.
Qed.

(*************** preservation for OSMutex *****************) 

Lemma sem_ecb_p_mutex_set_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs wls wls' sid pip pip' o o', 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    get els sid = Some (absmutexsem pip o, wls) -> 
    SEM_ECB_P locmp ptrmp (set els sid (absmutexsem pip' o', wls')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hsep Hget.
  unfold SEM_ECB_P in *.
  introv Hgetp.
  lets H00: Hsep Hgetp.
  clear Hsep.
  destruct H00 as [Hcre1 | [Hcre2 | Hnm]].
  -
    simpljoin1.
    left. splits; auto. 
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    unfold is_sem in *.
    casetac sid eptr Ht Hf.
    subst.
    rewrite Hget in H1.
    simpljoin. inverts H1.
    rewrite set_a_get_a'; eauto. 
  -
    right; right.
    simpljoin1.
    splits; auto.
    destruct H0; auto.
    left.
    unfold is_evt.
    casetac sid eptr Ht' Hf'.
    subst.
    right. left. unfold is_mux. rewrite set_a_get_a.
    do 3 eexists; eauto.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a'; eauto.
Qed. 

Lemma mux_ecb_p_mux_set_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs wls wls' sid pip pip' o o', 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
     get els sid = Some (absmutexsem pip o, wls) -> 
    MUX_ECB_P locmp ptrmp (set els sid (absmutexsem pip' o', wls')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hmep Hget.
  unfold MUX_ECB_P in *.
  introv Hgetp.
  lets H00: Hmep Hgetp.
  clear Hmep.
  destruct H00 as [Hcre1 | [Hcre2 | Hnm]].
  - 
    simpljoin1.
    left. splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    unfold is_mux  in *.
    casetac sid eptr Ht hf.
    subst.
    rewrite set_a_get_a. eauto.
    rewrite set_a_get_a'; eauto.
  -
    right; right.
    simpljoin1.
    splits; auto.
    destruct H0; auto.
    left.
    unfold is_evt.
    casetac sid eptr Ht Hf.
    subst.
    right; left.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a; eauto.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a'; eauto.
Qed.   

Lemma mq_ecb_p_mux_set_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs wls wls' sid pip pip' o o', 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    get els sid = Some  (absmutexsem pip o, wls) -> 
    Q_ECB_P locmp ptrmp (set els sid (absmutexsem pip' o', wls')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hqep Hget.
  unfold Q_ECB_P in *.
  introv Hgetp.
  lets H00: Hqep Hgetp.
  clear Hqep.
  destruct H00 as (Hor3 & Hdel).
  split. 
  destruct Hor3 as [Hcre1 | [Hcre2 | Hnm]].
  - 
    simpljoin1.
    left. splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    casetac sid eptr Ht hf.
    subst.
    unfold is_que in H1.
    simpljoin1.
    rewrite Hget in H1.
    inverts H1.
    unfold is_que.
    rewrite set_a_get_a'; eauto.
  -
    right; right.
    simpljoin1.
    splits; auto.
    destruct H0; auto.
    left.
    unfold is_evt.
    casetac sid eptr Ht Hf.
    subst.
    right; left.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a; eauto.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a'; eauto.
  -
    introv Hdel'.
    specialize (Hdel Hdel').
    simpljoin1.
    splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold is_que in H.
    simpljoin1.
    rewrite Hget in H.
    inverts H.
    unfold is_que.
    rewrite set_a_get_a'; eauto.
Qed.

(* used for mutexcre *)

Require Import seplog_lemmas.

Lemma semecb_semnull_preserve:
  forall t0 locmp ptrmp muxp qp ecbls semeibs muxeibs qeibs v', 
    get ptrmp t0 = Some (muxp, Vnull, qp) -> 
    SEM_ECB_P locmp ptrmp ecbls Vnull nil semeibs muxeibs qeibs -> 
    SEM_ECB_P (set locmp t0 v') ptrmp ecbls Vnull nil semeibs muxeibs qeibs.  
Proof.
  introv Hget Hsp.
  unfold SEM_ECB_P in *.
  introv Hgett.
  assert (Hor: t = t0 \/ t <> t0) by tauto.
  destruct Hor.
  - subst.
    rewrite Hgett in Hget.
    inverts Hget.
  - lets H00: Hsp Hgett.
    asserts_rewrite (get (set locmp t0 v') t = get locmp t). 
    { join auto. }
    auto.
Qed.   

Lemma muxecb_semnull_preserve:
  forall t0 locmp ptrmp qp ecbls semeibs muxeibs qeibs v', 
    get ptrmp t0 = Some (Vnull, Vnull, qp) -> 
    MUX_ECB_P locmp ptrmp ecbls Vnull nil semeibs muxeibs qeibs -> 
    MUX_ECB_P (set locmp t0 v') ptrmp ecbls Vnull nil semeibs muxeibs qeibs.  
Proof.
  introv Hget Hmp.
  unfold MUX_ECB_P in *.
  introv Hgett.
  assert (Hor: t = t0 \/ t <> t0) by tauto.
  destruct Hor.
  - subst.
    rewrite Hget in Hgett.
    inverts Hgett.
  - lets H00: Hmp Hgett.
    asserts_rewrite (get (set locmp t0 v') t = get locmp t). 
    { join auto. }
    auto.
Qed.

Lemma qecb_semnull_preserve:
  forall t0 locmp ptrmp ecbls semeibs muxeibs qeibs v', 
    get ptrmp t0 = Some (Vnull, Vnull, Vnull) ->  
    Q_ECB_P locmp ptrmp ecbls Vnull nil semeibs muxeibs qeibs -> 
    Q_ECB_P (set locmp t0 v') ptrmp ecbls Vnull nil semeibs muxeibs qeibs.  
Proof.
  introv Hget Hmp.
  unfold Q_ECB_P in *.
  introv Hgett.
  assert (Hor: t = t0 \/ t <> t0) by tauto.
  destruct Hor.
  - subst.
    rewrite Hget in Hgett.
    inverts Hgett.
  - lets H00: Hmp Hgett.
    asserts_rewrite (get (set locmp t0 v') t = get locmp t). 
    { join auto. }
    destruct H00. splits; auto.
    introv Hgetl.
    apply H1 in Hgetl.
    destructs Hgetl.
    splits; auto.
    introv Hf. apply H3. 
    simpljoin1.
    exists x.
    splits; auto. 
    assert (Hcs: x = t0 \/ x <> t0) by tauto.
    destruct Hcs.
    subst.
    unfold evptr_of_tsk in H6.
    destruct H6.
    simpljoin1. rewrite Hget in H6. inverts H6.
    destruct H6.
    simpljoin1. rewrite Hget in H6. inverts H6. 
    simpljoin1. rewrite Hget in H6. inverts H6.
    asserts_rewrite (get (set locmp t0 v') x = get locmp x) in H5. 
    { join auto. }
    auto.
Qed.

Lemma cre_nodup_null_cre1_preserve:
  forall t locmp ptrmp,
    get ptrmp t = Some (Vnull, Vnull, Vnull) ->
    evcre_nodup locmp ptrmp ->
    evcre_nodup (set locmp t (V$ __EvLoc_ecbcre1)) ptrmp. 
Proof.
  introv Hget Hnd.
  unfold evcre_nodup in *.
  introv Hneqt Hget1 Hget2 Hevp1 Hevp2.
  assert (Hor1: t1 = t \/ t1 <> t) by tauto.
  destruct Hor1.
  - subst.
    unfold evptr_of_tsk in Hevp1.
    destruct Hevp1. simpljoin1. tryfalse.
    destruct H. simpljoin1. tryfalse. simpljoin1. tryfalse.
  - assert (Hor2: t2 = t \/ t2 <> t) by tauto.
    destruct Hor2.
    + subst.
      unfold evptr_of_tsk in Hevp2.
      destruct Hevp2. simpljoin1. tryfalse.
      destruct H0. simpljoin1. tryfalse. simpljoin1. tryfalse.
    + assert (Heq1: get (set locmp t (V$ __EvLoc_ecbcre1)) t1 = get locmp t1)
        by join auto.
      rewrite Heq1 in *.
      assert (Heq2: get (set locmp t (V$ __EvLoc_ecbcre1)) t2 = get locmp t2) 
        by join auto.
      rewrite Heq2 in *.
      lets H00: Hnd Hneqt Hget1 Hget2 Hevp1 Hevp2. 
      auto.
Qed.  

Lemma del_nodup_null_cre1_preserve:
  forall t locmp ptrmp,
    get ptrmp t = Some (Vnull, Vnull, Vnull) ->
    evdel_nodup locmp ptrmp ->
    evdel_nodup (set locmp t (V$ __EvLoc_ecbcre1)) ptrmp.  
Proof.
  introv Hget Hnd.
  unfold evdel_nodup in *.
  introv Hneqt Hget1 Hget2 Hevp1 Hevp2.
  assert (Hor1: t1 = t \/ t1 <> t) by tauto.
  destruct Hor1.
  - subst.
    unfold evptr_of_tsk in Hevp1.
    destruct Hevp1. simpljoin1. tryfalse.
    destruct H. simpljoin1. tryfalse. simpljoin1. tryfalse.
  - assert (Hor2: t2 = t \/ t2 <> t) by tauto.
    destruct Hor2.
    + subst.
      unfold evptr_of_tsk in Hevp2.
      destruct Hevp2. simpljoin1. tryfalse.
      destruct H0. simpljoin1. tryfalse. simpljoin1. tryfalse.
    + assert (Heq1: get (set locmp t (V$ __EvLoc_ecbcre1)) t1 = get locmp t1)
        by join auto.
      rewrite Heq1 in *.
      assert (Heq2: get (set locmp t (V$ __EvLoc_ecbcre1)) t2 = get locmp t2) 
        by join auto.
      rewrite Heq2 in *.
      lets H00: Hnd Hneqt Hget1 Hget2 Hevp1 Hevp2. 
      auto.
Qed.  

Lemma semecb_preserve_cre1_mux:
  forall locmp ptrmp ecbls hd' vl vll semeibs muxeibs qeibs ct sid, 
    SEM_ECB_P locmp ptrmp ecbls (Vptr sid) (vl::vll) semeibs muxeibs qeibs -> 
    get ecbls sid = None -> 
    V_OSEventListPtr vl = Some hd' -> 
    isptr hd' -> 
    ~ptr_in_ecblist (Vptr sid) hd' vll -> 
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 sid) ->
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 sid) -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_normal sid) -> 
    (* (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel sid) ->    *)
    SEM_ECB_P (set locmp ct (V$ __EvLoc_ecbcre1)) (set ptrmp ct (Vptr sid, Vnull, Vnull))
              ecbls hd' vll semeibs muxeibs qeibs.  
Proof.
  introv Hsep Hnone Hnxtptr Hisptr Hnotin Hsem Hmux Hque Hncre1 Hncre2.
  introv Hnnm.
  (* introv Hndel. *)
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - subst t.
    rewrite set_a_get_a.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
(*     left. *)
(*     splits; auto. *)
(*     eapply inactive_ecb_no_eib_ref; eauto. *)
  - rewrite set_a_get_a' in Hgetp'; auto.
    lets H00: Hsep Hgetp'.
    clear Hsep.
    rewrite set_a_get_a'; auto.
    destruct H00 as [Hcre1 | [Hcre2 | Hnrm]].
    + left.
      destructs Hcre1.
      splits; auto.
      unfold isptr in Hisptr.
      destruct Hisptr.
      subst hd'. introv Hf. unfold ptr_in_ecblist in Hf. destruct vll; tryfalse.
      destruct H4. subst hd'. 
      eapply n_ptr_in_ecblist_tail; eauto.
    + right. left. 
      auto.
    + right. right.
      destructs Hnrm.
      splits; auto.
      destruct H1.
      left; auto.
      right.
      assert (Hneq: eptr <> sid).
      {
        introv Heq. apply Hnnm.
        subst.
        exists t. unfold tsk_loc_ev. splits; auto.
        do 3 eexists. splits; eauto.
      }
      eapply ptr_in_ecblist_tail; eauto.
Qed.       

Lemma muxecb_preserve_cre1_mux:
  forall locmp ptrmp ecbls hd' vl vll semeibs muxeibs qeibs ct sid, 
    MUX_ECB_P locmp ptrmp ecbls (Vptr sid) (vl::vll) semeibs muxeibs qeibs -> 
    get ecbls sid = None -> 
    V_OSEventListPtr vl = Some hd' -> 
    isptr hd' -> 
    ~ptr_in_ecblist (Vptr sid) hd' vll -> 
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 sid) ->
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 sid) -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_normal sid) -> 
    MUX_ECB_P (set locmp ct (V$ __EvLoc_ecbcre1)) (set ptrmp ct (Vptr sid, Vnull, Vnull))
              ecbls hd' vll semeibs muxeibs qeibs.  
Proof.
  introv Hmep Hnone Hnxtptr Hisptr Hnotin Hsem Hmux Hque Hncre1 Hncre2.
  introv Hnnm.
  (* introv Hndel. *)
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - subst t.
    rewrite set_a_get_a.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
    left.
    splits; auto.
    eapply inactive_ecb_no_eib_ref; eauto.
  - rewrite set_a_get_a' in Hgetp'; auto.
    rewrite set_a_get_a'; auto.
    lets H00: Hmep Hgetp'.
    clear Hmep.

    destruct H00 as [Hcre1 | [Hcre2 | Hnrm]].
    + left.
      destructs Hcre1.
      splits; auto.
      unfold isptr in Hisptr.
      destruct Hisptr.
      subst hd'. introv Hf. unfold ptr_in_ecblist in Hf. destruct vll; tryfalse.
      destruct H4. subst hd'. 
      eapply n_ptr_in_ecblist_tail; eauto.
    + right. left. 
      auto.
    + right. right.
      destructs Hnrm.
      splits; auto.
      destruct H1.
      left; auto.
      right.
      assert (Hneq: eptr <> sid).
      {
        introv Heq. apply Hnnm.
        subst.
        exists t. unfold tsk_loc_ev. splits; auto.
        do 3 eexists. splits; eauto.
      }
      eapply ptr_in_ecblist_tail; eauto.
Qed.       

Lemma qecb_preserve_cre1_mux:
  forall locmp ptrmp ecbls hd' vl vll semeibs muxeibs qeibs ct sid, 
    Q_ECB_P locmp ptrmp ecbls (Vptr sid) (vl::vll) semeibs muxeibs qeibs -> 
    get ecbls sid = None -> 
    V_OSEventListPtr vl = Some hd' -> 
    isptr hd' -> 
    ~ptr_in_ecblist (Vptr sid) hd' vll -> 
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 sid) ->
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 sid) -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_normal sid) -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel sid) ->
    Q_ECB_P (set locmp ct (V$ __EvLoc_ecbcre1)) (set ptrmp ct (Vptr sid, Vnull, Vnull))
            ecbls hd' vll semeibs muxeibs qeibs.  
Proof.
  introv Hqep Hnone Hnxtptr Hisptr Hnotin Hsem Hmux Hque Hncre1 Hncre2.
  introv Hnnm Hndel.
  (* introv Hndel. *)
  unfold Q_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - subst t.
    rewrite set_a_get_a.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'. 
  - rewrite set_a_get_a' in Hgetp'; auto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    rewrite set_a_get_a'; auto.
    split.
    +
      destruct H00 as [[Hcre1 | [Hcre2 | Hnrm]] Hdel].
      * left. 
        destructs Hcre1. 
        splits; auto.
        unfold isptr in Hisptr.
        destruct Hisptr.
        subst hd'. introv Hf. unfold ptr_in_ecblist in Hf. destruct vll; tryfalse.
        destruct H4. subst hd'. 
        eapply n_ptr_in_ecblist_tail; eauto.
      * right. left.
        auto.
      * right. right.
        destructs Hnrm.
        splits; auto.
        destruct H1.
        left; auto.
        right.
        assert (Hneq: eptr <> sid).
        {
          destruct H0.
          introv Heq. apply Hnnm. subst.
          exists t. unfold tsk_loc_ev. splits; auto.
          do 3 eexists. splits; eauto.
          introv Heq. apply Hndel. subst.
          exists t. unfold tsk_loc_ev. splits; auto.
          do 3 eexists. splits; eauto.        
        }
        eapply ptr_in_ecblist_tail; eauto.
    +
      introv Hdel.
      destruct H00 as (H' & Hdel0).
      lets H00: Hdel0 Hdel.
      destructs H00.
      splits; auto.
      introv Hf. apply H1. 
      destruct Hf as (t0 & Hor & Hep).
      assert (Hneq: eptr <> sid).
      {
        introv Heq.
        subst.
        unfold is_que in H0.
        destruct H0 as (x & y & pqws & qws & Hget). (* add pqws *)
        unfold get in Hnone. unfold EcbMap in Hnone.
        unfold get in Hget. unfold EcbMap in Hget.
        rewrite Hnone in Hget. inverts Hget. 
      }
      assert (Hneqct: t0 <> ct).
      {
        intro. subst.
        unfold evptr_of_tsk in Hep. 
        destruct Hep.
        do 2 destruct H3. rewrite set_a_get_a in H3. inverts H3.
        tryfalse.
        destruct H3.
        do 2 destruct H3. rewrite set_a_get_a in H3. inverts H3. (* apply Hneq; auto. *)
        do 2 destruct H3. rewrite set_a_get_a in H3. inverts H3.
      }
      rewrite set_a_get_a' in Hor; eauto.
      exists t0.
      splits; auto.
      unfold evptr_of_tsk in *.
      rewrite set_a_get_a' in Hep; auto.
Qed.  
  

Lemma evcre_nodup_cre1_preserve_mux:
  forall locmp ptrmp eid ct, 
    evcre_nodup locmp ptrmp ->
    ~(exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid) ->
    ~(exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid) -> 
    evcre_nodup (set locmp ct (V$ __EvLoc_ecbcre1)) (set ptrmp ct (Vptr eid, Vnull, Vnull)). 
Proof.
  introv Hndp Hnex1 Hnex2.
  unfold evcre_nodup.
  introv Hneqt Hget1 Hget2 Hptr1 Hptr2.
  assert (H: t1 = ct \/ t1 <> ct) by tauto.  
  destruct H.
  -
    subst.
    assert (eptr1 = eid). 
    {
      unfold evptr_of_tsk in Hptr1.    
      destruct Hptr1.
      simpljoin1. rewrite set_a_get_a in H. inverts H.
      auto.
      destruct H.
      simpljoin1. rewrite set_a_get_a in H. inverts H. (* auto. *)
      simpljoin1. rewrite set_a_get_a in H. inverts H.
    }
    subst.
    rewrite set_a_get_a' in Hget2; eauto.
    unfold evptr_of_tsk in Hptr2.
    rewrite set_a_get_a' in Hptr2; eauto.
    introv Heqp.
    subst.
    destruct Hptr2.  
    simpljoin1.
    destruct Hget2.
    apply Hnex1. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    apply Hnex2. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    destruct H.
    simpljoin1.
    destruct Hget2.
    apply Hnex1. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    apply Hnex2. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    simpljoin1.
    destruct Hget2.
    apply Hnex1. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    apply Hnex2. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
  -
    assert (H': t2 = ct \/ t2 <> ct) by tauto.
    destruct H'.
    +
      subst.
      assert (eptr2 = eid).
      {
        unfold evptr_of_tsk in Hptr2.
        destruct Hptr2.
        simpljoin1. rewrite set_a_get_a in H0. inverts H0.
        auto.
        destruct H0.
        simpljoin1. rewrite set_a_get_a in H0. inverts H0. (* auto. *)
        simpljoin1. rewrite set_a_get_a in H0. inverts H0.
      }
      subst.
      rewrite set_a_get_a' in Hget1; eauto.
      unfold evptr_of_tsk in Hptr1.
      rewrite set_a_get_a' in Hptr1; eauto.
      introv Heqp.
      subst.
      destruct Hptr1.
      simpljoin1.
      destruct Hget1.
      apply Hnex1. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
      apply Hnex2. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
      destruct H0.
      simpljoin1.
      destruct Hget1.
      apply Hnex1. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
      apply Hnex2. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
      simpljoin1.
      destruct Hget1.
      apply Hnex1. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
      apply Hnex2. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    +
      rewrite set_a_get_a' in Hget1; eauto.
      rewrite set_a_get_a' in Hget2; eauto.
      unfold evcre_nodup in Hndp.
      lets H00: Hndp Hneqt Hget1 Hget2.
      eapply H00; eauto.
      unfold evptr_of_tsk in Hptr1. rewrite set_a_get_a' in Hptr1; eauto.
      unfold evptr_of_tsk in Hptr2. rewrite set_a_get_a' in Hptr2; eauto.
Qed.  

Lemma evdel_nodup_cre1_preserve_mux: 
  forall locmp ptrmp eid ct, 
    evdel_nodup locmp ptrmp ->
    ~(exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid) ->
    ~(exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid) -> 
    evdel_nodup (set locmp ct (V$ __EvLoc_ecbcre1)) (set ptrmp ct (Vptr eid, Vnull, Vnull)). 
Proof.
  introv Hevdel Hnex1 Hnex2.
  unfold evdel_nodup.
  introv Hneqt Hdel1 Hdel2 Hptr1 Hptr2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst.
  rewrite set_a_get_a in Hdel1. inverts Hdel1.
  rewrite set_a_get_a' in Hdel1; eauto.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst.
  rewrite set_a_get_a in Hdel2. inverts Hdel2.
  rewrite set_a_get_a' in Hdel2; eauto.
  lets H00: Hevdel Hneqt Hdel1 Hdel2.  
  eapply H00; eauto.
  unfold evptr_of_tsk in Hptr1. rewrite set_a_get_a' in Hptr1; eauto.
  unfold evptr_of_tsk in Hptr2. rewrite set_a_get_a' in Hptr2; eauto. 
Qed.  

Lemma evdel_nodup_cre2_preserve: 
  forall locmp ptrmp ct, 
    evdel_nodup locmp ptrmp ->
    evdel_nodup (set locmp ct (V$ __EvLoc_ecbcre2)) ptrmp. 
Proof.
  introv Hdnp.
  unfold evdel_nodup in*.
  introv Hneqt Hget1 Hget2 Hp1 Hp2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst t1.
  rewrite set_a_get_a in Hget1.
  inverts Hget1.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst t2.
  rewrite set_a_get_a in Hget2.
  inverts Hget2.
  rewrite set_a_get_a' in Hget1, Hget2; eauto.
Qed.   

Lemma cre_nodup_no_cre1_mux: 
  forall locmp ptrmp ct sid, 
    evcre_nodup locmp ptrmp ->  
    get locmp ct = Some (V$ __EvLoc_ecbcre1) -> 
    get ptrmp ct = Some (Vptr sid, Vnull, Vnull) -> 
    ~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 sid. 
Proof.
  introv Hndp Hcre1 Hp.
  introv Hex.
  destruct Hex as (t & (Hneq & Htle)).
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hl & (mp & sp & qp & Hp' & Hor)).
  unfold evcre_nodup in Hndp.
  destruct Hor.
  - 
    subst mp.
    assert (Hf: sid <> sid).
    {
      apply Hndp with (t1 := t) (t2 := ct); auto.
      unfold evptr_of_tsk. left. do 2 eexists; eauto.
      unfold evptr_of_tsk. (* right. *) left. do 2 eexists; eauto.
    }
    apply Hf; auto.
  -
    destruct H.
    +
      subst sp.
      assert (Hf: sid <> sid). 
      {
        apply Hndp with (t1 := t) (t2 := ct); auto.
        unfold evptr_of_tsk. right. left. do 2 eexists; eauto.
        unfold evptr_of_tsk. (* right. *) left. do 2 eexists; eauto.
      }
      apply Hf; auto.
    +
      subst qp.
      assert (Hf: sid <> sid).
      {
        apply Hndp with (t1 := t) (t2 := ct); auto.
        unfold evptr_of_tsk. right. right. do 2 eexists; eauto.
        unfold evptr_of_tsk. (* right. *) left. do 2 eexists; eauto.
      }
      apply Hf; auto.
Qed.  

Lemma cre_nodup_no_cre2_mux: 
  forall locmp ptrmp ct sid, 
    evcre_nodup locmp ptrmp ->  
    get locmp ct = Some (V$ __EvLoc_ecbcre1) -> 
    get ptrmp ct = Some (Vptr sid, Vnull, Vnull) -> 
    ~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 sid. 
Proof.
  introv Hndp Hcre1 Hp.
  introv Hex.
  destruct Hex as (t & (Hneq & Htle)).
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hl & (mp & sp & qp & Hp' & Hor)).
  unfold evcre_nodup in Hndp.
  destruct Hor.
  - 
    subst mp.
    assert (Hf: sid <> sid).
    {
      apply Hndp with (t1 := t) (t2 := ct); auto.
      unfold evptr_of_tsk. left. do 2 eexists; eauto.
      unfold evptr_of_tsk. (* right. *) left. do 2 eexists; eauto.
    }
    apply Hf; auto.
  -
    destruct H.
    +
      subst sp.
      assert (Hf: sid <> sid). 
      {
        apply Hndp with (t1 := t) (t2 := ct); auto.
        unfold evptr_of_tsk. right. left. do 2 eexists; eauto.
        unfold evptr_of_tsk. (* right. *) left. do 2 eexists; eauto.
      }
      apply Hf; auto.
    +
      subst qp.
      assert (Hf: sid <> sid).
      {
        apply Hndp with (t1 := t) (t2 := ct); auto.
        unfold evptr_of_tsk. right. right. do 2 eexists; eauto.
        unfold evptr_of_tsk. (* right. *) left. do 2 eexists; eauto.
      }
      apply Hf; auto.
Qed.  

Lemma evcre_nodup_cre2_preserve_mux: 
  forall locmp ptrmp ct sid,  
    evcre_nodup locmp ptrmp ->
    get ptrmp ct = Some (Vptr sid, Vnull, Vnull) -> 
    (~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 sid) -> 
    (~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 sid) -> 
    evcre_nodup (set locmp ct (V$ __EvLoc_ecbcre2)) ptrmp. 
Proof. 
  introv Hndp Hp Hnex1 Hnex2.
  unfold evcre_nodup in *.
  introv Hneq Hget1 Hget2 Hp1 Hp2 Heq.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  -
    subst t1.
    assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
    destruct Hor2.
    + 
      subst t2.
      apply Hneq; auto.
    +
      rewrite set_a_get_a' in Hget2; eauto.
      destruct Hget2.
      *
        apply Hnex1.
        exists t2. splits; auto.
        unfold tsk_loc_ev.
        splits; auto.
        subst eptr2.
        assert (eptr1 = sid).
        {
          unfold evptr_of_tsk  in Hp1.
          destruct Hp1.
          simpljoin1.
          rewrite Hp in H1. inverts H1. auto.
          destruct H1.
          simpljoin1. rewrite Hp in H1. inverts H1. (* auto. *)
          simpljoin1. rewrite Hp in H1. inverts H1.
        }
        subst eptr1.
        unfold evptr_of_tsk in Hp2.
        destruct Hp2.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        destruct H1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
      *
        apply Hnex2.
        exists t2. splits; auto.
        unfold tsk_loc_ev.
        splits; auto.
        subst eptr2.
        assert (eptr1 = sid).
        {
          unfold evptr_of_tsk  in Hp1.
          destruct Hp1.
          simpljoin1.
          rewrite Hp in H1. inverts H1. auto.
          destruct H1.
          simpljoin1. rewrite Hp in H1. inverts H1. (* auto. *)
          simpljoin1. rewrite Hp in H1. inverts H1.
        }
        subst eptr1.
        unfold evptr_of_tsk in Hp2.
        destruct Hp2.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        destruct H1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
  -
    assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
    destruct Hor2.
    + 
      subst t2.
      rewrite set_a_get_a' in Hget1; eauto.
      destruct Hget1.
      * 
        apply Hnex1.
        exists t1. splits; auto.
        unfold tsk_loc_ev.
        splits; auto.
        subst eptr1.
        assert (eptr2 = sid).
        {
          unfold evptr_of_tsk  in Hp2.
          destruct Hp2.
          simpljoin1.
          rewrite Hp in H1. inverts H1. auto.
          destruct H1.
          simpljoin1. rewrite Hp in H1. inverts H1. (* auto. *)
          simpljoin1. rewrite Hp in H1. inverts H1.
        }
        subst eptr2.
        unfold evptr_of_tsk in Hp1.
        destruct Hp1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        destruct H1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
      *
        apply Hnex2.
        exists t1. splits; auto.
        unfold tsk_loc_ev.
        splits; auto.
        subst eptr1.
        assert (eptr2 = sid).
        {
          unfold evptr_of_tsk  in Hp2.
          destruct Hp2.
          simpljoin1.
          rewrite Hp in H1. inverts H1. auto.
          destruct H1.
          simpljoin1. rewrite Hp in H1. inverts H1. (* auto. *)
          simpljoin1. rewrite Hp in H1. inverts H1.
        }
        subst eptr2.
        unfold evptr_of_tsk in Hp1.
        destruct Hp1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        destruct H1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
    +
      rewrite set_a_get_a' in Hget1, Hget2; eauto.
      lets H00: Hndp Hneq Hget1 Hget2 Hp1 Hp2.
      apply H00 in Heq. 
      auto.
Qed.      

Lemma sem_ecb_cre2_preserve_mux: 
  forall locmp ptrmp ecbls fecbh ecbvl ct prio eptr semeibs muxeibs qeibs, 
    SEM_ECB_P locmp ptrmp ecbls fecbh ecbvl semeibs muxeibs qeibs ->  
    (* get locmp ct = Some (V$ __EvLoc_ecbcre1) -> *)
    get ptrmp ct = Some (Vptr eptr, Vnull, Vnull) -> 
    get ecbls eptr = None ->  
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eptr) -> 
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eptr) -> 
    SEM_ECB_P (set locmp ct (V$ __EvLoc_ecbcre2)) ptrmp (set ecbls eptr (absmutexsem prio None, nil))
              fecbh ecbvl semeibs muxeibs qeibs.  
Proof.
  introv Hsep (* Hgetl *) Hgetp Hnone Hsem Hmux Hq Hnex1 Hnex2.
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - (* t = ct *)
    subst t.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
   (*  right. left.
    splits.
    rewrite set_a_get_a. auto.
    eapply inactive_ecb_no_eib_ref; eauto.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'; auto.
    unfold is_sem.
    do 2 eexists.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
    rewrite set_a_get_a. eauto.  *)
  - (* t <> ct *)
    rewrite set_a_get_a'; eauto.
    lets H00: Hsep Hgetp'.
    clear Hsep.
    destruct H00.
(*     destruct H0 as (H01 & H02 & H03 & H04). *)
    + 
      left.
      simpljoin1. splits; auto.
      rewrite set_a_get_a'; auto.
      introv Heqptr.
      subst eptr.
      apply Hnex1.
      exists t. splits; auto. 
      unfold tsk_loc_ev.
      splits; auto.
      do 3 eexists. eauto.
    +
      destruct H0. 
      right. left.
      simpljoin1.
      splits; auto.
      unfold is_sem.
      rewrite set_a_get_a'; auto.
      introv Heqptr.
      subst eptr.
      apply Hnex2.
      exists t. splits; auto. 
      unfold tsk_loc_ev.
      splits; auto.
      do 3 eexists. eauto.
      (* assert (Hor': eptr = eptr0 \/ eptr <> eptr0) by tauto.
      destruct Hor'.
      subst.  unfold is_sem. rewrite set_a_get_a. do 2 eexists; eauto.
      unfold is_sem. rewrite set_a_get_a'; eauto.  *)

      right. right.
      simpljoin1.
      splits; auto.
      destruct H1.
      2: { right; auto. }
      left. 
      unfold is_evt in *. 
      assert (Hor': eptr = eptr0 \/ eptr <> eptr0) by tauto.
      destruct Hor'.
      subst.
      right. left. unfold is_mux. rewrite set_a_get_a. do 3 eexists; eauto. 
      unfold is_sem, is_mux, is_que.
      rewrite set_a_get_a'; eauto.
Qed.    

Lemma mux_ecb_cre2_preserve_mux: 
  forall locmp ptrmp ecbls fecbh ecbvl ct prio eptr semeibs muxeibs qeibs, 
    MUX_ECB_P locmp ptrmp ecbls fecbh ecbvl semeibs muxeibs qeibs ->  
    (* get locmp ct = Some (V$ __EvLoc_ecbcre1) -> *)
    get ptrmp ct = Some (Vptr eptr, Vnull, Vnull) -> 
    get ecbls eptr = None ->  
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eptr) -> 
(*     ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eptr) ->  *)
    MUX_ECB_P (set locmp ct (V$ __EvLoc_ecbcre2)) ptrmp (set ecbls eptr (absmutexsem prio None, nil))
              fecbh ecbvl semeibs muxeibs qeibs.  
Proof.
  introv Hmep (* Hgetl *) Hgetp Hnone Hsem Hmux Hq Hnex(* 1 Hnex2 *).
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - (* t = ct *)
    subst t.
    right. left.
    splits.
    rewrite set_a_get_a. auto.
     eapply inactive_ecb_no_eib_ref; eauto.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'; auto.
    unfold is_mux.
    do 3 eexists.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
    rewrite set_a_get_a. eauto. 
(*     rewrite Hgetp in Hgetp'. *)
(*     inverts Hgetp'. *)
  - (* t <> ct *)
    rewrite set_a_get_a'; eauto.
    lets H00: Hmep Hgetp'.
    clear Hmep.
    destruct H00.
    + 
      left.
      simpljoin1. splits; auto.
      rewrite set_a_get_a'; auto.
      introv Heqptr.
      subst eptr.
      apply Hnex.
      exists t. splits; auto. 
      unfold tsk_loc_ev.
      splits; auto.
      do 3 eexists. eauto.
    +
      destruct H0. 
      right. left.
      simpljoin1.
      splits; auto.
      assert (Hor': eptr = eptr0 \/ eptr <> eptr0) by tauto.
      destruct Hor'.
      subst.  unfold is_mux. rewrite set_a_get_a. do 3 eexists; eauto.
      unfold is_mux. rewrite set_a_get_a'; eauto.
      (* unfold is_mux.
      rewrite set_a_get_a'; eauto.
      introv Heqptr.
      subst eptr.
      apply Hnex2.
      exists t.
      split; auto.
      unfold tsk_loc_ev.
      split; auto.
      do 3 eexists. splits; eauto. *)

      right. right.
      simpljoin1.
      splits; auto.
      destruct H1.
      2: { right; auto. }
      left. 
      unfold is_evt in *. 
      assert (Hor': eptr = eptr0 \/ eptr <> eptr0) by tauto.
      destruct Hor'.
      subst.
      right. left. unfold is_mux. rewrite set_a_get_a. do 3 eexists; eauto. 
      unfold is_sem, is_mux, is_que.
      rewrite set_a_get_a'; eauto.
Qed.   

Lemma q_ecb_cre2_preserve_mux: 
  forall locmp ptrmp ecbls fecbh ecbvl ct prio eptr semeibs muxeibs qeibs, 
    Q_ECB_P locmp ptrmp ecbls fecbh ecbvl semeibs muxeibs qeibs ->  
    get locmp ct = Some (V$ __EvLoc_ecbcre1) -> 
    get ptrmp ct = Some (Vptr eptr, Vnull, Vnull) -> 
    get ecbls eptr = None ->  
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eptr) -> 
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eptr) -> 
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel eptr) -> 
    Q_ECB_P (set locmp ct (V$ __EvLoc_ecbcre2)) ptrmp (set ecbls eptr (absmutexsem prio None, nil))
              fecbh ecbvl semeibs muxeibs qeibs.  
Proof.
  introv Hqep Hgetl Hgetp Hnone Hsem Hmux Hq Hnex1 Hnex2 Hnex3.
  unfold Q_ECB_P in *. 
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - (* t = ct *)
    subst t.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
  - (* t <> ct *)
    rewrite set_a_get_a'; eauto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    destruct H00 as (Hor3 & Hdel).
    split. 
    destruct Hor3.
    * left.
      simpljoin1. splits; auto.
      rewrite set_a_get_a'; auto.
      introv Heqptr.
      subst eptr.
      apply Hnex1.
      exists t. splits; auto. 
      unfold tsk_loc_ev.
      splits; auto.
      do 3 eexists. eauto.
    * destruct H0.
      right. left.
      simpljoin1.
      splits; auto.
      unfold is_que.
      rewrite set_a_get_a'; eauto.
      introv Heqptr. subst eptr.
      apply Hnex2.
      exists t. splits; auto. unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto. 

      simpljoin1.
      right. right.
      split; auto.
      destruct H1.
      2: { right. auto. }
      left.
      unfold is_evt in *.
      assert (Hor': eptr = eptr0 \/ eptr <> eptr0) by tauto.
      destruct Hor'.
      subst.
      right. left. unfold is_mux. rewrite set_a_get_a. do 3 eexists; eauto. 
      unfold is_sem, is_mux, is_que.
      rewrite set_a_get_a'; eauto.
    *
      introv Hlocdel.
      lets H00: Hdel Hlocdel.
      unfold is_que. rewrite set_a_get_a'; eauto. 
      simpljoin1. 
      splits; auto.
      2: { (* eptr <> eptr0 *) 
        introv Heqptr.  subst eptr.
        apply Hnex3.
        exists t. split; auto.
        unfold tsk_loc_ev.
        split; auto.
        do 3 eexists; eauto.
      }
      introv Hex.
      apply H1.
      destruct Hex as (t' & Hcre12 & Hevptr).
      assert (t' = ct \/ t' <> ct) by tauto.
      destruct H3.
      subst.
      exists ct.
      split; auto.
      rewrite set_a_get_a' in Hcre12; eauto. 
Qed.

(* used for pthread_mutex_init *)

Ltac mytac :=
  heat; jeauto2.

Lemma evref_same_type_preserve_mux:
  forall eptr semeibs muxeibs mqeibs pos ow tp rcnt prot prioc wq cnsa mc, 
    evref_same_type eptr semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    evref_same_type eptr semeibs  (set muxeibs pos (Holder, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs. 
Proof.
  introv Hest Hget.
  unfold evref_same_type in *.
  destructs Hest.
  splits.
  -
    introv Hs.
    lets H00: H Hs. destructs H00. splits; auto.
    intro Hset. apply H2.
    unfold muxeib_ref in Hset. unfold muxeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst. rewrite set_a_get_a in H4. inverts H4.
    rewrite set_a_get_a' in H4; eauto.
    repeat eexists; eauto.
  -
    introv Hm.
    unfold muxeib_ref in *.
    simpljoin1.
    casetac pos x Ht Hf.
    subst. rewrite set_a_get_a in H2. inverts H2.
    subst. rewrite set_a_get_a' in H2; eauto.
    eapply H0. repeat eexists; eauto.
  -  
    introv Hq.
    lets H00: H1 Hq. destructs H00. splits; auto.
    intro Hset. apply H3.
    unfold muxeib_ref in Hset. unfold muxeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst. rewrite set_a_get_a in H4. inverts H4.
    rewrite set_a_get_a' in H4; eauto.
    repeat eexists; eauto.
Qed.

Lemma eibref_distinct_null_holder_preserve_mux:
  forall semeibs muxeibs mqeibs pos ow tp rcnt prot prioc wq cnsa mc, 
    eibref_distinct semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    eibref_distinct semeibs  (set muxeibs pos (Holder, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs. 
Proof. 
  introv Hed Hget.
  unfold eibref_distinct in *.
  intros.
  specialize (Hed eptr).
  mytac. splits; auto.
  eapply evref_same_type_preserve_mux; eauto.
  unfold muxref_distinct in *.
  introv Hget1 Hget2.
  casetac pos pos1 Heq1 Hneq1.
  subst. rewrite set_a_get_a in Hget1. inverts Hget1.
  casetac pos pos2 Heq2 Hneq2.
  subst. rewrite set_a_get_a in Hget2. inverts Hget2.
  rewrite set_a_get_a' in Hget1; eauto.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.  

Lemma SEM_ECB_P_null_holder_preserve_mux: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos ow tp rcnt prot prioc wq cnsa mc, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs  (set muxeibs pos (Holder, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs.
Proof.
  introv Hsep Hget.
  unfold SEM_ECB_P in *.
  introv Hptr.
  lets H00: Hsep Hptr. clear Hsep.
  destruct H00.
  - 
    left.
    simpljoin1.
    splits; auto.
    introv Href. apply H1.
    unfold eib_ref in *.
    destruct Href; auto.
    destruct H3; auto.
    right. left. unfold muxeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H3. inverts H3.
    rewrite set_a_get_a' in H3; eauto.
    repeat eexists; eauto.
  -
    destruct H.
    +
      right; left.
      simpljoin1.
      splits; auto.
      introv Href.
      apply H0.
      unfold eib_ref in Href. unfold eib_ref.
      destruct Href; auto.
      destruct H2; auto.
      right. left.
      unfold muxeib_ref in *.
      simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H2. inverts H2.
      rewrite set_a_get_a' in H2; eauto.
      repeat eexists; eauto.
    +
      simpljoin1.
      right. right.
      splits; auto.
Qed.

Lemma MUX_ECB_P_null_holder_preserve_mux: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos ow tp rcnt prot prioc wq cnsa mc, 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs  (set muxeibs pos (Holder, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs. 
Proof.
  introv Hmep Hget.
  unfold MUX_ECB_P in *.
  introv Hptr.
  lets H00: Hmep Hptr. clear Hmep.
  destruct H00.
  -
    left.
    simpljoin1.
    splits; auto.
    introv Href. apply H1.
    unfold eib_ref in *.
    destruct Href; auto.
    destruct H3; auto.
    right. left. unfold muxeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H3. inverts H3.
    rewrite set_a_get_a' in H3; eauto.
    repeat eexists; eauto.
  -
    destruct H.
    +
      right; left.
      simpljoin1.
      splits; auto.
      introv Href.
      apply H0.
      unfold eib_ref in Href. unfold eib_ref.
      destruct Href; auto.
      destruct H2; auto.
      right. left.
      unfold muxeib_ref in *.
      simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H2. inverts H2.
      rewrite set_a_get_a' in H2; eauto.
      repeat eexists; eauto.
    +
      simpljoin1.
      right. right.
      splits; auto.
Qed.

Lemma Q_ECB_P_null_holder_preserve_mux: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos ow tp rcnt prot prioc wq cnsa mc, 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs  (set muxeibs pos (Holder, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs.  
Proof.
  introv Hqep Hget.
  unfold Q_ECB_P in *.
  introv Hptr.
  lets H00: Hqep Hptr. clear Hqep.
  destruct H00 as (Hor & Hdel).
  split.
  - (* part 1 *)
    destruct Hor.
    + 
      left.
      simpljoin1.
      splits; auto.
      introv Href. apply H1.
      unfold eib_ref in *.
      destruct Href; auto.
      destruct H3; auto.
      right. left. unfold muxeib_ref in *. simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H3. inverts H3.
      rewrite set_a_get_a' in H3; eauto.
      repeat eexists; eauto.
    +
      destruct H.
      *
        right; left.
        simpljoin1.
        splits; auto.
        introv Href.
        apply H0.
        unfold eib_ref in Href. unfold eib_ref.
        destruct Href; auto.
        destruct H2; auto.
        right. left.
        unfold muxeib_ref in *.
        simpljoin1.
        casetac pos x Heq Hneq.
        subst. rewrite set_a_get_a in H2. inverts H2.
        rewrite set_a_get_a' in H2; eauto.
        repeat eexists; eauto.
      *    
        simpljoin1.
        right. right.
        splits; auto.
  - (* part 2 *)
    clear Hor.
    introv Hgetl.
    specialize (Hdel Hgetl).
    simpljoin1.
    splits; auto.
    introv Href.
    apply H1.
    unfold eib_ref in Href. unfold eib_ref.
     destruct Href; auto.
      destruct H2; auto.
      right. left. unfold muxeib_ref in *. simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H2. inverts H2.
      rewrite set_a_get_a' in H2; eauto.
      repeat eexists; eauto.
Qed.

Lemma evref_same_type_infonull_preserve_mux:
  forall semeibs muxeibs mqeibs eptr pos ow tp rcnt prot prioc wq cnsa mc,
    evref_same_type eptr semeibs muxeibs mqeibs ->
    evref_same_type eptr semeibs  (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs. 
Proof.
  introv Hst.
  unfold evref_same_type in *.
  simpljoin1.
  splits; auto.
  -
    introv Hs.
    apply H in Hs.
    simpljoin1.
    splits; auto.
    introv Href. apply H2.
    unfold muxeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H4. inverts H4.
    rewrite set_a_get_a' in H4; eauto.
    repeat eexists; eauto.
  -
    introv Hm.
    apply H0.
    unfold muxeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H2. inverts H2.
    rewrite set_a_get_a' in H2; eauto.
    repeat eexists; eauto.
  -
    introv Hq.
    lets H00: H1 Hq.
    simpljoin1. splits; auto.
    introv Href. apply H3.
    unfold muxeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H4. inverts H4.
    rewrite set_a_get_a' in H4; eauto.
    repeat eexists; eauto.
Qed.

Lemma muxeib_ref_infonull_preserve:
  forall muxeibs pos ow tp rcnt prot prioc wq cnsa mc eptr, 
    muxeib_ref  (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) eptr ->
    muxeib_ref muxeibs eptr.
Proof.
  introv Hmr.
  unfold muxeib_ref in *.
  simpljoin1.
  casetac pos x He Hne.
  subst.
  rewrite set_a_get_a in H. inverts H.
  rewrite set_a_get_a' in H; eauto.
  repeat eexists; eauto.
Qed.

Lemma eibref_infonull_preserve_mux:
  forall semeibs pos ow tp rcnt prot prioc wq cnsa mc muxeibs qeibs eptr, 
    eib_ref semeibs (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) qeibs eptr -> 
    eib_ref semeibs muxeibs qeibs eptr. 
Proof.
  introv Her.
  unfold eib_ref in *.
  destruct Her; auto.
  destruct H; auto.
  right. left. eapply muxeib_ref_infonull_preserve; eauto.
Qed.

Lemma sem_ecb_p_infonull_preserve_mux: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs pos ow tp rcnt prot prioc wq cnsa mc tid, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    SEM_ECB_P (set locmp tid (V$ __EvLoc_normal)) ptrmp ecbls fecbh fecbvl
              semeibs (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) qeibs.
Proof.
  introv Hsep.
  unfold SEM_ECB_P in *.
  introv Hnull Hgetp.
  casetac tid t Heq Hneq.
  -
    subst.
    rewrite Hnull in Hgetp.
    inverts Hgetp.
  -
    rewrite set_a_get_a'; eauto.
    clear Hnull.
    lets H00: Hsep Hgetp.
    destruct H00.
    left.
    simpljoin1. splits; auto.
    introv Hf. apply H1.
    eapply eibref_infonull_preserve_mux; eauto.

    destruct H.
    right. left.
    simpljoin1.
    splits; auto.
    introv Hf; apply H0. 
    eapply eibref_infonull_preserve_mux; eauto.

    right. right.
    simpljoin1.
    splits; auto.
Qed.

Lemma mux_ecb_p_infonull_preserve_mux: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs pos ow tp rcnt prot prioc wq cnsa mc tid, 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    MUX_ECB_P (set locmp tid (V$ __EvLoc_normal)) ptrmp ecbls fecbh fecbvl
              semeibs (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) qeibs.
Proof.
  introv Hmep. 
  unfold MUX_ECB_P in *.
  introv Hnull Hgetp.
  casetac tid t Heq Hneq.
  -
    subst.
    rewrite Hnull in Hgetp.
    inverts Hgetp.
  -
    rewrite set_a_get_a'; eauto.
    clear Hnull.
    lets H00: Hmep Hgetp.
    destruct H00.
    left.
    simpljoin1. splits; auto.
    introv Hf. apply H1.
    eapply eibref_infonull_preserve_mux; eauto.

    destruct H.
    right. left.
    simpljoin1.
    splits; auto.
    introv Hf; apply H0. 
    eapply eibref_infonull_preserve_mux; eauto.

    right. right.
    simpljoin1.
    splits; auto.
Qed.

Lemma q_ecb_p_infonull_preserve_mux: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs pos ow tp rcnt prot prioc wq cnsa mc tid, 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    Q_ECB_P (set locmp tid (V$ __EvLoc_normal)) ptrmp ecbls fecbh fecbvl
              semeibs (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) qeibs.
Proof.
  introv Hqep. 
  unfold Q_ECB_P in *.
  introv Hnull Hgetp.
  casetac tid t Heq Hneq.
  -
    subst.
    rewrite Hnull in Hgetp.
    inverts Hgetp.
  -
    rewrite set_a_get_a'; eauto.
    clear Hnull.
    lets H00: Hqep Hgetp.
    destruct H00 as (Hor3 & Hdel).
    split.
    destruct Hor3.
    left.
    simpljoin1. splits; auto.
    introv Hf. apply H1.
    eapply eibref_infonull_preserve_mux; eauto.

    destruct H.
    right. left.
    simpljoin1.
    splits; auto.
    introv Hf; apply H0. 
    eapply eibref_infonull_preserve_mux; eauto.

    right. right.
    simpljoin1.
    splits; auto.
    introv Hget.
    lets H00: Hdel Hget.
    simpljoin1. splits; auto.
    2: {
      introv Hf; apply H1.
      eapply eibref_infonull_preserve_mux; eauto.
    }
    introv Hex; apply H0.
    destruct Hex as (t' & Hcre12 & Hevptr).
    casetac tid t' Heq' Hneq'.
    subst.
    rewrite set_a_get_a in Hcre12. destruct Hcre12; tryfalse. 
    rewrite set_a_get_a' in Hcre12;eauto. 
Qed.

Lemma muxref_distinct_infonull_preserve:
  forall muxeibs ep pos ow tp rcnt prot prioc wq cnsa mc, 
    muxref_distinct muxeibs ep->
    muxref_distinct (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) ep.  
Proof.
  introv Hdis.
  unfold muxref_distinct in *.
  introv Hget1 Hget2.
  casetac pos pos1 Ht Hf.
  subst. rewrite set_a_get_a in Hget1. inverts Hget1.
  rewrite set_a_get_a' in Hget1; eauto.
  casetac pos pos2 Ht' Hf'.
  subst. rewrite set_a_get_a in Hget2. inverts Hget2.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.
  
Lemma eibref_distinct_infonull_preserve_mux: 
  forall semeibs muxeibs mqeibs pos ow tp rcnt prot prioc wq cnsa mc, 
    eibref_distinct semeibs muxeibs mqeibs ->
    eibref_distinct semeibs (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs.
Proof.
  introv Hed.
  unfold eibref_distinct in *.
  intros.
  specialize (Hed eptr).
  simpljoin1. splits; auto.
  eapply evref_same_type_infonull_preserve_mux; eauto.
  unfold muxref_distinct.
  introv Hget1 Hget2.
  eapply muxref_distinct_infonull_preserve; eauto.
Qed.

Lemma evdel_nodup_normal_preserve: 
  forall locmp ptrmp ct, 
    evdel_nodup locmp ptrmp ->
    evdel_nodup (set locmp ct (V$ __EvLoc_normal)) ptrmp.  
Proof.
  introv Hdnp.
  unfold evdel_nodup in *.
  introv Hneqt Hget1 Hget2 Hp1 Hp2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst t1.
  rewrite set_a_get_a in Hget1.
  inverts Hget1.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst t2.
  rewrite set_a_get_a in Hget2.
  inverts Hget2.
  rewrite set_a_get_a' in Hget1, Hget2; eauto.
Qed.   

Lemma evdel_nodup_normal_null_preserve:
  forall locmp ptrmp ct,
    evdel_nodup locmp ptrmp -> 
    evdel_nodup (set locmp ct (V$ __EvLoc_normal)) (set ptrmp ct (Vnull, Vnull, Vnull)). 
Proof.
  introv Hdnp.
  unfold evdel_nodup in *.
  introv Hneqt Hget1 Hget2 Hp1 Hp2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst t1.
  rewrite set_a_get_a in Hget1.
  inverts Hget1.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst t2.
  rewrite set_a_get_a in Hget2.
  inverts Hget2.
  rewrite set_a_get_a' in Hget1, Hget2; eauto.
  unfold evptr_of_tsk in Hp1, Hp2.
  rewrite set_a_get_a' in Hp1, Hp2; eauto.
Qed.   

Lemma evcre_nodup_normal_preserve:  
  forall locmp ptrmp ct, 
    evcre_nodup locmp ptrmp ->
    evcre_nodup (set locmp ct (V$ __EvLoc_normal)) ptrmp.   
Proof.
  introv Hdnp.
  unfold evcre_nodup in *.
  introv Hneqt Hget1 Hget2 Hp1 Hp2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst t1.
  rewrite set_a_get_a in Hget1.
  inverts Hget1; tryfalse.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst t2.
  rewrite set_a_get_a in Hget2.
  inverts Hget2; tryfalse.
  rewrite set_a_get_a' in Hget1, Hget2; eauto.
Qed.

Lemma evcre_nodup_normal_null_preserve:
  forall locmp ptrmp ct,
    evcre_nodup locmp ptrmp -> 
    evcre_nodup (set locmp ct (V$ __EvLoc_normal)) (set ptrmp ct (Vnull, Vnull, Vnull)). 
Proof.
  introv Hdnp.
  unfold evcre_nodup in *.
  introv Hneqt Hget1 Hget2 Hp1 Hp2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst t1.
  rewrite set_a_get_a in Hget1.
  inverts Hget1; tryfalse.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst t2.
  rewrite set_a_get_a in Hget2.
  inverts Hget2; tryfalse.
  rewrite set_a_get_a' in Hget1, Hget2; eauto.
  unfold evptr_of_tsk in Hp1, Hp2.
  rewrite set_a_get_a' in Hp1, Hp2; eauto.
Qed.


Lemma eibref_distinct_noref_eid_preserve_mux: 
  forall semeibs muxeibs mqeibs eid pos ow tp rcnt prot prioc wq cnsa mc, 
    eibref_distinct semeibs muxeibs mqeibs ->  
    ~ eib_ref semeibs muxeibs mqeibs eid -> 
    eibref_distinct semeibs (set muxeibs pos (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs.  
Proof. 
  introv Hed Hnref.
  unfold eibref_distinct in *.
  intro.
  specialize (Hed eptr).
  simpljoin1.
  splits; auto.
  -
    unfold evref_same_type.
    splits.
    +
      introv Hsref.
      funfold H.
      lets Hget: Hsref.
      eapply H in Hsref.
      simpljoin1.
      splits; auto.
      introv Href.
      unfold eib_ref in Hnref.
      unfold muxeib_ref in *.
      simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H7. inverts H7.
      eapply Hnref; auto.
      apply H5.
      rewrite set_a_get_a' in H7; eauto.
      repeat eexists; eauto.
    +
      introv Hmref.
      unfold muxeib_ref in *.
      simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H3. inverts H3.
      unfold eib_ref in Hnref.
      clear -Hnref; intuition.
      rewrite set_a_get_a' in H3; eauto.
      eapply H.
      unfold muxeib_ref.
      repeat eexists; eauto.
    +
      introv Hqref.
      funfold H.
      lets Hget: Hqref.
      eapply H4 in Hqref.
      simpljoin1.
      splits; auto.
      introv Href.
      unfold eib_ref in Hnref.
      unfold muxeib_ref in *.
      simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H7. inverts H7.
      eapply Hnref; auto.
      apply H6.
      rewrite set_a_get_a' in H7; eauto.
      repeat eexists; eauto.
  -
    unfold muxref_distinct in H1. unfold muxref_distinct.
    introv Hget1 Hget2.
    casetac pos pos1 He Hne.
    subst. rewrite set_a_get_a in Hget1. inverts Hget1.
    casetac pos1 pos2 He' Hne'.
    subst. rewrite set_a_get_a in Hget2. inverts Hget2.
    auto.
    rewrite set_a_get_a' in Hget2; eauto.
    false. apply Hnref.
    unfold eib_ref. right. left.
    unfold muxeib_ref. repeat eexists; eauto.
    rewrite set_a_get_a' in Hget1; eauto.
    casetac pos pos2 He' Hne'.
    subst. 
    rewrite set_a_get_a in Hget2; eauto.
    inverts Hget2.

    false. apply Hnref.
    unfold eib_ref. right. left.
    unfold muxeib_ref. repeat eexists.  eauto.
    rewrite set_a_get_a' in Hget2; eauto.
Qed.


Lemma evcre_nodup_cre1_cre2_contra_mux: 
  forall t tid eid locmp ptrmp, 
    evcre_nodup locmp ptrmp -> 
    t <> tid -> 
    tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid ->
    get locmp tid = Some (V$ __EvLoc_ecbcre2) ->
    get ptrmp tid = Some (Vptr eid, Vnull, Vnull) ->  
    False. 
Proof.
  introv Hcrendp Htne Htle Hgetl Hgetp.
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hgetl' & (mq & sp & qp & (Hgetp' & Hor3))).
  unfold evcre_nodup in Hcrendp.
  specialize (Hcrendp t tid eid eid Htne (or_introl Hgetl') (or_intror Hgetl)).
  cut (eid <> eid).
  intro Hf. tryfalse.
  apply Hcrendp.
  unfold evptr_of_tsk.
  destruct Hor3.
  subst. left. do 2 eexists; eauto.
  destruct H.
  subst. right; left. do 2 eexists; eauto.
  subst. right; right. do 2 eexists; eauto.
  unfold evptr_of_tsk.
  left. eauto.
Qed.   

Lemma evcre_nodup_cre2_cre2_contra_mux: 
  forall t tid eid locmp ptrmp, 
    evcre_nodup locmp ptrmp -> 
    t <> tid -> 
    tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid ->
    get locmp tid = Some (V$ __EvLoc_ecbcre2) ->
    get ptrmp tid = Some (Vptr eid, Vnull, Vnull) ->  
    False. 
Proof.
  introv Hcrendp Htne Htle Hgetl Hgetp.
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hgetl' & (mq & sp & qp & (Hgetp' & Hor3))).
  unfold evcre_nodup in Hcrendp.
  specialize (Hcrendp t tid eid eid Htne (or_intror Hgetl') (or_intror Hgetl)).
  cut (eid <> eid).
  intro Hf. tryfalse.
  apply Hcrendp.
  unfold evptr_of_tsk.
  destruct Hor3.
  subst. left. do 2 eexists; eauto.
  destruct H.
  subst. right; left. do 2 eexists; eauto.
  subst. right; right. do 2 eexists; eauto.
  unfold evptr_of_tsk.
  left. eauto.
Qed.   

Lemma ecbdel_mux_contra:  
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs t eid, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs -> 
    tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel eid ->
    is_mux ecbls eid ->
    False.
Proof.
  introv Hsep Hmep Hqep Htle Hmux.
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hgetl & (mp & sp & qp & (Hgetp & Hor3))).
  destruct Hor3.
  -
    subst.
    unfold MUX_ECB_P in Hmep.
    lets H00: Hmep Hgetp.
    rewrite Hgetl in H00.
    destruct H00.  simpljoin1. tryfalse. destruct H. simpljoin1. tryfalse. simpljoin1. tryfalse.
  -
    destruct H; subst.
    +
      unfold SEM_ECB_P in Hsep.
      lets H00: Hsep Hgetp.
      rewrite Hgetl in H00.
      inverts H00.
      simpljoin1. tryfalse. inverts H. simpljoin1. tryfalse. simpljoin1. tryfalse.
    +
      unfold Q_ECB_P in Hqep.
      lets H00: Hqep Hgetp.
      destruct H00 as (Hor3 & Hdel).
      apply Hdel in Hgetl.
      simpljoin1.
      clear - Hmux H.
      unfold is_mux in *. unfold is_que in *.
      simpljoin1.
      rewrite H in H0.
      inverts H0.
Qed.


Lemma n_eibref_diff_ptr_preserve_mux: 
  forall semeibs muxeibs mqeibs eptr eid pos ow tp rcnt prot prioc wq cnsa mc, 
    ~ eib_ref semeibs muxeibs mqeibs eptr ->
    eptr <> eid ->
    ~ eib_ref semeibs (set muxeibs pos (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs eptr. 
Proof.
  introv Hnref Hneq Heibref.
  apply Hnref.
  unfold eib_ref in *.
  inverts Heibref; auto.
  destruct H; auto.
  right. left.
  unfold muxeib_ref in *.
  simpljoin1.
  casetac pos x He Hne.
  subst. rewrite set_a_get_a in H. inverts H.
  tryfalse.
  rewrite set_a_get_a' in H; eauto. 
  repeat eexists; eauto.
Qed.  
  
Lemma SEM_ECB_P_normal_null_preserve_mux: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs tid eid ow tp rcnt prot prioc wq cnsa mc pos, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid) -> 
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid) -> 
    SEM_ECB_P (set locmp tid (V$ __EvLoc_normal)) (set ptrmp tid (Vnull, Vnull, Vnull)) ecbls
              fecbh fecbvl semeibs (set muxeibs pos (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs.
Proof.
  introv Hsep Hncre1 Hncre2.
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  casetac tid t Hteq Htne.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hsep Hgetp'.
    clear Hsep.
    rewrite set_a_get_a'; eauto.
    destruct H00.
    +
      destruct H as (Hgetl & Hnin & Hnref & Hnone).
      casetac eptr eid He Hne.
      * 
        subst.
        false.
        apply Hncre1.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.
      *
        left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve_mux; eauto.
    +
      destruct H.
      *
        destruct H as (Hgetl & Hnin & Hnref & Hnone).
        casetac eptr eid He Hne.
        subst.
        false.
        apply Hncre2.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.

        right. left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve_mux; eauto.
        unfold is_sem. eauto.
      *
        destruct H as (Hgetl & Hor2).
        right; right.
        splits; auto.
Qed.

Lemma MUX_ECB_P_normal_null_preserve_mux: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs tid eid ow tp rcnt prot prioc wq cnsa mc pos, 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid) -> 
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid) -> 
    MUX_ECB_P (set locmp tid (V$ __EvLoc_normal)) (set ptrmp tid (Vnull, Vnull, Vnull)) ecbls fecbh fecbvl semeibs (set muxeibs pos (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs.
Proof.
  introv Hmep Hncre1 Hncre2.
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  casetac tid t Hteq Htne.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hmep Hgetp'.
    clear Hmep.
    rewrite set_a_get_a'; eauto.
    destruct H00.
    +
      destruct H as (Hgetl & Hnin & Hnref & Hnone).
      casetac eptr eid He Hne.
      * 
        subst.
        false.
        apply Hncre1.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.
      *
        left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve_mux; eauto.
    +
      destruct H.
      *
        destruct H as (Hgetl & Hnin & Hnref & Hnone).
        casetac eptr eid He Hne.
        subst.
        false.
        apply Hncre2.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.

        right. left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve_mux; eauto.
        unfold is_mux. eauto.
      *
        destruct H as (Hgetl & Hor2).
        right; right.
        splits; auto.
Qed.

Lemma Q_ECB_P_normal_null_preserve_mux: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs tid eid ow tp rcnt prot prioc wq cnsa mc pos, 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid) -> 
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid) -> 
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel eid) ->  
    Q_ECB_P (set locmp tid (V$ __EvLoc_normal)) (set ptrmp tid (Vnull, Vnull, Vnull)) ecbls fecbh fecbvl semeibs (set muxeibs pos (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs.
Proof.
  introv Hqep Hncre1 Hncre2 Hndel.
  unfold Q_ECB_P in *. 
  introv Hgetp'. 
  casetac tid t Hteq Htne.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    rewrite set_a_get_a'; eauto.
    destruct H00 as (Hor3 & Hdel).
    split.
    destruct Hor3.
    +
      destruct H as (Hgetl & Hnin & Hnref & Hnone).
      casetac eptr eid He Hne.
      * 
        subst.
        false.
        apply Hncre1.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.
      *
        left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve_mux; eauto.
    +
      destruct H.
      *
        destruct H as (Hgetl & Hnin & Hnref & Hnone).
        casetac eptr eid He Hne.
        subst.
        false.
        apply Hncre2.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.

        right. left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve_mux; eauto.
        unfold is_que. eauto.
      *
        destruct H as (Hgetl & Hor2).
        right; right.
        splits; auto.
    +
      introv Hgetl'.
      specialize (Hdel Hgetl').
      simpljoin1. splits; auto.
      introv Hex. apply H0.
      destruct Hex as (t' & Hcre12 & Hep).
      casetac tid t' Ht Hf.
      subst. rewrite set_a_get_a in Hcre12. destruct Hcre12; tryfalse.
      rewrite set_a_get_a' in Hcre12; eauto. 
      exists t'. splits; auto.
      unfold evptr_of_tsk in Hep. rewrite set_a_get_a' in Hep; eauto.
      eapply n_eibref_diff_ptr_preserve_mux; eauto.
      casetac eptr eid Ht' Hf'.
      subst.
      false. apply Hndel. exists t. splits; auto.
      unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.
      auto.
Qed.

Lemma muxeib_ref_set_preseve_gen:
forall muxeibs eptr pos e ow tp rcnt prot prioc wq cnsa mc ow' tp' rcnt' prot' prioc' wq' cnsa' mc',
muxeib_ref (set muxeibs pos (e, ow', tp', rcnt', prot', prioc', wq', cnsa', mc')) eptr ->
get muxeibs pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) ->
muxeib_ref muxeibs eptr.
Proof.
introv Hm Hget.
unfold muxeib_ref in *. 
simpljoin1.
casetac pos x Ht Hf.
subst.
rewrite set_a_get_a in H.
inverts H.
repeat eexists; eauto.
rewrite set_a_get_a' in H; eauto.
repeat eexists; eauto.
Qed.

Lemma eibref_distinct_set_pos_muxeib_gen: 
  forall semeibs muxeibs mqeibs pos e ow tp rcnt prot prioc wq cnsa mc ow' tp' rcnt' prot' prioc' wq' cnsa' mc', 
    eibref_distinct semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    eibref_distinct semeibs (set muxeibs pos (e, ow', tp', rcnt', prot', prioc', wq', cnsa', mc')) mqeibs. 
Proof.
  introv Hed Hget.
  unfold eibref_distinct in *.
  intro.
  specialize (Hed eptr).
  simpljoin1.
  splits; auto.
  -
    unfold evref_same_type in *.
    simpljoin1.
    splits; auto.
    introv Hre.
    lets Hcp: Hre.
    apply H in Hcp.
    destruct Hcp as (Hcpm & Hcpq).
    split; auto.
    unfold muxeib_ref in Hcpm. 
    unfold muxeib_ref.
    introv Hm.
    simpljoin1.
    apply Hcpm.
    casetac pos x Ht Hf.
    subst.
    rewrite set_a_get_a in H5.
    inverts H5.
     repeat eexists; eauto.
    rewrite set_a_get_a' in H5; eauto.
    repeat eexists; eauto.
    +
      introv Hm.
      eapply H3.
      unfold muxeib_ref in *.
      simpljoin1.
      casetac pos x Ht Hf.
      subst.
      rewrite set_a_get_a in H5.
      inverts H5.
      repeat eexists; eauto.
      rewrite set_a_get_a' in H5; eauto.
      repeat eexists; eauto.
   +
      introv Hq.
      apply H4 in Hq.
      destruct Hq as (Hs & Hm).
      split; auto.
      unfold muxeib_ref in Hm. 
      unfold muxeib_ref.
      introv Hm'.
      simpljoin1.
      apply Hm.
      casetac pos x Ht Hf.
      subst.
      rewrite set_a_get_a in H5.
      inverts H5.
      repeat eexists; eauto.
      rewrite set_a_get_a' in H5; eauto.
      repeat eexists; eauto.
  -
    unfold muxref_distinct in *.
    introv Hget1 Hget2.
    casetac pos pos1 Ht Hf.
    subst. rewrite set_a_get_a in Hget1. inverts Hget1.
    casetac pos1 pos2 Ht' Hf'.
    subst. rewrite set_a_get_a in Hget2. inverts Hget2. auto.    
    rewrite set_a_get_a' in Hget2; eauto.
    rewrite set_a_get_a' in Hget1; eauto.
    casetac pos pos2 Ht' Hf'.
    subst.
    rewrite set_a_get_a in Hget2.
    inverts Hget2.
    eapply H1; eauto.
    rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma n_eibref_set_mux_preserve_gen: 
  forall semeibs muxeibs mqeibs eptr pos e ow tp rcnt prot prioc wq cnsa mc ow' tp' rcnt' prot' prioc' wq' cnsa' mc', 
    ~ eib_ref semeibs muxeibs mqeibs eptr -> 
    get muxeibs pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    ~ eib_ref semeibs (set muxeibs pos (e, ow', tp', rcnt', prot', prioc', wq', cnsa', mc')) mqeibs eptr. 
Proof.
  introv Hnr Hget.
  introv Hf. apply Hnr.
  unfold eib_ref in Hf. unfold eib_ref.
  destruct Hf; auto.
  destruct H; auto.
  right. left.
  eapply muxeib_ref_set_preseve_gen; eauto.
Qed.

Lemma SEM_ECB_P_set_mutex_preserve_gen:  
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos e ow tp rcnt prot prioc wq cnsa mc ow' tp' rcnt' prot' prioc' wq' cnsa' mc', 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
     get muxeibs pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs (set muxeibs pos (e, ow', tp', rcnt', prot', prioc', wq', cnsa', mc')) mqeibs.
Proof.
  introv Hsep Hget.
  unfold SEM_ECB_P in *.
  introv Hget'.
  lets H00: Hsep Hget'. clear Hsep.
  destruct H00.
  left.
  simpljoin1. splits; auto.
  eapply n_eibref_set_mux_preserve_gen; eauto.
  destruct H.
  simpljoin1.
  right; left.
  splits; auto.
  eapply n_eibref_set_mux_preserve_gen; eauto.
  simpljoin1.
  right; right.
  splits; eauto.
Qed.

Lemma MUX_ECB_P_set_mux_preserve_gen:  
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos e ow tp rcnt prot prioc wq cnsa mc ow' tp' rcnt' prot' prioc' wq' cnsa' mc', 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs (set muxeibs pos (e, ow', tp', rcnt', prot', prioc', wq', cnsa', mc')) mqeibs.
Proof.
  introv Hmep Hget.
  unfold MUX_ECB_P in *.
  introv Hget'.
  lets H00: Hmep Hget'. clear Hmep.
  destruct H00.
  left.
  simpljoin1. splits; auto.
  eapply n_eibref_set_mux_preserve_gen; eauto.
  destruct H.
  simpljoin1.
  right; left.
  splits; auto.
  eapply n_eibref_set_mux_preserve_gen; eauto.
  simpljoin1.
  right; right.
  splits; eauto.
Qed.

Lemma Q_ECB_P_set_mux_preserve_gen:  
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos e ow tp rcnt prot prioc wq cnsa mc ow' tp' rcnt' prot' prioc' wq' cnsa' mc', 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get muxeibs pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs (set muxeibs pos (e, ow', tp', rcnt', prot', prioc', wq', cnsa', mc')) mqeibs.
Proof.
  introv Hqep Hget.
  unfold Q_ECB_P in *.
  introv Hget'.
  lets H00: Hqep Hget'. clear Hqep.
  destruct H00 as (Hor3 & Hdel).
  split. 
  -
    destruct Hor3.
    left.
    simpljoin1. splits; auto.
    eapply n_eibref_set_mux_preserve_gen; eauto.
    destruct H.
    simpljoin1.
    right; left.
    splits; auto.
    eapply n_eibref_set_mux_preserve_gen; eauto.
    simpljoin1.
    right; right.
    splits; eauto.
  -
    introv Hgetl.
    apply Hdel in Hgetl.
    simpljoin1.
    splits; auto.
    eapply n_eibref_set_mux_preserve_gen; eauto.
Qed.

Lemma eib_ref_no_tsk_cre1: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs eid, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs -> 
    eib_ref semeibs muxeibs mqeibs eid -> 
    ~exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre1 eid.
Proof.
  introv Hsep Hmep Hqep Heref Hex.
  destruct Hex as (t' & Htle).
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hgetl & muxp & semp & qp & Hgetp & Hor).
  destruct Hor as [Hmp | [Hsp | Hqp]]; subst.
  lets H00: mux_ecb_cre1 Hmep Hgetl Hgetp.
  simpljoin1.
  apply H0 in Heref. inverts Heref.
  lets H00: sem_ecb_cre1 Hsep Hgetl Hgetp.
  simpljoin1.
  apply H0 in Heref. inverts Heref.
  lets H00: q_ecb_cre1 Hqep Hgetl Hgetp.
  simpljoin1.
  apply H0 in Heref. inverts Heref.  
Qed. 

Lemma eib_ref_no_tsk_cre2: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs eid, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs -> 
    eib_ref semeibs muxeibs mqeibs eid -> 
    ~exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre2 eid.
Proof.
  introv Hsep Hmep Hqep Heref Hex.
  destruct Hex as (t' & Htle).
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hgetl & muxp & semp & qp & Hgetp & Hor).
  destruct Hor as [Hmp | [Hsp | Hqp]]; subst.
  lets H00: mux_ecb_cre2 Hmep Hgetl Hgetp.
  simpljoin1.
  apply H in Heref. inverts Heref.
  lets H00: sem_ecb_cre2 Hsep Hgetl Hgetp.
  simpljoin1.
  apply H in Heref. inverts Heref.
  lets H00: q_ecb_cre2 Hqep Hgetl Hgetp.
  simpljoin1.
  apply H in Heref. inverts Heref.  
Qed. 

Lemma eib_ref_no_tsk_del: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs eid, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs -> 
    eib_ref semeibs muxeibs mqeibs eid -> 
    ~exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbdel eid.
Proof.
  introv Hsep Hmep Hqep Heref Hex.
  destruct Hex as (t' & Htle).
  lets H00: ecb_del Hsep Hmep Hqep Htle.
  simpljoin1.
  apply H1 in Heref.
  inverts Heref. 
Qed.

Lemma eibref_sametype_muxdel_preserve:
  forall semeibs muxeibs mqeibs eptr pos ow tp rcnt prot prioc wq cnsa mc,
    evref_same_type eptr semeibs muxeibs mqeibs ->
    evref_same_type eptr semeibs (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs. 
Proof.
  introv Hst.
  unfold evref_same_type in *.
  simpljoin1.
  splits; auto.
  -
    introv Hs.
    apply H in Hs.
    simpljoin1.
    splits; auto.
    introv Href. apply H2.
    unfold muxeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H4. inverts H4.
    rewrite set_a_get_a' in H4; eauto.
    repeat eexists; eauto.
  -
    introv Hm.
    apply H0.
    unfold muxeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H2. inverts H2.
    rewrite set_a_get_a' in H2; eauto.
    repeat eexists; eauto.
  -
    introv Hq.
    lets H00: H1 Hq.
    simpljoin1. splits; auto.
    introv Href. apply H3.
    unfold muxeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H4. inverts H4.
    rewrite set_a_get_a' in H4; eauto.
    repeat eexists; eauto.
Qed.

Lemma muxref_distinct_muxdel_preserve:
  forall muxeibs ep pos ow tp rcnt prot prioc wq cnsa mc, 
    muxref_distinct muxeibs ep->
    muxref_distinct (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) ep.  
Proof.
  introv Hdis.
  unfold muxref_distinct in *.
  introv Hget1 Hget2.
  casetac pos pos1 Ht Hf.
  subst. rewrite set_a_get_a in Hget1. inverts Hget1.
  rewrite set_a_get_a' in Hget1; eauto.
  casetac pos pos2 Ht' Hf'.
  subst. rewrite set_a_get_a in Hget2. inverts Hget2.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma eibref_distinct_muxdel_preserve: 
  forall semeibs muxeibs mqeibs pos ow tp rcnt prot prioc wq cnsa mc, 
    eibref_distinct semeibs muxeibs mqeibs ->
    eibref_distinct semeibs (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs.
Proof.
  introv Hed.
  unfold eibref_distinct in *.
  intros.
  specialize (Hed eptr).
  simpljoin1. splits; auto.
  eapply eibref_sametype_muxdel_preserve; eauto.
  unfold muxref_distinct.
  introv Hget1 Hget2.
  eapply muxref_distinct_muxdel_preserve; eauto.
Qed.

(* Lemma muxeib_ref_infonull_preserve:
  forall muxeibs pos ow tp rcnt prot prioc wq cnsa eptr, 
    muxeib_ref  (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa)) eptr ->
    muxeib_ref muxeibs eptr.
Proof.
  introv Hmr.
  unfold muxeib_ref in *.
  simpljoin1.
  casetac pos x He Hne.
  subst.
  rewrite set_a_get_a in H. inverts H.
  rewrite set_a_get_a' in H; eauto.
  repeat eexists; eauto.
Qed. *)

Lemma eib_ref_muxdel_preserve:
  forall semeibs pos ow tp rcnt prot prioc wq cnsa mc muxeibs qeibs eptr, 
    eib_ref semeibs (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) qeibs eptr -> 
    eib_ref semeibs muxeibs qeibs eptr. 
Proof.
  introv Her.
  unfold eib_ref in *.
  destruct Her; auto.
  destruct H; auto.
  right. left. eapply muxeib_ref_infonull_preserve; eauto.
Qed.

Lemma eibref_distinct_muxref_nsemref:
  forall semeibs muxeibs mqeibs eid, 
    eibref_distinct semeibs muxeibs mqeibs ->
    muxeib_ref muxeibs eid ->
    ~semeib_ref semeibs eid. 
Proof.
  introv Hd Hsr Hmr.
  unfold eibref_distinct in Hd.
  lets H00: Hd eid.
  clear Hd.
  destruct H00 as (Hst & Hsd & Hmd & Hqd).
  unfold evref_same_type in Hst.
  simpljoin1.
  apply H0 in Hsr.
  simpljoin1.
  tryfalse.
Qed.

Lemma eibref_distinct_muxref_nmqref:
  forall semeibs muxeibs mqeibs eid, 
    eibref_distinct semeibs muxeibs mqeibs ->
    muxeib_ref muxeibs eid ->
    ~mqeib_ref mqeibs eid. 
Proof.
  introv Hd Hsr Hmr.
  unfold eibref_distinct in Hd.
  lets H00: Hd eid.
  clear Hd.
  destruct H00 as (Hst & Hsd & Hmd & Hqd).
  unfold evref_same_type in Hst.
  simpljoin1.
  apply H0 in Hsr.
  simpljoin1.
  tryfalse.
Qed.

Lemma sem_ecb_p_muxdel_preserve: 
  forall locmp ptrmp els els' fecbh fecbvl semeibs muxeibs mqeibs pos ow tp rcnt prot prioc wq cnsa mc o ct pevent_blk i1 eptr etbl eid, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    isptr fecbh -> 
    get ptrmp ct = Some (Vnull, Vnull, Vnull) ->
    get muxeibs pos = Some (Valid_Addr (pevent_blk, Int.zero), ow, tp, rcnt, prot, prioc, wq, cnsa, mc) ->
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre1 eid) ->
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre2 eid) ->
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbdel eid) -> 
    join els' (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els  ->
    SEM_ECB_P locmp ptrmp els' (Vptr eid)
              ((V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: eptr :: etbl :: fecbh :: nil) :: fecbvl)
              semeibs (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs. 
Proof.
  introv Hsep Hisptr Hgetp Heib Hncre1 Hncre2 Hndel Hjo.
  unfold SEM_ECB_P in Hsep.
  unfold SEM_ECB_P.
  introv Hgetp'.
  lets H00: Hsep Hgetp'.
  clear Hsep.
  casetac t ct Heqt Hneqt.
  -
    subst.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
  -
    destruct H00 as [Hcre1 | [Hcre2 | Hnml]].
    +
      destruct Hcre1 as (Hgetl' & Hnin & Hnref & Hnone).
      left.
      split; auto.
      casetac eptr0 eid Heqe Hneqe.
      *
        subst.
        false. apply Hncre1.
        exists t.
        unfold tsk_loc_ev.
        split; auto.
        do 3 eexists. split; eauto.
      *
        splits; auto.
        introv Hptrin. apply Hnin.
        eapply ptr_in_ecblist_tail; eauto. 
        introv Hf. apply Hnref. eapply eib_ref_muxdel_preserve; eauto.
        clear -Hjo Hnone.
        eapply join_get_none_rev1; eauto.
    +
      destruct Hcre2 as (Hgetl' & Hnref & Hsem).
      right. left.
      splits; auto.
      introv Hf. apply Hnref. eapply eib_ref_muxdel_preserve; eauto.
      casetac eptr0 eid Ht Hf.
      subst.
      false. apply Hncre2. exists t.
      unfold tsk_loc_ev. splits; auto.
      do 3 eexists. split; eauto.
      unfold is_sem in Hsem. unfold is_sem.
      simpljoin1.
      exists x x0.
      assert (join (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els' els).
      join auto.
      eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
    +
      destruct Hnml as (Hgetl' & Hor).
      right. right.
      split; auto.
      casetac eptr0 eid Ht Hf.
      *
        subst.
        right.
        unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
        asserts_rewrite ((os_inv.beq_addrval eid eid) = true).
        {
          unfold os_inv.beq_addrval.
          destruct eid.
          rewrite OSTimeTickPure.beq_pos_true.
          rewrite Int.eq_true.
          tauto. (* pure_auto.  *)     }
        auto.
      *
        destruct Hor. 
        left.
        unfold is_evt in H. unfold is_evt.
        destruct H.
        left. unfold is_sem in H. unfold is_sem. simpljoin1. exists x x0.
        assert (join (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        destruct H.
        right; left. unfold is_mux in H. unfold is_mux. simpljoin1. exists x x0 x1.
        assert (join (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right; right. unfold is_que in H. unfold is_que. simpljoin1. exists x x0 x1 x2.
        assert (join (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right.
        unfold ptr_in_ecblist.
        unfold ptr_in_ecblist in H.
        unfold ptr_in_ecbsllseg; fold ptr_in_ecbsllseg.
        destruct (beq_val (Vptr eptr0) (Vptr eid)) eqn: E.
        auto.
        change (V_OSEventListPtr
                  (V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: eptr :: etbl :: fecbh :: nil)) with (Some fecbh).
        simpl. auto.
Qed.

Lemma mq_ecb_p_muxdel_preserve: 
  forall locmp ptrmp els els' fecbh fecbvl semeibs muxeibs mqeibs pos ow tp rcnt prot prioc wq cnsa mc o ct pevent_blk i1 eptr etbl eid, 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    isptr fecbh -> 
    get ptrmp ct = Some (Vnull, Vnull, Vnull) ->
    get muxeibs pos = Some (Valid_Addr (pevent_blk, Int.zero), ow, tp, rcnt, prot, prioc, wq, cnsa, mc) ->
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre1 eid) ->
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre2 eid) ->
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbdel eid) -> 
     join els' (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els  ->
    Q_ECB_P locmp ptrmp els' (Vptr eid)
              ((V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: eptr :: etbl :: fecbh :: nil) :: fecbvl)
              semeibs (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc)) mqeibs. 
Proof.
  introv Hqep Hisptr Hgetp Heib Hncre1 Hncre2 Hndel Hjo.
  unfold Q_ECB_P in Hqep.
  unfold Q_ECB_P.
  introv Hgetp'.
  lets H00: Hqep Hgetp'.
  clear Hqep.
  casetac t ct Heqt Hneqt.
  -
    subst.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
  -
    destruct H00 as (Hor3 & Hdel).
    split.  
    destruct Hor3 as [Hcre1 | [Hcre2 | Hnml]].
    +
      destruct Hcre1 as (Hgetl' & Hnin & Hnref & Hnone).
      left.
      split; auto.
      casetac eptr0 eid Heqe Hneqe.
      *
        subst.
        false. apply Hncre1.
        exists t.
        unfold tsk_loc_ev.
        split; auto.
        do 3 eexists. split; eauto.
      *
        splits; auto.
        introv Hptrin. apply Hnin.
        eapply ptr_in_ecblist_tail; eauto. 
        introv Hf. apply Hnref. eapply eib_ref_muxdel_preserve; eauto.
        clear -Hjo Hnone.
        eapply join_get_none_rev1; eauto.
    +
      destruct Hcre2 as (Hgetl' & Hnref & Hque).
      right. left.
      splits; auto.
      introv Hf. apply Hnref. eapply eib_ref_muxdel_preserve; eauto.
      casetac eptr0 eid Ht Hf.
      subst.
      false. apply Hncre2. exists t.
      unfold tsk_loc_ev. splits; auto.
      do 3 eexists. split; eauto.
      unfold is_que in Hque. unfold is_que.
      simpljoin1.
      exists x x0 x1 x2.
      assert (join (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els' els).
      join auto.
      eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
    +
      destruct Hnml as (Hgetl' & Hor).
      right. right.
      split; auto.
      casetac eptr0 eid Ht Hf.
      *
        subst.
        right.
        unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
        asserts_rewrite ((os_inv.beq_addrval eid eid) = true).
        {
          unfold os_inv.beq_addrval.
          destruct eid.
          rewrite OSTimeTickPure.beq_pos_true.
          rewrite Int.eq_true.
          tauto.
(*           pure_auto. *)
        }
        auto.
      *
        destruct Hor. 
        left.
        unfold is_evt in H. unfold is_evt.
        destruct H.
        left. unfold is_sem in H. unfold is_sem. simpljoin1. exists x x0.
        assert (join (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        destruct H.
        right; left. unfold is_mux in H. unfold is_mux. simpljoin1. exists x x0 x1.
        assert (join (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right; right. unfold is_que in H. unfold is_que. simpljoin1. exists x x0 x1 x2.
        assert (join (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right.
        unfold ptr_in_ecblist.
        unfold ptr_in_ecblist in H.
        unfold ptr_in_ecbsllseg; fold ptr_in_ecbsllseg.
        destruct (beq_val (Vptr eptr0) (Vptr eid)) eqn: E.
        auto.
        change (V_OSEventListPtr
                  (V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: eptr :: etbl :: fecbh :: nil)) with (Some fecbh).
        simpl. auto.
    +
      introv Hecbdel.
      specialize (Hdel Hecbdel).
      destruct Hdel as (Hque & Hnptr & Hnref).
      casetac eptr0 eid Heeq Heneq.  
      subst.
      false.
      apply Hndel. exists t. unfold tsk_loc_ev. split; auto.
      do 3 eexists. splits; eauto.
      splits; auto.
      unfold is_que in Hque. unfold is_que.
      simpljoin1.
      exists x x0 x1 x2.
      assert (join (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els' els).
      join auto.
      eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
      introv Hf. apply Hnref.
      eapply eib_ref_muxdel_preserve; eauto.
Qed. 

Lemma mux_ecb_p_muxdel_preserve: 
  forall locmp ptrmp els els' fecbh fecbvl semeibs muxeibs mqeibs pos ow tp rcnt prot prioc wq cnsa mc o ct pevent_blk i1 eptr etbl eid, 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    isptr fecbh -> 
    get ptrmp ct = Some (Vnull, Vnull, Vnull) ->
    get muxeibs pos = Some (Valid_Addr (pevent_blk, Int.zero), ow, tp, rcnt, prot, prioc, wq, cnsa, mc) ->
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre1 eid) ->
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre2 eid) ->
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbdel eid) -> 
    join els' (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els  ->
    MUX_ECB_P locmp ptrmp els' (Vptr eid)
              ((V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: eptr :: etbl :: fecbh :: nil) :: fecbvl)
              semeibs (set muxeibs pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa,mc)) mqeibs. 
Proof.
  introv Hmep Hisptr Hgetp Heib Hncre1 Hncre2 Hndel Hjo.
  unfold MUX_ECB_P in Hmep.
  unfold MUX_ECB_P.
  introv Hgetp'.
  lets H00: Hmep Hgetp'.
  clear Hmep.
  casetac t ct Heqt Hneqt.
  -
    subst.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
  -
    destruct H00 as [Hcre1 | [Hcre2 | Hnml]].
    +
      destruct Hcre1 as (Hgetl' & Hnin & Hnref & Hnone).
      left.
      split; auto.
      casetac eptr0 eid Heqe Hneqe.
      *
        subst.
        false. apply Hncre1.
        exists t.
        unfold tsk_loc_ev.
        split; auto.
        do 3 eexists. split; eauto.
      *
        splits; auto.
        introv Hptrin. apply Hnin.
        eapply ptr_in_ecblist_tail; eauto. 
        introv Hf. apply Hnref. eapply eib_ref_muxdel_preserve; eauto.
        clear -Hjo Hnone.
        eapply join_get_none_rev1; eauto.
    +
      destruct Hcre2 as (Hgetl' & Hnref & Hmux).
      right. left.
      splits; auto.
      introv Hf. apply Hnref. eapply eib_ref_muxdel_preserve; eauto.
      casetac eptr0 eid Ht Hf.
      subst.
      false. apply Hncre2. exists t.
      unfold tsk_loc_ev. splits; auto.
      do 3 eexists. split; eauto.
      unfold is_mux in Hmux. unfold is_mux.
      simpljoin1.
      exists x x0 x1.
      assert (join (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els' els).
      join auto.
      eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
    +
      destruct Hnml as (Hgetl' & Hor).
      right. right.
      split; auto.
      casetac eptr0 eid Ht Hf.
      *
        subst.
        right.
        unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
        asserts_rewrite ((os_inv.beq_addrval eid eid) = true).
        {
          unfold os_inv.beq_addrval.
          destruct eid.
          rewrite OSTimeTickPure.beq_pos_true.
          rewrite Int.eq_true.
          tauto.
(*           pure_auto. *)
        }
        auto.
      *
        destruct Hor. 
        left.
        unfold is_evt in H. unfold is_evt.
        destruct H.
        left. unfold is_sem in H. unfold is_sem. simpljoin1. exists x x0.
        assert (join (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        destruct H.
        right; left. unfold is_mux in H. unfold is_mux. simpljoin1. exists x x0 x1.
        assert (join (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right; right. unfold is_que in H. unfold is_que. simpljoin1. exists x x0 x1 x2. (* add x2 *)
        assert (join (sig eid (absmutexsem (i1 >>ᵢ $ 8) o, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right.
        unfold ptr_in_ecblist.
        unfold ptr_in_ecblist in H.
        unfold ptr_in_ecbsllseg; fold ptr_in_ecbsllseg.
        destruct (beq_val (Vptr eptr0) (Vptr eid)) eqn: E.
        auto.
        change (V_OSEventListPtr
                  (V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: eptr :: etbl :: fecbh :: nil)) with (Some fecbh).
        simpl. auto.
Qed.

(* used for mutex *)

Lemma evdel_nodup_normal_muxptr_preserve:
forall (locmp : EvAuxLocMod.map) (ptrmp : EvAuxPtrMod.map)
    (tid0 : Modules.tid) vp,
  isptr vp ->
  evdel_nodup locmp ptrmp ->
  get locmp tid0 = Some (V$ __EvLoc_normal) ->
  get ptrmp tid0 = Some (Vnull, Vnull, Vnull) ->
  evdel_nodup locmp (set ptrmp tid0 (vp, Vnull, Vnull)).
Proof.
  introv Hvp Hnd Hgetl Hgetp.
  destruct Hvp as [Hvp | (sid & Hvp)];
  subst vp.
  eapply EvAuxPtrMod.get_set_same in Hgetp.
  unfold set; unfold EvAuxPtrMap.
  rewrite Hgetp. auto.
  unfold evdel_nodup in *.
  introv Hneq Hgetl1 Hgetl2 Hptr1 Hptr2.
  casetac t1 tid0 Ht Hf.
  subst.
  rewrite Hgetl in Hgetl1. tryfalse.
  unfold evptr_of_tsk in Hptr1. 
  rewrite set_a_get_a' in Hptr1; eauto.
  casetac t2 tid0 Ht' Hf'.
  subst.
  rewrite Hgetl in Hgetl2. tryfalse.
  unfold evptr_of_tsk in Hptr2.
  rewrite set_a_get_a' in Hptr2; eauto.
Qed.

Lemma evcre_nodup_normal_muxptr_preserve:
  forall (locmp : EvAuxLocMod.map) (ptrmp : EvAuxPtrMod.map) 
    (tid : tid) vp,
   isptr vp ->
  evcre_nodup locmp ptrmp ->
  get locmp tid = Some (V$ __EvLoc_normal) ->
  get ptrmp tid = Some (Vnull, Vnull, Vnull) ->
  evcre_nodup locmp (set ptrmp tid (vp, Vnull, Vnull)).
Proof.
  introv Hvp Hnd Hgetl Hgetp.
  destruct Hvp as [Hvp | (sid & Hvp)];
  subst vp.
  eapply EvAuxPtrMod.get_set_same in Hgetp.
  unfold set; unfold EvAuxPtrMap.
  rewrite Hgetp. auto.
  unfold evcre_nodup in *.
  introv Hneq Hgetl1 Hgetl2 Hptr1 Hptr2.
  casetac t1 tid Ht Hf.
  subst.
  rewrite Hgetl in Hgetl1. destruct Hgetl1; tryfalse.
  unfold evptr_of_tsk in Hptr1. 
  rewrite set_a_get_a' in Hptr1; eauto.
  casetac t2 tid Ht' Hf'.
  subst.
  rewrite Hgetl in Hgetl2. destruct Hgetl2; tryfalse.
  unfold evptr_of_tsk in Hptr2.
  rewrite set_a_get_a' in Hptr2; eauto.
Qed.

Lemma sem_ecb_p_muxptr_normal_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs eid tid, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) ->
    is_mux els eid ->
    SEM_ECB_P locmp (set ptrmp tid (Vptr eid, Vnull, Vnull)) els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hsep Hgetl Hgetp Hmux.
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
 - rewrite set_a_get_a' in Hgetp'; eauto.
Qed.

Lemma mux_ecb_p_muxptr_normal_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs eid tid, 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) ->
    is_mux els eid ->
    MUX_ECB_P locmp (set ptrmp tid (Vptr eid, Vnull, Vnull)) els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hmep Hgetl Hgetp Hmux.
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
    right. right.
    splits; auto.
    left. unfold is_evt. auto.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
Qed.

Lemma mq_ecb_p_muxptr_normal_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs eid tid, 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) ->
    is_mux els eid ->
    Q_ECB_P locmp (set ptrmp tid (Vptr eid, Vnull, Vnull)) els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hqep Hgetl Hgetp Hmux.
  unfold Q_ECB_P in *.
  introv Hgetp'.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    destruct H00 as (Hor3 & Hdel).
    split.
    auto. 
    introv Hdel'.
    apply Hdel in Hdel'.
    simpljoin.
    splits; auto.
    introv Hex.
    apply H0.
    simpljoin1.
    casetac x tid Ht' Hf'.
    subst.
    rewrite Hgetl in H2. destruct H2; tryfalse. 
    unfold evptr_of_tsk in H3. 
    rewrite set_a_get_a' in H3; eauto.
Qed.

Lemma get_aux:
forall s vloc muxptr semptr qptr locmp ptrmp p1 tcbl1 tcbcur tcbl2 p2 rtbl ct tcbls P,
 s |= HEvLoc locmp ** HEvPtr ptrmp ** tcbllsegevaux p1 (tcbl1 ++ (tcbcur::tcbl2)) locmp ptrmp **
          AOSTCBList p1 p2 tcbl1 (tcbcur::tcbl2) rtbl ct tcbls **
         p_local OSLInv ct (logic_val (V$ 1)
                     :: logic_val vloc
                     :: logic_val muxptr :: logic_val semptr :: logic_val qptr :: nil) ** P ->
get ptrmp ct = Some (muxptr, semptr,qptr) /\
get locmp ct = Some vloc.
Proof.
introv Hsat.
sep lifts (3:: nil)%nat in Hsat.
eapply tcbllsegevaux_split3_join2_frm in Hsat; eauto.
sep normal in Hsat.
sep destruct Hsat.
sep split in Hsat.
subst.
assert (Hct_eq: (Vptr x10) = p2).
{ sep lifts (1:: 6 :: nil)%nat in Hsat.
    eapply tcblist_llsegaux_match_tn_frm in Hsat; eauto.
}
subst.
assert (ct = x10).
{ unfold AOSTCBList in Hsat. 
    sep normal in Hsat. sep destruct Hsat. sep split in Hsat.
    simpljoin1.
    congruence.
}
subst.
unfold p_local in Hsat. 
unfold OSLInv in Hsat.
unfold LINV in Hsat.
sep normal in Hsat.
sep destruct Hsat.
sep split in Hsat.
inverts H. inverts H6.
destruct H7 as (Hflag & Hevloc & Hmuxp &Hsemp & Hqp).
assert (x0 = x13).
{ gen_eq_muxp. clear -Hmuxp.  destruct Hmuxp; simpljoin; simpl; auto. }
assert (x1 = x14).
{ gen_eq_semp. clear -Hsemp.  destruct Hsemp; simpljoin; simpl; auto. }
assert (x2 = x15).
{ gen_eq_mqp. clear -Hqp.  destruct Hqp; simpljoin; simpl; auto. }
assert (x = x12).
{ gen_eq_evloc. clear -Hevloc.  destruct Hevloc as [ Heq | [Heq | [Heq | Heq]]]; simpljoin; simpl; auto. }
substs.
split; eapply join_get_get_r;
try eapply join_get_get_l;
eauto.
join auto.
join auto.
Qed.

Lemma mux_ecb_nml: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs semp qp eid ct, 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get ptrmp ct = Some (Vptr eid, semp, qp) ->
    get locmp ct = Some (V$ os_code_defs.__EvLoc_normal) ->
    (is_evt els eid \/ ptr_in_ecblist (Vptr eid) fecbh fecbvl).
Proof.
  introv Hsep Hgetp Hgetl.
  unfold MUX_ECB_P in Hsep.
  lets H00: Hsep Hgetp.
  clear Hsep.
  destruct H00 as [Hcre1 | [Hcre2 | Hdel]]; simpljoin1.
  rewrite Hgetl in H.
  tryfalse.
  rewrite Hgetl in H.
  tryfalse.
  auto.
Qed.  

(* used for sempost/ mutexpost/ semflush*)

Require Import ifun_spec.
Require Import seplog_trm_tacs.

Lemma llsegevaux_set_node : 
  forall vltcb vltcb' p s P head vl vl' locmp ptrmp,
    s |= llsegevaux head Vnull vltcb locmp ptrmp V_OSTCBNext ** P -> 
    tcblist_get p head vltcb = Some vl -> 
    set_node p vl' head vltcb = vltcb' -> 
    same_prev_next vl vl' -> 
    s |= llsegevaux head Vnull vltcb' locmp ptrmp V_OSTCBNext ** P. 
Proof.
  inductions vltcb.
  -
    intros.
    unfold llsegevaux in H.
    destruct vltcb'.
    unfold llsegevaux. sep auto.
    simpl in H1.
    inverts H1.
  -
    introv Hsat Htg Hsn Hspn.
    unfold llsegevaux in Hsat.
    fold llsegevaux in Hsat.
    sep normal in Hsat.
    sep destruct Hsat.
    sep split in Hsat.
    simpl in Hsn.
    destruct (beq_val p head) eqn: E.
    +
      subst vltcb'.
      unfold tcblist_get in Htg.
      rewrite E in Htg. inverts Htg. 
      unfold llsegevaux; fold llsegevaux.
      sep normal.
      exists x x0 x1 x2 x3 x4. do 2 eexists.
      sep split; eauto.
      unfolds in Hspn. 
      rewrite H0 in Hspn.
      destruct (V_OSTCBNext vl').
      simpljoin1.
      tryfalse.
    +
      destruct a.
      unfold V_OSTCBNext in H0. simpl in H0. inverts H0.
      rewrite <- Hsn.
      unfold llsegevaux; fold llsegevaux.
      unfolds in H0. simpl in H0. inverts H0.
      sep normal. sep eexists. 
      sep cancel evaux_node.
      sep_lifts_trms llsegevaux.
      eapply IHvltcb; eauto.
      sep cancel llsegevaux. 
      sep split; eauto.
      simpl in Htg. rewrite E in Htg.
      auto. 
Qed.

(* used for sem init *)

Lemma evref_same_type_preserve:
  forall eptr semeibs muxeibs mqeibs pos tp sc, 
    evref_same_type eptr semeibs muxeibs mqeibs ->
    get semeibs pos = Some (infonull, tp, sc) -> 
    evref_same_type eptr (set semeibs pos (infohold, tp, sc)) muxeibs mqeibs. 
Proof.
  introv Hest Hget.
  unfold evref_same_type in *.
  destructs Hest.
  splits.
  -
    introv Hs.
    unfold semeib_ref in *.
    simpljoin1.
    casetac pos x Ht Hf.
    subst. rewrite set_a_get_a in H2. inverts H2.
    apply H. 
    rewrite set_a_get_a' in H2; eauto.
  -
    introv Hm.
    lets H00: H0 Hm. destructs H00. splits; auto.
    introv Hs. apply H2.
    unfold semeib_ref in Hs. unfold semeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst. rewrite set_a_get_a in H4. inverts H4.
    rewrite set_a_get_a' in H4; eauto.
  -  
    introv Hq.
    lets H00: H1 Hq. destructs H00. splits; auto.
    introv Hs. apply H2.
    unfold semeib_ref in Hs. unfold semeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst. rewrite set_a_get_a in H4. inverts H4.
    rewrite set_a_get_a' in H4; eauto.
Qed.

Lemma eibref_distinct_null_holder_preserve: 
  forall tp pos semeibs muxeibs mqeibs sc, 
    eibref_distinct semeibs muxeibs mqeibs ->
    get semeibs pos = Some (infonull, tp, sc) -> 
    eibref_distinct (set semeibs pos (infohold, tp, sc)) muxeibs mqeibs. 
Proof. 
  introv Hed Hget.
  unfold eibref_distinct in *.
  intros.
  specialize (Hed eptr).
  mytac. splits; auto.
  eapply evref_same_type_preserve; eauto.
  unfold semref_distinct in *.
  introv Hget1 Hget2.
  casetac pos pos1 Heq1 Hneq1.
  subst. rewrite set_a_get_a in Hget1. inverts Hget1.
  casetac pos pos2 Heq2 Hneq2.
  subst. rewrite set_a_get_a in Hget2. inverts Hget2.
  rewrite set_a_get_a' in Hget1; eauto.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma SEM_ECB_P_null_holder_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos tp sc, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get semeibs pos = Some (infonull, tp, sc) ->
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl (set semeibs pos (infohold, tp, sc)) muxeibs mqeibs.
Proof.
  introv Hsep Hget.
  unfold SEM_ECB_P in *.
  introv Hptr.
  lets H00: Hsep Hptr. clear Hsep.
  destruct H00.
  - 
    left.
    simpljoin1.
    splits; auto.
    introv Href. apply H1.
    unfold eib_ref in *.
    destruct Href.
    left. unfold semeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H3. inverts H3.
    rewrite set_a_get_a' in H3; eauto.
    destruct H3; auto.
  -
    destruct H.
    +
      right; left.
      simpljoin1.
      splits; auto.
      introv Href.
      apply H0.
      unfold eib_ref in Href. unfold eib_ref.
      destruct Href.
      left.
      unfold semeib_ref in *.
      simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H2. inverts H2.
      rewrite set_a_get_a' in H2; eauto.
      destruct H2; auto.
    +    
      simpljoin1.
      right. right.
      splits; auto.
Qed.

Lemma MUX_ECB_P_null_holder_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos tp sc, 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get semeibs pos = Some (infonull, tp, sc) ->
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl (set semeibs pos (infohold, tp, sc)) muxeibs mqeibs. 
Proof.
  introv Hmep Hget.
  unfold MUX_ECB_P in *.
  introv Hptr.
  lets H00: Hmep Hptr. clear Hmep.
  destruct H00.
  - 
    left.
    simpljoin1.
    splits; auto.
    introv Href. apply H1.
    unfold eib_ref in *.
    destruct Href.
    left. unfold semeib_ref in *. simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H3. inverts H3.
    rewrite set_a_get_a' in H3; eauto.
    destruct H3; auto.
  -
    destruct H.
    +
      right; left.
      simpljoin1.
      splits; auto.
      introv Href.
      apply H0.
      unfold eib_ref in Href. unfold eib_ref.
      destruct Href.
      left.
      unfold semeib_ref in *.
      simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H2. inverts H2.
      rewrite set_a_get_a' in H2; eauto.
      destruct H2; auto.
    +    
      simpljoin1.
      right. right.
      splits; auto.
Qed.

Lemma Q_ECB_P_null_holder_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos tp sc, 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get semeibs pos = Some (infonull, tp, sc) ->
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl (set semeibs pos (infohold, tp, sc)) muxeibs mqeibs.  
Proof.
  introv Hqep Hget.
  unfold Q_ECB_P in *.
  introv Hptr.
  lets H00: Hqep Hptr. clear Hqep.
  destruct H00 as (Hor & Hdel).
  split.
  - (* part 1 *)
    destruct Hor.
    + 
      left.
      simpljoin1.
      splits; auto.
      introv Href. apply H1.
      unfold eib_ref in *.
      destruct Href.
      left. unfold semeib_ref in *. simpljoin1.
      casetac pos x Heq Hneq.
      subst. rewrite set_a_get_a in H3. inverts H3.
      rewrite set_a_get_a' in H3; eauto.
      destruct H3; auto.
    +
      destruct H.
      *
        right; left.
        simpljoin1.
        splits; auto.
        introv Href.
        apply H0.
        unfold eib_ref in Href. unfold eib_ref.
        destruct Href.
        left.
        unfold semeib_ref in *.
        simpljoin1.
        casetac pos x Heq Hneq.
        subst. rewrite set_a_get_a in H2. inverts H2.
        rewrite set_a_get_a' in H2; eauto.
        destruct H2; auto.
      *    
        simpljoin1.
        right. right.
        splits; auto.
  - (* part 2 *)
    clear Hor.
    introv Hgetl.
    specialize (Hdel Hgetl).
    simpljoin1.
    splits; auto.
    introv Href.
    apply H1.
    unfold eib_ref in Href. unfold eib_ref.
    destruct Href.
    left.
    unfold semeib_ref in *.
    simpljoin1.
    casetac pos x Heq Hneq.
    subst. rewrite set_a_get_a in H2. inverts H2.
    rewrite set_a_get_a' in H2; eauto.
    destruct H2; auto.
Qed.

Lemma evref_same_type_infonull_preserve:
  forall semeibs muxeibs mqeibs eptr pos tp sc,
    evref_same_type eptr semeibs muxeibs mqeibs ->
    evref_same_type eptr (set semeibs pos (infonull, tp, sc)) muxeibs mqeibs. 
Proof.
  introv Hst.
  unfold evref_same_type in *.
  simpljoin1.
  splits; auto.
  -
    introv Hs.
    apply H.
    unfold semeib_ref in Hs. unfold semeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst. rewrite set_a_get_a in H2. inverts H2.
    rewrite set_a_get_a' in H2; eauto.
  -
    introv Hm.
    lets H00: H0 Hm.
    simpljoin1. splits; auto.
    introv Hs. apply H2.
    unfold semeib_ref in Hs. unfold semeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst. rewrite set_a_get_a in H4. inverts H4.
    rewrite set_a_get_a' in H4; eauto.
  -
    introv Hq.
    lets H00: H1 Hq.
    simpljoin1. splits; auto.
    introv Hs. apply H2.
    unfold semeib_ref in Hs. unfold semeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst. rewrite set_a_get_a in H4. inverts H4.
    rewrite set_a_get_a' in H4; eauto.    
Qed.

Lemma semeib_ref_infonull_preserve:
  forall semeibs pos tp sc eptr, 
    semeib_ref (set semeibs pos (infonull, tp, sc)) eptr ->
    semeib_ref semeibs eptr.
Proof.
  introv Hsr.
  unfold semeib_ref in *.
  simpljoin1.
  casetac pos x He Hne.
  subst.
  rewrite set_a_get_a in H. inverts H.
  rewrite set_a_get_a' in H; eauto.
Qed.

Lemma eibref_infonull_preserve:
  forall semeibs pos tp sc muxeibs qeibs eptr, 
    eib_ref (set semeibs pos (infonull, tp, sc)) muxeibs qeibs eptr -> 
    eib_ref semeibs muxeibs qeibs eptr. 
Proof.
  introv Her.
  unfold eib_ref in *.
  destruct Her.
  left. eapply semeib_ref_infonull_preserve; eauto.
  right. auto.
Qed.

Lemma sem_ecb_p_infonull_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs pos tp sc tid, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    SEM_ECB_P (set locmp tid (V$ __EvLoc_normal)) ptrmp ecbls fecbh fecbvl
              (set semeibs pos (infonull, tp, sc)) muxeibs qeibs.
Proof.
  introv Hsep.
  unfold SEM_ECB_P in *.
  introv Hnull Hgetp.
  casetac tid t Heq Hneq.
  -
    subst.
    rewrite Hnull in Hgetp.
    inverts Hgetp.
  -
    rewrite set_a_get_a'; eauto.
    clear Hnull.
    lets H00: Hsep Hgetp.
    destruct H00.
    left.
    simpljoin1. splits; auto.
    introv Hf. apply H1.
    eapply eibref_infonull_preserve; eauto.

    destruct H.
    right. left.
    simpljoin1.
    splits; auto.
    introv Hf; apply H0. 
    eapply eibref_infonull_preserve; eauto.

    right. right.
    simpljoin1.
    splits; auto.
Qed.

Lemma mux_ecb_p_infonull_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs pos tp sc tid, 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    MUX_ECB_P (set locmp tid (V$ __EvLoc_normal)) ptrmp ecbls fecbh fecbvl
              (set semeibs pos (infonull, tp, sc)) muxeibs qeibs.
Proof.
  introv Hmep. 
  unfold MUX_ECB_P in *.
  introv Hnull Hgetp.
  casetac tid t Heq Hneq.
  -
    subst.
    rewrite Hnull in Hgetp.
    inverts Hgetp.
  -
    rewrite set_a_get_a'; eauto.
    clear Hnull.
    lets H00: Hmep Hgetp.
    destruct H00.
    left.
    simpljoin1. splits; auto.
    introv Hf. apply H1.
    eapply eibref_infonull_preserve; eauto.

    destruct H.
    right. left.
    simpljoin1.
    splits; auto.
    introv Hf; apply H0. 
    eapply eibref_infonull_preserve; eauto.

    right. right.
    simpljoin1.
    splits; auto.
Qed.

Lemma q_ecb_p_infonull_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs pos tp sc tid, 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    Q_ECB_P (set locmp tid (V$ __EvLoc_normal)) ptrmp ecbls fecbh fecbvl
              (set semeibs pos (infonull, tp, sc)) muxeibs qeibs.
Proof.
  introv Hqep. 
  unfold Q_ECB_P in *.
  introv Hnull Hgetp.
  casetac tid t Heq Hneq.
  -
    subst.
    rewrite Hnull in Hgetp.
    inverts Hgetp.
  -
    rewrite set_a_get_a'; eauto.
    clear Hnull.
    lets H00: Hqep Hgetp.
    destruct H00 as (Hor3 & Hdel).
    split.
    destruct Hor3.
    left.
    simpljoin1. splits; auto.
    introv Hf. apply H1.
    eapply eibref_infonull_preserve; eauto.

    destruct H.
    right. left.
    simpljoin1.
    splits; auto.
    introv Hf; apply H0. 
    eapply eibref_infonull_preserve; eauto.

    right. right.
    simpljoin1.
    splits; auto.
    introv Hget.
    lets H00: Hdel Hget.
    simpljoin1. splits; auto.
    2: {
      introv Hf; apply H1.
      eapply eibref_infonull_preserve; eauto.
    }
    introv Hex; apply H0.
    destruct Hex as (t' & Hcre12 & Hevptr).
    casetac tid t' Heq' Hneq'.
    subst.
    rewrite set_a_get_a in Hcre12. destruct Hcre12; tryfalse. 
    rewrite set_a_get_a' in Hcre12;eauto. 
Qed.
  
Lemma semref_distinct_infonull_preserve:
  forall semeibs ep pos tp sc, 
    semref_distinct semeibs ep->
    semref_distinct (set semeibs pos (infonull, tp, sc)) ep.  
Proof.
  introv Hdis.
  unfold semref_distinct in *.
  introv Hget1 Hget2.
  casetac pos pos1 Ht Hf.
  subst. rewrite set_a_get_a in Hget1. inverts Hget1.
  rewrite set_a_get_a' in Hget1; eauto.
  casetac pos pos2 Ht' Hf'.
  subst. rewrite set_a_get_a in Hget2. inverts Hget2.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.
  
Lemma eibref_distinct_infonull_preserve: 
  forall semeibs muxeibs mqeibs pos tp sc, 
    eibref_distinct semeibs muxeibs mqeibs ->
    eibref_distinct (set semeibs pos (infonull, tp, sc)) muxeibs mqeibs.
Proof.
  introv Hed.
  unfold eibref_distinct in *.
  intros.
  specialize (Hed eptr).
  simpljoin1. splits; auto.
  eapply evref_same_type_infonull_preserve; eauto.
  unfold semref_distinct.
  introv Hget1 Hget2.
  eapply semref_distinct_infonull_preserve; eauto.
Qed.

Lemma eibref_distinct_noref_eid_preserve: 
  forall semeibs muxeibs mqeibs eid pos tp sc, 
    eibref_distinct semeibs muxeibs mqeibs ->  
    ~ eib_ref semeibs muxeibs mqeibs eid -> 
    eibref_distinct (set semeibs pos (infotid eid, tp, sc)) muxeibs mqeibs.  
Proof. 
  introv Hed Hnref.
  unfold eibref_distinct in *.
  intro.
  specialize (Hed eptr).
  simpljoin1.
  splits; auto.
  -
    unfold evref_same_type.
    splits.
    +
      introv Hsref.
      unfold semeib_ref in Hsref.
      simpljoin1.
      casetac pos x Heq Hne.
      subst. rewrite set_a_get_a in H3. inverts H3.
      unfold eib_ref in Hnref.
      clear -Hnref. intuition.
      rewrite set_a_get_a' in H3; eauto.
      unfold evref_same_type in H.
      simpljoin1.
      apply H; auto.
      unfold semeib_ref. do 2 eexists; eauto.
    +
      introv Hmref.
      unfold muxeib_ref in Hmref. 
      simpljoin1.
      split.
      2: {
        unfold evref_same_type in H.
        simpljoin1.
        assert (HH: muxeib_ref muxeibs eptr).
        unfold muxeib_ref. do 8 eexists. eauto.
        apply H4 in HH. simpljoin1. auto.
      }
      unfold semeib_ref.
      introv Hex. simpljoin1.
      casetac pos x8 He Hne.
      subst. rewrite set_a_get_a in H4. inverts H4.
      apply Hnref.
      unfold eib_ref.
      right. left.
      unfold muxeib_ref. repeat eexists; eauto.
      rewrite set_a_get_a' in H4; eauto.
      unfold evref_same_type in H.
      simpljoin1.
      assert (HH: muxeib_ref muxeibs eptr).
      unfold muxeib_ref. do 8 eexists; eauto.
      apply H5 in HH.
      simpljoin1. apply H7.
      unfold semeib_ref. do 2 eexists; eauto.
    +
      introv Hqref.
      unfold mqeib_ref in Hqref.
      simpljoin1.
      split.
      2: {
        unfold evref_same_type in H.
        simpljoin1.
        assert (HH: mqeib_ref mqeibs eptr).
        unfold mqeib_ref. do 6 eexists; eauto.
        apply H5 in HH. simpljoin1. auto.
      }
      unfold semeib_ref.
      introv Hex. simpljoin1.
      casetac pos x6 He Hne.
      subst. rewrite set_a_get_a in H4. inverts H4.
      apply Hnref.
      unfold eib_ref.
      right. right. 
      unfold muxeib_ref. repeat eexists; eauto.
      rewrite set_a_get_a' in H4; eauto.
      unfold evref_same_type in H.
      simpljoin1.
      assert (HH: mqeib_ref mqeibs eptr).
      unfold mqeib_ref. do 6 eexists; eauto.
      apply H6 in HH.
      simpljoin1. apply H7.
      unfold semeib_ref. do 2 eexists; eauto.
  -
    unfold semref_distinct in H0. unfold semref_distinct.
    introv Hget1 Hget2.
    casetac pos pos1 He Hne.
    subst. rewrite set_a_get_a in Hget1. inverts Hget1.
    casetac pos1 pos2 He' Hne'.
    subst. rewrite set_a_get_a in Hget2. inverts Hget2.
    auto.
    rewrite set_a_get_a' in Hget2; eauto.
    false. apply Hnref.
    unfold eib_ref. left.
    unfold semeib_ref. do 2 eexists; eauto.
    rewrite set_a_get_a' in Hget1; eauto.
    casetac pos pos2 He' Hne'.
    subst. 
    rewrite set_a_get_a in Hget2; eauto.
    inverts Hget2.

    false. apply Hnref.
    unfold eib_ref. left.
    unfold semeib_ref. do 2 eexists.  eauto.
    rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma evcre_nodup_cre1_cre2_contra: 
  forall t tid eid locmp ptrmp, 
    evcre_nodup locmp ptrmp -> 
    t <> tid -> 
    tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid ->
    get locmp tid = Some (V$ __EvLoc_ecbcre2) ->
    get ptrmp tid = Some (Vnull, Vptr eid, Vnull) ->  
    False. 
Proof.
  introv Hcrendp Htne Htle Hgetl Hgetp.
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hgetl' & (mq & sp & qp & (Hgetp' & Hor3))).
  unfold evcre_nodup in Hcrendp.
  specialize (Hcrendp t tid eid eid Htne (or_introl Hgetl') (or_intror Hgetl)).
  cut (eid <> eid).
  intro Hf. tryfalse.
  apply Hcrendp.
  unfold evptr_of_tsk.
  destruct Hor3.
  subst. left. do 2 eexists; eauto.
  destruct H.
  subst. right; left. do 2 eexists; eauto.
  subst. right; right. do 2 eexists; eauto.
  unfold evptr_of_tsk.
  right; left. eauto.
Qed.

Lemma evcre_nodup_cre2_cre2_contra: 
  forall t tid eid locmp ptrmp, 
    evcre_nodup locmp ptrmp -> 
    t <> tid -> 
    tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid ->
    get locmp tid = Some (V$ __EvLoc_ecbcre2) ->
    get ptrmp tid = Some (Vnull, Vptr eid, Vnull) ->  
    False. 
Proof.
  introv Hcrendp Htne Htle Hgetl Hgetp.
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hgetl' & (mq & sp & qp & (Hgetp' & Hor3))).
  unfold evcre_nodup in Hcrendp.
  specialize (Hcrendp t tid eid eid Htne (or_intror Hgetl') (or_intror Hgetl)).
  cut (eid <> eid).
  intro Hf. tryfalse.
  apply Hcrendp.
  unfold evptr_of_tsk.
  destruct Hor3.
  subst. left. do 2 eexists; eauto.
  destruct H.
  subst. right; left. do 2 eexists; eauto.
  subst. right; right. do 2 eexists; eauto.
  unfold evptr_of_tsk.
  right; left. eauto.
Qed.

Lemma ecbdel_sem_contra:  
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs t eid, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs ->
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs qeibs -> 
    tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel eid ->
    is_sem ecbls eid ->
    False.
Proof.
  introv Hsep Hmep Hqep Htle Hsem.
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hgetl & (mp & sp & qp & (Hgetp & Hor3))).
  destruct Hor3.
  -
    subst.
    unfold MUX_ECB_P in Hmep.
    lets H00: Hmep Hgetp.
    rewrite Hgetl in H00.
    destruct H00.  simpljoin1. tryfalse. destruct H. simpljoin1. tryfalse. simpljoin1. tryfalse.
  -
    destruct H; subst.
    +
      unfold SEM_ECB_P in Hsep.
      lets H00: Hsep Hgetp.
      rewrite Hgetl in H00.
      inverts H00.
      simpljoin1. tryfalse. inverts H. simpljoin1. tryfalse. simpljoin1. tryfalse.
    +
      unfold Q_ECB_P in Hqep.
      lets H00: Hqep Hgetp.
      destruct H00 as (Hor3 & Hdel).
      apply Hdel in Hgetl.
      simpljoin1.
      clear - Hsem H.
      unfold is_sem in *. unfold is_que in *.
      simpljoin1.
      rewrite H in H0.
      inverts H0.
Qed.

Lemma n_eibref_diff_ptr_preserve: 
  forall semeibs muxeibs mqeibs eptr eid pos tp sc, 
    ~ eib_ref semeibs muxeibs mqeibs eptr ->
    eptr <> eid ->
    ~ eib_ref (set semeibs pos (infotid eid, tp, sc)) muxeibs mqeibs eptr. 
Proof.
  introv Hnref Hneq Heibref.
  apply Hnref.
  unfold eib_ref in *.
  inverts Heibref.
  2: { auto. }
  left.
  unfold semeib_ref in *.
  simpljoin1.
  casetac pos x He Hne.
  subst. rewrite set_a_get_a in H. inverts H.
  tryfalse.
  rewrite set_a_get_a' in H; eauto. 
Qed.
  
Lemma SEM_ECB_P_normal_null_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs tid eid tp sc pos, 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid) -> 
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid) -> 
    SEM_ECB_P (set locmp tid (V$ __EvLoc_normal)) (set ptrmp tid (Vnull, Vnull, Vnull)) ecbls fecbh fecbvl (set semeibs pos (infotid eid, tp, sc)) muxeibs mqeibs.
Proof.
  introv Hsep Hncre1 Hncre2.
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  casetac tid t Hteq Htne.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hsep Hgetp'.
    clear Hsep.
    rewrite set_a_get_a'; eauto.
    destruct H00.
    +
      destruct H as (Hgetl & Hnin & Hnref & Hnone).
      casetac eptr eid He Hne.
      * 
        subst.
        false.
        apply Hncre1.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.
      *
        left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve; eauto.
    +
      destruct H.
      *
        destruct H as (Hgetl & Hnin & Hnref & Hnone).
        casetac eptr eid He Hne.
        subst.
        false.
        apply Hncre2.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.

        right. left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve; eauto.
        unfold is_sem. eauto.
      *
        destruct H as (Hgetl & Hor2).
        right; right.
        splits; auto.
Qed.

Lemma MUX_ECB_P_normal_null_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs tid eid tp sc pos, 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid) -> 
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid) -> 
    MUX_ECB_P (set locmp tid (V$ __EvLoc_normal)) (set ptrmp tid (Vnull, Vnull, Vnull)) ecbls fecbh fecbvl (set semeibs pos (infotid eid, tp, sc)) muxeibs mqeibs.
Proof.
  introv Hmep Hncre1 Hncre2.
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  casetac tid t Hteq Htne.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hmep Hgetp'.
    clear Hmep.
    rewrite set_a_get_a'; eauto.
    destruct H00.
    +
      destruct H as (Hgetl & Hnin & Hnref & Hnone).
      casetac eptr eid He Hne.
      * 
        subst.
        false.
        apply Hncre1.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.
      *
        left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve; eauto.
    +
      destruct H.
      *
        destruct H as (Hgetl & Hnin & Hnref & Hnone).
        casetac eptr eid He Hne.
        subst.
        false.
        apply Hncre2.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.

        right. left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve; eauto.
        unfold is_mux. eauto.
      *
        destruct H as (Hgetl & Hor2).
        right; right.
        splits; auto.
Qed.

Lemma Q_ECB_P_normal_null_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs tid eid tp sc pos, 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid) -> 
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid) -> 
    ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel eid) ->  
    Q_ECB_P (set locmp tid (V$ __EvLoc_normal)) (set ptrmp tid (Vnull, Vnull, Vnull)) ecbls fecbh fecbvl (set semeibs pos (infotid eid, tp, sc)) muxeibs mqeibs.
Proof.
  introv Hqep Hncre1 Hncre2 Hndel.
  unfold Q_ECB_P in *. 
  introv Hgetp'. 
  casetac tid t Hteq Htne.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    rewrite set_a_get_a'; eauto.
    destruct H00 as (Hor3 & Hdel).
    split.
    destruct Hor3.
    +
      destruct H as (Hgetl & Hnin & Hnref & Hnone).
      casetac eptr eid He Hne.
      * 
        subst.
        false.
        apply Hncre1.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.
      *
        left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve; eauto.
    +
      destruct H.
      *
        destruct H as (Hgetl & Hnin & Hnref & Hnone).
        casetac eptr eid He Hne.
        subst.
        false.
        apply Hncre2.
        exists t. splits; auto.
        unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.

        right. left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve; eauto.
        unfold is_que. eauto.
      *
        destruct H as (Hgetl & Hor2).
        right; right.
        splits; auto.
    +
      introv Hgetl'.
      specialize (Hdel Hgetl').
      simpljoin1. splits; auto.
      introv Hex. apply H0.
      destruct Hex as (t' & Hcre12 & Hep).
      casetac tid t' Ht Hf.
      subst. rewrite set_a_get_a in Hcre12. destruct Hcre12; tryfalse.
      rewrite set_a_get_a' in Hcre12; eauto. 
      exists t'. splits; auto.
      unfold evptr_of_tsk in Hep. rewrite set_a_get_a' in Hep; eauto.
      eapply n_eibref_diff_ptr_preserve; eauto.
      casetac eptr eid Ht' Hf'.
      subst.
      false. apply Hndel. exists t. splits; auto.
      unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto.
      auto.
Qed.

Lemma eibref_distinct_set_pos_semeib: 
  forall semeibs muxeibs mqeibs pos e tp sc tp' sc', 
    eibref_distinct semeibs muxeibs mqeibs ->
    get semeibs pos = Some (e, tp, sc) -> 
    eibref_distinct (set semeibs pos (e, tp', sc')) muxeibs mqeibs. 
Proof.
  introv Hed Hget.
  unfold eibref_distinct in *.
  intro.
  specialize (Hed eptr).
  simpljoin1.
  splits; auto.
  -
    unfold evref_same_type in *.
    simpljoin1.
    splits; auto.
    introv Hre.
    apply H.
    unfold semeib_ref in Hre. unfold semeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst.
    rewrite set_a_get_a in H5.
    inverts H5.
    do 2 eexists; eauto.
    rewrite set_a_get_a' in H5; eauto.
    introv Hme.
    apply H3 in Hme.
    simpljoin1. splits; auto.
    introv H_. apply H5. 
    unfold semeib_ref in H_. unfold semeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst.
    rewrite set_a_get_a in H7.
    inverts H7.
    do 2 eexists; eauto.
    rewrite set_a_get_a' in H7; eauto.
    introv Hqe.
    apply H4 in Hqe.
    simpljoin1. splits; auto.
    introv H_. apply H5. 
    unfold semeib_ref in H_. unfold semeib_ref.
    simpljoin1.
    casetac pos x Ht Hf.
    subst.
    rewrite set_a_get_a in H7.
    inverts H7.
    do 2 eexists; eauto.
    rewrite set_a_get_a' in H7; eauto.
  -
    unfold semref_distinct in *.
    introv Hget1 Hget2.
    casetac pos pos1 Ht Hf.
    subst. rewrite set_a_get_a in Hget1. inverts Hget1.
    casetac pos1 pos2 Ht' Hf'.
    subst. rewrite set_a_get_a in Hget2. inverts Hget2. auto.    
    rewrite set_a_get_a' in Hget2; eauto.
    rewrite set_a_get_a' in Hget1; eauto.
    casetac pos pos2 Ht' Hf'.
    subst.
    rewrite set_a_get_a in Hget2.
    inverts Hget2.
    eapply H0; eauto.
    rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma n_eibref_set_sem_type_preserve: 
  forall semeibs muxeibs mqeibs eptr pos e tp sc tp' sc', 
    ~ eib_ref semeibs muxeibs mqeibs eptr -> 
    get semeibs pos = Some (e, tp, sc) ->
    ~ eib_ref (set semeibs pos (e, tp', sc')) muxeibs mqeibs eptr. 
Proof.
  introv Hnr Hget.
  introv Hf. apply Hnr.
  unfold eib_ref in Hf. unfold eib_ref.
  destruct Hf.
  2: { auto. }
  left.
  unfold semeib_ref in *.
  simpljoin1.
  casetac pos x Ht Hf.
  subst. rewrite set_a_get_a in H. inverts H.
  do 2 eexists; eauto.
  rewrite set_a_get_a' in H; eauto.
Qed.

Lemma SEM_ECB_P_set_sem_type_preserve:  
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos e tp sc tp' sc', 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get semeibs pos = Some (e, tp, sc) -> 
    SEM_ECB_P locmp ptrmp ecbls fecbh fecbvl (set semeibs pos (e, tp', sc')) muxeibs mqeibs.
Proof.
  introv Hsep Hget.
  unfold SEM_ECB_P in *.
  introv Hget'.
  lets H00: Hsep Hget'. clear Hsep.
  destruct H00.
  left.
  simpljoin1. splits; auto.
  eapply n_eibref_set_sem_type_preserve; eauto.
  destruct H.
  simpljoin1.
  right; left.
  splits; auto.
  eapply n_eibref_set_sem_type_preserve; eauto.
  simpljoin1.
  right; right.
  splits; eauto.
Qed.

Lemma MUX_ECB_P_set_sem_type_preserve:  
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos e tp sc tp' sc', 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get semeibs pos = Some (e, tp, sc) -> 
    MUX_ECB_P locmp ptrmp ecbls fecbh fecbvl (set semeibs pos (e, tp', sc')) muxeibs mqeibs.
Proof.
  introv Hmep Hget.
  unfold MUX_ECB_P in *.
  introv Hget'.
  lets H00: Hmep Hget'. clear Hmep.
  destruct H00.
  left.
  simpljoin1. splits; auto.
  eapply n_eibref_set_sem_type_preserve; eauto.
  destruct H.
  simpljoin1.
  right; left.
  splits; auto.
  eapply n_eibref_set_sem_type_preserve; eauto.
  simpljoin1.
  right; right.
  splits; eauto.
Qed.

Lemma Q_ECB_P_set_sem_type_preserve:  
  forall locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs pos e tp sc tp' sc', 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl semeibs muxeibs mqeibs ->
    get semeibs pos = Some (e, tp, sc) -> 
    Q_ECB_P locmp ptrmp ecbls fecbh fecbvl (set semeibs pos (e, tp', sc')) muxeibs mqeibs.
Proof.
  introv Hqep Hget.
  unfold Q_ECB_P in *.
  introv Hget'.
  lets H00: Hqep Hget'. clear Hqep.
  destruct H00 as (Hor3 & Hdel).
  split. 
  -
    destruct Hor3.
    left.
    simpljoin1. splits; auto.
    eapply n_eibref_set_sem_type_preserve; eauto.
    destruct H.
    simpljoin1.
    right; left.
    splits; auto.
    eapply n_eibref_set_sem_type_preserve; eauto.
    simpljoin1.
    right; right.
    splits; eauto.
  -
    introv Hgetl.
    apply Hdel in Hgetl.
    simpljoin1.
    splits; auto.
    eapply n_eibref_set_sem_type_preserve; eauto.
Qed.

(* used for sem destroy *)

Lemma eibref_sametype_semdel_preserve:
  forall eptr semeibs muxeibs mqeibs pos tp sc, 
    evref_same_type eptr semeibs muxeibs mqeibs -> 
    evref_same_type eptr (set semeibs pos (infonull, tp, sc)) muxeibs mqeibs. 
Proof.
  introv Hst.
  unfold evref_same_type in *.
  simpljoin1.
  splits.
  -
    introv Hsr.
    cut (semeib_ref semeibs eptr).
    auto.
    unfold semeib_ref. unfold semeib_ref in Hsr.
    simpljoin1.
    casetac pos x Heq Hneq.
    subst.
    rewrite set_a_get_a in H2; eauto.
    inverts H2.
    rewrite set_a_get_a' in H2; eauto.
  -
    introv Hmr.
    apply H0 in Hmr.
    simpljoin1. splits; auto.
    introv Hsr. apply H2. 
    unfold semeib_ref. unfold semeib_ref in Hsr.
    simpljoin1.
    casetac pos x Heq Hneq.
    subst.
    rewrite set_a_get_a in H4; eauto.
    inverts H4.
    rewrite set_a_get_a' in H4; eauto.
  -
    introv Hqr.
    apply H1 in Hqr.
    simpljoin1. splits; auto.
    introv Hsr. apply H2. 
    unfold semeib_ref. unfold semeib_ref in Hsr.
    simpljoin1.
    casetac pos x Heq Hneq.
    subst.
    rewrite set_a_get_a in H4; eauto.
    inverts H4.
    rewrite set_a_get_a' in H4; eauto.
Qed.

Lemma semref_distinct_semdel_preserve: 
  forall semeibs eptr pos tp sc, 
    semref_distinct semeibs eptr -> 
    semref_distinct (set semeibs pos (infonull, tp, sc)) eptr. 
Proof.
  introv Hsr.
  unfold semref_distinct in *.
  introv Hget1 Hget2.
  casetac pos pos1 Heq Hneq.
  subst.
  rewrite set_a_get_a in Hget1; eauto.
  inverts Hget1.
  rewrite set_a_get_a' in Hget1; eauto.
  casetac pos pos2 Heq' Hneq'.
  subst.
  rewrite set_a_get_a in Hget2; eauto.
  inverts Hget2.
  rewrite set_a_get_a' in Hget2; eauto.
Qed. 

Lemma eibref_distinct_semdel_preserve: 
  forall semeibs muxeibs mqeibs pos tp sc, 
    eibref_distinct semeibs muxeibs mqeibs -> 
    eibref_distinct (set semeibs pos (infonull, tp, sc)) muxeibs mqeibs. 
Proof.
  introv Hed.
  unfold eibref_distinct in *.
  intro eptr.
  specialize (Hed eptr).
  simpljoin1.
  splits; auto.
  eapply eibref_sametype_semdel_preserve; eauto.
  eapply semref_distinct_semdel_preserve; eauto.
Qed. 

Lemma eib_ref_semdel_preserve: 
  forall pos tp sc semeibs muxeibs mqeibs eid, 
    eib_ref (set semeibs pos (infonull, tp, sc)) muxeibs mqeibs eid -> 
    eib_ref semeibs muxeibs mqeibs eid.  
Proof.
  introv Her.
  unfold eib_ref in *.
  destruct Her.
  left.
  unfold semeib_ref in *.  
  simpljoin1.
  casetac pos x Ht Hf.
  subst.
  rewrite set_a_get_a in H. inverts H.
  rewrite set_a_get_a' in H; eauto.
  right. auto.
Qed.

Local Open Scope list_scope.

Lemma sem_ecb_p_semdel_preserve: 
  forall locmp ptrmp els els' fecbh fecbvl semeibs muxeibs mqeibs pos tp sc ct pevent_blk i1 eptr etbl eid, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    isptr fecbh -> 
    get ptrmp ct = Some (Vnull, Vnull, Vnull) ->
    get semeibs pos = Some (infotid (pevent_blk, Int.zero), tp, sc) -> 
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre1 eid) ->
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre2 eid) ->
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbdel eid) -> 
    join els' (sig eid (abssem i1, nil)) els -> 
    SEM_ECB_P locmp ptrmp els' (Vptr eid)
              ((V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: eptr :: etbl :: fecbh :: nil) :: fecbvl)
              (set semeibs pos (infonull, tp, sc)) muxeibs mqeibs. 
Proof.
  introv Hsep Hisptr Hgetp Heib Hncre1 Hncre2 Hndel Hjo.
  unfold SEM_ECB_P in Hsep.
  unfold SEM_ECB_P.
  introv Hgetp'.
  lets H00: Hsep Hgetp'.
  clear Hsep.
  casetac t ct Heqt Hneqt.
  -
    subst.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
  -
    destruct H00 as [Hcre1 | [Hcre2 | Hnml]].
    +
      destruct Hcre1 as (Hgetl' & Hnin & Hnref & Hnone).
      left.
      split; auto.
      casetac eptr0 eid Heqe Hneqe.
      *
        subst.
        false. apply Hncre1.
        exists t.
        unfold tsk_loc_ev.
        split; auto.
        do 3 eexists. split; eauto.
      *
        splits; auto.
        introv Hptrin. apply Hnin.
        eapply ptr_in_ecblist_tail; eauto. 
        introv Hf. apply Hnref. eapply eib_ref_semdel_preserve; eauto.
        clear -Hjo Hnone.
        eapply join_get_none_rev1; eauto.
    +
      destruct Hcre2 as (Hgetl' & Hnref & Hsem).
      right. left.
      splits; auto.
      introv Hf. apply Hnref. eapply eib_ref_semdel_preserve; eauto.
      casetac eptr0 eid Ht Hf.
      subst.
      false. apply Hncre2. exists t.
      unfold tsk_loc_ev. splits; auto.
      do 3 eexists. split; eauto.
      unfold is_sem in Hsem. unfold is_sem.
      simpljoin1.
      exists x x0.
      assert (join (sig eid (abssem i1, nil)) els' els).
      join auto.
      eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
    +
      destruct Hnml as (Hgetl' & Hor).
      right. right.
      split; auto.
      casetac eptr0 eid Ht Hf.
      *
        subst.
        right.
        unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
        asserts_rewrite ((os_inv.beq_addrval eid eid) = true).
        {
          unfold os_inv.beq_addrval.
          destruct eid.
          rewrite OSTimeTickPure.beq_pos_true.
          rewrite Int.eq_true.
          tauto.
(*           pure_auto. *)
        }
        auto.
      *
        destruct Hor. 
        left.
        unfold is_evt in H. unfold is_evt.
        destruct H.
        left. unfold is_sem in H. unfold is_sem. simpljoin1. exists x x0.
        assert (join (sig eid (abssem i1, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        destruct H.
        right; left. unfold is_mux in H. unfold is_mux. simpljoin1. exists x x0 x1.
        assert (join (sig eid (abssem i1, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right; right. unfold is_que in H. unfold is_que. simpljoin1. exists x x0 x1 x2. (* add x2 *)
        assert (join (sig eid (abssem i1, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right.
        unfold ptr_in_ecblist.
        unfold ptr_in_ecblist in H.
        unfold ptr_in_ecbsllseg; fold ptr_in_ecbsllseg.
        destruct (beq_val (Vptr eptr0) (Vptr eid)) eqn: E.
        auto.
        change (V_OSEventListPtr
                  (V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: eptr :: etbl :: fecbh :: nil)) with (Some fecbh).
        simpl. auto.
Qed. 

Lemma mq_ecb_p_semdel_preserve: 
  forall locmp ptrmp els els' fecbh fecbvl semeibs muxeibs mqeibs pos tp sc ct pevent_blk i1 eptr etbl eid, 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    isptr fecbh -> 
    get ptrmp ct = Some (Vnull, Vnull, Vnull) ->
    get semeibs pos = Some (infotid (pevent_blk, Int.zero), tp, sc) -> 
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre1 eid) ->
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre2 eid) ->
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbdel eid) -> 
    join els' (sig eid (abssem i1, nil)) els -> 
    Q_ECB_P locmp ptrmp els' (Vptr eid)
              ((V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: eptr :: etbl :: fecbh :: nil) :: fecbvl)
              (set semeibs pos (infonull, tp, sc)) muxeibs mqeibs. 
Proof.
  introv Hqep Hisptr Hgetp Heib Hncre1 Hncre2 Hndel Hjo.
  unfold Q_ECB_P in Hqep.
  unfold Q_ECB_P.
  introv Hgetp'.
  lets H00: Hqep Hgetp'.
  clear Hqep.
  casetac t ct Heqt Hneqt.
  -
    subst.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
  -
    destruct H00 as (Hor3 & Hdel).
    split.  
    destruct Hor3 as [Hcre1 | [Hcre2 | Hnml]].
    +
      destruct Hcre1 as (Hgetl' & Hnin & Hnref & Hnone).
      left.
      split; auto.
      casetac eptr0 eid Heqe Hneqe.
      *
        subst.
        false. apply Hncre1.
        exists t.
        unfold tsk_loc_ev.
        split; auto.
        do 3 eexists. split; eauto.
      *
        splits; auto.
        introv Hptrin. apply Hnin.
        eapply ptr_in_ecblist_tail; eauto. 
        introv Hf. apply Hnref. eapply eib_ref_semdel_preserve; eauto.
        clear -Hjo Hnone.
        eapply join_get_none_rev1; eauto.
    +
      destruct Hcre2 as (Hgetl' & Hnref & Hque).
      right. left.
      splits; auto.
      introv Hf. apply Hnref. eapply eib_ref_semdel_preserve; eauto.
      casetac eptr0 eid Ht Hf.
      subst.
      false. apply Hncre2. exists t.
      unfold tsk_loc_ev. splits; auto.
      do 3 eexists. split; eauto.
      unfold is_que in Hque. unfold is_que.
      simpljoin1.
      exists x x0 x1 x2. (* add x2 *)
      assert (join (sig eid (abssem i1, nil)) els' els).
      join auto.
      eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
    +
      destruct Hnml as (Hgetl' & Hor).
      right. right.
      split; auto.
      casetac eptr0 eid Ht Hf.
      *
        subst.
        right.
        unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
        asserts_rewrite ((os_inv.beq_addrval eid eid) = true).
        {
          unfold os_inv.beq_addrval.
          destruct eid.
          rewrite OSTimeTickPure.beq_pos_true.
          rewrite Int.eq_true.
          tauto.
(*           pure_auto. *)
        }
        auto.
      *
        destruct Hor. 
        left.
        unfold is_evt in H. unfold is_evt.
        destruct H.
        left. unfold is_sem in H. unfold is_sem. simpljoin1. exists x x0.
        assert (join (sig eid (abssem i1, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        destruct H.
        right; left. unfold is_mux in H. unfold is_mux. simpljoin1. exists x x0 x1.
        assert (join (sig eid (abssem i1, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right; right. unfold is_que in H. unfold is_que. simpljoin1. exists x x0 x1 x2. (* add x2 *)
        assert (join (sig eid (abssem i1, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right.
        unfold ptr_in_ecblist.
        unfold ptr_in_ecblist in H.
        unfold ptr_in_ecbsllseg; fold ptr_in_ecbsllseg.
        destruct (beq_val (Vptr eptr0) (Vptr eid)) eqn: E.
        auto.
        change (V_OSEventListPtr
                  (V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: eptr :: etbl :: fecbh :: nil)) with (Some fecbh).
        simpl. auto.
    +
      introv Hecbdel.
      specialize (Hdel Hecbdel).
      destruct Hdel as (Hque & Hnptr & Hnref).
      casetac eptr0 eid Heeq Heneq.  
      subst.
      false.
      apply Hndel. exists t. unfold tsk_loc_ev. split; auto.
      do 3 eexists. splits; eauto.
      splits; auto.
      unfold is_que in Hque. unfold is_que.
      simpljoin1.
      exists x x0 x1 x2. (* add x2 *)
      assert (join (sig eid (abssem i1, nil)) els' els).
      join auto.
      eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
      introv Hf. apply Hnref.
      eapply eib_ref_semdel_preserve; eauto.
Qed. 

Lemma mux_ecb_p_semdel_preserve: 
  forall locmp ptrmp els els' fecbh fecbvl semeibs muxeibs mqeibs pos tp sc ct pevent_blk i1 eptr etbl eid, 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    isptr fecbh -> 
    get ptrmp ct = Some (Vnull, Vnull, Vnull) ->
    get semeibs pos = Some (infotid (pevent_blk, Int.zero), tp, sc) -> 
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre1 eid) ->
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbcre2 eid) ->
    ~ (exists t', tsk_loc_ev locmp ptrmp t' __EvLoc_ecbdel eid) -> 
    join els' (sig eid (abssem i1, nil)) els -> 
    MUX_ECB_P locmp ptrmp els' (Vptr eid)
              ((V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: eptr :: etbl :: fecbh :: nil) :: fecbvl)
              (set semeibs pos (infonull, tp, sc)) muxeibs mqeibs. 
Proof.
  introv Hmep Hisptr Hgetp Heib Hncre1 Hncre2 Hndel Hjo.
  unfold MUX_ECB_P in Hmep.
  unfold MUX_ECB_P.
  introv Hgetp'.
  lets H00: Hmep Hgetp'.
  clear Hmep.
  casetac t ct Heqt Hneqt.
  -
    subst.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
  -
    destruct H00 as [Hcre1 | [Hcre2 | Hnml]].
    +
      destruct Hcre1 as (Hgetl' & Hnin & Hnref & Hnone).
      left.
      split; auto.
      casetac eptr0 eid Heqe Hneqe.
      *
        subst.
        false. apply Hncre1.
        exists t.
        unfold tsk_loc_ev.
        split; auto.
        do 3 eexists. split; eauto.
      *
        splits; auto.
        introv Hptrin. apply Hnin.
        eapply ptr_in_ecblist_tail; eauto. 
        introv Hf. apply Hnref. eapply eib_ref_semdel_preserve; eauto.
        clear -Hjo Hnone.
        eapply join_get_none_rev1; eauto.
    +
      destruct Hcre2 as (Hgetl' & Hnref & Hmux).
      right. left.
      splits; auto.
      introv Hf. apply Hnref. eapply eib_ref_semdel_preserve; eauto.
      casetac eptr0 eid Ht Hf.
      subst.
      false. apply Hncre2. exists t.
      unfold tsk_loc_ev. splits; auto.
      do 3 eexists. split; eauto.
      unfold is_mux in Hmux. unfold is_mux.
      simpljoin1.
      exists x x0 x1.
      assert (join (sig eid (abssem i1, nil)) els' els).
      join auto.
      eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
    +
      destruct Hnml as (Hgetl' & Hor).
      right. right.
      split; auto.
      casetac eptr0 eid Ht Hf.
      *
        subst.
        right.
        unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
        asserts_rewrite ((os_inv.beq_addrval eid eid) = true).
        {
          unfold os_inv.beq_addrval.
          destruct eid.
          rewrite OSTimeTickPure.beq_pos_true.
          rewrite Int.eq_true.
          tauto.
(*           pure_auto. *)
        }
        auto.
      *
        destruct Hor. 
        left.
        unfold is_evt in H. unfold is_evt.
        destruct H.
        left. unfold is_sem in H. unfold is_sem. simpljoin1. exists x x0.
        assert (join (sig eid (abssem i1, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        destruct H.
        right; left. unfold is_mux in H. unfold is_mux. simpljoin1. exists x x0 x1.
        assert (join (sig eid (abssem i1, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right; right. unfold is_que in H. unfold is_que. simpljoin1. exists x x0 x1 x2. (* add x2 *)
        assert (join (sig eid (abssem i1, nil)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right.
        unfold ptr_in_ecblist.
        unfold ptr_in_ecblist in H.
        unfold ptr_in_ecbsllseg; fold ptr_in_ecbsllseg.
        destruct (beq_val (Vptr eptr0) (Vptr eid)) eqn: E.
        auto.
        change (V_OSEventListPtr
                  (V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: eptr :: etbl :: fecbh :: nil)) with (Some fecbh).
        simpl. auto.
Qed. 

(* used for OSSemCreate *)

Lemma semecb_preserve_cre1:
  forall locmp ptrmp ecbls hd' vl vll semeibs muxeibs qeibs ct sid, 
    SEM_ECB_P locmp ptrmp ecbls (Vptr sid) (vl::vll) semeibs muxeibs qeibs -> 
    get ecbls sid = None -> 
    V_OSEventListPtr vl = Some hd' -> 
    isptr hd' -> 
    ~ptr_in_ecblist (Vptr sid) hd' vll -> 
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 sid) ->
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 sid) -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_normal sid) -> 
    (* (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel sid) ->    *)
    SEM_ECB_P (set locmp ct (V$ __EvLoc_ecbcre1)) (set ptrmp ct (Vnull, Vptr sid, Vnull))
              ecbls hd' vll semeibs muxeibs qeibs.  
Proof.
  introv Hsep Hnone Hnxtptr Hisptr Hnotin Hsem Hmux Hque Hncre1 Hncre2.
  introv Hnnm.
  (* introv Hndel. *)
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - subst t.
    rewrite set_a_get_a.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
    left.
    splits; auto.
    eapply inactive_ecb_no_eib_ref; eauto.
  - rewrite set_a_get_a' in Hgetp'; auto.
    lets H00: Hsep Hgetp'.
    clear Hsep.
    rewrite set_a_get_a'; auto.
    destruct H00 as [Hcre1 | [Hcre2 | Hnrm]].
    + left.
      destructs Hcre1.
      splits; auto.
      unfold isptr in Hisptr.
      destruct Hisptr.
      subst hd'. introv Hf. unfold ptr_in_ecblist in Hf. destruct vll; tryfalse.
      destruct H4. subst hd'. 
      eapply n_ptr_in_ecblist_tail; eauto.
    + right. left. 
      auto.
    + right. right.
      destructs Hnrm.
      splits; auto.
      destruct H1.
      left; auto.
      right.
      assert (Hneq: eptr <> sid).
      {
        introv Heq. apply Hnnm.
        subst.
        exists t. unfold tsk_loc_ev. splits; auto.
        do 3 eexists. splits; eauto.
      }
      eapply ptr_in_ecblist_tail; eauto.
Qed.

Lemma muxecb_preserve_cre1:
  forall locmp ptrmp ecbls hd' vl vll semeibs muxeibs qeibs ct sid, 
    MUX_ECB_P locmp ptrmp ecbls (Vptr sid) (vl::vll) semeibs muxeibs qeibs -> 
    get ecbls sid = None -> 
    V_OSEventListPtr vl = Some hd' -> 
    isptr hd' -> 
    ~ptr_in_ecblist (Vptr sid) hd' vll -> 
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 sid) ->
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 sid) -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_normal sid) -> 
    MUX_ECB_P (set locmp ct (V$ __EvLoc_ecbcre1)) (set ptrmp ct (Vnull, Vptr sid, Vnull))
              ecbls hd' vll semeibs muxeibs qeibs.  
Proof.
  introv Hmep Hnone Hnxtptr Hisptr Hnotin Hsem Hmux Hque Hncre1 Hncre2.
  introv Hnnm.
  (* introv Hndel. *)
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - subst t.    
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'. 
  - rewrite set_a_get_a' in Hgetp'; auto.
    rewrite set_a_get_a'; auto.
    lets H00: Hmep Hgetp'.
    clear Hmep.

    destruct H00 as [Hcre1 | [Hcre2 | Hnrm]].
    + left.
      destructs Hcre1.
      splits; auto.
      unfold isptr in Hisptr.
      destruct Hisptr.
      subst hd'. introv Hf. unfold ptr_in_ecblist in Hf. destruct vll; tryfalse.
      destruct H4. subst hd'. 
      eapply n_ptr_in_ecblist_tail; eauto.
    + right. left. 
      auto.
    + right. right.
      destructs Hnrm.
      splits; auto.
      destruct H1.
      left; auto.
      right.
      assert (Hneq: eptr <> sid).
      {
        introv Heq. apply Hnnm.
        subst.
        exists t. unfold tsk_loc_ev. splits; auto.
        do 3 eexists. splits; eauto.
      }
      eapply ptr_in_ecblist_tail; eauto.
Qed.

Lemma qecb_preserve_cre1:
  forall locmp ptrmp ecbls hd' vl vll semeibs muxeibs qeibs ct sid, 
    Q_ECB_P locmp ptrmp ecbls (Vptr sid) (vl::vll) semeibs muxeibs qeibs -> 
    get ecbls sid = None -> 
    V_OSEventListPtr vl = Some hd' -> 
    isptr hd' -> 
    ~ptr_in_ecblist (Vptr sid) hd' vll -> 
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 sid) ->
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 sid) -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_normal sid) -> 
    (~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel sid) ->
    Q_ECB_P (set locmp ct (V$ __EvLoc_ecbcre1)) (set ptrmp ct (Vnull, Vptr sid, Vnull))
            ecbls hd' vll semeibs muxeibs qeibs.  
Proof.
  introv Hqep Hnone Hnxtptr Hisptr Hnotin Hsem Hmux Hque Hncre1 Hncre2.
  introv Hnnm Hndel.
  (* introv Hndel. *)
  unfold Q_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - subst t.
    rewrite set_a_get_a.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'. 
  - rewrite set_a_get_a' in Hgetp'; auto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    rewrite set_a_get_a'; auto.
    split.
    +
      destruct H00 as [[Hcre1 | [Hcre2 | Hnrm]] Hdel].
      * left. 
        destructs Hcre1. 
        splits; auto.
        unfold isptr in Hisptr.
        destruct Hisptr.
        subst hd'. introv Hf. unfold ptr_in_ecblist in Hf. destruct vll; tryfalse.
        destruct H4. subst hd'. 
        eapply n_ptr_in_ecblist_tail; eauto.
      * right. left.
        auto.
      * right. right.
        destructs Hnrm.
        splits; auto.
        destruct H1.
        left; auto.
        right.
        assert (Hneq: eptr <> sid).
        {
          destruct H0.
          introv Heq. apply Hnnm. subst.
          exists t. unfold tsk_loc_ev. splits; auto.
          do 3 eexists. splits; eauto.
          introv Heq. apply Hndel. subst.
          exists t. unfold tsk_loc_ev. splits; auto.
          do 3 eexists. splits; eauto.        
        }
        eapply ptr_in_ecblist_tail; eauto.
    +
      introv Hdel.
      destruct H00 as (H' & Hdel0).
      lets H00: Hdel0 Hdel.
      destructs H00.
      splits; auto.
      introv Hf. apply H1. 
      destruct Hf as (t0 & Hor & Hep).
      assert (Hneq: eptr <> sid).
      {
        introv Heq.
        subst.
        unfold is_que in H0.
        destruct H0 as (x & y & pwl & qws & Hget).
        unfold get in Hnone. unfold EcbMap in Hnone.
        unfold get in Hget. unfold EcbMap in Hget.
        rewrite Hnone in Hget. inverts Hget. 
      }
      assert (Hneqct: t0 <> ct).
      {
        intro. subst.
        unfold evptr_of_tsk in Hep. 
        destruct Hep.
        do 2 destruct H3. rewrite set_a_get_a in H3. inverts H3.
        destruct H3.
        do 2 destruct H3. rewrite set_a_get_a in H3. inverts H3. apply Hneq; auto.
        do 2 destruct H3. rewrite set_a_get_a in H3. inverts H3.
      }
      rewrite set_a_get_a' in Hor; eauto.
      exists t0.
      splits; auto.
      unfold evptr_of_tsk in *.
      rewrite set_a_get_a' in Hep; auto.
Qed.
  

Lemma evcre_nodup_cre1_preserve:
  forall locmp ptrmp eid ct, 
    evcre_nodup locmp ptrmp ->
    ~(exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid) ->
    ~(exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid) -> 
    evcre_nodup (set locmp ct (V$ __EvLoc_ecbcre1)) (set ptrmp ct (Vnull, Vptr eid, Vnull)). 
Proof.
  introv Hndp Hnex1 Hnex2.
  unfold evcre_nodup.
  introv Hneqt Hget1 Hget2 Hptr1 Hptr2.
  assert (H: t1 = ct \/ t1 <> ct) by tauto.  
  destruct H.
  -
    subst.
    assert (eptr1 = eid). 
    {
      unfold evptr_of_tsk in Hptr1.    
      destruct Hptr1.
      simpljoin1. rewrite set_a_get_a in H. inverts H.
      destruct H.
      simpljoin1. rewrite set_a_get_a in H. inverts H. auto.
      simpljoin1. rewrite set_a_get_a in H. inverts H.
    }
    subst.
    rewrite set_a_get_a' in Hget2; eauto.
    unfold evptr_of_tsk in Hptr2.
    rewrite set_a_get_a' in Hptr2; eauto.
    introv Heqp.
    subst.
    destruct Hptr2.  
    simpljoin1.
    destruct Hget2.
    apply Hnex1. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    apply Hnex2. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    destruct H.
    simpljoin1.
    destruct Hget2.
    apply Hnex1. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    apply Hnex2. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    simpljoin1.
    destruct Hget2.
    apply Hnex1. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    apply Hnex2. exists t2. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
  -
    assert (H': t2 = ct \/ t2 <> ct) by tauto.
    destruct H'.
    +
      subst.
      assert (eptr2 = eid).
      {
        unfold evptr_of_tsk in Hptr2.
        destruct Hptr2.
        simpljoin1. rewrite set_a_get_a in H0. inverts H0.
        destruct H0.
        simpljoin1. rewrite set_a_get_a in H0. inverts H0. auto.
        simpljoin1. rewrite set_a_get_a in H0. inverts H0.
      }
      subst.
      rewrite set_a_get_a' in Hget1; eauto.
      unfold evptr_of_tsk in Hptr1.
      rewrite set_a_get_a' in Hptr1; eauto.
      introv Heqp.
      subst.
      destruct Hptr1.
      simpljoin1.
      destruct Hget1.
      apply Hnex1. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
      apply Hnex2. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
      destruct H0.
      simpljoin1.
      destruct Hget1.
      apply Hnex1. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
      apply Hnex2. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
      simpljoin1.
      destruct Hget1.
      apply Hnex1. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
      apply Hnex2. exists t1. unfold tsk_loc_ev. splits; auto. do 3 eexists. splits; eauto.
    +
      rewrite set_a_get_a' in Hget1; eauto.
      rewrite set_a_get_a' in Hget2; eauto.
      unfold evcre_nodup in Hndp.
      lets H00: Hndp Hneqt Hget1 Hget2.
      eapply H00; eauto.
      unfold evptr_of_tsk in Hptr1. rewrite set_a_get_a' in Hptr1; eauto.
      unfold evptr_of_tsk in Hptr2. rewrite set_a_get_a' in Hptr2; eauto.
Qed.  

Lemma evdel_nodup_cre1_preserve: 
  forall locmp ptrmp eid ct, 
    evdel_nodup locmp ptrmp ->
    ~(exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid) ->
    ~(exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid) -> 
    evdel_nodup (set locmp ct (V$ __EvLoc_ecbcre1)) (set ptrmp ct (Vnull, Vptr eid, Vnull)). 
Proof.
  introv Hevdel Hnex1 Hnex2.
  unfold evdel_nodup.
  introv Hneqt Hdel1 Hdel2 Hptr1 Hptr2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst.
  rewrite set_a_get_a in Hdel1. inverts Hdel1.
  rewrite set_a_get_a' in Hdel1; eauto.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst.
  rewrite set_a_get_a in Hdel2. inverts Hdel2.
  rewrite set_a_get_a' in Hdel2; eauto.
  lets H00: Hevdel Hneqt Hdel1 Hdel2.  
  eapply H00; eauto.
  unfold evptr_of_tsk in Hptr1. rewrite set_a_get_a' in Hptr1; eauto.
  unfold evptr_of_tsk in Hptr2. rewrite set_a_get_a' in Hptr2; eauto. 
Qed.

Lemma cre_nodup_no_cre1: 
  forall locmp ptrmp ct sid, 
    evcre_nodup locmp ptrmp ->  
    get locmp ct = Some (V$ __EvLoc_ecbcre1) -> 
    get ptrmp ct = Some (Vnull, Vptr sid, Vnull) -> 
    ~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 sid. 
Proof.
  introv Hndp Hcre1 Hp.
  introv Hex.
  destruct Hex as (t & (Hneq & Htle)).
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hl & (mp & sp & qp & Hp' & Hor)).
  unfold evcre_nodup in Hndp.
  destruct Hor.
  - 
    subst mp.
    assert (Hf: sid <> sid).
    {
      apply Hndp with (t1 := t) (t2 := ct); auto.
      unfold evptr_of_tsk. left. do 2 eexists; eauto.
      unfold evptr_of_tsk. right. left. do 2 eexists; eauto.
    }
    apply Hf; auto.
  -
    destruct H.
    +
      subst sp.
      assert (Hf: sid <> sid). 
      {
        apply Hndp with (t1 := t) (t2 := ct); auto.
        unfold evptr_of_tsk. right. left. do 2 eexists; eauto.
        unfold evptr_of_tsk. right. left. do 2 eexists; eauto.
      }
      apply Hf; auto.
    +
      subst qp.
      assert (Hf: sid <> sid).
      {
        apply Hndp with (t1 := t) (t2 := ct); auto.
        unfold evptr_of_tsk. right. right. do 2 eexists; eauto.
        unfold evptr_of_tsk. right. left. do 2 eexists; eauto.
      }
      apply Hf; auto.
Qed.  

Lemma cre_nodup_no_cre2: 
  forall locmp ptrmp ct sid, 
    evcre_nodup locmp ptrmp ->  
    get locmp ct = Some (V$ __EvLoc_ecbcre1) -> 
    get ptrmp ct = Some (Vnull, Vptr sid, Vnull) -> 
    ~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 sid. 
Proof.
  introv Hndp Hcre1 Hp.
  introv Hex.
  destruct Hex as (t & (Hneq & Htle)).
  unfold tsk_loc_ev in Htle.
  destruct Htle as (Hl & (mp & sp & qp & Hp' & Hor)).
  unfold evcre_nodup in Hndp.
  destruct Hor.
  - 
    subst mp.
    assert (Hf: sid <> sid).
    {
      apply Hndp with (t1 := t) (t2 := ct); auto.
      unfold evptr_of_tsk. left. do 2 eexists; eauto.
      unfold evptr_of_tsk. right. left. do 2 eexists; eauto.
    }
    apply Hf; auto.
  -
    destruct H.
    +
      subst sp.
      assert (Hf: sid <> sid). 
      {
        apply Hndp with (t1 := t) (t2 := ct); auto.
        unfold evptr_of_tsk. right. left. do 2 eexists; eauto.
        unfold evptr_of_tsk. right. left. do 2 eexists; eauto.
      }
      apply Hf; auto.
    +
      subst qp.
      assert (Hf: sid <> sid).
      {
        apply Hndp with (t1 := t) (t2 := ct); auto.
        unfold evptr_of_tsk. right. right. do 2 eexists; eauto.
        unfold evptr_of_tsk. right. left. do 2 eexists; eauto.
      }
      apply Hf; auto.
Qed.  

Lemma evcre_nodup_cre2_preserve: 
  forall locmp ptrmp ct sid,  
    evcre_nodup locmp ptrmp ->
    get ptrmp ct = Some (Vnull, Vptr sid, Vnull) -> 
    (~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 sid) -> 
    (~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 sid) -> 
    evcre_nodup (set locmp ct (V$ __EvLoc_ecbcre2)) ptrmp. 
Proof. 
  introv Hndp Hp Hnex1 Hnex2.
  unfold evcre_nodup in *.
  introv Hneq Hget1 Hget2 Hp1 Hp2 Heq.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  -
    subst t1.
    assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
    destruct Hor2.
    + 
      subst t2.
      apply Hneq; auto.
    +
      rewrite set_a_get_a' in Hget2; eauto.
      destruct Hget2.
      *
        apply Hnex1.
        exists t2. splits; auto.
        unfold tsk_loc_ev.
        splits; auto.
        subst eptr2.
        assert (eptr1 = sid).
        {
          unfold evptr_of_tsk  in Hp1.
          destruct Hp1.
          simpljoin1.
          rewrite Hp in H1. inverts H1.
          destruct H1.
          simpljoin1. rewrite Hp in H1. inverts H1. auto.
          simpljoin1. rewrite Hp in H1. inverts H1.
        }
        subst eptr1.
        unfold evptr_of_tsk in Hp2.
        destruct Hp2.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        destruct H1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
      *
        apply Hnex2.
        exists t2. splits; auto.
        unfold tsk_loc_ev.
        splits; auto.
        subst eptr2.
        assert (eptr1 = sid).
        {
          unfold evptr_of_tsk  in Hp1.
          destruct Hp1.
          simpljoin1.
          rewrite Hp in H1. inverts H1.
          destruct H1.
          simpljoin1. rewrite Hp in H1. inverts H1. auto.
          simpljoin1. rewrite Hp in H1. inverts H1.
        }
        subst eptr1.
        unfold evptr_of_tsk in Hp2.
        destruct Hp2.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        destruct H1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
  -
    assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
    destruct Hor2.
    + 
      subst t2.
      rewrite set_a_get_a' in Hget1; eauto.
      destruct Hget1.
      * 
        apply Hnex1.
        exists t1. splits; auto.
        unfold tsk_loc_ev.
        splits; auto.
        subst eptr1.
        assert (eptr2 = sid).
        {
          unfold evptr_of_tsk  in Hp2.
          destruct Hp2.
          simpljoin1.
          rewrite Hp in H1. inverts H1.
          destruct H1.
          simpljoin1. rewrite Hp in H1. inverts H1. auto.
          simpljoin1. rewrite Hp in H1. inverts H1.
        }
        subst eptr2.
        unfold evptr_of_tsk in Hp1.
        destruct Hp1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        destruct H1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
      *
        apply Hnex2.
        exists t1. splits; auto.
        unfold tsk_loc_ev.
        splits; auto.
        subst eptr1.
        assert (eptr2 = sid).
        {
          unfold evptr_of_tsk  in Hp2.
          destruct Hp2.
          simpljoin1.
          rewrite Hp in H1. inverts H1.
          destruct H1.
          simpljoin1. rewrite Hp in H1. inverts H1. auto.
          simpljoin1. rewrite Hp in H1. inverts H1.
        }
        subst eptr2.
        unfold evptr_of_tsk in Hp1.
        destruct Hp1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        destruct H1.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
        simpljoin1. rewrite H1. do 3 eexists; eauto.
    +
      rewrite set_a_get_a' in Hget1, Hget2; eauto.
      lets H00: Hndp Hneq Hget1 Hget2 Hp1 Hp2.
      apply H00 in Heq. 
      auto.
Qed.

Lemma sem_ecb_cre2_preserve: 
  forall locmp ptrmp ecbls fecbh ecbvl ct n eptr semeibs muxeibs qeibs, 
    SEM_ECB_P locmp ptrmp ecbls fecbh ecbvl semeibs muxeibs qeibs ->  
    (* get locmp ct = Some (V$ __EvLoc_ecbcre1) -> *)
    get ptrmp ct = Some (Vnull, Vptr eptr, Vnull) -> 
    get ecbls eptr = None ->  
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eptr) -> 
    SEM_ECB_P (set locmp ct (V$ __EvLoc_ecbcre2)) ptrmp (set ecbls eptr (abssem n, nil))
              fecbh ecbvl semeibs muxeibs qeibs.  
Proof.
  introv Hsep (* Hgetl *) Hgetp Hnone Hsem Hmux Hq Hnex.
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - (* t = ct *)
    subst t.
    right. left.
    splits.
    rewrite set_a_get_a. auto.
    eapply inactive_ecb_no_eib_ref; eauto.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'; auto.
    unfold is_sem.
    do 2 eexists.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
    rewrite set_a_get_a. eauto. 
  - (* t <> ct *)
    rewrite set_a_get_a'; eauto.
    lets H00: Hsep Hgetp'.
    clear Hsep.
    destruct H00.
    + 
      left.
      simpljoin1. splits; auto.
      rewrite set_a_get_a'; auto.
      introv Heqptr.
      subst eptr.
      apply Hnex.
      exists t. splits; auto. 
      unfold tsk_loc_ev.
      splits; auto.
      do 3 eexists. eauto.
    +
      destruct H0. 
      right. left.
      simpljoin1.
      splits; auto.
      assert (Hor': eptr = eptr0 \/ eptr <> eptr0) by tauto.
      destruct Hor'.
      subst.  unfold is_sem. rewrite set_a_get_a. do 2 eexists; eauto.
      unfold is_sem. rewrite set_a_get_a'; eauto. 

      right. right.
      simpljoin1.
      splits; auto.
      destruct H1.
      2: { right; auto. }
      left. 
      unfold is_evt in *. 
      assert (Hor': eptr = eptr0 \/ eptr <> eptr0) by tauto.
      destruct Hor'.
      subst.
      left. unfold is_sem. rewrite set_a_get_a. do 2 eexists; eauto. 
      unfold is_sem, is_mux, is_que.
      rewrite set_a_get_a'; eauto.
Qed.

Lemma mux_ecb_cre2_preserve: 
  forall locmp ptrmp ecbls fecbh ecbvl ct n eptr semeibs muxeibs qeibs, 
    MUX_ECB_P locmp ptrmp ecbls fecbh ecbvl semeibs muxeibs qeibs ->  
    (* get locmp ct = Some (V$ __EvLoc_ecbcre1) -> *)
    get ptrmp ct = Some (Vnull, Vptr eptr, Vnull) -> 
    get ecbls eptr = None ->  
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eptr) -> 
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eptr) -> 
    MUX_ECB_P (set locmp ct (V$ __EvLoc_ecbcre2)) ptrmp (set ecbls eptr (abssem n, nil))
              fecbh ecbvl semeibs muxeibs qeibs.  
Proof.
  introv Hmep (* Hgetl *) Hgetp Hnone Hsem Hmux Hq Hnex1 Hnex2.
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - (* t = ct *)
    subst t.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
  - (* t <> ct *)
    rewrite set_a_get_a'; eauto.
    lets H00: Hmep Hgetp'.
    clear Hmep.
    destruct H00.
    + 
      left.
      simpljoin1. splits; auto.
      rewrite set_a_get_a'; auto.
      introv Heqptr.
      subst eptr.
      apply Hnex1.
      exists t. splits; auto. 
      unfold tsk_loc_ev.
      splits; auto.
      do 3 eexists. eauto.
    +
      destruct H0. 
      right. left.
      simpljoin1.
      splits; auto.
      unfold is_mux.
      rewrite set_a_get_a'; eauto.
      introv Heqptr.
      subst eptr.
      apply Hnex2.
      exists t.
      split; auto.
      unfold tsk_loc_ev.
      split; auto.
      do 3 eexists. splits; eauto.

      right. right.
      simpljoin1.
      splits; auto.
      destruct H1.
      2: { right; auto. }
      left. 
      unfold is_evt in *. 
      assert (Hor': eptr = eptr0 \/ eptr <> eptr0) by tauto.
      destruct Hor'.
      subst.
      left. unfold is_sem. rewrite set_a_get_a. do 2 eexists; eauto. 
      unfold is_sem, is_mux, is_que.
      rewrite set_a_get_a'; eauto.
Qed.   

Lemma q_ecb_cre2_preserve: 
  forall locmp ptrmp ecbls fecbh ecbvl ct n eptr semeibs muxeibs qeibs, 
    Q_ECB_P locmp ptrmp ecbls fecbh ecbvl semeibs muxeibs qeibs ->  
    get locmp ct = Some (V$ __EvLoc_ecbcre1) -> 
    get ptrmp ct = Some (Vnull, Vptr eptr, Vnull) -> 
    get ecbls eptr = None ->  
    RH_SEM_EINFO_ECB_P ecbls semeibs -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs ecbls -> 
    RH_EIBlk_ECBlk_Q_P ecbls qeibs -> 
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eptr) -> 
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eptr) -> 
    ~(exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel eptr) -> 
    Q_ECB_P (set locmp ct (V$ __EvLoc_ecbcre2)) ptrmp (set ecbls eptr (abssem n, nil))
              fecbh ecbvl semeibs muxeibs qeibs.  
Proof.
  introv Hqep Hgetl Hgetp Hnone Hsem Hmux Hq Hnex1 Hnex2 Hnex3.
  unfold Q_ECB_P in *. 
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - (* t = ct *)
    subst t.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
  - (* t <> ct *)
    rewrite set_a_get_a'; eauto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    destruct H00 as (Hor3 & Hdel).
    split. 
    destruct Hor3.
    * left.
      simpljoin1. splits; auto.
      rewrite set_a_get_a'; auto.
      introv Heqptr.
      subst eptr.
      apply Hnex1.
      exists t. splits; auto. 
      unfold tsk_loc_ev.
      splits; auto.
      do 3 eexists. eauto.
    * destruct H0.
      right. left.
      simpljoin1.
      splits; auto.
      unfold is_que.
      rewrite set_a_get_a'; eauto.
      introv Heqptr. subst eptr.
      apply Hnex2.
      exists t. splits; auto. unfold tsk_loc_ev. splits; auto. do 3 eexists; eauto. 

      simpljoin1.
      right. right.
      split; auto.
      destruct H1.
      2: { right. auto. }
      left.
      unfold is_evt in *.
      assert (Hor': eptr = eptr0 \/ eptr <> eptr0) by tauto.
      destruct Hor'.
      subst.
      left. unfold is_sem. rewrite set_a_get_a. do 2 eexists; eauto. 
      unfold is_sem, is_mux, is_que.
      rewrite set_a_get_a'; eauto.
    *
      introv Hlocdel.
      lets H00: Hdel Hlocdel.
      unfold is_que. rewrite set_a_get_a'; eauto. 
      simpljoin1. 
      splits; auto.
      2: { (* eptr <> eptr0 *) 
        introv Heqptr.  subst eptr.
        apply Hnex3.
        exists t. split; auto.
        unfold tsk_loc_ev.
        split; auto.
        do 3 eexists; eauto.
      }
      introv Hex.
      apply H1.
      destruct Hex as (t' & Hcre12 & Hevptr).
      assert (t' = ct \/ t' <> ct) by tauto.
      destruct H3.
      subst.
      exists ct.
      split; auto.
      rewrite set_a_get_a' in Hcre12; eauto. 
Qed.

Lemma mq_ecb_nml: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs semp mutp eid ct, 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get ptrmp ct = Some (mutp, semp, Vptr eid) ->
    get locmp ct = Some (V$ os_code_defs.__EvLoc_normal) ->
    (is_evt els eid \/ ptr_in_ecblist (Vptr eid) fecbh fecbvl).
Proof.
  introv Hsep Hgetp Hgetl.
  unfold Q_ECB_P in Hsep.
  lets H00: Hsep Hgetp.
  clear Hsep.
  destruct H00.
  destruct H.
  simpljoin1. rewrite Hgetl in H. tryfalse.
  destruct H.
  simpljoin1. rewrite Hgetl in H. tryfalse.
  simpljoin1.
  destruct H.
  simpljoin1. auto.
  simpljoin1. rewrite Hgetl in H. tryfalse.
Qed.


Lemma evcre_nodup_normal_qptr_preserve:
  forall (locmp : EvAuxLocMod.map) (ptrmp : EvAuxPtrMod.map) 
    (tid : tid) vp,
   isptr vp ->
  evcre_nodup locmp ptrmp ->
  get locmp tid = Some (V$ __EvLoc_normal) ->
  get ptrmp tid = Some (Vnull, Vnull, Vnull) ->
  evcre_nodup locmp (set ptrmp tid (Vnull, Vnull, vp)).
Proof.
  introv Hvp Hnd Hgetl Hgetp.
  destruct Hvp as [Hvp | (sid & Hvp)];
  subst vp.
  eapply EvAuxPtrMod.get_set_same in Hgetp.
  unfold set; unfold EvAuxPtrMap.
  rewrite Hgetp. auto.
  unfold evcre_nodup in *.
  introv Hneq Hgetl1 Hgetl2 Hptr1 Hptr2.
  casetac t1 tid Ht Hf.
  subst.
  rewrite Hgetl in Hgetl1. destruct Hgetl1; tryfalse.
  unfold evptr_of_tsk in Hptr1. 
  rewrite set_a_get_a' in Hptr1; eauto.
  casetac t2 tid Ht' Hf'.
  subst.
  rewrite Hgetl in Hgetl2. destruct Hgetl2; tryfalse.
  unfold evptr_of_tsk in Hptr2.
  rewrite set_a_get_a' in Hptr2; eauto.
Qed.

Lemma evdel_nodup_normal_qptr_preserve:
forall (locmp : EvAuxLocMod.map) (ptrmp : EvAuxPtrMod.map)
    (tid0 : Modules.tid) vp,
  isptr vp ->
  evdel_nodup locmp ptrmp ->
  get locmp tid0 = Some (V$ __EvLoc_normal) ->
  get ptrmp tid0 = Some (Vnull, Vnull, Vnull) ->
  evdel_nodup locmp (set ptrmp tid0 (Vnull , Vnull, vp)).
Proof.
  introv Hvp Hnd Hgetl Hgetp.
  destruct Hvp as [Hvp | (sid & Hvp)];
  subst vp.
  eapply EvAuxPtrMod.get_set_same in Hgetp.
  unfold set; unfold EvAuxPtrMap.
  rewrite Hgetp. auto.
  unfold evdel_nodup in *.
  introv Hneq Hgetl1 Hgetl2 Hptr1 Hptr2.
  casetac t1 tid0 Ht Hf.
  subst.
  rewrite Hgetl in Hgetl1. tryfalse.
  unfold evptr_of_tsk in Hptr1. 
  rewrite set_a_get_a' in Hptr1; eauto.
  casetac t2 tid0 Ht' Hf'.
  subst.
  rewrite Hgetl in Hgetl2. tryfalse.
  unfold evptr_of_tsk in Hptr2.
  rewrite set_a_get_a' in Hptr2; eauto.
Qed.

Lemma mq_ecb_p_qptr_normal_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs eid tid, 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) ->
    is_que els eid ->
    Q_ECB_P locmp (set ptrmp tid (Vnull, Vnull, Vptr eid)) els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
 introv Hqep Hgetl Hgetp Hq.
  unfold Q_ECB_P in *.
  introv Hgetp'.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
    splits. 
    right. right. split. left. auto.
    left. unfold is_evt. right. right. auto.
    intros. 
    split. auto. split.
    simpl.
    rewrite H in Hgetl. tryfalse.
    rewrite H in Hgetl. tryfalse.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    destruct H00 as (Hor3 & Hdel).
    split.
    auto. 
    introv Hdel'.
    apply Hdel in Hdel'.
    simpljoin.
    splits; auto.
    introv Hex.
    apply H0.
    simpljoin1.
    casetac x tid Ht' Hf'.
    subst.
    rewrite Hgetl in H2. destruct H2; tryfalse. 
    unfold evptr_of_tsk in H3. 
    rewrite set_a_get_a' in H3; eauto.
Qed.

Lemma mux_ecb_p_qptr_normal_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs eid tid, 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) ->
    is_que els eid ->
    MUX_ECB_P locmp (set ptrmp tid (Vnull, Vnull , Vptr eid)) els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hmep Hgetl Hgetp Hsem.
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  casetac tid t Ht Hf.
  -
    subst. 
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
Qed.

Lemma sem_ecb_p_qptr_normal_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs eid tid, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    get ptrmp tid = Some (Vnull, Vnull, Vnull) ->
    is_que els eid ->
    SEM_ECB_P locmp (set ptrmp tid (Vnull , Vnull, Vptr eid)) els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hsep Hgetl Hgetp Hmux.
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
 - rewrite set_a_get_a' in Hgetp'; eauto.
Qed.

(*************** preservation for OSQ *****************) 

Lemma sem_ecb_p_mq_set_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs sid ml n pwl wl ml' n' pwl' wl', 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    get els sid = Some (absmsgq ml n pwl ,wl) -> 
    SEM_ECB_P locmp ptrmp (set els sid (absmsgq ml' n' pwl' ,wl')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hsep Hget.
  unfold SEM_ECB_P in *.
  introv Hgetp.
  lets H00: Hsep Hgetp.
  clear Hsep.
  destruct H00 as [Hcre1 | [Hcre2 | Hnm]].
  -
    simpljoin1.
    left. splits; auto. 
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    unfold is_sem in *.
    casetac sid eptr Ht Hf.
    subst.
    rewrite Hget in H1.
    simpljoin. inverts H1.
    rewrite set_a_get_a'; eauto. 
  -
    right; right.
    simpljoin1.
    splits; auto.
    destruct H0; auto.
    left.
    unfold is_evt.
    casetac sid eptr Ht' Hf'.
    subst.
    right. right. unfold is_que. rewrite set_a_get_a.
    do 3 eexists; eauto.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a'; eauto.
Qed. 

Lemma mux_ecb_p_mq_set_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs sid ml n pwl wl ml' n' pwl' wl', 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
     get els sid = Some  (absmsgq ml n pwl ,wl) -> 
    MUX_ECB_P locmp ptrmp (set els sid (absmsgq ml' n' pwl' ,wl')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hmep Hget.
  unfold MUX_ECB_P in *.
  introv Hgetp.
  lets H00: Hmep Hgetp.
  clear Hmep.
  destruct H00 as [Hcre1 | [Hcre2 | Hnm]].
  - 
    simpljoin1.
    left. splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
   right; left.
    simpljoin1.
    splits; auto.
    unfold is_mux in *.
    casetac sid eptr Ht Hf.
    subst.
    rewrite Hget in H1.
    simpljoin. inverts H1.
    rewrite set_a_get_a'; eauto. 
  -
    right; right.
    simpljoin1.
    splits; auto.
    destruct H0; auto.
    left.
    unfold is_evt.
    casetac sid eptr Ht Hf.
    subst.
    right; right.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a; eauto.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a'; eauto.
Qed.   

Lemma mq_ecb_p_mq_set_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs sid ml n pwl wl ml' n' pwl' wl', 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    get els sid = Some (absmsgq ml n pwl ,wl) -> 
    Q_ECB_P locmp ptrmp (set els sid (absmsgq ml' n' pwl' ,wl')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hqep Hget.
  unfold Q_ECB_P in *.
  introv Hgetp.
  lets H00: Hqep Hgetp.
  clear Hqep.
  destruct H00 as (Hor3 & Hdel).
  split. 
  destruct Hor3 as [Hcre1 | [Hcre2 | Hnm]].
  - 
    simpljoin1.
    left. splits; auto.
    casetac sid eptr Ht Hf.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2.
    tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    right; left.
    simpljoin1.
    splits; auto.
    unfold is_que in *.
    casetac sid eptr Ht Hf.
    subst.
    rewrite set_a_get_a; eauto.
    rewrite set_a_get_a'; eauto. 
  -
    right; right.
    simpljoin1.
    splits; auto.
    destruct H0; auto.
    left.
    unfold is_evt.
    casetac sid eptr Ht Hf.
    subst.
    right; right.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a; eauto.
    unfold is_sem, is_mux, is_que.
    rewrite set_a_get_a'; eauto.
  -
    introv Hdel'.
    specialize (Hdel Hdel').
    simpljoin1.
    splits; auto.
    unfold is_que in *.
    casetac sid eptr Ht Hf.
    subst.
    rewrite set_a_get_a; eauto.
    rewrite set_a_get_a'; eauto. 
Qed.

(* used for OSQDel *)

Lemma evdel_nodup_del_nodel:
  forall locmp ptrmp ct eid, 
    tsk_loc_ev locmp ptrmp ct __EvLoc_ecbdel eid ->
    evdel_nodup locmp ptrmp ->
    ~exists t', t' <> ct /\ tsk_loc_ev locmp ptrmp t' __EvLoc_ecbdel eid. 
Proof.
  introv Htle Hnd.
  introv Hf.
  destruct Hf as (t' & Hdiff & Htle').
  unfold tsk_loc_ev in *.
  destruct Htle as (Hgetl & Hptr).
  destruct Htle' as (Hgetl' & Hptr').
  lets H00: Hnd Hdiff Hgetl' Hgetl.
  instantiate (1:=eid) in H00.
  instantiate (1:=eid) in H00. 
  assert (Hpt': evptr_of_tsk t' ptrmp eid).
  {
    simpljoin1.
    unfold evptr_of_tsk.
    destruct H1 as [Hp | [Hp | Hp]]; subst. 
    left. do 2 eexists; eauto.
    right; left. do 2 eexists; eauto.
    right; right. do 2 eexists; eauto. 
  }
  assert (Hpt: evptr_of_tsk ct ptrmp eid).
  {
    simpljoin1.
    unfold evptr_of_tsk.
    destruct H2 as [Hp | [Hp | Hp]]; subst. 
    left. do 2 eexists; eauto.
    right; left. do 2 eexists; eauto.
    right; right. do 2 eexists; eauto. 
  }
  specialize (H00 Hpt' Hpt).
  apply H00. auto. 
Qed. 

Lemma sem_ecb_p_qdel_preserve: 
  forall locmp ptrmp els els' fecbh fecbvl semeibs muxeibs mqeibs ct i msgs maxlen pwl wl eptr etbl eid pegrp lpetbl, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    isptr fecbh -> 
    get ptrmp ct = Some (Vnull, Vnull, Vptr eid) -> 
    (~ eib_ref semeibs muxeibs mqeibs eid) ->
    (~ (exists t0,
           (get locmp t0 = Some (V$ __EvLoc_ecbcre1) \/
            get locmp t0 = Some (V$ __EvLoc_ecbcre2)) /\
           evptr_of_tsk t0 ptrmp eid)) ->
    (~ (exists t', t' <> ct /\ tsk_loc_ev locmp ptrmp t' __EvLoc_ecbdel eid)) -> 
    join els' (sig eid (absmsgq msgs maxlen pwl, wl)) els -> 
    SEM_ECB_P locmp (set ptrmp ct (Vnull, Vnull, Vnull)) els' (Vptr eid)
              ((V$ OS_EVENT_TYPE_UNUSED :: Vint32 Int.zero :: Vint32 i :: eptr :: etbl :: fecbh :: pegrp :: lpetbl :: nil) :: fecbvl)
              semeibs muxeibs mqeibs.
Proof.
  introv Hsep Hisptr Hgetp Hnref Hncre Hndel Hjo.
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  casetac ct t Heqt Hneqt.
  -
    subst.
    rewrite set_a_get_a in Hgetp'. inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hsep Hgetp'. clear Hsep.
    destruct H00 as [Hcre1 | [Hcre2 | Hnml]].
    +
      destruct Hcre1 as (Hgetl' & Hnin & Hnref' & Hnone).
      left.
      split; auto.
      casetac eptr0 eid Heqe Hneqe.
      * subst.
        assert (Hf: get els eid = Some (absmsgq msgs maxlen pwl, wl)).
        { eapply join_get_r; eauto. apply get_a_sig_a. }
        rewrite Hnone in Hf. inverts Hf.
      * splits; auto.
        introv Hin'; apply Hnin.
        eapply ptr_in_ecblist_tail; eauto.
        eapply join_get_none_rev1; eauto.
    +
      destruct Hcre2 as (Hgetl' & Hnref' & Hsem). 
      right. left.
      splits; auto.
      unfold is_sem in *.
      simpljoin1.
      casetac eptr0 eid Ht Hf.
      * subst.
        assert (Hf: get els eid = Some (absmsgq msgs maxlen pwl, wl)).
        { eapply join_get_r; eauto. apply get_a_sig_a. }
        unfold get, EcbMap in H.
        unfold get, EcbMap in Hf.
        rewrite H in Hf. inverts Hf.
      * exists x x0.
        assert (join (sig eid (absmsgq msgs maxlen pwl, wl)) els' els). 
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
    +
      destruct Hnml as (Hgetl' & Hor). 
      right; right.
      split; auto.
      casetac eptr0 eid Ht Hf.
      * subst.
        right.
        unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
        asserts_rewrite ((os_inv.beq_addrval eid eid) = true).
        {
          unfold os_inv.beq_addrval.
          destruct eid.
          rewrite OSTimeTickPure.beq_pos_true. 
          rewrite Int.eq_true.
          tauto.
        }
        auto.
      * destruct Hor. 
        left.
        unfold is_evt in H. unfold is_evt.
        assert (join (sig eid (absmsgq msgs maxlen pwl, wl)) els' els).
        join auto.
        destruct H.
        left. unfold is_sem in H. unfold is_sem. simpljoin1. exists x x0.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        destruct H.
        right; left. unfold is_mux in H. unfold is_mux. simpljoin1. exists x x0 x1.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right; right. unfold is_que in H. unfold is_que. simpljoin1. exists x x0 x1 x2.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right.
        unfold ptr_in_ecblist.
        unfold ptr_in_ecblist in H.
        unfold ptr_in_ecbsllseg; fold ptr_in_ecbsllseg.
        destruct (beq_val (Vptr eptr0) (Vptr eid)) eqn: E.
        auto.
        unfold V_OSEventListPtr; simpl.
        auto.
Qed.

Lemma mux_ecb_p_qdel_preserve: 
  forall locmp ptrmp els els' fecbh fecbvl semeibs muxeibs mqeibs ct i msgs maxlen pwl wl eptr etbl eid pegrp lpetbl, 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    isptr fecbh -> 
    get ptrmp ct = Some (Vnull, Vnull, Vptr eid) -> 
    (~ eib_ref semeibs muxeibs mqeibs eid) ->
    (~ (exists t0,
           (get locmp t0 = Some (V$ __EvLoc_ecbcre1) \/
            get locmp t0 = Some (V$ __EvLoc_ecbcre2)) /\
           evptr_of_tsk t0 ptrmp eid)) ->
    (~ (exists t', t' <> ct /\ tsk_loc_ev locmp ptrmp t' __EvLoc_ecbdel eid)) -> 
    join els' (sig eid (absmsgq msgs maxlen pwl, wl)) els -> 
    MUX_ECB_P locmp (set ptrmp ct (Vnull, Vnull, Vnull)) els' (Vptr eid)
              ((V$ OS_EVENT_TYPE_UNUSED :: Vint32 Int.zero :: Vint32 i :: eptr :: etbl :: fecbh :: pegrp :: lpetbl :: nil) :: fecbvl)
              semeibs muxeibs mqeibs.
Proof.
  introv Hmep Hisptr Hgetp Hnref Hncre Hndel Hjo.
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  casetac ct t Heqt Hneqt.
  -
    subst.
    rewrite set_a_get_a in Hgetp'. inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hmep Hgetp'. clear Hmep. 
    destruct H00 as [Hcre1 | [Hcre2 | Hnml]].
    +
      destruct Hcre1 as (Hgetl' & Hnin & Hnref' & Hnone).
      left.
      split; auto.
      casetac eptr0 eid Heqe Hneqe.
      * subst.
        assert (Hf: get els eid = Some (absmsgq msgs maxlen pwl, wl)).
        { eapply join_get_r; eauto. apply get_a_sig_a. }
        rewrite Hnone in Hf. inverts Hf.
      * splits; auto.
        introv Hin'; apply Hnin.
        eapply ptr_in_ecblist_tail; eauto.
        eapply join_get_none_rev1; eauto.
    +
      destruct Hcre2 as (Hgetl' & Hnref' & Hmux). 
      right. left.
      splits; auto.
      unfold is_mux in *.
      simpljoin1.
      casetac eptr0 eid Ht Hf.
      * subst.
        assert (Hf: get els eid = Some (absmsgq msgs maxlen pwl, wl)).
        { eapply join_get_r; eauto. apply get_a_sig_a. }
        unfold get, EcbMap in H.
        unfold get, EcbMap in Hf.
        rewrite H in Hf. inverts Hf.
      * exists x x0 x1.
        assert (join (sig eid (absmsgq msgs maxlen pwl, wl)) els' els). 
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
    +
      destruct Hnml as (Hgetl' & Hor). 
      right; right.
      split; auto.
      casetac eptr0 eid Ht Hf.
      * subst.
        right.
        unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
        asserts_rewrite ((os_inv.beq_addrval eid eid) = true).
        {
          unfold os_inv.beq_addrval.
          destruct eid.
          rewrite beq_pos_true. 
          rewrite Int.eq_true.
          tauto.
        }
        auto.
      * destruct Hor. 
        left.
        unfold is_evt in H. unfold is_evt.
        assert (join (sig eid (absmsgq msgs maxlen pwl, wl)) els' els).
        join auto.
        destruct H.
        left. unfold is_sem in H. unfold is_sem. simpljoin1. exists x x0.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        destruct H.
        right; left. unfold is_mux in H. unfold is_mux. simpljoin1. exists x x0 x1.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right; right. unfold is_que in H. unfold is_que. simpljoin1. exists x x0 x1 x2.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right.
        unfold ptr_in_ecblist.
        unfold ptr_in_ecblist in H.
        unfold ptr_in_ecbsllseg; fold ptr_in_ecbsllseg.
        destruct (beq_val (Vptr eptr0) (Vptr eid)) eqn: E.
        auto.
        unfold V_OSEventListPtr; simpl.
        auto.
Qed.

Lemma evptr_of_tsk_setnull3_preserve:
  forall x ct eptr ptrmp, 
    evptr_of_tsk x (set ptrmp ct (Vnull, Vnull, Vnull)) eptr ->
    evptr_of_tsk x ptrmp eptr. 
Proof.
  introv Het.
  unfold evptr_of_tsk in*.
  casetac ct x Ht Hf.
  subst. rewrite set_a_get_a in Het.
  destruct Het as [H_ | [H_ | H_]]; simpljoin1; tryfalse. 
  rewrite set_a_get_a' in Het;  eauto.
Qed.

Lemma mq_ecb_p_qdel_preserve: 
  forall locmp ptrmp els els' fecbh fecbvl semeibs muxeibs mqeibs ct i msgs maxlen pwl wl eptr etbl eid pegrp lpetbl, 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    isptr fecbh -> 
    get ptrmp ct = Some (Vnull, Vnull, Vptr eid) -> 
    (~ eib_ref semeibs muxeibs mqeibs eid) ->
    (~ (exists t0,
           (get locmp t0 = Some (V$ __EvLoc_ecbcre1) \/
            get locmp t0 = Some (V$ __EvLoc_ecbcre2)) /\
           evptr_of_tsk t0 ptrmp eid)) ->
    (~ (exists t', t' <> ct /\ tsk_loc_ev locmp ptrmp t' __EvLoc_ecbdel eid)) -> 
    join els' (sig eid (absmsgq msgs maxlen pwl, wl)) els -> 
    Q_ECB_P locmp (set ptrmp ct (Vnull, Vnull, Vnull)) els' (Vptr eid)
            ((V$ OS_EVENT_TYPE_UNUSED :: Vint32 Int.zero :: Vint32 i :: eptr :: etbl :: fecbh :: pegrp :: lpetbl :: nil) :: fecbvl)
            semeibs muxeibs mqeibs.
Proof.
  introv Hqep Hisptr Hgetp Hnref Hncre Hndel Hjo.
  unfold Q_ECB_P in *. 
  introv Hgetp'.
  casetac ct t Heqt Hneqt.
  -
    subst. rewrite set_a_get_a in Hgetp'. inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    destruct H00 as (Hor3 & Hdel).
    split.
    +
      casetac eptr0 eid Heqe Hneqe.
      * subst.
        destruct Hor3 as [Hcre1 | [Hcre2 | Hcre3]].
        simpljoin1.
        false. apply Hncre.
        exists t. split. auto.
        clear -Hgetp'.
        unfold evptr_of_tsk. right; right. do 2 eexists; eauto.
        simpljoin1.
        false. apply Hncre.
        exists t. split. auto.
        unfold evptr_of_tsk. right; right. do 2 eexists; eauto.
        simpljoin1.
        right; right.
        split; auto.
        right.
        unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
        asserts_rewrite ((os_inv.beq_addrval eid eid) = true).
        {
          unfold os_inv.beq_addrval.
          destruct eid.
          rewrite beq_pos_true. 
          rewrite Int.eq_true.
          tauto.
        }
        auto.
      * destruct Hor3 as [Hcre1 | [Hcre2 | Hcre3]]; simpljoin1.
        left.
        splits; auto. 
        introv Hin'; apply H0.
        eapply ptr_in_ecblist_tail; eauto.
        eapply join_get_none_rev1; eauto.          
        right; left.
        splits; auto.
        unfold is_que in *.
        simpljoin1.
        exists x x0 x1 x2.          
        assert (join (sig eid (absmsgq msgs maxlen pwl, wl)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right; right.
        splits; auto.
        destruct H0.
        left. 
        unfold is_evt in H0. unfold is_evt. 
        assert (join (sig eid (absmsgq msgs maxlen pwl, wl)) els' els).
        join auto.
        destruct H0.
        left. unfold is_sem in H0. unfold is_sem. simpljoin1. exists x x0.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        destruct H0.
        right; left. unfold is_mux in H0. unfold is_mux. simpljoin1. exists x x0 x1.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right; right. unfold is_que in H0. unfold is_que. simpljoin1. exists x x0 x1 x2.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right.
        unfold ptr_in_ecblist.
        unfold ptr_in_ecblist in H.
        unfold ptr_in_ecbsllseg; fold ptr_in_ecbsllseg.
        destruct (beq_val (Vptr eptr0) (Vptr eid)) eqn: E.
        auto.
        unfold V_OSEventListPtr; simpl.
        auto.
    +
      introv Hgetl'.
      lets H00: Hdel Hgetl'. clear Hdel.
      simpljoin1.
      splits; auto.
      2: {
        introv Hex; apply H0.
        simpljoin1.
        exists x.
        split; auto.
        eapply evptr_of_tsk_setnull3_preserve; eauto.
      }
      casetac eptr0 eid Ht Hf.
      *
        subst.
        clear -Hgetp' Hgetl' Hndel Hneqt.
        false. 
        apply Hndel.
        exists t.
        split; auto.
        unfold tsk_loc_ev. 
        split; auto.
        do 3 eexists; eauto. 
      *
        assert (join (sig eid (absmsgq msgs maxlen pwl, wl)) els' els).
        join auto.
        unfold is_que in H. unfold is_que. simpljoin1. exists x x0 x1 x2.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
Qed.

