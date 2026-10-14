
Require Import sem_language.
Require Import sem_sys.
Require Import succ_gen.
Require Import sem_invs.

Require Import sem_init_preserves_inv.
Require Import sem_initbin_preserves_inv.
Require Import sem_destroy_preserves_inv.
Require Import sem_wait_preserves_inv.
Require Import sem_trywait_preserves_inv.
Require Import sem_timedwait_preserves_inv.
Require Import sem_signal_preserves_inv.

Require Import steq_inv_preserve.

Require Import asrt_sat_apis.

Lemma sem_init_preserves_inv: 
  forall k vl cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map), 
    nth_error (get_all_succs (seminit vl)) k = Some cd ->
    spec_step sc cd O lau cd' O' lau' ->
    get O curtid = Some (oscurt t) -> 
    get laump t = Some lau ->
    laump' = set laump t lau' -> 
    dtinv O laump ->
    dtinv O' laump'.
Proof.
  introv Hnth Hstep Hct Hlau Hlau' Hsatinv.
  assert (Hor: 
    ~(get O abstcblsid = get O' abstcblsid /\
        get O absecblsid = get O' absecblsid /\
        get O gauxstid = get O' gauxstid /\
        get O atidlsid = get O' atidlsid /\ 
        lau = lau')
    \/ 
      (get O abstcblsid = get O' abstcblsid /\
         get O absecblsid = get O' absecblsid /\
         get O gauxstid = get O' gauxstid /\
         get O atidlsid = get O' atidlsid /\ 
         lau = lau')) 
  by tauto.
  destruct Hor as [Hn | Hy].
  - eapply sem_init_preserves_inv_; eauto.
  - eapply steq_preserves_inv; eauto. 
Qed.

Lemma sem_initbin_preserves_inv: 
  forall k vl cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map), 
    nth_error (get_all_succs (seminitbin vl)) k = Some cd ->
    spec_step sc cd O lau cd' O' lau' ->
    get O curtid = Some (oscurt t) -> 
    get laump t = Some lau ->
    laump' = set laump t lau' -> 
    dtinv O laump ->
    dtinv O' laump'.
Proof.
  introv Hnth Hstep Hct Hlau Hlau' Hsatinv.
  assert (Hor: 
    ~(get O abstcblsid = get O' abstcblsid /\
        get O absecblsid = get O' absecblsid /\
        get O gauxstid = get O' gauxstid /\
        get O atidlsid = get O' atidlsid /\ 
        lau = lau')
    \/ 
      (get O abstcblsid = get O' abstcblsid /\
         get O absecblsid = get O' absecblsid /\
         get O gauxstid = get O' gauxstid /\
         get O atidlsid = get O' atidlsid /\ 
         lau = lau')) 
  by tauto.
  destruct Hor as [Hn | Hy].
  - eapply sem_initbin_preserves_inv_; eauto.
  - eapply steq_preserves_inv; eauto. 
Qed.

Lemma sem_wait_preserves_inv: 
  forall k vl cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map), 
    nth_error (get_all_succs (semwait vl)) k = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau cd' O' lau' ->
    get O curtid = Some (oscurt t) -> 
    get laump t = Some lau ->
    laump' = set laump t lau' -> 
    dtinv O laump ->
    dtinv O' laump'.
Proof.
  introv Hnth Hss Hgct Hgl Hl' Hdti.
  assert (Hor: 
    ~(get O abstcblsid = get O' abstcblsid /\
        get O absecblsid = get O' absecblsid /\
        get O gauxstid = get O' gauxstid /\
        get O atidlsid = get O' atidlsid /\ 
        lau = lau')
    \/ 
      (get O abstcblsid = get O' abstcblsid /\
         get O absecblsid = get O' absecblsid /\
         get O gauxstid = get O' gauxstid /\
         get O atidlsid = get O' atidlsid /\ 
         lau = lau')) 
  by tauto.
  destruct Hor as [Hn | Hy].
  - eapply sem_wait_preserves_inv_; eauto.
  - eapply steq_preserves_inv; eauto.
Qed. 

Lemma sem_trywait_preserves_inv: 
  forall k vl cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map), 
    nth_error (get_all_succs (semtrywait vl)) k = Some cd ->
    spec_step sc cd O lau cd' O' lau' ->
    get O curtid = Some (oscurt t) -> 
    get laump t = Some lau ->
    laump' = set laump t lau' -> 
    dtinv O laump ->
    dtinv O' laump'.
Proof. 
  introv Hnth Hss Hgct Hgl Hl' Hdti.
  assert (Hor: 
    ~(get O abstcblsid = get O' abstcblsid /\
        get O absecblsid = get O' absecblsid /\
        get O gauxstid = get O' gauxstid /\
        get O atidlsid = get O' atidlsid /\ 
        lau = lau')
    \/ 
      (get O abstcblsid = get O' abstcblsid /\
         get O absecblsid = get O' absecblsid /\
         get O gauxstid = get O' gauxstid /\
         get O atidlsid = get O' atidlsid /\ 
         lau = lau')) 
  by tauto.
  destruct Hor as [Hn | Hy].
  - eapply sem_trywait_preserves_inv_; eauto.
  - eapply steq_preserves_inv; eauto. 
Qed. 

Lemma sem_timedwait_preserves_inv: 
  forall k vl cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map), 
    nth_error (get_all_succs (semtimedwait vl)) k = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau cd' O' lau' ->
    get O curtid = Some (oscurt t) -> 
    get laump t = Some lau ->
    laump' = set laump t lau' -> 
    dtinv O laump ->
    dtinv O' laump'.
Proof.
  introv Hnth Hss Hgct Hgl Hl' Hdti.
  assert (Hor: 
    ~(get O abstcblsid = get O' abstcblsid /\
        get O absecblsid = get O' absecblsid /\
        get O gauxstid = get O' gauxstid /\
        get O atidlsid = get O' atidlsid /\ 
        lau = lau')
    \/ 
      (get O abstcblsid = get O' abstcblsid /\
         get O absecblsid = get O' absecblsid /\
         get O gauxstid = get O' gauxstid /\
         get O atidlsid = get O' atidlsid /\ 
         lau = lau')) 
  by tauto.
  destruct Hor as [Hn | Hy].
  - eapply sem_timedwait_preserves_inv_; eauto.
  - eapply steq_preserves_inv; eauto.
Qed. 

Lemma sem_signal_preserves_inv: 
  forall k vl cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map), 
    nth_error (get_all_succs (semsignal vl)) k = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau cd' O' lau' -> 
    get O curtid = Some (oscurt t) -> 
    get laump t = Some lau ->
    laump' = set laump t lau' -> 
    dtinv O laump ->
    dtinv O' laump'.
Proof.
  introv Hnth Hstep Hct Hlau Hlau' Hsatinv.
  assert (Hor: 
    ~(get O abstcblsid = get O' abstcblsid /\
        get O absecblsid = get O' absecblsid /\
        get O gauxstid = get O' gauxstid /\
        get O atidlsid = get O' atidlsid /\ 
        lau = lau')
    \/ 
      (get O abstcblsid = get O' abstcblsid /\
         get O absecblsid = get O' absecblsid /\
         get O gauxstid = get O' gauxstid /\
         get O atidlsid = get O' atidlsid /\ 
         lau = lau')) 
  by tauto.
  destruct Hor as [Hn | Hy].
  - eapply sem_signal_preserves_inv_; eauto.
  - eapply steq_preserves_inv; eauto. 
Qed.

Lemma sem_destroy_preserves_inv: 
  forall k vl cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map), 
    nth_error (get_all_succs (semdestroy vl)) k = Some cd ->
    spec_step sc cd O lau cd' O' lau' ->
    get O curtid = Some (oscurt t) -> 
    get laump t = Some lau ->
    laump' = set laump t lau' -> 
    no_pend_on_deletion cd O laump -> 
    dtinv O laump ->
    dtinv O' laump'.
Proof.
  introv Hnth Hstep Hct Hlau Hlau' Hsatinv.
  assert (Hor: 
    ~(get O abstcblsid = get O' abstcblsid /\
        get O absecblsid = get O' absecblsid /\
        get O gauxstid = get O' gauxstid /\
        get O atidlsid = get O' atidlsid /\ 
        lau = lau')
    \/ 
      (get O abstcblsid = get O' abstcblsid /\
         get O absecblsid = get O' absecblsid /\
         get O gauxstid = get O' gauxstid /\
         get O atidlsid = get O' atidlsid /\ 
         lau = lau')) 
  by tauto.
  destruct Hor as [Hn | Hy].
  - eapply sem_destroy_preserves_inv_; eauto.
  - eapply steq_preserves_inv; eauto. 
Qed.
