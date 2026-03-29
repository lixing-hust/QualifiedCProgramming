Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.

Lemma Nodup_exists_repetition: forall {A: Type} (l: list A),
  ~ NoDup l -> 
  exists x l1 l2 l3, l = l1 ++ x :: l2 ++ x :: l3.
Proof.
  intros A l.
  induction l as [|a l IH].
  - intro H; exfalso; apply H; constructor.
  - intros; rewrite NoDup_cons_iff in H. 
    assert (In a l \/ ~ NoDup l) by tauto; clear H. 
    destruct H0.
    + apply in_split in H. destruct H as [l1 [l2 H]].
      exists a, nil, l1, l2. 
      simpl; rewrite H; auto.
    + apply IH in H. destruct H as [x [l1 [l2 [l3 H]]]].
      exists x, (a :: l1), l2, l3.
      simpl; rewrite H; auto.
Qed.

Lemma Nodup_split_constructors :
  forall {A: Type} (p1 p2 : list A) (e : A),
    NoDup (p1 ++ e :: p2) ->
    ~ In e p1 /\ ~ In e p2.
Proof.
  intros. 
  apply NoDup_remove_2 in H. 
  rewrite in_app_iff in H. 
  tauto.
Qed.