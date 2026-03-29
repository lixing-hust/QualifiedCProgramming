(** Monadic operations for the option type. *)
(** Reference: https://gitlab.mpi-sws.org/iris/stdpp/-/blob/master/stdpp/option.v *)

From MonadLib Require Import Monad.
Import MonadNotation. Local Open Scope monad_scope.

Require Import Coq.Unicode.Utf8.

#[export] Instance option_monad: Monad option := {
  bind := fun A B mx f =>
    match mx with Some x => f x | None => None end;
  ret := @Some;
}.
Arguments Monad.bind _ _ _ _ !mx / f.
Arguments Monad.ret _ _ _ !x /.

Definition option_map (A B: Type) (f: A -> B) (x: option A) : option B :=
  match x with
  | None => None
  | Some y => Some (f y)
  end.

#[export] Instance option_fmap: FMap option := @option_map.


Lemma fmap_Some {A B} (f : A -> B) mx y :
  f <$> mx = Some y <-> ∃ x, mx = Some x ∧ y = f x.
Proof.
  split.
  - destruct mx; simpl. 2: congruence. injection 1 as H; subst.
    eexists; split; auto.
  - intros (? & -> & ?); subst; auto.
Qed.

Lemma fmap_Some_1 {A B} (f : A -> B) mx y :
  f <$> mx = Some y -> ∃ x, mx = Some x ∧ y = f x.
Proof. apply fmap_Some. Qed.
Lemma fmap_Some_2 {A B} (f : A -> B) mx x : mx = Some x -> f <$> mx = Some (f x).
Proof. intros. apply fmap_Some; eauto. Qed.

From Coq Require Import ssreflect ssrfun ssrbool.

Lemma fmap_None {A B} (f : A -> B) mx : f <$> mx = None <-> mx = None.
Proof. by destruct mx. Qed.
Lemma option_fmap_id {A} (mx : option A) : id <$> mx = mx.
Proof. by destruct mx. Qed.

Lemma bind_Some {A B} (f : A -> option B) (mx : option A) y :
  mx ≫= f = Some y <-> ∃ x, mx = Some x ∧ f x = Some y.
Proof. destruct mx; simpl.
  - split. 1: intros H; eexists; eauto.
    intros (? & H & ?); injection H as H; subst; auto.
  - split; try congruence.
    intros (? & H & ?); congruence.
Qed.
Lemma bind_None {A B} (f : A -> option B) (mx : option A) :
  mx ≫= f = None <-> mx = None ∨ ∃ x, mx = Some x ∧ f x = None.
Proof.
  split.
  - destruct mx; simpl; intros.
    + right; eexists; eauto.
    + left; auto.
  - intros [-> | (? & -> & ?)]; simpl; auto.
Qed.
Lemma bind_with_Some {A} (mx : option A) : mx ≫= Some = mx.
Proof. by destruct mx. Qed.

Lemma bind_Some_l {A B} (f : A -> option B) x :
  Some x ≫= f = f x.
Proof. reflexivity. Qed.
Lemma bind_None_l {A B} (f : A -> option B) :
  None ≫= f = None.
Proof. reflexivity. Qed.

Ltac simpl_option_monad :=
  repeat match goal with
  | [ H: context [ Some _ ≫= _ ] |- _ ] => rewrite bind_Some_l in H
  | [ H: context [ None ≫= _ ] |- _ ] => rewrite bind_None_l in H
  | [ |- context [ Some _ ≫= _ ] ] => rewrite bind_Some_l
  | [ |- context [ None ≫= _ ] ] => rewrite bind_None_l
  end.

(* Test the tactic *)
Lemma test_simpl_option_monad (A B: Type) (f: A -> option B) (x: A) :
  (Some x ≫= f) = f x ∧ (None ≫= f) = None.
Proof. simpl_option_monad. split; reflexivity. Qed.
Lemma test_simpl_option_monad_in_hyp (A B: Type) (f: A -> option B) (x: A) :
  (Some x ≫= f) = f x -> (None ≫= f) = None -> True.
Proof. intros. simpl_option_monad. tauto. Qed.
