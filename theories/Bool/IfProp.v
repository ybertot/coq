(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Bool.

Inductive IfProp (A B:Prop) : bool -> Prop :=
  | Iftrue : A -> IfProp A B true
  | Iffalse : B -> IfProp A B false.

Hint Resolve Iftrue Iffalse: bool v62.

Lemma Iftrue_inv : forall (A B:Prop) (b:bool), IfProp A B b -> b = true -> A.
destruct 1; intros; auto with bool.
case diff_true_false; auto with bool.
Qed.

Lemma Iffalse_inv :
 forall (A B:Prop) (b:bool), IfProp A B b -> b = false -> B.
destruct 1; intros; auto with bool.
case diff_true_false; trivial with bool.
Qed.

Lemma IfProp_true : forall A B:Prop, IfProp A B true -> A.
intros.
inversion H.
assumption.
Qed.

Lemma IfProp_false : forall A B:Prop, IfProp A B false -> B.
intros.
inversion H.
assumption.
Qed.

Lemma IfProp_or : forall (A B:Prop) (b:bool), IfProp A B b -> A \/ B.
destruct 1; auto with bool.
Qed.

Lemma IfProp_sum : forall (A B:Prop) (b:bool), IfProp A B b -> {A} + {B}.
destruct b; intro H.
left; inversion H; auto with bool.
right; inversion H; auto with bool.
Qed.
