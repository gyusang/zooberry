(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Interrupt abstract domain. *)

Set Implicit Arguments.

Require Import Morphisms.
Require Import vgtac DLat TStr DomBasic.

Module Intr <: LAT.

Inductive t' : Type :=
| Bot
| Enabled
| Disabled
| Top.

Definition t := t'.

Definition eq (x y : t) : Prop := Logic.eq x y.

Definition le (x y : t) : Prop :=
  match x, y with
  | Bot, _ => True
  | _, Top => True
  | Enabled, Enabled => True
  | Disabled, Disabled => True
  | _, _ => False
  end.

Lemma eq_refl : forall x : t, eq x x.
Proof. unfold eq; auto. Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. unfold eq; intros; subst; auto. Qed.

Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. unfold eq; intros; subst; auto. Qed.

Lemma le_refl : forall x y : t, eq x y -> le x y.
Proof. unfold eq; intros; subst; destruct y; simpl; auto. Qed.

Lemma le_antisym : forall x y : t, le x y -> le y x -> eq x y.
Proof. destruct x, y; simpl; unfold eq; intuition. Qed.

Lemma le_trans : forall x y z : t, le x y -> le y z -> le x z.
Proof. destruct x, y, z; simpl; intuition. Qed.

Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
Proof.
unfold eq; destruct x, y; try (left; reflexivity); right; discriminate.
Defined.

Definition le_dec (x y : t) : {le x y} + {~ le x y}.
Proof.
destruct x, y; simpl; auto; right; intuition.
Defined.

Definition bot : t := Bot.

Lemma bot_prop : forall x : t, le bot x.
Proof. destruct x; simpl; auto. Qed.

Definition join (x y : t) : t :=
  match x, y with
  | Bot, z | z, Bot => z
  | Top, _ | _, Top => Top
  | Enabled, Enabled => Enabled
  | Disabled, Disabled => Disabled
  | _, _ => Top
  end.

Lemma join_left : forall x y : t, le x (join x y).
Proof. destruct x, y; simpl; auto. Qed.

Lemma join_right : forall x y : t, le y (join x y).
Proof. destruct x, y; simpl; auto. Qed.

Lemma join_lub :
  forall x y u : t, le x u -> le y u -> le (join x y) u.
Proof. destruct x, y, u; simpl; intuition. Qed.

Definition meet (x y : t) : t :=
  match x, y with
  | Bot, _ | _, Bot => Bot
  | Top, z | z, Top => z
  | Enabled, Enabled => Enabled
  | Disabled, Disabled => Disabled
  | _, _ => Bot
  end.

Lemma meet_left : forall x y : t, le (meet x y) x.
Proof. destruct x, y; simpl; auto. Qed.

Lemma meet_right : forall x y : t, le (meet x y) y.
Proof. destruct x, y; simpl; auto. Qed.

Lemma meet_glb :
  forall x y l : t, le l x -> le l y -> le l (meet x y).
Proof. destruct x, y, l; simpl; intuition. Qed.

Definition widen : t -> t -> t := join.
Definition narrow : t -> t -> t := meet.

Include JoinMeetProp.

Definition may_enabled (x : t) : bool :=
  match x with
  | Enabled | Top => true
  | _ => false
  end.

Definition is_disabled (x : t) : bool :=
  match x with
  | Disabled => true
  | _ => false
  end.

End Intr.

Axiom str_intr_state : string_t.
Extract Constant str_intr_state => """__zooberry_intr_state""".

Definition loc_of_intr_state : Loc.t :=
  loc_of_var (var_of_gvar str_intr_state).

Axiom is_irq_handler : string_t -> bool.
Axiom is_enable_irq : string_t -> bool.
Axiom is_disable_irq : string_t -> bool.

Extract Constant is_irq_handler =>
"fun s ->
  let suffix = ""IRQHandler"" in
  let len_s = String.length s in
  let len_suffix = String.length suffix in
  len_s >= len_suffix
  && String.sub s (len_s - len_suffix) len_suffix = suffix".

Extract Constant is_enable_irq =>
"fun s ->
  let suffix = ""EnableIRQ"" in
  let len_s = String.length s in
  let len_suffix = String.length suffix in
  len_s >= len_suffix
  && String.sub s (len_s - len_suffix) len_suffix = suffix".

Extract Constant is_disable_irq =>
"fun s ->
  let suffix = ""DisableIRQ"" in
  let len_s = String.length s in
  let len_suffix = String.length suffix in
  len_s >= len_suffix
  && String.sub s (len_s - len_suffix) len_suffix = suffix".

Lemma loc_of_intr_state_mor : Proper (Loc.eq) loc_of_intr_state.
Proof. by apply Loc.eq_refl. Qed.
