(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.
Require Import UniDB.Spec.Subst.
Require Import UniDB.Morph.Depth.
Require Import UniDB.Morph.Weaken.

(******************************************************************************)

Inductive Shift : Type :=
  shift (ξ : Depth Weaken).

Instance iLkShift {T : Type} {vrT : Vr T} : Lk T Shift :=
  fun ξ i => let (ξ') := ξ in vr T (lk Ix (Depth Weaken) ξ' i).

Instance iUpShift : Up Shift := fun ξ δ =>
  let (ξ') := ξ in shift (up (Depth Weaken) ξ' δ).

Instance iWkmShift : Wkm Shift := fun δ =>
  shift (wkm _ δ).

Instance iIdmWeaken : Idm Shift :=
  shift (idm _ ).

Instance iUpHomShift : UpHom Shift.
Proof.
  constructor; intro ξ; destruct ξ; cbn; intros;
    now rewrite ?up_suc, ?up_zero.
Qed.

Instance iLkRenWeaken {T : Type} {vrT : Vr T} : LkRen T Shift := {}.
Proof. intros; destruct ξ; auto. Qed.

Instance iLkWkmShift {T : Type} {vrT : Vr T} : LkWkm T Shift := {}.
Proof.
  intros; apply (f_equal (vr T)).
  rewrite lk_wkm.
  reflexivity.
Qed.

Instance iLkUpShift {T : Type} `{WkVr T} : LkUp T Shift.
Proof.
  apply make_lkup_inst_ren; intro ξ; destruct ξ; cbn; intros;
    repeat change (up ?Ξ ?ξ 1) with (up₁ Ξ ξ);
    now rewrite ?lk_up₁_zero, ?lk_up₁_suc.
Qed.

(******************************************************************************)
