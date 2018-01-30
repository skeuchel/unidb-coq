(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.
Require Import UniDB.Spec.Subst.

(******************************************************************************)

Inductive Weaken : Set :=
  | weaken_id
  | weaken_wk (ξ : Weaken).

Fixpoint weakenIx (ξ : Weaken) (i : Ix) : Ix :=
  match ξ with
    | weaken_id     => i
    | weaken_wk ξ   => S (weakenIx ξ i)
  end.

Fixpoint wkWeaken (δ : Dom) (ξ : Weaken) : Weaken :=
  match δ with
  | O    => ξ
  | S δ' => weaken_wk (wkWeaken δ' ξ)
  end.

Lemma weakenIx_wkWeaken (δ : Dom) (ξ : Weaken) (i : Ix) :
  weakenIx (wkWeaken δ ξ) i = wk Ix δ (weakenIx ξ i).
Proof. induction δ; cbn; now f_equal. Qed.

Fixpoint weaken_comp (ξ₁ ξ₂ : Weaken) {struct ξ₂} : Weaken :=
  match ξ₂ with
    | weaken_id => ξ₁
    | weaken_wk ξ₂' => weaken_wk (weaken_comp ξ₁ ξ₂')
  end.

(******************************************************************************)

Instance iWkWeaken : Wk Weaken := wkWeaken.
Instance iWkHomWeaken : WkHom Weaken.
Proof. constructor; reflexivity. Qed.

Instance iLkWeaken {T : Type} {vrT : Vr T} : Lk T Weaken :=
  fun ξ i => vr T (weakenIx ξ i).

Instance iIdmWeaken : Idm Weaken := weaken_id.
Instance iWkmWeaken : Wkm Weaken := fun δ => wkWeaken δ weaken_id.
Instance iCompWeaken : Comp Weaken := weaken_comp.

(******************************************************************************)

Instance iWkmHomWeaken : WkmHom Weaken.
Proof. constructor; reflexivity. Qed.

Instance iLkRenWeaken {T : Type} {vrT : Vr T} : LkRen T Weaken := {}.
Proof. reflexivity. Qed.

Instance iLkIdmWeaken {T : Type} {vrT : Vr T} : LkIdm T Weaken := {}.
Proof. reflexivity. Qed.

Instance iLkWkmWeaken {T : Type} {vrT : Vr T} : LkWkm T Weaken := {}.
Proof.
  intros; cbn.
  apply (f_equal (vr T)), weakenIx_wkWeaken.
Qed.

Lemma wk_comp_weaken (ξ₁ ξ₂ : Weaken) (δ : Dom) :
  wk Weaken δ (comp Weaken ξ₁ ξ₂) = comp Weaken ξ₁ (wk Weaken δ ξ₂).
Proof.
  induction δ; cbn.
  - auto.
  - apply (f_equal (weaken_wk)); auto.
Qed.

Lemma lk_wk₁_weaken {T : Type} `{WkVr T} (ξ : Weaken) (i : Ix) :
  lk T Weaken (wk₁ Weaken ξ) i = wk₁ T (lk T Weaken ξ i).
Proof. symmetry; apply wk₁_vr. Qed.

(* Lemma lk_wk_weaken {T : Type} `{WkVr T} (δ : Dom) (ξ : Weaken) (i : Ix) : *)
(*   lk T Weaken (wk δ ξ) i = wk δ (lk T Weaken ξ i). *)
(* Proof.   *)
(*   lk-wk-weaken δ ξ i = trans *)
(*     (cong (vr T) (lkIx-wk-weaken δ ξ i)) *)
(*     (sym (wk-vr T δ (lk Ix Weaken ξ i))) *)
(* Qed. *)

Instance iLkRenCompWeaken {T : Type} {vrT : Vr T} : LkRenComp T Weaken := {}.
Proof.
  intros; apply (f_equal (vr T)).
  induction ξ₂; simpl; auto.
Qed.

Instance iCompIdmWeaken : CompIdm Weaken := {}.
Proof.
  - auto.
  - induction ξ; simpl; auto.
    apply (f_equal weaken_wk); auto.
Qed.

Instance iCompAssocWeaken : CompAssoc Weaken := {}.
Proof.
  induction ξ₃; simpl; auto.
  apply (f_equal weaken_wk); auto.
Qed.

Lemma comp_wkm_weaken (ξ : Weaken) (δ : Dom) :
  comp Weaken ξ (wkm Weaken δ) = wk Weaken δ ξ.
Proof.
  induction δ; simpl; auto.
  apply (f_equal weaken_wk); auto.
Qed.

(******************************************************************************)
