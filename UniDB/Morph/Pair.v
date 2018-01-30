(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.

Reserved Notation "ξ ⊗ ζ"
  (at level 43, no associativity).

(******************************************************************************)

Inductive Pair (Ξ Ζ : Type) : Type :=
  make_pair (ξ : Ξ) (ζ : Ζ).
Notation "ξ ⊗ ζ" := (make_pair _ _ ξ ζ).

Instance iHCompPair {Ξ Ζ : Type} : HComp Ξ Ζ (Pair Ξ Ζ) :=
  make_pair Ξ Ζ.

Section UpPair.
  Context {Ξ : Type} `{Up Ξ} {Ζ : Type} `{Up Ζ}.

  Global Instance iUpPair : Up (Pair Ξ Ζ) :=
    fun ξζ δ => let (ξ , ζ) := ξζ in (up Ξ ξ δ) ⊗ (up Ζ ζ δ).
  Global Instance iUpHomPair `{!UpHom Ξ, !UpHom Ζ} :
    UpHom (Pair Ξ Ζ) := {}.
  Proof.
    - intros ξ; destruct ξ; cbn.
      now rewrite ?up_zero.
    - intros ξ δ; destruct ξ; cbn.
      now rewrite ?up_suc, ?up_zero.
  Qed.

  Global Instance iUpHCompPair `{!UpHom Ξ, !UpHom Ζ} :
    UpHComp Ξ Ζ (Pair Ξ Ζ) := {}.
  Proof. reflexivity. Qed.

End UpPair.

(******************************************************************************)

Require Import UniDB.Spec.Subst.

Instance iLkPair
  {T : Type} `{Tr T T}
  {Ξ : Type} `{Lk T Ξ}
  {Ζ : Type} `{Lk T Ζ, Up Ζ} :
  Lk T (Pair Ξ Ζ) := fun ξζ i =>
    match ξζ with ξ ⊗ ζ => tr T T Ζ (lk T Ξ ξ i) ζ end.

Class TrPair
  (T : Type) `{Tr T T}
  (X : Type) `{Tr T X} :=
  tr_pair :
    ∀ {Ξ : Type} `{Lk T Ξ, Up Ξ, !UpHom Ξ}
      {Ζ : Type} `{Lk T Ζ, Up Ζ, !UpHom Ζ}
      (x : X) (ξ : Ξ) (ζ : Ζ),
      tr T X Ζ (tr T X Ξ x ξ) ζ = tr T X (Pair Ξ Ζ) x (ξ ⊗ ζ).

(******************************************************************************)

Instance iLkHCompTrPair
  {T : Type} {vrT : Vr T} {trTT : Tr T T}
  {Ξ : Type} {lkTΞ : Lk T Ξ} {upΞ : Up Ξ}
  {Ζ : Type} {lkTΖ : Lk T Ζ} {upΖ : Up Ζ} :
  LkHCompTr T Ξ Ζ (Pair Ξ Ζ) := {}.
Proof. reflexivity. Qed.

Lemma iLkUpPairRenaming
  {T : Type} `{Vr T, Wk T, Tr T T, !TrVr T}
  {Ξ : Type} `{Lk T Ξ, Up Ξ, !LkUp T Ξ, Lk Ix Ξ, !LkRen T Ξ, !LkUp Ix Ξ}
  {Ζ : Type} `{Lk T Ζ, Up Ζ, !LkUp T Ζ} :
  LkUp T (Pair Ξ Ζ).
Proof.
  constructor; intros; destruct ξ as [ξ ζ]; cbn;
    change (up Ξ ξ 1) with (up₁ Ξ ξ);
    change (up Ζ ζ 1) with (up₁ Ζ ζ);
    now rewrite ?(lk_ren T), ?tr_vr,
      ?lk_up₁_zero, ?lk_up₁_suc, ?lk_up_wk.
Qed.

Lemma iLkUpPairSubstitution
  {T : Type} {vrT : Vr T} {wkT : Wk T} {trTT : Tr T T}
  {trVrT : TrVr T}
  {Ξ : Type} {lkTΞ : Lk T Ξ} {upΞ : Up Ξ} {lkUpTΞ : LkUp T Ξ}
  {Ζ : Type} {lkTΖ : Lk T Ζ} {upΖ : Up Ζ} {lkUpTΖ : LkUp T Ζ}
  (hyp : ∀ (δ : Dom) (ζ : Ζ) (t : T),
           tr T T Ζ (wk T δ t) (up Ζ ζ δ) = wk T δ (tr T T Ζ t ζ)) :
  LkUp T (Pair Ξ Ζ).
Proof.
  constructor; intros; destruct ξ as [ξ ζ]; cbn;
    change (up Ξ ξ 1) with (up₁ Ξ ξ);
    change (up Ζ ζ 1) with (up₁ Ζ ζ).
  - now rewrite lk_up₁_zero, tr_vr, lk_up₁_zero.
  - rewrite lk_up₁_suc.
    apply (hyp 1).
  - now rewrite lk_up_wk.
Qed.

Instance iLkUpPair
  (T : Type) {vrT : Vr T} {wkT : Wk T} {trTT : Tr T T}
  {trVrT : TrVr T} {trWkTT : TrWk T T}
  (Ξ : Type) {lkTΞ : Lk T Ξ} {upΞ : Up Ξ} {lkUpTΞ : LkUp T Ξ}
  (Ζ : Type) {lkTΖ : Lk T Ζ} {upΖ : Up Ζ}
  {upHomΖ : UpHom Ζ} {lkUpTΖ : LkUp T Ζ} :
  LkUp T (Pair Ξ Ζ).
Proof. apply iLkUpPairSubstitution, tr_wk. Qed.

(******************************************************************************)
