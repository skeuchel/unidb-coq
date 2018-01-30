(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.

(******************************************************************************)

(** Application of a substitution for sort T to a term of sort X. *)
Class Tr (T X : Type) :=
  tr : ∀ (Ξ : Type) {lkTΞ : Lk T Ξ} {upΞ : Up Ξ} (x : X) (ξ : Ξ), X.
Arguments tr T X {_} Ξ {_ _} x ξ.

Instance iTrIx : Tr Ix Ix :=
  fun Ξ _ _ i ξ => lk Ix Ξ ξ i.

Class TrVr (T : Type) `{Vr T, Tr T T} :=
  tr_vr : ∀ (Ξ : Type) {lkTΞ : Lk T Ξ} {upΞ : Up Ξ} (ξ : Ξ) (i : Ix),
             tr T T Ξ (vr T i) ξ = lk T Ξ ξ i.

Instance iTrVrIx : TrVr Ix.
Proof. constructor. Qed.

Class LkCompTr
      (T : Type) {vrT : Vr T} {trTT : Tr T T}
      (Ξ : Type) {lkTΞ : Lk T Ξ} {upΞ : Up Ξ} {compΞ : Comp Ξ} :=
  lk_comp_tr : ∀ (ξ₁ ξ₂ : Ξ) (i : Ix),
                 lk T Ξ (comp Ξ ξ₁ ξ₂) i = tr T T Ξ (lk T Ξ ξ₁ i) ξ₂.

Class LkHCompTr
      (T : Type) {vrT : Vr T} {trTT : Tr T T}
      (Ξ : Type) {lkTΞ : Lk T Ξ} {upΞ : Up Ξ}
      (Ζ : Type) {lkTΖ : Lk T Ζ} {upΖ : Up Ζ}
      (Θ : Type) {lkTΘ : Lk T Θ} {upΘ : Up Θ}
      {hcompΞΖΘ : HComp Ξ Ζ Θ} :=
  lk_hcomp_tr : ∀ (ξ : Ξ) (ζ : Ζ) (i : Ix),
                  lk T Θ (hcomp Ξ Ζ Θ ξ ζ) i = tr T T Ζ (lk T Ξ ξ i) ζ.

Class TrIdm
      (T : Type) `{Vr T, Wk T}
      (X : Type) `{Tr T X} :=
  tr_idm : ∀ {Ξ : Type} `{Lk T Ξ, Up Ξ, Idm Ξ}
             `{!UpHom Ξ, !LkIdm T Ξ, !LkUp T Ξ},
           ∀ (x : X), tr T X Ξ x (idm Ξ) = x.

Class TrRel
  (T : Type) `{Vr T}
  (X : Type) `{Tr T X} :=
  tr_rel_ext :
    ∀ {Ξ : Type} `{Lk T Ξ, Up Ξ, !UpHom Ξ}
      {Ζ : Type} `{Lk T Ζ, Up Ζ, !UpHom Ζ}
      (x : X) {ξ : Ξ} {ζ : Ζ} (hyp : Extended T Ξ Ζ ξ ζ),
      tr T X Ξ x ξ = tr T X Ζ x ζ.

Lemma tr_rel_pw
  (T : Type) `{Vr T, Wk T}
  (X : Type) `{Tr T X, !TrRel T X}
  {Ξ : Type} `{Lk T Ξ, Up Ξ, !UpHom Ξ, !LkUp T Ξ}
  {Ζ : Type} `{Lk T Ζ, Up Ζ, !UpHom Ζ, !LkUp T Ζ} :
  ∀ {ξ : Ξ} {ζ : Ζ} (hyp : Pointwise T Ξ Ζ ξ ζ) (x : X),
    tr T X Ξ x ξ = tr T X Ζ x ζ.
Proof.
  intros.
  apply tr_rel_ext.
  apply pointwise_to_extended.
  intros; now apply pointwise_up.
Qed.
Arguments tr_rel_pw {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} ξ ζ hyp x.

Class TrWkmWk
  (T : Type) `{Vr T, Wk T}
  (X : Type) `{Wk X, Tr T X} :=
  tr_wkm_wk :
    ∀ (Ξ : Type) `{Lk T Ξ, Up Ξ, Wkm Ξ}
      `{!UpHom Ξ, !LkUp T Ξ, !LkWkm T Ξ}
      (δ : Dom) (x : X),
      tr T X Ξ x (wkm Ξ δ) = wk X δ x.

Lemma tr_wkm₁_wk₁
  {T : Type} `{Vr T, Wk T}
  {X : Type} `{Wk X, Tr T X, !TrWkmWk T X}
  {Ξ : Type} `{Lk T Ξ, Up Ξ, Wkm Ξ, !UpHom Ξ, !LkUp T Ξ, !LkWkm T Ξ} :
  ∀ (x : X), tr T X Ξ x (wkm₁ Ξ) = wk₁ X x.
Proof. apply (tr_wkm_wk Ξ 1). Qed.
Arguments tr_wkm_wk {_ _ _} {_ _ _ _} {_ _ _ _ _ _ _} δ x.
Arguments tr_wkm₁_wk₁ {_ _ _} {_ _ _ _} {_ _ _ _ _ _ _} x.

Class TrWk
  (T : Type) `{Vr T, Wk T}
  (X : Type) `{Wk X, Tr T X} :=
  tr_wk :
    ∀ (Ξ : Type) `{Lk T Ξ, Up Ξ, !UpHom Ξ, !LkUp T Ξ}
      (δ : Dom) (ξ : Ξ) (x : X),
      tr T X Ξ (wk X δ x) (up Ξ ξ δ) = wk X δ (tr T X Ξ x ξ).

Lemma tr_wk₁
  {T : Type} `{Vr T, Wk T}
  {X : Type} `{Wk X, Tr T X, !TrWk T X}
  {Ξ : Type} `{Lk T Ξ, Up Ξ, !UpHom Ξ, !LkUp T Ξ} :
  ∀ (ξ : Ξ) (x : X),
    tr T X Ξ (wk₁ X x) (up₁ Ξ ξ) = wk₁ X (tr T X Ξ x ξ).
Proof. apply (tr_wk Ξ 1). Qed.
Arguments tr_wk {_ _ _} {_ _ _ _} {_ _ _ _ _} δ ξ x.
Arguments tr_wk₁ {_ _ _} {_ _ _ _} {_ _ _ _ _} ξ x.

Class TrComp
  (T : Type) `{Vr T, Wk T, Tr T T}
  (X : Type) `{Tr T X} :=
  tr_comp :
    ∀ (Ξ : Type) `{Lk T Ξ, Up Ξ, Comp Ξ, !UpHom Ξ, !LkUp T Ξ, !LkCompTr T Ξ}
      (ξ₁ : Ξ) (ξ₂ : Ξ) (x : X),
      tr T X Ξ x (comp Ξ ξ₁ ξ₂) = tr T X Ξ (tr T X Ξ x ξ₁) ξ₂.
Arguments tr_comp {_ _ _ _} {_ _ _} {_ _ _ _ _ _ _} ξ₁ ξ₂ x.

(******************************************************************************)

Section InteractionLemmas.

  Section BetaComm.

    Class BetaComm
      (T : Type) `{Tr T T}
      (Ξ : Type) `{Lk T Ξ, Up Ξ, Beta T Ξ, Comp Ξ} :=
      beta₁_comm : ∀ (t : T) (ξ : Ξ),
        comp Ξ (beta₁ T Ξ t) ξ = comp Ξ (up₁ Ξ ξ) (beta₁ T Ξ (tr T T Ξ t ξ)).

  End BetaComm.

End InteractionLemmas.

Hint Unfold TrVr.
Hint Unfold LkHCompTr.

(******************************************************************************)
