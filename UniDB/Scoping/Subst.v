(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.
Require Import UniDB.Spec.Subst.
Require Import UniDB.Scoping.Core.

(******************************************************************************)

Section WsSubst.

  Class WsTr
    (T: Type) `{Vr T, Wk T, Ws T}
    (X: Type) `{Ws X, Tr T X} :=
      ws_ap:
        ∀ (Ξ : Type) `{Lk T Ξ, Up Ξ, !UpHom Ξ, !WsUp T Ξ, !LkUp T Ξ}
          {γ₁ : Dom} {x : X} (wx : ⟨ γ₁ ⊢ x ⟩)
          {γ₂ : Dom} {ξ : Ξ} (wξ : WsSub T Ξ γ₁ γ₂ ξ),
          ⟨ γ₂ ⊢ tr T X Ξ x ξ ⟩.

End WsSubst.

Section WsTrNat.

  Definition SubMorph
    (T : Type) `{Ws T}
    (Ξ : Type) `{Lk T Ξ}
    (Ζ : Type) `{Lk T Ζ}
    (γ γξ γζ : Dom) (ξ : Ξ) (ζ : Ζ) : Prop :=
    ∀ (i: Ix), ⟨ γξ ⊢ lk T Ξ ξ i ⟩ → ⟨ γζ ⊢ lk T Ζ ζ i ⟩.

  Class SubMorphUp
    (T : Type) `{Ws T}
    (Ξ : Type) `{Lk T Ξ, Up Ξ}
    (Ζ : Type) `{Lk T Ζ, Up Ζ} : Prop :=
    { submorph_up₁ :
        ∀ (γ γξ γζ : Dom) (ξ : Ξ) (ζ : Ζ),
          SubMorph T Ξ Ζ γ     γξ     γζ     ξ         ζ →
          SubMorph T Ξ Ζ (S γ) (S γξ) (S γζ) (up₁ Ξ ξ) (up₁ Ζ ζ);
      submorph_up :
        ∀ (γ γξ γζ : Dom) (ξ : Ξ) (ζ : Ζ) (δ : Dom),
          SubMorph T Ξ Ζ γ       γξ       γζ       ξ          ζ →
          SubMorph T Ξ Ζ (γ ∪ δ) (γξ ∪ δ) (γζ ∪ δ) (up Ξ ξ δ) (up Ζ ζ δ)
    }.

  Lemma submorph_ix_stx
    {T : Type} `{Vr T, Ws T, !WsVr T}
    {Ξ : Type} `{Lk Ix Ξ, Lk T Ξ, !LkRen T Ξ}
    {Ζ : Type} `{Lk Ix Ζ, Lk T Ζ, !LkRen T Ζ} :
    ∀ (γ γξ γζ : Dom) (ξ : Ξ) (ζ : Ζ),
      SubMorph Ix Ξ Ζ γ γξ γζ ξ ζ ↔
      SubMorph T Ξ Ζ γ γξ γζ ξ ζ.
  Proof.
    intros; constructor; intro ξζ; (* constructor;  *)intros i ξi.
    - rewrite (lk_ren T) in ξi. apply wsi_vr in ξi.
      rewrite (lk_ren T). apply ws_vr.
      now apply ξζ.
    - apply (ws_vr (T:=T)) in ξi. rewrite <- (lk_ren T) in ξi.
      apply (wsi_vr (T:=T)). rewrite <- (lk_ren T).
      now apply ξζ.
  Qed.

  Lemma submorphix_up₁
    (Ξ : Type) `{Lk Ix Ξ, Up Ξ, !LkUp Ix Ξ}
    (Ζ : Type) `{Lk Ix Ζ, Up Ζ, !LkUp Ix Ζ}
    (γ γξ γζ : Dom) (ξ : Ξ) (ζ : Ζ) :
    SubMorph Ix Ξ Ζ γ     γξ     γζ     ξ         ζ →
    SubMorph Ix Ξ Ζ (S γ) (S γξ) (S γζ) (up₁ Ξ ξ) (up₁ Ζ ζ).
  Proof.
    intro mξζ; (* constructor;  *)intros i ξi.
    destruct i; cbn in *.
    - rewrite lk_up₁_zero.
      constructor.
    - rewrite lk_up₁_suc.
      rewrite lk_up₁_suc in ξi.
      inversion ξi.
      constructor.
      apply mξζ; trivial.
  Qed.

  Lemma submorphix_up
    (Ξ : Type) `{Lk Ix Ξ, Up Ξ, !UpHom Ξ, !LkUp Ix Ξ}
    (Ζ : Type) `{Lk Ix Ζ, Up Ζ, !UpHom Ζ, !LkUp Ix Ζ}
    (γ γξ γζ : Dom) (ξ : Ξ) (ζ : Ζ) (δ : Dom):
    SubMorph Ix Ξ Ζ γ       γξ       γζ       ξ          ζ →
    SubMorph Ix Ξ Ζ (γ ∪ δ) (γξ ∪ δ) (γζ ∪ δ) (up Ξ ξ δ) (up Ζ ζ δ).
  Proof.
    intro mξζ; induction δ; cbn; rewrite ?up_zero, ?up_suc;
      auto using (submorphix_up₁ Ξ Ζ).
  Qed.

  Lemma isubmorph_up₁_ren
    (T : Type) `{Vr T, Ws T, !WsVr T}
    (Ξ : Type) `{Lk Ix Ξ, Lk T Ξ, Up Ξ, !LkRen T Ξ, !LkUp Ix Ξ}
    (Ζ : Type) `{Lk Ix Ζ, Lk T Ζ, Up Ζ, !LkRen T Ζ, !LkUp Ix Ζ}
    (γ γξ γζ : Dom) (ξ : Ξ) (ζ : Ζ) :
    SubMorph T Ξ Ζ γ     γξ     γζ     ξ         ζ →
    SubMorph T Ξ Ζ (S γ) (S γξ) (S γζ) (up₁ Ξ ξ) (up₁ Ζ ζ).
  Proof.
    intros mξζ.
    apply submorph_ix_stx.
    apply submorphix_up₁; trivial.
    apply (submorph_ix_stx (T:=T)); trivial.
  Qed.

  Lemma isubmorph_up_ren
    (T : Type) `{Vr T, Ws T, !WsVr T}
    (Ξ : Type) `{Lk Ix Ξ, Lk T Ξ, Up Ξ, !UpHom Ξ, !LkRen T Ξ, !LkUp Ix Ξ}
    (Ζ : Type) `{Lk Ix Ζ, Lk T Ζ, Up Ζ, !UpHom Ζ, !LkRen T Ζ, !LkUp Ix Ζ}
    (γ γξ γζ : Dom) (ξ : Ξ) (ζ : Ζ) (δ : Dom):
    SubMorph T Ξ Ζ γ       γξ       γζ       ξ          ζ →
    SubMorph T Ξ Ζ (γ ∪ δ) (γξ ∪ δ) (γζ ∪ δ) (up Ξ ξ δ) (up Ζ ζ δ).
  Proof.
    intros mξζ.
    apply submorph_ix_stx.
    apply submorphix_up; trivial.
    apply (submorph_ix_stx (T:=T)); trivial.
  Qed.

  Lemma isubmorph_up₁_bla
    (T : Type) `{Vr T, Wk T, Ws T, !WsVr T, !WsWk T}
    (Ξ : Type) `{Lk T Ξ, Up Ξ, !LkUp T Ξ}
    (Ζ : Type) `{Lk T Ζ, Up Ζ, !LkUp T Ζ}
    (γ γξ γζ : Dom) (ξ : Ξ) (ζ : Ζ) :
    SubMorph T Ξ Ζ γ     γξ     γζ     ξ         ζ →
    SubMorph T Ξ Ζ (S γ) (S γξ) (S γζ) (up₁ Ξ ξ) (up₁ Ζ ζ).
  Proof.
    intros mξζ i.
    destruct i; cbn;
      rewrite ?lk_up₁_zero, ?lk_up₁_suc; intros.
    - apply ws_vr; constructor.
    - now apply ws_wk₁, mξζ, wsi_wk₁.
  Qed.

  Lemma isubmorph_up_bla
    (T : Type) `{Vr T, Wk T, Ws T, !WsVr T, !WsWk T}
    (Ξ : Type) `{Lk T Ξ, Up Ξ, !UpHom Ξ, !LkUp T Ξ}
    (Ζ : Type) `{Lk T Ζ, Up Ζ, !UpHom Ζ, !LkUp T Ζ}
    (γ γξ γζ : Dom) (ξ : Ξ) (ζ : Ζ) (δ : Dom) :
    SubMorph T Ξ Ζ γ       γξ       γζ       ξ          ζ →
    SubMorph T Ξ Ζ (γ ∪ δ) (γξ ∪ δ) (γζ ∪ δ) (up Ξ ξ δ) (up Ζ ζ δ).
  Proof.
    intros mξζ; induction δ; cbn; rewrite ?up_zero, ?up_suc;
      auto using (isubmorph_up₁_bla T Ξ Ζ).
  Qed.

  Lemma submorph_idm_initial
    (T : Type) `{Vr T, Wk T, Ws T, !WsVr T, !WsWk T}
    (Ξ : Type) `{Lk T Ξ, Idm Ξ, !LkIdm T Ξ}
    (Ζ : Type) `{Lk T Ζ}
    {γ₁ γ₂ : Dom} {ζ : Ζ} (wζ : WsSub T Ζ γ₁ γ₂ ζ) :
    SubMorph T Ξ Ζ γ₁ γ₁ γ₂ (idm Ξ) ζ.
  Proof.
    intros i wi.
    apply wζ, (wsi_vr (T:=T)).
    now rewrite lk_idm in wi.
  Qed.

  Global Instance iSubMorphUp
    {T : Type} `{Vr T, Wk T, Ws T, !WsVr T, !WsWk T}
    {Ξ : Type} `{Lk T Ξ, Up Ξ, !UpHom Ξ, !LkUp T Ξ}
    {Ζ : Type} `{Lk T Ζ, Up Ζ, !UpHom Ζ, !LkUp T Ζ} :
    SubMorphUp T Ξ Ζ.
  Proof.
    constructor.
    - apply (isubmorph_up₁_bla T Ξ Ζ).
    - apply (isubmorph_up_bla T Ξ Ζ).
  Qed.

  Class WsTrNat
    (T : Type) `{Ws T} (X : Type) `{Tr T X, Ws X} :=
    ws_tr_nat :
      ∀ (Ξ : Type) `{Lk T Ξ, Up Ξ}
        (Ζ : Type) `{Lk T Ζ, Up Ζ}
        `{!SubMorphUp T Ξ Ζ}
        (x : X)
        (γ γξ γζ : Dom) (ξ : Ξ) (ζ : Ζ)
        (ξζm : SubMorph T Ξ Ζ γ γξ γζ ξ ζ),
        ⟨ γξ ⊢ tr T X Ξ x ξ ⟩ → ⟨ γζ ⊢ tr T X Ζ x ζ ⟩.

End WsTrNat.

(******************************************************************************)
