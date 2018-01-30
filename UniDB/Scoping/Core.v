(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.

Reserved Notation "γ ∋ i"          (at level 80).
Reserved Notation "⟨  γ ⊢ t  ⟩"    (at level 0, γ at level 98, t at level 98).

(******************************************************************************)

Class Ws (X: Type) := ws: Dom → X → Prop.
Notation "⟨  γ ⊢ t  ⟩" := (ws γ t).

Inductive wsIx : Dom → Ix → Prop :=
  | ws0 γ   :         S γ ∋ 0
  | wsS γ i : γ ∋ i → S γ ∋ S i
where "γ ∋ i" := (wsIx γ i).

Instance WsIx : Ws Ix := { ws := wsIx }.

Section BasicClasses.

  Class WsVr (T: Type) {wsT: Ws T} {vrT: Vr T} :=
    { ws_vr: ∀ (γ: Dom) (i: Ix), γ ∋ i → ⟨ γ ⊢ (vr T i) ⟩;
      wsi_vr: ∀ (γ: Dom) (i: Ix), ⟨ γ ⊢ (vr T i) ⟩ → γ ∋ i
    }.

  Global Instance iWsVrIx : WsVr Ix.
  Proof. now constructor. Qed.

  Class WsWk (X: Type) {wsX: Ws X} {wkX: Wk X} :=
    { ws_wk₁: ∀ (γ: Dom) (x: X), ⟨ γ ⊢ x ⟩ → ⟨ S γ ⊢ wk₁ X x ⟩;
      ws_wk: ∀ (γ δ: Dom) (x: X), ⟨ γ ⊢ x ⟩ → ⟨ γ ∪ δ ⊢ wk X δ x ⟩;
      wsi_wk₁: ∀ (γ: Dom) (x: X), ⟨ S γ ⊢ wk₁ X x ⟩ → ⟨ γ ⊢ x ⟩;
      wsi_wk: ∀ (γ δ: Dom) (x: X), ⟨ γ ∪ δ ⊢ wk X δ x ⟩ → ⟨ γ ⊢ x ⟩
    }.

  Global Instance iWsWk : WsWk Ix.
  Proof.
    constructor.
    - now constructor.
    - intros; induction δ; cbn.
      + trivial.
      + now constructor.
    - now inversion 1.
    - intros; induction δ; cbn in *.
      + trivial.
      + inversion H; subst; auto.
  Qed.

End BasicClasses.

Definition WsSub T Ξ {lkTΞ : Lk T Ξ} {wsX: Ws T} (γ δ: Dom) (ξ: Ξ) : Prop :=
  ∀ (i: Ix), γ ∋ i → ⟨ δ ⊢ lk T Ξ ξ i ⟩.

Section WsUp.

  Class WsUp (T : Type) `{Ws T} (Ξ : Type) `{Up Ξ, Lk T Ξ} :=
    { ws_up₁ :  ∀ {γ₁ γ₂: Dom} {ξ : Ξ},
                  WsSub T Ξ γ₁ γ₂ ξ →
                  WsSub T Ξ (S γ₁) (S γ₂) (up₁ Ξ ξ);
      wsi_up₁ : ∀ {γ₁ γ₂: Dom} {ξ : Ξ},
                  WsSub T Ξ (S γ₁) (S γ₂) (up₁ Ξ ξ) →
                  WsSub T Ξ γ₁ γ₂ ξ;
      ws_up :   ∀ {γ₁ γ₂: Dom} {ξ : Ξ} (δ : Dom),
                  WsSub T Ξ γ₁       γ₂       ξ →
                  WsSub T Ξ (γ₁ ∪ δ) (γ₂ ∪ δ) (up Ξ ξ δ);
      wsi_up :  ∀ {γ₁ γ₂: Dom} {ξ : Ξ} (δ : Dom),
                  WsSub T Ξ (γ₁ ∪ δ) (γ₂ ∪ δ) (up Ξ ξ δ) →
                  WsSub T Ξ γ₁       γ₂       ξ
    }.

  (* Context {T : Type} `{Vr T, Wk T, Ws T, !WsVr T, !WsWk T}. *)
  (* Context {Ξ : Type} `{Lk T Ξ, Up Ξ, !LkUp T Ξ}. *)

  (* Lemma ws_up₁ (γ₁ γ₂: Dom) : *)
  (*   ∀ (ξ : Ξ), *)
  (*     ⟨ ξ   : γ₁ => γ₂ ⟩ → *)
  (*     ⟨ ξ↑₁ : S γ₁ => S γ₂ ⟩. *)
  (* Proof. *)
  (*   intros ? ? ? ws_i. *)
  (*   inversion ws_i; subst; cbn in *. *)
  (*   - rewrite lk_up₁_zero. *)
  (*     apply ws_vr; constructor. *)
  (*   - rewrite lk_up₁_suc. *)
  (*     apply ws_wk₁; auto. *)
  (* Qed. *)

  (* Lemma wsi_up₁ (γ₁ γ₂: Dom) : *)
  (*   ∀ (ξ : Ξ), *)
  (*     ⟨ ξ↑₁ : S γ₁ => S γ₂ ⟩ → *)
  (*     ⟨ ξ   : γ₁ => γ₂ ⟩. *)
  (* Proof. *)
  (*   intros ? ws_ξ ? ws_i. *)
  (*   apply wsi_wk₁. *)
  (*   rewrite <- lk_up₁_suc. *)
  (*   apply ws_ξ. *)
  (*   now constructor. *)
  (* Qed. *)

  (* Lemma ws_up `{!UpHom Ξ} (γ₁ γ₂: Dom) : *)
  (*   ∀ (ξ : Ξ) (δ : Dom), *)
  (*     ⟨ ξ     : γ₁     => γ₂     ⟩ → *)
  (*     ⟨ ξ ↑ δ : γ₁ ∪ δ => γ₂ ∪ δ ⟩. *)
  (* Proof. *)
  (*   intros ? ? ?. *)
  (*   induction δ; cbn. *)
  (*   - now rewrite up_zero. *)
  (*   - rewrite up_suc. *)
  (*     now apply ws_up₁. *)
  (* Qed. *)

  (* Lemma wsi_up `{!UpHom Ξ} (γ₁ γ₂: Dom) : *)
  (*   ∀ (ξ : Ξ) (δ : Dom), *)
  (*     ⟨ ξ ↑ δ : γ₁ ∪ δ => γ₂ ∪ δ ⟩ → *)
  (*     ⟨ ξ     : γ₁     => γ₂     ⟩. *)
  (* Proof. *)
  (*   intros ? ? ws_ξδ. *)
  (*   induction δ; cbn in *. *)
  (*   - now rewrite up_zero in ws_ξδ. *)
  (*   - apply IHδ. *)
  (*     apply wsi_up₁. *)
  (*     now rewrite <- up_suc. *)
  (* Qed. *)

End WsUp.

Section WsIdm.

  Context {T : Type} `{WsVr T}.
  Context {Ξ : Type} `{Lk T Ξ, Idm Ξ, !LkIdm T Ξ}.

  Lemma ws_idm (γ: Dom) :
    WsSub T Ξ γ γ (idm Ξ).
  Proof.
    intros i ws_i.
    rewrite lk_idm.
    now apply ws_vr.
  Qed.

End WsIdm.

Section WsWkm.

  Context {T: Type} `{WsVr T}.
  Context {Ξ : Type} `{Lk T Ξ, Wkm Ξ, !LkWkm T Ξ}.

  Lemma ws_wkm₁ (γ: Dom) :
    WsSub T Ξ γ (S γ) (wkm₁ Ξ).
  Proof.
    intros i ws_i.
    rewrite lk_wkm₁.
    apply ws_vr.
    now constructor.
  Qed.

  Lemma ws_wkm (γ δ: Dom) :
    WsSub T Ξ γ (γ ∪ δ) (wkm Ξ δ).
  Proof.
    intros i ws_i.
    rewrite lk_wkm.
    now apply ws_vr, ws_wk.
  Qed.

End WsWkm.

Section WsSnoc.

  Context {T: Type} `{Ws T}.
  Context {Ξ : Type} `{LkSnoc T Ξ}.

  Lemma ws_snoc (γ₁ γ₂: Dom) (ξ: Ξ) (t: T) :
    WsSub T Ξ γ₁ γ₂ ξ → ⟨ γ₂ ⊢ t ⟩ →
    WsSub T Ξ (S γ₁) γ₂ (snoc T Ξ ξ t).
  Proof.
    intros ? ? ?; inversion 1; subst;
      rewrite ?lk_snoc_zero, ?lk_snoc_suc; auto.
  Qed.

  Lemma wsi_snoc_sub (γ₁ γ₂: Dom) (ξ: Ξ) (t: T) :
    WsSub T Ξ (S γ₁) γ₂ (snoc T Ξ ξ t) →
    WsSub T Ξ γ₁ γ₂ ξ.
  Proof.
    intros wξ i wi.
    specialize (wξ (S i)).
    rewrite lk_snoc_suc in wξ.
    apply wξ.
    now constructor.
  Qed.

  Lemma wsi_snoc_tm (γ₁ γ₂: Dom) (ξ: Ξ) (t: T) :
    WsSub T Ξ (S γ₁) γ₂ (snoc T Ξ ξ t) →
    ⟨ γ₂ ⊢ t ⟩.
  Proof.
    intros wξ.
    specialize (wξ 0).
    rewrite lk_snoc_zero in wξ.
    apply wξ.
    now constructor.
  Qed.

End WsSnoc.

Section WsBeta.

  Context {T: Type} `{WsVr T}.
  Context {Ξ : Type} `{Lk T Ξ, Beta T Ξ, !LkBeta T Ξ}.

  Lemma ws_beta₁ (γ: Dom) (t: T) :
    ⟨ γ ⊢ t ⟩ →
    WsSub T Ξ (S γ) γ (beta₁ T Ξ t).
  Proof.
    intros ? ?.
    inversion 1; subst.
    - now rewrite lk_beta₁_zero.
    - rewrite lk_beta₁_suc.
      now apply ws_vr.
  Qed.

  Lemma wsi_beta₁ (γ: Dom) (t: T) :
    WsSub T Ξ (S γ) γ (beta₁ T Ξ t) →
    ⟨ γ ⊢ t ⟩.
  Proof.
    intros ws_b.
    specialize (ws_b 0 (ws0 _)).
    now rewrite lk_beta₁_zero in ws_b.
  Qed.

End WsBeta.

(******************************************************************************)
