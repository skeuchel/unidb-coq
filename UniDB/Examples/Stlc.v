Require Import UniDB.
Require Import List.
Import ListNotations.

Inductive Ty : Set :=
  | arr (σ τ : Ty)
  | top.

Inductive Tm : Set :=
  | var (i : Ix)
  | abs (σ : Ty) (t : Tm)
  | app (t1 t2 : Tm)
  | ttt.

Fixpoint trTm {Ξ : Type} `{Lk Tm Ξ, Up Ξ} (t : Tm) (ξ : Ξ) : Tm :=
  match t with
  | var i     => lk Tm Ξ ξ i
  | abs σ t   => abs σ (trTm t ξ↑₁)
  | app t1 t2 => app (trTm t1 ξ) (trTm t2 ξ)
  | ttt       => ttt
  end.

Instance UniDBTm : UniDBVar Tm := {| VrT := var; TrT := @trTm |}.
Instance UnidebTmLemmas : UniDBVarLemmas Tm.
Proof. unidb_derive_instance. Qed.

Fixpoint getvar (Γ : list Ty) (i : Ix) : option Ty :=
  match Γ , i with
   | []       , _    => None
   | T  :: Γ' , O    => Some T
   | T' :: Γ' , S i' => getvar Γ' i'
  end.

Inductive Typing (Γ : list Ty) : Tm → Ty → Prop :=
  | T_Var {i τ} :
      getvar Γ i = Some τ →
      Typing Γ (var i) τ
  | T_Unit :
      Typing Γ ttt top
  | T_Abs {t σ τ} :
      Typing (σ :: Γ) t τ →
      Typing Γ (abs σ t) (arr σ τ)
  | T_App {t1 t2 σ τ} :
      Typing Γ t1 (arr σ τ) → Typing Γ t2 σ →
      Typing Γ (app t1 t2) τ.

(* Substitute 0 for s in x *)
Definition subTm {X : Type} `{Tr Tm X} (s : Tm) (x : X) : X :=
  tr Tm X (Reg Tm) x (beta₁ Tm (Reg Tm) s).

Inductive red : Tm → Tm → Prop :=
  | red_app1 {t1 t1' t2} :
      red t1 t1' → red (app t1 t2) (app t1' t2)
  | red_app2 {t1 t2 t2'} :
      red t2 t2' → red (app t1 t2) (app t1 t2')
  | red_abs  {σ t t'} :
      red t t' → red (abs σ t) (abs σ t')
  | red_beta₁ {σ s t} :
      red (app (abs σ t) s) (subTm s t).

(* Metatheory. *)

Section StrongNormalization.

  Definition Cand := Tm → Prop.
  Definition Neutral : Cand :=
    fun t => match t with
               | abs _ _ => False
               | _       => True
             end.

  Inductive SN (t : Tm) : Prop :=
    | sn_i : (∀ t', red t t' → SN t') → SN t.

  Record CR (P : Cand) :=
    { cr_sn : ∀ t, P t → SN t;
      cr_cl : ∀ t, P t → ∀ t', red t t' → P t';
      cr_nt : ∀ t, Neutral t → (∀ t', red t t' → P t') → P t
    }.
  Arguments cr_sn [_] _ [_] _.
  Arguments cr_cl [_] _ [_] _ [_] _.
  Arguments cr_nt [_] _ [_] _ _.

  Lemma sn_d {t} (sn_t: SN t) : ∀ t', red t t' → SN t'.
  Proof. destruct sn_t; auto. Qed.

  Lemma cr_SN : CR SN.
  Proof. constructor; eauto using sn_d, sn_i. Qed.

  Lemma sn_ttt : SN ttt.
  Proof. constructor; inversion 1. Qed.

  Lemma sn_inv_app {t1} t2 (sn: SN (app t1 t2)) : SN t1.
  Proof. depind sn; constructor; eauto using red. Qed.

  Lemma red_ap {t t' : Tm} (r : red t t') :
    ∀ (ξ : Reg Tm), red t[ξ] t'[ξ].
  Proof.
    induction r; cbn; intros; try constructor; auto.
    repeat change (trTm ?t ?ξ) with (t[ξ]); usimpl; constructor.
  Qed.

  Lemma sn_beta_var {t} n (sn: SN (t[beta₁ Tm (Reg Tm) (var n)])) : SN t.
  Proof. depind sn; constructor; eauto using red_ap. Qed.

  Lemma cr_var {P:Cand} (crP : CR P) : ∀ n, P (var n).
  Proof. intros; apply cr_nt; simpl; auto; inversion 1. Qed.

  Definition ARR (P R: Cand) : Cand :=
    fun (t1: Tm) => ∀ t2, P t2 → R (app t1 t2).
  Definition PI (F: Cand → Cand) : Cand :=
    fun M => ∀ P, CR P → F P M.

  Lemma cr_ARR {P R} {CR_P: CR P} {CR_R: CR R} : CR (ARR P R).
  Proof with cbn; eauto using red.
    constructor.
    - intros t ARR_t; eapply (sn_inv_app (var 0)), (cr_sn CR_R), ARR_t, cr_var...
    - intros t ARR_t t' r s P_s; eapply (cr_cl CR_R)...
    - intros t nt_t Hyp t' P_t'; apply (cr_nt CR_R)...
      generalize (cr_sn CR_P P_t').
      induction 1 as [t']; intros t'' r.
      inversion r; subst.
      + eapply Hyp...
      + eapply cr_nt... eapply H0... eapply cr_cl...
      + destruct nt_t.
  Qed.

  Lemma cr_PI {F} (cr_F: (∀ P, CR P → CR (F P))) : CR (PI F).
  Proof.
    constructor; cbn.
    - intros t PI_t; refine (cr_sn (cr_F _ cr_SN) (PI_t _ cr_SN)).
    - intros t PI_t t' r P CR_P; refine (cr_cl (cr_F _ CR_P) (PI_t _ CR_P) r).
    - intros t NT_t PI_t' P CR_P; refine (cr_nt (cr_F _ CR_P) NT_t _).
      intros; apply PI_t'; eauto using cr_SN.
  Qed.

  Lemma arr_beta_expand {P R} (crP: CR P) (crR: CR R) :
    ∀ T M, (∀ N, P N → R (M[beta₁ _ _ N])) →
      ARR P R (abs T M).
  Proof.
    intros T M H.
    assert (SN_M : SN M) by eauto using (sn_beta_var 0), (cr_sn crR), (cr_var crP).
    revert H.
    induction SN_M; intros Hyp L1 ?.
    assert (SN_L1: SN L1) by eauto using (cr_sn crP).
    induction SN_L1.
    apply (cr_nt crR); simpl; auto.
    intros ? r.
    depind r; eauto.
    * dependent destruction r; eauto.
      unfold ARR in *; eauto using (cr_cl crR), red_ap.
    * eauto using (cr_cl crP).
  Qed.

  Fixpoint Int (T: Ty) : Cand :=
    match T with
      | top       => SN
      | arr T1 T2 => ARR (Int T1) (Int T2)
    end.

  Lemma cr_Int (T: Ty) : CR (Int T).
  Proof. induction T; eauto using cr_SN, cr_ARR. Qed.

  Definition IntEnv Γ (ξ: Reg Tm) : Prop :=
    ∀ x T, getvar Γ x = Some T → Int T (lk _ _ ξ x).

  Lemma fundamental_theorem {Γ M T} (wt: Typing Γ M T) :
    ∀ ξ, IntEnv Γ ξ → Int T (M[ξ]).
  Proof.
    induction wt; intros ξ IntEnv_Γ; cbn.
    - now apply IntEnv_Γ.
    - apply sn_ttt.
    - apply arr_beta_expand; cbn; intros; eauto using cr_Int.
      repeat change (trTm ?t ?ξ) with (t[ξ]).
      change (reg_up₁ ?ξ) with (ξ↑₁).
      rewrite <- tr_comp.
      apply IHwt; simpl.
      unfold IntEnv; intros.
      destruct x; inversion H0; subst.
      + cbn; trivial.
      + rewrite lk_comp_tr.
        rewrite lk_up₁_suc.
        rewrite <- (tr_wkm₁_wk₁ (Ξ := Reg Tm)).
        usimpl.
        now apply IntEnv_Γ.
    - cbn in *; unfold ARR in *; auto.
  Qed.

  Lemma fundamental_theorem_idm {Γ M T} (wt: Typing Γ M T) : Int T M.
  Proof.
    rewrite <- (tr_idm (Ξ := Reg Tm)); apply (fundamental_theorem wt).
    unfold IntEnv; intros; apply cr_var; eauto using cr_Int.
  Qed.

  Theorem strong_normalization {Γ t T} (wt: Typing Γ t T) : SN t.
  Proof.
    eauto using (cr_sn (cr_Int T)), fundamental_theorem_idm.
  Qed.

End StrongNormalization.

(* Section WsTm. *)

(*   Inductive WsTm (γ : Dom) : Tm → Prop := *)
(*     | ws_var {i} (ws_i : γ ∋ i): ⟨ γ ⊢ var i ⟩ *)
(*     | ws_abs {σ t} (ws_t : ⟨ S γ ⊢ t ⟩): ⟨ γ ⊢ abs σ t ⟩ *)
(*     | ws_app {t1 t2} (ws_t1 : ⟨ γ ⊢ t1 ⟩) (ws_t2 : ⟨ γ ⊢ t2 ⟩): *)
(*         ⟨ γ ⊢ app t1 t2 ⟩ *)
(*     | ws_ttt : ⟨ γ ⊢ ttt ⟩ *)
(*   where "⟨ γ ⊢ t ⟩" := (WsTm γ t). *)

(*   Global Instance iWsTm : Ws Tm := WsTm. *)

(* End WsTm. *)


Section TypeSafety.

  (* Well-typed substitution for the substitution lemma of the Typing relation.
     Funny that this is not needed for strong normalization. *)
  Definition WtSub {Ξ} `{Lk Tm Ξ} (Γ Δ: list Ty) (ξ: Ξ) : Prop :=
    ∀ (i: Ix) (τ : Ty), getvar Γ i = Some τ → Typing Δ (lk Tm Ξ ξ i) τ.

  Class WtSubUp (Ξ : Type) `{Lk Tm Ξ, Up Ξ} :=
    wtsub_up₁ : ∀ {ξ : Ξ} {Γ Δ : list Ty} (wξ : WtSub Γ Δ ξ) (σ : Ty), WtSub (σ :: Γ) (σ :: Δ) (ξ↑₁).

  Lemma typing_tr {Ξ} `{Lk Tm Ξ, Up Ξ, !WtSubUp Ξ} {Γ t τ} (wt : Typing Γ t τ) :
    ∀ (ξ : Ξ) (Δ : list Ty) (wξ : WtSub Γ Δ ξ), Typing Δ (tr Tm Tm Ξ t ξ) τ.
  Proof.
    induction wt; cbn; intros.
    - auto.
    - constructor.
    - constructor.
      now apply IHwt, wtsub_up₁.
    - econstructor; auto.
  Qed.

  Lemma iWtSubUpRen {Ξ : Type} `{Lk Ix Ξ, Lk Tm Ξ, Up Ξ, !LkRen Tm Ξ, !LkUp Tm Ξ} : WtSubUp Ξ.
  Proof.
    intros ξ Γ Δ wξ σ i τ wi.
    unfold WtSub in wξ.
    destruct i; cbn in wi.
    - inversion wi; subst.
      rewrite lk_up₁_zero.
      repeat constructor.
    - rewrite lk_up₁_suc.
      rewrite (lk_ren Tm).
      constructor; cbn.
      specialize (wξ _ _ wi).
      rewrite (lk_ren Tm) in wξ.
      now inversion wξ.
  Qed.

  Lemma typing_wk₁ {Γ t τ} (wt : Typing Γ t τ) (σ : Ty) :
    Typing (σ :: Γ) (wk₁ Tm t) τ.
  Proof.
    pose proof (iWtSubUpRen (Ξ := Shift)).
    apply (typing_tr wt).
    repeat intro.
    rewrite lk_wkm.
    now repeat constructor.
  Qed.

  Instance iWtSubUp {Ξ} `{Lk Tm Ξ, Up Ξ, !LkUp Tm Ξ} : WtSubUp Ξ := {}.
  Proof.
    intros ξ Γ Δ wξ σ i τ wi.
    destruct i; cbn in wi.
    - inversion wi; subst.
      rewrite lk_up₁_zero.
      repeat constructor.
    - rewrite lk_up₁_suc.
      apply typing_wk₁.
      now apply wξ.
  Qed.

  Lemma wtsub_beta₁ {Ξ} `{Lk Tm Ξ, Beta Tm Ξ, !LkBeta Tm Ξ} :
    ∀ {Γ t σ} (wt : Typing Γ t σ),
      WtSub (σ :: Γ) Γ (beta₁ Tm Ξ t).
  Proof.
    intros ? ? ? ? i ? wi.
    destruct i; cbn in wi.
    - inversion wi; subst.

      now rewrite lk_beta₁_zero.
    - rewrite lk_beta₁_suc.
      now constructor.
  Qed.

  Fixpoint Value (t : Tm) : Prop :=
    match t with
      | ttt      => True
      | abs _ _  => True
      | _        => False
    end.

  Lemma can_form_tarr {Γ t σ τ} (v: Value t) (wt: Typing Γ t (arr σ τ)) :
    ∃ t2, t = abs σ t2.
  Proof. depind wt; try contradiction; exists t; reflexivity. Qed.

  Lemma progress (t : Tm) (τ : Ty) (wt: Typing ([]) t τ) :
    Value t ∨ ∃ t', red t t'.
  Proof with try (subst; eauto using red).
    depind wt; cbn; auto.
    - destruct IHwt1 as [v1|[t1' r1]]...
      destruct IHwt2 as [v2|[t2' r2]]...
      destruct (can_form_tarr v1 wt1)...
  Qed.

  Lemma preservation {Γ t U} (wt: Typing Γ t U) :
    ∀ {t'}, red t t' → Typing Γ t' U.
  Proof.
    induction wt; intros t' e; inversion e; subst; eauto using Typing.
    - inversion wt1; subst.
      apply (typing_tr H0).
      eapply (wtsub_beta₁ wt2).
  Qed.

End TypeSafety.
