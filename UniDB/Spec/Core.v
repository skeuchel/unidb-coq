(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Export Coq.Unicode.Utf8.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

(******************************************************************************)

Set Maximal Implicit Insertion.

Ltac crushRewriter :=
  repeat
    match goal with
      | [H : _ = _  |- _] => rewrite H
      | [H : ∀ _, _ |- _] => progress rewrite H by now trivial
    end.

(* Injectivity property. *)
Definition Inj {A B} (f: A → B) : Prop :=
  ∀ x y, f x = f y → x = y.
Hint Unfold Inj.

(** * Basic definitions

    This Section contains basic definitions for the de Bruijn representation
    of the abstract syntax.  *)

(** ** Domains *)

(** [Dom] is the representation of domains of typing contexts
    or of simultaneous renamings/substitutions. For the de
    Bruijn representation with a single sort with variables,
    we can represent domains as natural numbers. *)
Definition Dom: Set := nat.

Fixpoint dunion (δ₁ δ₂: Dom) {struct δ₂} : Dom :=
  match δ₂ with
    | O    => δ₁
    | S δ₂ => S (dunion δ₁ δ₂)
  end.
Notation "δ₁ ∪ δ₂" := (dunion δ₁ δ₂) (at level 55, left associativity).

Lemma dunion_assoc (δ₁ δ₂ δ₃: Dom) :
  δ₁ ∪ (δ₂ ∪ δ₃) = (δ₁ ∪ δ₂) ∪ δ₃.
Proof. induction δ₃; cbn; congruence. Qed.

Section FoldlDom.

  Context {X : Type}.
  Variable s : X → X.

  Fixpoint foldlDom (δ: Dom) (x: X) : X :=
    match δ with
      | O   => x
      | S δ => foldlDom δ (s x)
    end.

End FoldlDom.

(** ** De Bruijn indices. *)
Definition Ix : Set := nat.

(** * Syntactic sort related type-classes *)

Section Sorts.

  Section Vars.

    (** Class for syntactic sorts with variables. *)
    Class Vr (T: Type) := vr : Ix → T.
    Global Arguments vr _ {_} i.

    Class VrInj (T: Type) `{Vr T} := vr_inj : Inj (vr T).

  End Vars.

  Global Arguments vr_inj {_ _ _} _ _ _.
  Global Instance iVrIx: Vr Ix := fun i => i.
  Global Instance iVrInjIx: VrInj Ix.
  Proof. now unfold VrInj. Qed.

  Section Weaken.

    (** Class for syntactic sorts that can be weakened. Every sort
        can decide for itself how weakening is implemented. *)
    Class Wk (X : Type) := wk : ∀ (δ : Dom) (x : X), X.
    Global Arguments wk X {_} δ x.
    Definition wk₁ {X : Type} `{Wk X} (x : X) := wk X 1 x.
    Global Arguments wk₁ X {_} x.

    Class WkInj (X : Type) `{Wk X} := wk_inj : ∀ (δ : Dom), Inj (wk X δ).
    Lemma wk₁_inj {X : Type} `{WkInj X} : Inj (wk₁ X).
    Proof. exact (wk_inj 1). Qed.
    Class WkHom (X : Type) `{Wk X} :=
      { wk_zero : ∀ (x : X), wk X 0 x = x;
        wk_suc  : ∀ (δ : Dom) (x : X), wk X (S δ) x = wk₁ X (wk X δ x)
      }.

    Section WeakenIx.
      (** Weaken of indices. Just a flipped addition. *)
      Fixpoint wkIx (δ : Dom) (i : Ix) : Ix :=
        match δ with
        | O    => i
        | S δ' => S (wkIx δ' i)
        end.
      Global Instance iWkIx: Wk Ix := wkIx.
      Global Instance iWkInjIx : WkInj Ix := {}.
      Proof. intro δ; induction δ; auto. Qed.
      Global Instance iWkHomIx : WkHom Ix.
      Proof. constructor; auto. Qed.
    End WeakenIx.

  End Weaken.

  Section WeakenVarInteraction.

    (* Weakening on variables should coincide with the weakening
       of indices. *)
    Class WkVr (T : Type) `{Vr T, Wk T} :=
      wk_vr : ∀ (δ : Dom) (i: Ix),
                 wk T δ (vr T i) = vr T (wk Ix δ i).

    Lemma wk₁_vr {T : Type} `{WkVr T} :
      ∀ (i: Ix), wk₁ T (vr T i) = vr T (S i).
    Proof. exact (wk_vr 1). Qed.

    Global Instance iWkVrIx : WkVr Ix := {}.
    Proof. auto. Qed.

  End WeakenVarInteraction.

End Sorts.

Extract Constant wkIx => "( + )".
Lemma wkIx_extract_sound :
  ∀ δ i, wkIx δ i = δ + i.
Proof. intro δ; induction δ; auto. Qed.

(******************************************************************************)

Section Operations.

  Class Lk (T Ξ : Type) := lk : ∀ (ξ : Ξ) (i : Ix), T.
  Global Arguments lk T Ξ {_} ξ i.

  Class Up (Ξ : Type) := up : ∀ (ξ: Ξ) (δ: Dom), Ξ.
  Global Arguments up Ξ {_} ξ δ.
  Definition up₁ {Ξ : Type} `{Up Ξ} (ξ: Ξ) : Ξ := up Ξ ξ 1.
  Global Arguments up₁ Ξ {_} ξ.

  Class UpHom (Ξ : Type) `{Up Ξ} :=
    { up_zero : ∀ (ξ : Ξ), up Ξ ξ 0 = ξ;
      up_suc  : ∀ (ξ : Ξ) (δ: Dom), up Ξ ξ (S δ) = up₁ Ξ (up Ξ ξ δ)
    }.

  Lemma up_dunion {Ξ : Type} `{UpHom Ξ} :
    ∀ (ξ : Ξ) (δ₁ δ₂ : Dom), up Ξ ξ (δ₁ ∪ δ₂) = up Ξ (up Ξ ξ δ₁) δ₂.
  Proof.
    intros; revert δ₁; induction δ₂; intros; cbn.
    - now rewrite up_zero.
    - now rewrite ?up_suc, IHδ₂.
  Qed.

  Class Comp (Ξ : Type) := comp : ∀ (ξ₁ ξ₂: Ξ), Ξ.
  Global Arguments comp Ξ {_} ξ₁ ξ₂.

  Class Idm (Ξ : Type) := idm : Ξ.
  Global Arguments idm Ξ {_}.
  Class Wkm (Ξ : Type) := wkm : Dom → Ξ.
  Global Arguments wkm Ξ {_} δ.
  Definition wkm₁ {Ξ : Type} `{Wkm Ξ} : Ξ := wkm Ξ 1.
  Global Arguments wkm₁ Ξ {_}.

  Class WkmHom (Ξ : Type) `{Wkm Ξ, Idm Ξ, Comp Ξ} :=
    { wkm_zero : wkm Ξ 0 = idm Ξ;
      wkm_suc  : ∀ (δ: Dom),
                   wkm Ξ (S δ) = comp Ξ (wkm Ξ δ) (wkm₁ Ξ)
    }.

  Class Snoc (T Ξ : Type) := snoc : ∀ (ξ: Ξ) (t: T), Ξ.
  Global Arguments snoc T Ξ {_} ξ t.
  Class Beta (T Ξ : Type) := beta₁ : ∀ (t: T), Ξ.
  Global Arguments beta₁ T Ξ {_} t.

End Operations.

(* Arguments wkm_zero {Ξ _ _ _ _ _}. *)
(* Arguments wkm_suc {Ξ _ _ _ _ _} δ. *)

(******************************************************************************)

Section LookupLemmas.

  Class LkRen
    (T : Type) {vrT : Vr T}
    (Ξ : Type) {lkIxΞ : Lk Ix Ξ} {lkTΞ : Lk T Ξ} :=
    lk_ren : ∀ (ξ : Ξ) (i : Ix),
      lk T Ξ ξ i = vr T (lk Ix Ξ ξ i).
  Global Arguments lk_ren T {_ _ _ _ _} ξ i.

  Class LkRenComp
    (T : Type) {vrT : Vr T}
    (Ξ : Type) {lkIxΞ : Lk Ix Ξ} {lkTΞ : Lk T Ξ} {compΞ : Comp Ξ}
    {lkRenTΞ : LkRen T Ξ} :=
    lk_ren_comp : ∀ (ξ₁ ξ₂ : Ξ) (i : Ix),
                    lk T Ξ (comp Ξ ξ₁ ξ₂) i = lk T Ξ ξ₂ (lk Ix Ξ ξ₁ i).

  Class LkUp
    (T : Type) {vrT : Vr T} {wkT : Wk T}
    (Ξ : Type) {lkTΞ : Lk T Ξ} {upΞ : Up Ξ} :=
    { lk_up₁_zero : ∀ (ξ : Ξ),
                      lk T Ξ (up₁ Ξ ξ) 0 = vr T 0;
      lk_up₁_suc : ∀ (ξ : Ξ) (i : Ix),
                     lk T Ξ (up₁ Ξ ξ) (S i) = wk₁ T (lk T Ξ ξ i);
      lk_up_wk : ∀ (δ : Dom) (ξ : Ξ) (i : Ix),
                   lk T Ξ (up Ξ ξ δ) (wk Ix δ i) = wk T δ (lk T Ξ ξ i)
    }.

  Lemma lk_up₁_wk₁
    {T : Type} {vrT : Vr T} {wkT : Wk T}
    {Ξ : Type} {lkTΞ : Lk T Ξ} {upΞ : Up Ξ} {lkUpΞ : LkUp T Ξ} :
    ∀ (ξ : Ξ) (i : Ix),
      lk T Ξ (up₁ Ξ ξ) (wk₁ Ix i) = wk₁ T (lk T Ξ ξ i).
  Proof. exact lk_up₁_suc. Qed.

  Lemma make_lkup_inst
    {T : Type} {vrT : Vr T} {wkT : Wk T} {wkHomT : WkHom T}
    {Ξ : Type} {lkTΞ : Lk T Ξ} {upΞ : Up Ξ} {upHomΞ : UpHom Ξ}
    (hyp_zero : ∀ (ξ : Ξ),
                  lk T Ξ (up₁ Ξ ξ) 0 = vr T 0)
    (hyp_suc : ∀ (ξ : Ξ) (i : Ix),
                 lk T Ξ (up₁ Ξ ξ) (S i) = wk₁ T (lk T Ξ ξ i)) :
    LkUp T Ξ.
  Proof.
    assert (hyp_wk : ∀ (δ : Dom) (ξ : Ξ) (i : Ix),
                       lk T Ξ (up Ξ ξ δ) (wk Ix δ i) = wk T δ (lk T Ξ ξ i)).
    - induction δ; cbn; intros.
      + now rewrite ?wk_zero, up_zero.
      + now rewrite ?wk_suc, up_suc, <- IHδ, hyp_suc.
    - now constructor.
  Qed.

  Lemma make_lkup_inst_ren
    {T : Type} {vrT : Vr T} {wkT : Wk T} {wkVrT : WkVr T}
    {Ξ : Type} {lkIxΞ : Lk Ix Ξ} {lkTΞ : Lk T Ξ} {upΞ : Up Ξ}
    {lkRenTΞ : LkRen T Ξ} {upHomΞ : UpHom Ξ}
    (hyp_zero : ∀ (ξ : Ξ),
                  lk Ix Ξ (up₁ Ξ ξ) 0 = 0)
    (hyp_suc : ∀ (ξ : Ξ) (i : Ix),
                 lk Ix Ξ (up₁ Ξ ξ) (S i) = S (lk Ix Ξ ξ i)) :
    LkUp T Ξ.
  Proof.
    assert (LkUp Ix Ξ) by now apply make_lkup_inst.
    constructor; intros; rewrite ?(lk_ren T), ?wk₁_vr, ?wk_vr;
      f_equal; now try apply lk_up_wk.
  Qed.

  Class LkIdm
    (T : Type) {vrT : Vr T}
    (Ξ : Type) {lkTΞ : Lk T Ξ} {idmΞ : Idm Ξ} :=
    lk_idm : ∀ (i : Ix),
               lk T Ξ (idm Ξ) i = vr T i.

  Class LkWkm
    (T : Type) {vrT : Vr T}
    (Ξ : Type) {lkTΞ : Lk T Ξ} {wkmΞ : Wkm Ξ} :=
    lk_wkm : ∀ (δ : Dom) (i : Ix),
               lk T Ξ (wkm Ξ δ) i = vr T (wk Ix δ i).

  Lemma lk_wkm₁ {T Ξ : Type} `{LkWkm T Ξ} :
    ∀ (i : Ix), lk T Ξ (wkm₁ Ξ) i = vr T (S i).
  Proof. exact (lk_wkm 1). Qed.

  Class LkSnoc
    (T : Type) {vrT : Vr T}
    (Ξ : Type) {lkTΞ : Lk T Ξ} {snocTΞ : Snoc T Ξ} :=
    { lk_snoc_zero : ∀ (ξ : Ξ) (t : T),
                       lk T Ξ (snoc T Ξ ξ t) 0 = t;
      lk_snoc_suc  : ∀ (ξ : Ξ) (t : T) (i : Ix),
                       lk T Ξ (snoc T Ξ ξ t) (S i) = lk T Ξ ξ i
    }.

  Class LkBeta
    (T : Type) {vrT : Vr T}
    (Ξ : Type) {lkTΞ : Lk T Ξ} {betaTΞ : Beta T Ξ} :=
    { lk_beta₁_zero : ∀ (t : T), lk T Ξ (beta₁ T Ξ t) 0 = t;
      lk_beta₁_suc  : ∀ (t : T) (i : Ix), lk T Ξ (beta₁ T Ξ t) (S i) = vr T i;
    }.

End LookupLemmas.

(******************************************************************************)

Section UpLemmas.

  Class UpIdm (Ξ : Type) `{Up Ξ, Idm Ξ} :=
    { up₁_idm : up₁ Ξ (idm Ξ) = idm Ξ;
      up_idm : ∀ (δ : Dom), up Ξ (idm Ξ) δ = idm Ξ
    }.

  Class UpComp (Ξ : Type) `{Up Ξ, Comp Ξ} :=
    up₁_comp : ∀ (ξ₁ ξ₂ : Ξ),
                 up₁ Ξ (comp Ξ ξ₁ ξ₂) = comp Ξ (up₁ Ξ ξ₁) (up₁ Ξ ξ₂).

  Lemma up_comp {Ξ : Type} `{UpComp Ξ, !UpHom Ξ} (ξ₁ ξ₂ : Ξ) (δ : Dom) :
    up Ξ (comp Ξ ξ₁ ξ₂) δ = comp Ξ (up Ξ ξ₁ δ) (up Ξ ξ₂ δ).
  Proof.
    induction δ.
    - now rewrite ?up_zero.
    - now rewrite ?up_suc, IHδ, up₁_comp.
  Qed.

  (* Lemma up₁_inj {Ξ : Type} `{Up Ξ, Lk Ix Ξ, !LkUp Ix Ξ} : *)
  (*   ∀ (ξ : Ξ), Inj (lk Ix Ξ ξ) → Inj (lk Ix Ξ (ξ↑₁)). *)
  (* Proof. *)
  (*   intros ξ Inj_ξ i j; *)
  (*     destruct i,j; try discriminate; *)
  (*       rewrite ?lk_up₁_zero, ?lk_up₁_suc; *)
  (*       try change (vr Ix 0) with (0); *)
  (*       cbn in *; auto; discriminate. *)
  (* Qed. *)

  (* Lemma up_inj {Ξ : Type} `{Up Ξ, !UpHom Ξ, Lk Ix Ξ, !LkUp Ix Ξ} : *)
  (*   ∀ (δ : Dom) (ξ : Ξ), Inj (lk Ix Ξ ξ) → Inj (lk Ix Ξ (ξ ↑ δ)). *)
  (* Proof. *)
  (*   induction δ; cbn; intros. *)
  (*   - now rewrite up_zero. *)
  (*   - rewrite up_suc. *)
  (*     apply up₁_inj; auto. *)
  (* Qed. *)

End UpLemmas.

Section CompLemmas.

  Class CompIdm (Ξ : Type) `{Idm Ξ, Comp Ξ} :=
    { comp_idm_right : ∀ (ξ : Ξ), comp Ξ ξ (idm Ξ) = ξ;
      comp_idm_left: ∀ (ξ : Ξ), comp Ξ (idm Ξ) ξ = ξ
    }.

  Class CompAssoc (Ξ : Type) `{Comp Ξ} :=
    comp_assoc : ∀ (ξ₁ ξ₂ ξ₃ : Ξ),
                   comp Ξ ξ₁ (comp Ξ ξ₂ ξ₃) = comp Ξ (comp Ξ ξ₁ ξ₂) ξ₃.

End CompLemmas.

(* Arguments comp_idm_right {_ _ _ _} _. *)
(* Arguments comp_idm_left {_ _ _ _} _. *)
(* Arguments comp_assoc {_ _ _} _ _ _. *)

(******************************************************************************)

Section InteractionLemmas.

  Class WkmBeta
        (T : Type)
        (Ξ : Type) {idmΞ : Idm Ξ} {wkmΞ : Wkm Ξ}
        {compΞ : Comp Ξ} {betaTΞ : Beta T Ξ} :=
    wkm₁_beta₁ : ∀ (t : T), comp Ξ (wkm₁ Ξ) (beta₁ T Ξ t) = idm Ξ.

  Section WkmComm.

    Variable Ξ : Type.
    Context {upΞ : Up Ξ} {wkmΞ : Wkm Ξ} {compΞ : Comp Ξ}.

    Class WkmComm :=
      wkm₁_comm : ∀ (ξ : Ξ), comp Ξ ξ (wkm₁ Ξ) = comp Ξ (wkm₁ Ξ) (up₁ Ξ ξ).

    Lemma wkm_comm `{WkmComm} {idmΞ : Idm Ξ}
          {upHomΞ : UpHom Ξ} {wkmHomΞ : WkmHom Ξ}
          {compIdmΞ : CompIdm Ξ} {compAssocΞ : CompAssoc Ξ}
          (ξ : Ξ) (δ : Dom) :
      comp Ξ ξ (wkm Ξ δ) = comp Ξ (wkm Ξ δ) (up Ξ ξ δ).
    Proof.
      induction δ; simpl.
      - now rewrite wkm_zero, up_zero, comp_idm_right, comp_idm_left.
      - rewrite wkm_suc, up_suc.
        rewrite comp_assoc.
        rewrite IHδ.
        rewrite <- comp_assoc.
        rewrite wkm₁_comm.
        now rewrite comp_assoc.
    Qed.

  End WkmComm.

End InteractionLemmas.

(******************************************************************************)

Class HComp (Ξ Ζ Θ : Type) :=
  hcomp : ∀ (ξ : Ξ) (ζ : Ζ), Θ.
Arguments hcomp Ξ Ζ Θ {_} ξ ζ.

Section HCompClasses.

  Class UpHComp
    (Ξ : Type) {upΞ : Up Ξ} {upHomΘ : UpHom Ξ}
    (Ζ : Type) {upΖ : Up Ζ} {upHomΘ : UpHom Ζ}
    (Θ : Type) {upΘ : Up Θ} {upHomΘ : UpHom Θ}
    {hcompΞΖΘ : HComp Ξ Ζ Θ} :=
    up₁_hcomp : ∀ (ξ : Ξ) (ζ : Ζ),
                  up₁ Θ (hcomp Ξ Ζ Θ ξ ζ) = hcomp Ξ Ζ Θ (up₁ Ξ ξ) (up₁ Ζ ζ).

  Lemma up_hcomp {Ξ Ζ Θ : Type} `{UpHComp Ξ Ζ Θ} (ξ : Ξ) (ζ : Ζ) (δ : Dom) :
    up Θ (hcomp Ξ Ζ Θ ξ ζ) δ = hcomp Ξ Ζ Θ (up Ξ ξ δ) (up Ζ ζ δ).
  Proof.
    induction δ.
    - now rewrite ?up_zero.
    - now rewrite ?up_suc, IHδ, up₁_hcomp.
  Qed.

  Class HCompIdmLeft
        (Ξ : Type) {idmΞ : Idm Ξ}
        (Ζ : Type)
        {hcompΞΖΖ : HComp Ξ Ζ Ζ} :=
    hcomp_idm_left : ∀ (ζ : Ζ), hcomp Ξ Ζ Ζ (idm Ξ) ζ = ζ.

  Class HCompIdmRight
        (Ξ : Type)
        (Ζ : Type) {idmΖ : Idm Ζ}
        {hcompΞΖΞ : HComp Ξ Ζ Ξ} :=
    hcomp_idm_right : ∀ (ξ : Ξ), hcomp Ξ Ζ Ξ ξ (idm Ζ) = ξ.

End HCompClasses.

(******************************************************************************)

Section Equality.

  Record Pointwise
    (T : Type)
    (Ξ : Type) `{Lk T Ξ}
    (Ζ : Type) `{Lk T Ζ}
    (ξ : Ξ) (ζ : Ζ) : Prop :=
    { lk_pw : ∀ (i : Ix), lk T Ξ ξ i = lk T Ζ ζ i }.
  (* Notation "ξ ≃ ζ" := (Pointwise _ ξ ζ). *)
  Hint Resolve lk_pw.

  Inductive Extended
    (T : Type)
    (Ξ : Type) `{Lk T Ξ, Up Ξ}
    (Ζ : Type) `{Lk T Ζ, Up Ζ} :
    Ξ → Ζ → Prop :=
    MakeExtended (ξ : Ξ) (ζ : Ζ) (δ : Dom)
      (hyp : ∀ (δ': Dom), Pointwise T Ξ Ζ (up Ξ ξ δ') (up Ζ ζ δ')) :
      Extended T Ξ Ζ (up Ξ ξ δ) (up Ζ ζ δ).
  (* Notation "ξ ≅ ζ" := (Extended ξ ζ). *)

  Section Pointwise.

    Lemma pointwise_up₁
      {T : Type} `{Vr T, Wk T}
      {Ξ : Type} `{Lk T Ξ, Up Ξ, !LkUp T Ξ}
      {Ζ : Type} `{Lk T Ζ, Up Ζ, !LkUp T Ζ} :
      ∀ (ξ : Ξ) (ζ : Ζ) (hyp: Pointwise T Ξ Ζ ξ ζ),
        Pointwise T Ξ Ζ (up₁ Ξ ξ) (up₁ Ζ ζ).
    Proof.
      constructor; intro i; destruct i.
      - now rewrite ?lk_up₁_zero.
      - rewrite ?lk_up₁_suc.
        f_equal; apply hyp.
    Qed.

    Lemma pointwise_up
      {T : Type} `{Vr T, Wk T}
      {Ξ : Type} `{Lk T Ξ, Up Ξ, !UpHom Ξ, !LkUp T Ξ}
      {Ζ : Type} `{Lk T Ζ, Up Ζ, !UpHom Ζ, !LkUp T Ζ} :
      ∀ (ξ : Ξ) (ζ : Ζ) (δ : Dom) (hyp : Pointwise T Ξ Ζ ξ ζ),
        Pointwise T Ξ Ζ (up Ξ ξ δ) (up Ζ ζ δ).
    Proof.
      intros; induction δ.
      - now rewrite ?up_zero.
      - rewrite ?up_suc; now apply pointwise_up₁.
    Qed.

  End Pointwise.

  Section Extended.

    Lemma extended_to_pointwise
      {T : Type} `{Vr T, Wk T}
      {Ξ : Type} `{Lk T Ξ, Up Ξ}
      {Ζ : Type} `{Lk T Ζ, Up Ζ} :
      ∀ (ξ : Ξ) (ζ : Ζ) (hyp : Extended T Ξ Ζ ξ ζ), Pointwise T Ξ Ζ ξ ζ.
    Proof. now destruct 1. Qed.

    Lemma lk_ext
      {T : Type} `{Vr T, Wk T}
      {Ξ : Type} `{Lk T Ξ, Up Ξ}
      {Ζ : Type} `{Lk T Ζ, Up Ζ}
      (ξ : Ξ) (ζ : Ζ) (hyp : Extended T Ξ Ζ ξ ζ) :
      ∀ (i : Ix), lk T Ξ ξ i = lk T Ζ ζ i.
    Proof. now apply lk_pw, extended_to_pointwise. Qed.

    Lemma pointwise_to_extended
      {T : Type} `{Vr T, Wk T}
      {Ξ : Type} `{Lk T Ξ, Up Ξ, !UpHom Ξ}
      {Ζ : Type} `{Lk T Ζ, Up Ζ, !UpHom Ζ} :
      ∀ (ξ : Ξ) (ζ : Ζ)
        (hyp: ∀ (δ: Dom), Pointwise T Ξ Ζ (up Ξ ξ δ) (up Ζ ζ δ)),
        Extended T Ξ Ζ ξ ζ.
    Proof.
      intros ? ? hyp.
      rewrite <- (up_zero ξ), <- (up_zero ζ).
      exact (MakeExtended T Ξ Ζ ξ ζ 0 hyp).
    Qed.

    Lemma extended_up₁
      {T : Type} `{Vr T, Wk T}
      {Ξ : Type} `{Lk T Ξ, Up Ξ, !UpHom Ξ}
      {Ζ : Type} `{Lk T Ζ, Up Ζ, !UpHom Ζ} :
      ∀ (ξ : Ξ) (ζ : Ζ) (hyp: Extended T Ξ Ζ ξ ζ),
        Extended T Ξ Ζ (up₁ Ξ ξ) (up₁ Ζ ζ).
    Proof.
      intros ? ? hyp; destruct hyp.
      rewrite <- ?up_suc.
      exact (MakeExtended T Ξ Ζ ξ ζ (S δ) hyp).
    Qed.

    Lemma extended_up
      {T : Type} `{Vr T, Wk T}
      {Ξ : Type} `{Lk T Ξ, Up Ξ, !UpHom Ξ}
      {Ζ : Type} `{Lk T Ζ, Up Ζ, !UpHom Ζ} :
      ∀ (ξ : Ξ) (ζ : Ζ) (hyp : Extended T Ξ Ζ ξ ζ) (δ : Dom),
        Extended T Ξ Ζ (up Ξ ξ δ) (up Ζ ζ δ).
    Proof.
      induction δ.
      - now rewrite ?up_zero.
      - rewrite ?up_suc.
        now apply extended_up₁.
    Qed.

  End Extended.

End Equality.

(* Arguments Pointwise {_ _ _ _ _} ξ ζ. *)
(* Arguments Extended {_ _ _ _ _ _ _} ξ ζ. *)
(* Arguments pointwise_up₁ {_ _ _ _ _ _ _ _ _ _ _} ξ ζ hyp. *)
(* Arguments pointwise_up {_ _ _ _ _ _ _ _ _ _ _ _ _} ξ ζ hyp δ. *)
(* Arguments extended_to_pointwise {_ _ _ _ _ _ _} ξ ζ hyp. *)
(* Arguments pointwise_to_extended {_ _ _ _ _ _ _ _ _} ξ ζ hyp. *)

Hint Resolve
  lk_pw pointwise_up₁ pointwise_up
  extended_up₁ extended_up
  extended_to_pointwise pointwise_to_extended : unidb_equality.

(******************************************************************************)
