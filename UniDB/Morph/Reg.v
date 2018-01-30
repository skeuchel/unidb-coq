(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.
Require Import UniDB.Spec.Subst.
Require Import UniDB.Morph.Weaken.

(******************************************************************************)

Inductive Reg (T : Type) : Type :=
  | reg_wk (ξ : Weaken)
  | reg_sn (ξ : Reg T) (t : T).

Arguments reg_wk {_} ξ.
Arguments reg_sn {_} ξ t.

Section Lookup.

  Context {T : Type} `{Vr T}.

  Fixpoint lk_reg (ξ : Reg T) (i : Ix) : T :=
    match ξ , i with
      | reg_wk ξ   , i   => lk T Weaken ξ i
      | reg_sn ξ t , O   => t
      | reg_sn ξ t , S i => lk_reg ξ i
    end.

  Global Instance iLkReg : Lk T (Reg T) := lk_reg.

End Lookup.

Section Weakening.

  Context {T : Type}.

  Fixpoint wk_reg `{Wk T} (δ : Dom) (ξ : Reg T) {struct ξ} : Reg T :=
    match ξ with
    | reg_wk ξ   => reg_wk (wk Weaken δ ξ)
    | reg_sn ξ t => reg_sn (wk_reg δ ξ) (wk T δ t)
    end.

  Global Instance iWkReg `{Wk T} : Wk (Reg T) := wk_reg.
  Global Instance iWkHomReg `{WkHom T} : WkHom (Reg T) := {}.
  Proof.
    - intro ξ; induction ξ; cbn.
      + reflexivity.
      + f_equal.
        * trivial.
        * apply wk_zero.
    - intros δ ξ; induction ξ; cbn.
      + reflexivity.
      + f_equal.
        * trivial.
        * apply wk_suc.
  Qed.

  Definition reg_up₁ `{Vr T, Wk T} (ξ : Reg T) : Reg T :=
    reg_sn (wk₁ (Reg T) ξ) (vr T 0).

  Fixpoint reg_up `{Vr T, Wk T} (ξ : Reg T) (δ : Dom) : Reg T :=
    match δ with
    | O => ξ
    | S δ => reg_up₁ (reg_up ξ δ)
    end.

  Global Instance iUpReg `{Vr T, Wk T} : Up (Reg T) := reg_up.
  Global Instance iUpHomReg `{Vr T, Wk T} : UpHom (Reg T).
  Proof. constructor; reflexivity. Qed.

  Global Instance iLkUpReg `{WkVr T, !WkHom T} : LkUp T (Reg T).
  Proof.
    apply make_lkup_inst.
    - auto.
    - induction ξ; intros.
      + cbn.
        do 2 rewrite (lk_ren T).
        now rewrite wk₁_vr.
      + destruct i.
        * trivial.
        * apply IHξ.
  Qed.

End Weakening.

Section RegInstances.

  Context {T : Type}.

  Global Instance iIdmReg : Idm (Reg T) := reg_wk weaken_id.
  Global Instance iWkmReg : Wkm (Reg T) := fun δ => reg_wk (wkm Weaken δ).
  Global Instance iBetaReg : Beta T (Reg T) := fun t => reg_sn (idm _) t.

End RegInstances.

Section RegLookupInstances.

  Context {T : Type} {vrT : Vr T}.

  Global Instance iLkIdmReg : LkIdm T (Reg T) := {}.
  Proof. auto. Qed.

  Global Instance iLkWkmReg {wkT : Wk T} : LkWkm T (Reg T) := {}.
  Proof. intros; apply (f_equal (vr T)), weakenIx_wkWeaken. Qed.

  Global Instance iLkBetaReg : LkBeta T (Reg T).
  Proof. constructor; reflexivity. Qed.

End RegLookupInstances.

Section HComposition.

  Context {T : Type}.

  Fixpoint reg_hcomp (ξ : Weaken) (ζ : Reg T) {struct ζ} :=
    match ζ with
    | reg_wk ζ   => reg_wk (comp Weaken ξ ζ)
    | reg_sn ζ t => match ξ with
                    | weaken_id   => reg_sn ζ t
                    | weaken_wk ξ => reg_hcomp ξ ζ
                    end
    end.

  Global Instance iHCompWeakenReg :
    HComp Weaken (Reg T) (Reg T) := reg_hcomp.
  Global Instance iHCompIdmLeftWeakenReg :
    HCompIdmLeft Weaken (Reg T) := {}.
  Proof.
    intros ζ; destruct ζ; cbn.
    - f_equal; apply comp_idm_left.
    - reflexivity.
  Qed.

  Lemma hcomp_assoc (ξ₁ ξ₂ : Weaken) (ξ₃ : Reg T) :
    hcomp Weaken (Reg T) (Reg T) ξ₁ (hcomp Weaken (Reg T) (Reg T) ξ₂ ξ₃) =
    hcomp Weaken (Reg T) (Reg T) (comp Weaken ξ₁ ξ₂) ξ₃.
  Proof.
    revert ξ₁ ξ₂.
    induction ξ₃; cbn; intros.
    - f_equal.
      apply comp_assoc.
    - now destruct ξ₂; cbn.
  Qed.

  Lemma wk_hcomp `{Wk T} (ξ₁ : Weaken) (ξ₂ : Reg T) :
    ∀ δ, wk (Reg T) δ (hcomp Weaken (Reg T) (Reg T) ξ₁ ξ₂) =
         hcomp Weaken (Reg T) (Reg T) ξ₁ (wk (Reg T) δ ξ₂).
  Proof.
    revert ξ₁; induction ξ₂; cbn; intros.
    - f_equal; apply wk_comp_weaken.
    - now destruct ξ₁; cbn.
  Qed.

End HComposition.

Section Composition.

  Context {T : Type} `{Vr T, Wk T, Tr T T}.

  Fixpoint reg_comp (ξ ζ : Reg T) {struct ξ} : Reg T :=
    match ξ with
    | reg_wk ξ   => hcomp Weaken (Reg T) (Reg T) ξ ζ
    | reg_sn ξ t => reg_sn (reg_comp ξ ζ) (tr T T (Reg T) t ζ)
    end.

  Global Instance iCompReg :
    Comp (Reg T) := reg_comp.

  Lemma hcomp_comp_assoc (ξ₁ : Weaken) :
    ∀ (ξ₂ ξ₃ : Reg T),
      hcomp Weaken (Reg T) (Reg T) ξ₁ (comp (Reg T) ξ₂ ξ₃) =
      comp (Reg T) (hcomp Weaken (Reg T) (Reg T) ξ₁ ξ₂) ξ₃.
  Proof.
    induction ξ₁; cbn; intros.
    - change weaken_id with (idm Weaken).
      now rewrite ?hcomp_idm_left.
    - destruct ξ₂; cbn.
      + apply hcomp_assoc.
      + trivial.
  Qed.

  Global Instance iCompIdmReg `{!WkVr T, !WkHom T, !TrIdm T T} :
    CompIdm (Reg T) := {}.
  Proof.
    - induction ξ; cbn.
      + reflexivity.
      + f_equal.
        * trivial.
        * apply tr_idm.
    - intros; cbn.
      apply hcomp_idm_left.
  Qed.

  Lemma lk_hcomp `{!TrVr T} :
    ∀ (ξ₁ : Weaken) (ξ₂ : Reg T) (i : Ix),
      lk T (Reg T) (hcomp Weaken (Reg T) (Reg T) ξ₁ ξ₂) i =
      tr T T (Reg T) (lk T Weaken ξ₁ i) ξ₂.
  Proof.
    intros.
    rewrite (lk_ren T (Ξ := Weaken)), tr_vr.
    revert ξ₁ i; induction ξ₂; cbn; intros.
    - apply lk_ren_comp.
    - now destruct ξ₁; cbn.
  Qed.

  Global Instance iLkCompTrReg `{!TrVr T} :
    LkCompTr T (Reg T) := {}.
  Proof.
    induction ξ₁.
    - apply lk_hcomp.
    - now destruct i; cbn.
  Qed.

  Lemma wk₁_comp `{!WkVr T, !WkHom T, !TrWk T T} :
    ∀ (ξ₁ ξ₂ : Reg T),
      wk₁ (Reg T) (comp (Reg T) ξ₁ ξ₂) =
      comp (Reg T) (wk₁ (Reg T) ξ₁) (up₁ (Reg T) ξ₂).
  Proof.
    induction ξ₁; cbn; intros.
    - apply wk_hcomp.
    - f_equal.
      + apply IHξ₁.
      + change (wk T 1) with (wk₁ T).
        change reg_up₁ with (up₁ (Reg T)).
        now rewrite tr_wk₁.
  Qed.

  Global Instance iUpCompReg `{!WkVr T, !WkHom T, !TrVr T, !TrWk T T} :
    UpComp (Reg T) := {}.
  Proof.
    intros; cbn; unfold reg_up₁; cbn.
    f_equal.
    - apply wk₁_comp.
    - now rewrite tr_vr; cbn.
  Qed.

  Global Instance iCompAssocReg
    `{!WkVr T, !WkHom T, !TrVr T, !TrComp T T, !TrWk T T} :
    CompAssoc (Reg T) := {}.
  Proof.
    induction ξ₁; cbn; intros.
    - apply hcomp_comp_assoc.
    - f_equal.
      + trivial.
      + apply tr_comp.
  Qed.

End Composition.

Section Interaction.

  Context {T : Type} `{Vr T, Wk T, Tr T T}.

  Global Instance iWkmBetaReg :
    WkmBeta T (Reg T) := {}.
  Proof. reflexivity. Qed.

  Lemma comp_wkm `{!WkVr T, !WkHom T, !TrWkmWk T T} :
    ∀ (ξ : Reg T), comp (Reg T) ξ (wkm₁ (Reg T)) = wk₁ (Reg T) ξ.
  Proof.
    induction ξ; cbn.
    - reflexivity.
    - f_equal.
      + trivial.
      + apply tr_wkm_wk.
  Qed.

  Global Instance iWkmCommReg
    `{!WkVr T, !WkHom T, !TrWkmWk T T} :
    WkmComm (Reg T) := {}.
  Proof.
    intros ξ.
    rewrite comp_wkm; cbn.
    change (weaken_id) with (idm Weaken).
    now rewrite hcomp_idm_left.
  Qed.

  Global Instance iBetaCommReg
    `{!WkVr T, !WkHom T, !TrVr T, !TrWkmWk T T, !TrComp T T, !TrWk T T, !TrIdm T T} :
    BetaComm T (Reg T) := {}.
  Proof.
    intros; cbn.
    f_equal.
    - change (weaken_id) with (idm Weaken).
      rewrite hcomp_idm_left.
      change (wk (Reg T) 1 ξ) with (wk₁ (Reg T) ξ).
      rewrite <- comp_wkm.
      rewrite <- comp_assoc.
      rewrite wkm₁_beta₁.
      now rewrite comp_idm_right.
    - now rewrite tr_vr, lk_beta₁_zero.
  Qed.

End Interaction.

(*
  reg-zero : (γ : Dom) → Reg T zero γ
  reg-zero zero    = reg-wk wkm₀
  reg-zero (suc γ) = reg-zero γ ⊙ wkm (Reg T) 1

  complete : (γ₁ γ₂ : Dom) (f : Ix γ₁ → T γ₂) → Reg T γ₁ γ₂
  complete zero     γ₂ f = reg-zero γ₂
  complete (suc γ₁) γ₂ f = reg-sn (complete γ₁ γ₂ (f ∘ suc)) (f zero)
 *)

(******************************************************************************)
