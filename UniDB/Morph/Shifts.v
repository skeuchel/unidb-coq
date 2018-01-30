(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.
Require Import UniDB.Spec.Subst.

Local Arguments lk _ _ {_} ξ i /.

(******************************************************************************)

Inductive Shifts : Set :=
  | shifts_id
  | shifts_wk (ξ : Shifts)
  | shifts_sk (ξ : Shifts).

Fixpoint shiftIx (ξ : Shifts) (i : Ix) : Ix :=
  match ξ , i with
    | shifts_id   , i   => i
    | shifts_wk ξ , i   => S (shiftIx ξ i)
    | shifts_sk ξ , O   => O
    | shifts_sk ξ , S i => S (shiftIx ξ i)
  end.

Definition shifts_up₁ (ξ : Shifts) :=
  match ξ with
    | shifts_id => shifts_id
    | _         => shifts_sk ξ
  end.
Arguments shifts_up₁ !ξ.

Fixpoint shifts_up (ξ : Shifts) (δ: Dom) :=
  match δ with
  | O => ξ
  | S δ => shifts_up₁ (shifts_up ξ δ)
  end.

Fixpoint shifts_wkm (δ:Dom) {struct δ} : Shifts :=
  match δ with
  | O    => shifts_id
  | S δ' => shifts_wk (shifts_wkm δ')
  end.

Fixpoint shifts_comp (ξ₁ ξ₂ : Shifts) {struct ξ₂} : Shifts :=
  match ξ₂ with
  | shifts_id      => ξ₁
  | shifts_wk ξ₂'  => shifts_wk (shifts_comp ξ₁ ξ₂')
  | shifts_sk ξ₂'  => match ξ₁ with
                      | shifts_id     => ξ₂
                      | shifts_wk ξ₁' => shifts_wk (shifts_comp ξ₁' ξ₂')
                      | shifts_sk ξ₁' => shifts_up₁ (shifts_comp ξ₁' ξ₂')
                      end
  end.


Instance iLkShifts {T : Type} `{Vr T} : Lk T Shifts :=
  fun ξ i => vr T (shiftIx ξ i).
Arguments iLkShifts {_ _} ξ i /.
Instance iUpShifts : Up Shifts := shifts_up.
Instance iIdmShifts : Idm Shifts  := shifts_id.
Instance iWkmShifts : Wkm Shifts := shifts_wkm.
Instance iCompShifts : Comp Shifts := shifts_comp.

(******************************************************************************)

Instance iUpHomShifts : UpHom Shifts.
Proof. constructor; reflexivity. Qed.
Instance iUpIdmShifts : UpIdm Shifts := {}.
Proof.
  - reflexivity.
  - induction δ; cbn.
    + reflexivity.
    + now rewrite IHδ.
Qed.

Instance iCompIdmShifts : CompIdm Shifts := {}.
Proof.
  - auto.
  - induction ξ; cbn; now f_equal.
Qed.

Instance iUpCompShifts : UpComp Shifts := {}.
Proof.
  destruct ξ₁, ξ₂; cbn; trivial.
    change shifts_id with (idm Shifts);
    now rewrite comp_idm_left.
Qed.

Instance iWkmHomShifts : WkmHom Shifts.
Proof. constructor; auto. Qed.

(* Ltac unidb_fold_shifts := *)
(*   match goal with *)
(*     | |- context[shifts_id] => *)
(*       change shifts_id with (idm Shifts) *)
(*     | |- context[iCompShifts ?ξ ?ζ] => *)
(*       change (iCompShifts ξ ζ) with (ξ ⊙ ζ) *)
(*     | |- context[shifts_up₁ ?ξ] => *)
(*       change (shifts_up₁ ξ) with (ξ ↑₁) *)
(*     | |- context[iUpShifts ?ξ ?δ] => *)
(*       change (iUpShifts ?ξ ?δ) with (ξ ↑ δ) *)
(*     | |- context[shiftIx ?ξ ?i] => *)
(*       change (shiftIx ξ i) with (lk Ix Shifts ξ i) *)
(*   end. *)

Section LookupShifts.

  Global Instance iLkRenShifts {T : Type} `{Vr T} : LkRen T Shifts.
  Proof. now unfold LkRen. Qed.

  Global Instance iLkIdmShifts {T : Type} `{Vr T} : LkIdm T Shifts.
  Proof. now unfold LkIdm. Qed.

  Global Instance iLkWkmShifts {T : Type} `{Vr T} : LkWkm T Shifts := {}.
  Proof.
    intros; cbn; f_equal.
    induction δ; cbn; auto.
  Qed.

  Global Instance iLkUpShifts {T : Type} `{WkVr T} : LkUp T Shifts.
  Proof. apply make_lkup_inst_ren; destruct ξ; reflexivity. Qed.

  Global Instance iLkCompTrShifts {T : Type} `{TrVr T} :
    LkCompTr T Shifts := {}.
  Proof.
    intros; cbn; rewrite tr_vr; cbn; f_equal.
    revert ξ₁ i.
    induction ξ₂; cbn; intros.
    - reflexivity.
    - f_equal; apply IHξ₂.
    - destruct ξ₁, i; cbn;
        try change (shiftIx (shifts_up₁ ?ξ) ?i) with (lk Ix Shifts (up₁ Shifts ξ) i);
        rewrite ?lk_up₁_zero, ?lk_up₁_suc; auto.
  Qed.

End LookupShifts.

(******************************************************************************)
