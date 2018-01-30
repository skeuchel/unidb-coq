(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.
Require Import UniDB.Spec.Subst.
Require Import UniDB.Morph.Pair.
Require Import UniDB.Morph.Shifts.
Require Import UniDB.Morph.Reg.
Require Import UniDB.Morph.Unit.

(******************************************************************************)

Lemma tr_wkm_rel
  (T : Type) {vrT : Vr T} {wkT : Wk T}
  (X : Type) {wkX : Wk X} {trTX : Tr T X}
  {trRelTX : TrRel T X}
  (Ξ : Type) {lkTΞ : Lk T Ξ} {upΞ : Up Ξ} {wkmΞ : Wkm Ξ}
  {lkUpTΞ : LkUp T Ξ} {upHomΞ : UpHom Ξ} {lkWkmTΞ : LkWkm T Ξ}
  (Ζ : Type) {lkTΖ : Lk T Ζ} {upΖ : Up Ζ} {wkmΖ : Wkm Ζ}
  {lkUpTΖ : LkUp T Ζ} {upHomΖ : UpHom Ζ} {lkWkmTΖ : LkWkm T Ζ} :
  ∀ (δ : Dom) (x : X),
     tr T X Ξ x (wkm Ξ δ) = tr T X Ζ x (wkm Ζ δ).
Proof.
  intros.
  apply tr_rel_pw; auto.
  constructor; intros.
  now rewrite !lk_wkm.
Qed.

Lemma tr_wkm₁_rel
  (T : Type) {vrT : Vr T} {wkT : Wk T}
  (X : Type) {wkX : Wk X} {trTX : Tr T X}
  {trRelTX : TrRel T X}
  (Ξ : Type) {lkTΞ : Lk T Ξ} {upΞ : Up Ξ} {wkmΞ : Wkm Ξ}
  {lkUpTΞ : LkUp T Ξ} {upHomΞ : UpHom Ξ} {lkWkmTΞ : LkWkm T Ξ}
  (Ζ : Type) {lkTΖ : Lk T Ζ} {upΖ : Up Ζ} {wkmΖ : Wkm Ζ}
  {lkUpTΖ : LkUp T Ζ} {upHomΖ : UpHom Ζ} {lkWkmTΖ : LkWkm T Ζ} :
  ∀ (x : X),
     tr T X Ξ x (wkm₁ Ξ) = tr T X Ζ x (wkm₁ Ζ).
Proof. apply (tr_wkm_rel T X Ξ Ζ 1). Qed.

Lemma iTrIdm
  (T : Type) {vrT : Vr T} {wkT : Wk T} {wkVrT : WkVr T}
  (X : Type) {trTX : Tr T X}
  {trRelTX : TrRel T X} {trIdmUnit : TrIdmUnit T X} :
  TrIdm T X.
Proof.
  unfold TrIdm; intros.
  replace (tr T X Ξ x (idm Ξ)) with (tr T X unit x tt).
  apply tr_idm_unit.
  apply tr_rel_pw; constructor; intros.
  now rewrite !lk_idm.
Qed.

Lemma iTrComp
  (T : Type) {vrT : Vr T} {wkT : Wk T} {trTT : Tr T T}
  {trVrT : TrVr T} {trWkTT : TrWk T T}
  (X : Type) {trTX : Tr T X}
  {apPairTX : TrPair T X} {trRelTX : TrRel T X} :
  TrComp T X.
Proof.
  intro; intros.
  rewrite tr_pair.
  apply tr_rel_pw.
  constructor; intros.
  now rewrite (lk_comp_tr ξ₁ ξ₂).
Qed.

Lemma tr_wk_generic
  {T : Type} {vrT : Vr T} {wkT : Wk T} {trTT : Tr T T}
  {trVrT : TrVr T} {trWkmWkTT : TrWkmWk T T}
  {X : Type} {wkX : Wk X} {trTX : Tr T X}
  {trWkmWkTX : TrWkmWk T X} {apPairTX : TrPair T X} {trRelTX : TrRel T X}
  (Ρ : Type) {lkTΡ : Lk T Ρ} {upΡ : Up Ρ} {wkmΡ : Wkm Ρ}
  {upHomΡ : UpHom Ρ} {lkUpTΡ : LkUp T Ρ} {lkWkmΡ : LkWkm T Ρ}
  {Ξ : Type} {lkTΞ : Lk T Ξ} {upΞ : Up Ξ}
  {upHomΞ : UpHom Ξ} {lkUpTΞ : LkUp T Ξ}
  {lkUpPairΞΡ : LkUp T (Pair Ξ Ρ)}
  {lkUpPairΡΞ : LkUp T (Pair Ρ Ξ)} :
  ∀ (δ : Dom) (ξ : Ξ) (x : X),
    tr T X Ξ (wk X δ x) (up Ξ ξ δ) = wk X δ (tr T X Ξ x ξ).
Proof.
  intros. rewrite <- ?(tr_wkm_wk (T:=T) (Ξ:=Ρ)), ?tr_pair.
  apply tr_rel_pw; constructor; intros; cbn.
  now rewrite lk_wkm, tr_vr, tr_wkm_wk, lk_up_wk.
Qed.

Lemma iTrWk
  (T : Type) {vrT : Vr T} {wkT : Wk T} {trTT : Tr T T}
  {wkVrT : WkVr T} {trVrT : TrVr T} {trWkmWkTT : TrWkmWk T T}
  {apPairTT : TrPair T T} {trRelTT : TrRel T T}
  (X : Type) {wkX : Wk X} {trTX : Tr T X}
  {trWkmWkTX : TrWkmWk T X} {apPairTX : TrPair T X} {trRelTX : TrRel T X} :
  TrWk T X.
Proof.
  unfold TrWk; intros ? ? ? ? ?.
  assert (LkUp T (Pair Shifts Shifts)) by
    (eapply iLkUpPairRenaming; auto with typeclass_instances).
  assert (LkUp T (Pair Shifts Ξ)) by
    (eapply iLkUpPairRenaming; auto with typeclass_instances).
  assert (LkUp T (Pair Ξ Shifts)).
    (eapply iLkUpPairSubstitution; auto with typeclass_instances).
  apply (tr_wk_generic Shifts).
  apply (tr_wk_generic Shifts).
Qed.

Lemma wk₁_inj'
  {T : Type} `{Vr T, Wk T, Tr T T, !WkVr T, !WkHom T, !TrVr T}
  {X : Type} `{Wk X, Tr T X, !TrWkmWk T X, !TrIdm T X, !TrComp T X} :
  Inj (wk₁ X).
Proof.
  intros x x' eqx.
  do 2 rewrite <- (tr_wkm₁_wk₁ (T:=T) (Ξ := Reg T)) in eqx.
  assert (eqx' : tr T X (Reg T) (tr T X (Reg T) x (wkm₁ (Reg T))) (beta₁ T (Reg T) (vr T 0)) =
          tr T X (Reg T) (tr T X (Reg T) x' (wkm₁ (Reg T))) (beta₁ T (Reg T) (vr T 0)))
    by congruence.
  now do 2 rewrite <- tr_comp, wkm₁_beta₁, tr_idm in eqx'.
Qed.

Lemma iWkInj
  (T : Type) `{Vr T, Wk T, Tr T T, !WkVr T, !WkHom T, !TrVr T}
  (X : Type) `{Wk X, Tr T X, !WkHom X, !TrWkmWk T X, !TrIdm T X, !TrComp T X} :
  WkInj X.
Proof.
  intros δ; induction δ; intros x x' eqx.
  - now do 2 rewrite wk_zero in eqx.
  - do 2 rewrite wk_suc in eqx.
    now apply (wk₁_inj' (T:=T)), IHδ in eqx.
Qed.

(******************************************************************************)
