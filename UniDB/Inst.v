(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.
Require Import UniDB.Spec.Subst.
Require Import UniDB.Morph.Pair.
Require Import UniDB.Morph.Reg.
Require Import UniDB.Morph.Shift.
Require Import UniDB.Morph.Shifts.
Require Import UniDB.Morph.Unit.
Require Import UniDB.Scoping.Core.
Require Import UniDB.Scoping.Subst.
Require Import UniDB.Inst.Subst.

(******************************************************************************)

Section SortWithVariables.

  Class UniDBVar (T : Type) : Type :=
    { VrT :> Vr T;
      TrT :> Tr T T
    }.

  Global Instance iWkUniDBVar {T : Type} `{UniDBVar T} : Wk T :=
    fun δ t => tr T T Shift t (wkm Shift δ).

  Class UniDBVarLemmas (T : Type) `{UniDBVar T} :=
    { VrInjT :> VrInj T;
      WkVrT :> WkVr T;
      WkHomT :> WkHom T;
      WkInjT :> WkInj T;
      TrVrT :> TrVr T;
      (***************************)
      TrRelT :> TrRel T T;
      TrIdmUnitT :> TrIdmUnit T T;
      TrPairT :> TrPair T T;
      (***************************)
      TrIdmT :> TrIdm T T;
      TrCompT :> TrComp T T;
      TrWkmWkT :> TrWkmWk T T;
      TrWkT :> TrWk T T
    }.

  Class UniDBVarWs (T : Type) `{Vr T, Tr T T}: Type :=
    { WsT :> Ws T;
      WsVrT :> WsVr T;
      WsTrNatT :> WsTrNat T T
    }.

  Class UniDBVarWsLemmas (T : Type)
    `{UniDBVar T, !UniDBVarLemmas T, !UniDBVarWs T} : Type :=
    { WsWkT :> WsWk T;
      WsTrT :> WsTr T T
    }.

  Lemma iWkVrUniDBVar (T : Type) `{UniDBVar T, !TrVr T} : WkVr T.
  Proof.
    intros δ i.
    change (wk T δ (vr T i)) with (tr T T Shift (vr T i) (wkm Shift δ)).
    now rewrite tr_vr, (lk_ren T), lk_wkm.
  Qed.

  Lemma iWkHomUniDBVar (T : Type)
    `{UniDBVar T, !WkVr T, !TrVr T, !TrIdm T T, !TrWkmWk T T, !TrComp T T} :
    WkHom T.
  Proof.
    constructor; intros;
      rewrite <- ?(tr_wkm_wk (Ξ := Shifts));
      rewrite <- ?(tr_wkm₁_wk₁ (Ξ := Shifts)).
    - change (wkm Shifts 0) with (idm Shifts).
      now rewrite tr_idm.
    - now rewrite <- tr_comp.
  Qed.

  Lemma iTrWkmWkUniDBVar (T : Type) `{UniDBVar T, !WkVr T, !TrRel T T} : TrWkmWk T T.
  Proof.
    unfold TrWkmWk; intros.
    change (wk T δ x) with (tr T T Shift x (wkm Shift δ)).
    apply (tr_wkm_rel T T Ξ Shift).
  Qed.

End SortWithVariables.

Section SortWithoutVariables.

  Class UniDBTerm (T : Type) `{Vr T} (X : Type) : Type :=
    { TrTX :> Tr T X
    }.

  Global Instance iWkUniDBTerm {T X : Type} `{UniDBTerm T X} : Wk X :=
    fun δ x => tr T X Shift x (wkm Shift δ).

  Class UniDBTermLemmas
    (T : Type) `{Wk T, Tr T T} (X : Type) `{UniDBTerm T X} : Type :=
    { WkHomX :> WkHom X;
      WkInjX :> WkInj X;
      TrIdmTX :> TrIdm T X;
      TrRelTX :> TrRel T X;
      TrPairTX :> TrPair T X;
      TrCompTX :> TrComp T X;
      TrWkmWkTX :> TrWkmWk T X;
      TrWkTX :> TrWk T X
    }.

  Lemma iWkHomUniDBTerm
    (T : Type) `{Vr T, Wk T, !WkVr T, !Tr T T, !TrVr T}
    (X : Type) `{!UniDBTerm T X, !TrIdm T X, !TrWkmWk T X, !TrComp T X} :
    WkHom X.
  Proof.
    constructor; intros;
      rewrite <- ?(tr_wkm_wk (Ξ := Shifts));
      rewrite <- ?(tr_wkm₁_wk₁ (Ξ := Shifts)).
    - change (wkm Shifts 0) with (idm Shifts).
      now rewrite tr_idm.
    - now rewrite <- tr_comp.
  Qed.

  Lemma iTrWkmWkUniDBTerm
    (T : Type) `{Vr T, Wk T, !WkVr T}
    (X : Type) `{!UniDBTerm T X, !TrRel T X} : TrWkmWk T X.
  Proof.
    unfold TrWkmWk; intros.
    change (wk X δ x) with (tr T X Shift x (wkm Shift δ)).
    apply (tr_wkm_rel T X Ξ Shift).
  Qed.

End SortWithoutVariables.

(******************************************************************************)

Ltac unidb_derive_instance_vrinj :=
  now inversion 1.

Ltac unidb_derive_instance_apidmunit T X :=
  let x := fresh in
    intro x;
    induction x; cbn;
    f_equal; auto;
    now apply tr_idm_unit.

(* Ltac unidb_derive_instance_apidm T X := *)
(*   apply (iTrIdm T X); *)
(*   let x := fresh in *)
(*     intro x; *)
(*     induction x; cbn; *)
(*     now f_equal. *)

Ltac unidb_derive_instance_trrel_auto T Ξ Ζ :=
  auto using
    (extended_up (T:=T) (Ξ:=Ξ) (Ζ:=Ζ)),
    (extended_up₁ (T:=T) (Ξ:=Ξ) (Ζ:=Ζ)).

Ltac unidb_derive_trrel T Ξ Ζ x :=
  induction x; intros; cbn in *;
  first
    [ (* Variable case *)
      now apply lk_ext
    | (* Constructor and solve using IHs. *)
      f_equal; unidb_derive_instance_trrel_auto T Ξ Ζ;
      (* Other group. *)
      now apply tr_rel_ext; unidb_derive_instance_trrel_auto T Ξ Ζ
    ].

Ltac unidb_derive_instance_trrel T :=
  let Ξ := fresh in
  let Ζ := fresh in
  let x := fresh in
  intros Ξ ? ? ? Ζ ? ? ? x;
  unidb_derive_trrel T Ξ Ζ x.

Ltac unidb_derive_trpair x :=
  induction x; intros; cbn in *;
  (* In case of a variable, both sides are definitionally equal and reflexivity
     solves this goal. It also takes care of trivial goals. *)
  try reflexivity;
  (* In the remaining cases, there's a constructor at the head after
  simplification. We try to solve automatically using the IHs. *)
  f_equal; auto;
  (* Everything remaining subgoal should be from a sort of a different mutually
     recursive group for which we already proved TrPair. Use that instance. *)
  now apply tr_pair.

Ltac unidb_derive_instance_trpair :=
  let x := fresh in
  intros ? ? ? ? ? ? ? ? x;
    unidb_derive_trpair x.

Ltac unidb_derive_instance_wsvr :=
  constructor; [ now constructor | now inversion 1 ].

Ltac unidb_derive_instance' :=
  auto with typeclass_instances;
  match goal with
    | |- VrInj ?T =>
      unidb_derive_instance_vrinj
    | |- TrIdmUnit ?T ?X =>
      unidb_derive_instance_apidmunit T X
    | |- TrRel ?T ?X =>
      unidb_derive_instance_trrel T
    | |- TrPair ?T ?X =>
      unidb_derive_instance_trpair
    | |- WsVr ?T =>
      unidb_derive_instance_wsvr
  end.

Ltac unidb_derive_instance_varlemmas T :=
  assert (VrInj T) by unidb_derive_instance';
  assert (TrVr T) by unidb_derive_instance';
  assert (WkVr T) by apply (iWkVrUniDBVar T);
  assert (TrPair T T) by unidb_derive_instance';
  assert (TrRel T T) by unidb_derive_instance';
  assert (TrIdmUnit T T) by unidb_derive_instance';
  assert (TrIdm T T) by apply (iTrIdm T T);
  assert (TrWkmWk T T) by apply (iTrWkmWkUniDBVar T);
  assert (TrWk T T) by apply (iTrWk T T);
  assert (TrComp T T) by apply (iTrComp T T);
  assert (WkHom T) by apply (iWkHomUniDBVar T);
  assert (WkInj T) by apply (iWkInj T T);
  now constructor.

Ltac unidb_derive_instance_termlemmas T X :=
  assert (TrPair T X) by unidb_derive_instance';
  assert (TrRel T X) by unidb_derive_instance';
  assert (TrIdmUnit T X) by unidb_derive_instance';
  assert (TrIdm T X) by apply (iTrIdm T X);
  assert (TrWkmWk T X) by apply (iTrWkmWkUniDBTerm T X);
  assert (TrWk T X) by apply (iTrWk T X);
  assert (TrComp T X) by apply (iTrComp T X);
  assert (WkHom X) by apply (iWkHomUniDBTerm T X);
  assert (WkInj X) by apply (iWkInj T X);
  now constructor.

Ltac unidb_derive_instance :=
  try unidb_derive_instance';
  match goal with
    | |- UniDBVarLemmas ?T =>
      unidb_derive_instance_varlemmas T
    | |- UniDBTermLemmas ?T ?X =>
      unidb_derive_instance_termlemmas T X
  end.

Lemma iSubMorphUpUnitShift
  {T : Type} `{Vr T, Ws T, !WsVr T} :
  SubMorphUp T unit Shift.
Proof.
  constructor.
  - apply (isubmorph_up₁_ren T unit Shift).
  - apply (isubmorph_up_ren T unit Shift).
Qed.

Lemma iSubMorphUpShiftUnit
  {T : Type} `{Vr T, Ws T, !WsVr T} :
  SubMorphUp T Shift unit.
Proof.
  constructor.
  - apply (isubmorph_up₁_ren T Shift unit).
  - apply (isubmorph_up_ren T Shift unit).
Qed.

Lemma submorph_idm_wkm
  (T : Type) `{Vr T, Ws T, !WsVr T}
  (Ξ : Type) `{Lk T Ξ, Idm Ξ, !LkIdm T Ξ}
  (Ζ : Type) `{Lk T Ζ, Wkm Ζ, !LkWkm T Ζ}
  {γ : Dom} (δ : Dom) :
  SubMorph T Ξ Ζ γ γ (γ ∪ δ) (idm Ξ) (wkm Ζ δ).
Proof.
  intros i.
  rewrite lk_idm, lk_wkm; intro.
  now apply ws_vr, ws_wk, (wsi_vr (T:=T)).
Qed.

Lemma submorph_wkm_idm
  (T : Type) `{Vr T, Ws T, !WsVr T}
  (Ξ : Type) `{Lk T Ξ, Wkm Ξ, !LkWkm T Ξ}
  (Ζ : Type) `{Lk T Ζ, Idm Ζ, !LkIdm T Ζ}
  {γ : Dom} (δ : Dom) :
  SubMorph T Ξ Ζ γ (γ ∪ δ) γ (wkm Ξ δ) (idm Ζ).
Proof.
  intros i.
  rewrite lk_idm, lk_wkm; intro.
  now apply wsi_vr, wsi_wk, (ws_vr (T:=T)) in H5.
Qed.

Section WsWk.

  Existing Instance iSubMorphUpUnitShift.
  Existing Instance iSubMorphUpShiftUnit.

  Lemma iWsWk (T : Type)
    `{UniDBVar T, !UniDBVarLemmas T, Ws T, !WsVr T, !WsTrNat T T} :
    WsWk T.
  Proof.
    constructor.
    - intros γ t wt.
      pose proof wt; rewrite <- (tr_idm (Ξ := unit)) in wt.
      refine (ws_tr_nat unit Shift t γ γ (S γ) (idm unit) (wkm₁ Shift) _ wt).
      refine (submorph_idm_wkm T unit Shift 1).
    - intros γ δ t wt.
      pose proof wt; rewrite <- (tr_idm (Ξ := unit)) in wt.
      refine (ws_tr_nat unit Shift t γ γ (γ ∪ δ) tt (wkm Shift δ) _ wt).
      apply (submorph_idm_wkm T unit Shift δ).
    - intros γ t wt.
      rewrite <- (tr_idm (Ξ := unit)).
      refine (ws_tr_nat Shift unit t γ (S γ) γ (wkm₁ Shift) tt _ wt).
      apply (submorph_wkm_idm T Shift unit 1).
    - intros γ δ t wt.
      rewrite <- (tr_idm (Ξ := unit)).
      refine (ws_tr_nat Shift unit t γ (γ ∪ δ) γ (wkm Shift δ) tt _ wt).
      apply (submorph_wkm_idm T Shift unit δ).
  Qed.

End WsWk.

Lemma iWsTrT (T : Type)
  `{UniDBVar T, !UniDBVarLemmas T, Ws T, !WsVr T, !WsWk T, !WsTrNat T T} :
  WsTr T T.
Proof.
  repeat intro.
  rewrite <- (tr_idm (Ξ := unit)) in wx.
  pose (idmξ := submorph_idm_initial T unit Ξ wξ).
  refine (ws_tr_nat unit Ξ x γ₁ γ₁ γ₂ (idm unit) ξ idmξ wx);
    auto with typeclass_instances.
Qed.

(******************************************************************************)

Global Arguments VrT T {_} i /.
Global Arguments TrT T {_} Ξ {_ _} x ξ /.

(******************************************************************************)
