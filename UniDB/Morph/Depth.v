(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.
Require Import UniDB.Spec.Subst.

(******************************************************************************)

Fixpoint lk_depth (δ : Dom) (i : Ix) : option Ix :=
  match δ , i with
  | O   , i   => Some i
  | S δ , O   => None
  | S δ , S i => lk_depth δ i
  end.

(* Definition lk_depth' (δ : Dom) (i : Ix) : option Ix := *)
(*   if lt_dec i δ then None else Some (i - δ). *)

(* Lemma lk_depth_equivalent : *)
(*   ∀ (δ : Dom) (i : Ix), *)
(*     lk_depth δ i = lk_depth' δ i. *)
(* Proof. *)
(*   induction δ; cbn; intros. *)
(*   - destruct i; reflexivity. *)
(*   - destruct i; cbn. *)
(*     + reflexivity. *)
(*     + rewrite IHδ. *)
(*       unfold lk_depth'. *)
(*       case (lt_dec i δ), (lt_dec (S i) (S δ)); *)
(*         cbn; trivial; omega. *)
(* Qed. *)

Lemma lk_depth_none (δ : Dom) :
  ∀ i, lk_depth δ i = None -> i < δ.
Proof.
  induction δ; cbn; intros; try discriminate.
  - destruct i.
    + apply le_n_S, le_0_n.
    + now apply le_n_S, IHδ.
Qed.

Lemma lk_depth_some (δ : Dom) :
  ∀ i j, lk_depth δ i = Some j -> i = wk Ix δ j.
Proof.
  induction δ; cbn; intros; try discriminate.
  - congruence.
  - destruct i.
    + discriminate.
    + f_equal; now apply IHδ.
Qed.

Inductive Depth (Ξ : Type) : Type :=
  | depth (ξ : Ξ) (δ : Dom).

Instance iLkDepth
  {T : Type} {vrT : Vr T} {wkT : Wk T}
  {Ξ : Type} {lkTΞ : Lk T Ξ} :
  Lk T (Depth Ξ) :=
  fun ξ i =>
    let (ξ' , δ) := ξ in
    match lk_depth δ i with
    | Some i' => wk T δ (lk T Ξ ξ' i')
    | None    => vr T i
    end.

Instance iUpDepth {Ξ : Type} : Up (Depth Ξ) :=
  fun ξ δ =>
    let (ξ₀ , δ₀) := ξ in
    depth _ ξ₀ (δ + δ₀).
Instance iUpHom {Ξ : Type} : UpHom (Depth Ξ).
Proof. constructor; intro ξ; destruct ξ; reflexivity. Qed.

Instance iIdmDepth {Ξ : Type} {idmΞ : Idm Ξ} : Idm (Depth Ξ) :=
  depth Ξ (idm Ξ) 0.
Instance iLkIdmDepth
         {T : Type} {vrT : Vr T} {wkT : Wk T} {wkHomT : WkHom T}
         {Ξ : Type} {lkTΞ : Lk T Ξ} {idmΞ : Idm Ξ} {lkIdmΞ : LkIdm T Ξ} :
  LkIdm T (Depth Ξ) := {}.
Proof. intros; cbn; now rewrite wk_zero. Qed.

Instance iWkmDepth {Ξ : Type} {wkmΞ : Wkm Ξ} : Wkm (Depth Ξ) :=
  fun δ => depth Ξ (wkm Ξ δ) 0.
Instance iLkWkmDepth
  {T : Type} {vrT : Vr T} {wkT : Wk T} {wkVrT : WkVr T} {wkHomT : WkHom T}
  {Ξ : Type} {lkTΞ : Lk T Ξ} {wkmΞ : Wkm Ξ} {lkWkmΞ : LkWkm T Ξ} :
  LkWkm T (Depth Ξ) := {}.
Proof.
  intros; cbn.
  now rewrite wk_zero, lk_wkm.
Qed.

Instance iBetaDepth {T Ξ : Type} `{Beta T Ξ} : Beta T (Depth Ξ) :=
  fun t => depth Ξ (beta₁ T Ξ t) 0.
Instance iLkUpDepth
  {T : Type} {vrT : Vr T} {wkT : Wk T} {wkVrT : WkVr T} {wkHomT : WkHom T} 
  {Ξ : Type} {lkTΞ : Lk T Ξ} :
  LkUp T (Depth Ξ).
Proof.
  apply make_lkup_inst.
  - intros; now destruct ξ.
  - intros; destruct ξ; cbn.
    destruct (lk_depth δ i).
    + apply wk_suc.
    + symmetry; apply wk₁_vr.
Qed.

(******************************************************************************)
