(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.
Require Import UniDB.Spec.Subst.

(******************************************************************************)

Record Sim (T : Type) : Type :=
  { lk_sim : ∀ (i : Ix), T }.
Arguments lk_sim {_} _ i.

Section Instances.
  Context {T : Type}.

  Global Instance iLkSim : Lk T (Sim T) := lk_sim.
  Global Instance iWkSim `{Wk T} : Wk (Sim T) :=
    fun δ ξ => {| lk_sim := fun i => wk T δ (lk_sim ξ i) |}.
  Global Instance iSnocSim : Snoc T (Sim T) :=
    fun ξ t => {| lk_sim := fun i =>
                              match i with
                              | 0 => t
                              | S i0 => lk_sim ξ i0
                              end
               |}.

  Definition sim_up₁ `{Vr T, Wk T} (ξ : Sim T) :=
    snoc T (Sim T) (wk₁ (Sim T) ξ) (vr T 0).
  Fixpoint sim_up `{Vr T, Wk T} (ξ : Sim T) (δ: Dom) :=
    match δ with
    | O => ξ
    | S δ => sim_up₁ (sim_up ξ δ)
    end.

  Global Instance iUpSim `{Vr T, Wk T} : Up (Sim T) := sim_up.
  Global Instance iIdmSim `{Vr T} : Idm (Sim T) := {| lk_sim := vr T |}.
  Global Instance iWkmSim `{Vr T} : Wkm (Sim T) := fun δ => {| lk_sim := fun i => vr T (wk Ix δ i) |}.
  Global Instance iBetaSim `{Vr T} : Beta T (Sim T) := fun t => snoc T (Sim T) (idm (Sim T)) t.
  Global Instance iCompSim `{Vr T, Wk T, Tr T T} : Comp (Sim T) :=
    fun ξ ζ => {| lk_sim := fun i => tr T T (Sim T) (lk T (Sim T) ξ i) ζ |}.
  Global Instance iUpHomSim `{Vr T, Wk T, !WkHom T} : UpHom (Sim T).
  Proof. constructor; reflexivity. Qed.
  Global Instance iLkUpSim `{Vr T, Wk T, !WkHom T} : LkUp T (Sim T).
  Proof. apply make_lkup_inst; reflexivity. Qed.

  Global Instance iLkWkmSim `{Vr T} : LkWkm T (Sim T) := {}.
  Proof. reflexivity. Qed.
  Global Instance iLkIdmSim `{Vr T} : LkIdm T (Sim T) := {}.
  Proof. reflexivity. Qed.
  Global Instance iLkBetaSim `{Vr T} : LkBeta T (Sim T).
  Proof. constructor; reflexivity. Qed.
  Global Instance iLkSnocSim `{Vr T} : LkSnoc T (Sim T).
  Proof. constructor; reflexivity. Qed.
  Global Instance iLkCompTrSim `{Vr T, Wk T, Tr T T} : LkCompTr T (Sim T) := {}.
  Proof. reflexivity. Qed.

End Instances.

(* module SimIxInstances (T : STX) where *)

(*   instance *)
(*     iLkSimIx : {vrT : Vr T} → Lk T (Sim Ix) *)
(*     lk {iLkSimIx} ξ i = vr T (lk Ix _ ξ i) *)

(*     iLkUpSimIx : {vrT : Vr T} {wkT : Wk T} *)
(*       {wkVrT : WkVr T} → LkUp T (Sim Ix) *)
(*     lk-↑₁-zero {iLkUpSimIx} ξ   = refl *)
(*     lk-↑₁-suc  {iLkUpSimIx} ξ i = sym (wk₁-vr T (lk Ix (Sim Ix) ξ i)) *)

(*     iLkWkmSimIx : {vrT : Vr T} → LkWkm T (Sim Ix) *)
(*     lk-wkm {iLkWkmSimIx} δ i = refl *)

(*     iLkIdmSimIx : {vrT : Vr T} → LkIdm T (Sim Ix) *)
(*     lk-idm {iLkIdmSimIx} i = refl *)

(*     iLkCompSimIx : {vrT : Vr T} {apTT : Tr T T} *)
(*       {apVrT : TrVr T} → LkCompTr T (Sim Ix) *)
(*     lk-⊙-tr {iLkCompSimIx} ξ₁ ξ₂ i = *)
(*       sym (ap-vr T (Sim Ix) ξ₂ (lk Ix (Sim Ix) ξ₁ i)) *)


