(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.
Require Import UniDB.Spec.Subst.

(******************************************************************************)

Instance iUpUnit : Up unit := fun _ _ => tt.
Instance iIdmUnit : Idm unit := tt.
Instance iCompUnit : Comp unit := fun _ _ => tt.

Instance iUpHomUnit : UpHom unit.
Proof. constructor; intro ξ; destruct ξ; reflexivity. Qed.
Instance iUpIdmUnit : UpIdm unit.
Proof. constructor; reflexivity. Qed.

Instance iLkUnit {T : Type} `{Vr T} : Lk T unit := fun _ i => vr T i.
Instance iLkIdmUnit {T : Type} `{Vr T} : LkIdm T unit.
Proof. constructor. Qed.
Instance iLkRenUnit {T : Type} `{Vr T} : LkRen T unit.
Proof. constructor. Qed.
Instance iLkUpUnit {T : Type} `{WkVr T} : LkUp T unit.
Proof. now apply make_lkup_inst_ren. Qed.

Class TrIdmUnit (T : Type) {vrT : Vr T} (X : Type) {trTX : Tr T X} :=
  tr_idm_unit : ∀ (x : X), tr T X unit x tt = x.

(******************************************************************************)
