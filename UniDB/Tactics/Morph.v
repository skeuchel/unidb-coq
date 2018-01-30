(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.
Require Import UniDB.Spec.Subst.
Require Import UniDB.Morph.Reg.
Require Import UniDB.Morph.Weaken.

(******************************************************************************)

(*
  @reg_up₁ : ∀ T : Type, Vr T → Wk T → Reg T → Reg T
  up₁ :      ∀ Ξ : Type, Up Ξ → Ξ → Ξ
 *)

Ltac unidb_fold_morph :=
  match goal with
  | H: context[@reg_up₁ ?T ?vrT ?wkT ?ξ] |- _ =>
    change (@reg_up₁ T vrT wkT ξ) with (@up₁ (Reg T) (iLkUpReg (T:=T)) ξ) in H
  | |- context[@reg_up₁ ?T ?vrT ?wkT ?ξ] =>
    change (@reg_up₁ T vrT wkT ξ) with (@up₁ (Reg T) (iUpReg (T:=T)) ξ)
  end.

(******************************************************************************)

(* repeat match goal with *)
(* | H: context[@reg_up₁ ?T ?vrT ?wkT ?ξ] |- _ => idtac *)
(*   (* change (@reg_up₁ T vrT wkT ξ) with (@up (Reg T) (iLkUpReg (T:=T)) ξ) in H *) *)
(* | |- context[@reg_up₁ ?T ?vrT ?wkT ?ξ] => *)
(*   change (@reg_up₁ T vrT wkT ξ) with (@up₁ (Reg T) (iUpReg (T:=T)) ξ) *)
(* end. *)
