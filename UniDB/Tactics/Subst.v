(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.
Require Import UniDB.Spec.Subst.
Require Import UniDB.Scoping.Core.
Require Import UniDB.Lemmas.Core.

(******************************************************************************)

(*
  Signatures:

    @tr T X trTX Ξ lkTΞ upΞ x ξ
    @tr_vr T vrT trTT trVrT Ξ lkTΞ upΞ ξ i
 *)

Ltac unidb_simpl_context_subst :=
  match goal with
    | _ => fail
  end.

Ltac unidb_simpl_conc_subst :=
  match goal with
    (* TrVr simplification *)
    | |- context[@tr ?T ?T ?trTT ?Ξ ?lkTΞ ?upΞ (@vr ?T ?vrT ?i) ?ξ] =>
      first
        [ change (@tr T T trTT Ξ lkTΞ upΞ (@vr T vrT i) ξ) with (@lk T Ξ lkTΞ ξ i)
        | rewrite (@tr_vr T vrT trTT _ Ξ lkTΞ upΞ ξ i)
        ]
  end.

(******************************************************************************)

Ltac unidb_rewrite_subst :=
  rewrite ?tr_up_wkm_comm, ?tr_up₁_wkm_comm, ?tr_wkm_comm, ?tr_up_wkm₁_comm,
    ?tr_up₁_wkm₁_comm, ?tr_wkm₁_comm, ?tr_up_wkm₁_beta₁, ?tr_up₁_wkm₁_beta₁,
    ?tr_wkm₁_beta₁, ?tr_up_beta₁_comm, ?tr_up₁_beta₁_comm, ?tr_beta₁_comm.

(******************************************************************************)
