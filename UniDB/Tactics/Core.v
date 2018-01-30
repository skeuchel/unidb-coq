(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.
Require Import UniDB.Scoping.Core.

(******************************************************************************)

Create HintDb ws.
Hint Constructors wsIx : ws.

(*
  Signatures:

    @vr T vrT i.
    @wk X wkX δ x.
    @wk₁ X wkX x
    @wk_vr T vrT wkT wkVrT δ i.
    @wk₁_vr T vrT wkT wkVrT i.
    @wk_zero X wkX wkHomX x
    @wk_suc X wkX wkHomX δ x
    @ap T X apTX Ξ lkTΞ upΞ x ξ
    @ap_vr T vrT apTT apVrT Ξ lkTΞ upΞ ξ i
 *)

Ltac unidb_simpl_context_core :=
  match goal with
    | H: False   |- _ => elim H
    | H: True    |- _ => clear H
    | H: _ ∧ _   |- _ => destruct H

    | H: ?x               = ?x               |- _ => clear H
    (* | H: ?x               ≠ ?x               |- _ => elim H; reflexivity *)
    | H: S _              = S _              |- _ => apply eq_add_S in H
    | H: @vr ?T ?vrT _    = @vr ?T ?vrT _    |- _ => eapply vr_inj in H; auto with typeclass_instances
    | H: @wk₁ ?X ?wkX _   = @wk₁ ?X ?wkX _   |- _ => eapply wk₁_inj in H; auto with typeclass_instances
    | H: @wk ?X ?wkX ?δ _ = @wk ?X ?wkX ?δ _ |- _ => eapply wk_inj in H; auto with typeclass_instances

    (* Ix simplification *)
    | H: context[@vr Ix iVrIx ?i]        |- _ => change (@vr Ix iVrIx i) with i in H
    | H: context[@wk₁ Ix iWkIx ?i]       |- _ => change (@wk₁ Ix iWkIx i) with (S i) in H
    | H: context[@wk Ix iWkIx (S ?δ) ?i] |- _ => change (@wk Ix iWkIx (S δ) i) with (S (@wk Ix iWkIx δ i)) in H

    (* wk₁ and up₁ folding *)
    | H: context[@wk ?X ?wkX 1 ?x] |- _ => change (@wk X wkX 1 x) with (@wk₁ X wkX x) in H
    | H: context[@up ?Ξ ?upΞ ?ξ 1] |- _ => change (@up Ξ upΞ ξ 1) with (@up₁ Ξ upΞ ξ) in H
  end.

Ltac unidb_simpl_conc_core :=
  match goal with
    (* | |- ?x               = ?x               => reflexivity *)
    | |- S _              = S _              => apply (f_equal S)
    | |- @vr ?T ?vrT _    = @vr ?T ?vrT _    => apply (f_equal (@vr T vrT))
    | |- @wk₁ ?X ?wkX _   = @wk₁ ?X ?wkX _   => apply (f_equal (@wk₁ X wkX))
    | |- @wk ?X ?wkX ?δ _ = @wk ?X ?wkX ?δ _ => apply (f_equal (@wk X wkX))

    (* Ix simplification *)
    | |- context[@vr Ix iVrIx ?i]        => change (@vr Ix iVrIx i) with i
    | |- context[@wk₁ Ix iWkIx ?i]       => change (@wk₁ Ix iWkIx i) with (S i)
    | |- context[@wk Ix iWkIx (S ?δ) ?i] => change (@wk Ix iWkIx (S δ) i) with (S (@wk Ix iWkIx δ i))

    (* Folding *)
    | |- context[@wk ?X ?wkX 1 ?x] => change (@wk X wkX 1 x) with (@wk₁ X wkX x)
    | |- context[@up ?Ξ ?upΞ ?ξ 1] => change (@up Ξ upΞ ξ 1) with (@up₁ Ξ upΞ ξ)

    (* WkVr simplficiation *)
    | |- context[@wk₁ ?T ?wkT (@vr ?T ?vrT ?i)] =>
      first
        [ change (@wk₁ T _ (@vr T _ i)) with (@vr T _ (S i))
        | rewrite (@wk₁_vr T vrT wkT _ i)
        ]
    | |- context[@wk ?T ?wkT ?δ (@vr ?T ?vrT ?i)] =>
      first
        [ change (@wk T _ δ (@vr T _ i)) with (@vr T _ (@wk Ix _ δ i))
        | rewrite (@wk_vr T vrT wkT _ δ i)
        ]

    (* WkHom simplification *)
    | |- context[@wk ?X ?wkX 0 ?x]      => rewrite (@wk_zero X wkX _ x)
    | |- context[@wk ?X ?wkX (S ?δ) ?x] => rewrite (@wk_suc X wkX _ δ x)

    | H : LkRen ?T ?Ξ |- context[@lk ?T ?Ξ _ ?ξ ?i] =>
      rewrite (@lk_ren T _ Ξ _ _ H ξ i)
    | H: LkUp ?T ?Ξ |- context[@lk ?T ?Ξ _ (@up₁ ?Ξ _ ?ξ) 0] =>
      rewrite (@lk_up₁_zero T _ _ Ξ _ _ H ξ)
    | H : LkUp ?T ?Ξ |- context[@lk ?T ?Ξ _ (@up₁ ?Ξ _ ?ξ) (S ?i)] =>
      rewrite (@lk_up₁_suc T _ _ Ξ _ _ H ξ i)
    | H : LkUp ?T ?Ξ |- context[@lk ?T ?Ξ _ (@up ?Ξ _ ?ξ ?δ) (@wk Ix _ ?δ ?i)] =>
      rewrite (@lk_up_wk T _ _ Ξ _ _ H δ ξ i)
    | |- context[@lk ?Ix ?Ξ _ (@up₁ ?Ξ _ ?ξ) 0] =>
      rewrite (@lk_up₁_zero Ix _ _ Ξ _ _ _ ξ)
    | |- context[@lk ?Ix ?Ξ _ (@up₁ ?Ξ _ ?ξ) (S ?i)] =>
      rewrite (@lk_up₁_suc Ix _ _ Ξ _ _ _ ξ i)
  end.

Ltac unidb_rewrite_core :=
  rewrite ?dunion_assoc, ?up_dunion.
(* , ?comp_up, ?comp_ups, *)
(*     (* ?up_liftSub, ?ups_liftSub, *) *)
(*     (* ?ap_liftSub, ?liftSub_wkm, ?liftSub_wkms, ?ap_lift, *) *)
(*     <- ?ap_comp, *)
(*     ?apply_wkm_comm,     ?apply_wkm_beta1_cancel,     ?apply_beta1_comm, *)
(*     ?apply_wkm_up_comm,  ?apply_wkm_beta1_up_cancel,  ?apply_beta1_up_comm, *)
(*     ?apply_wkm_up2_comm, ?apply_wkm_beta1_up2_cancel, ?apply_beta1_up2_comm, *)
(*     ?apply_wkm_ups_comm, ?apply_wkm_beta1_ups_cancel, ?apply_beta1_ups_comm. *)

(******************************************************************************)

Lemma wsiS (γ: Dom) (i: Ix) : S γ ∋ S i → γ ∋ i.
Proof. inversion 1; auto. Qed.

Hint Constructors wsIx : ws.
Hint Resolve wsiS : wsi.
Hint Resolve ws_snoc : ws.
Hint Resolve wsi_snoc_sub : wsi.
Hint Resolve wsi_snoc_tm : wsi.

Ltac unidb_simpl_scoping :=
  match goal with
    | H: 0 ∋ _      |- _ => inversion H
    | H: S _    ∋ O |- _ => clear H
    | H: S _ ∋ S _  |- _ => apply wsiS in H
    | H: S _ ∋ wk _ |- _ => apply wsiS in H
    | H: @ws ?X ?wsX (S ?δ) (@wk ?X ?vrX ?wkX ?x) |- _ =>
      apply (@wsi_wk X wsX vrX wkX _ δ x) in H
    | H: ∀ i, S _ ∋ i → _ |- _ =>
      let HS := fresh in
      let HO := fresh in
      pose proof (fun i wi => H (S i) (wsS _ i wi)) as HS;
      pose proof (H 0 (ws0 _)) as HO;
      clear H; cbn in HS; cbn in HO
    | H: ⟨ _ ⊢ vr _ ⟩ |- _ => eapply wsi_vr in H

    | wi : S _ ∋ ?i |- context[match ?i with _ => _ end] => destruct i
    (* | wi : S _ ∋ ?i |- context[@snoc ?T ?Ξ _ (_ · _) ?i] => destruct i *)
    | |- S _ ∋ 0              => apply ws0
    | |- S _ ∋ S _            => apply wsS
    | |- S _ ∋ wk _           => apply wsS
    (* | |- WsSub _ _ (@snoc ?T ?Ξ _ _ _)    => eapply ws_snoc *)

    | |- ⟨ S _ ⊢ wk₁ _ ⟩ => eapply ws_wk₁
    | |- ⟨ _   ⊢ vr _  ⟩ => eapply ws_vr
    (* | [ |- ⟨ _ ⊢ _[_] ⟩ ] => eapply wsAp *)
  end.

(******************************************************************************)
