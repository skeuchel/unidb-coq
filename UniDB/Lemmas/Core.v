(* Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Unique Solutions. *)

Require Import UniDB.Spec.Core.
Require Import UniDB.Spec.Subst.
Require Import UniDB.Morph.Pair.
Require Import UniDB.Morph.Reg.
Require Import UniDB.Morph.Shifts.
Require Import UniDB.Morph.Unit.

(******************************************************************************)

Section Pointful.

  Section TrWkmComm.

    Context
      {T: Type} `{Vr T, Wk T, Tr T T, !WkVr T, !TrVr T, !TrWk T T, !TrWkmWk T T}
      {X: Type} `{Wk X, Tr T X, !TrPair T X, !TrRel T X}
      {Ξ: Type} `{Lk T Ξ, Up Ξ, !UpHom Ξ, !LkUp T Ξ}
      {Ζ: Type} `{Lk T Ζ, Up Ζ, Wkm Ζ, !UpHom Ζ, !LkUp T Ζ, !LkWkm T Ζ}.

    Lemma tr_up_wkm_comm (δ η:Dom) (x:X) (ξ: Ξ) :
      tr T X Ζ (tr T X Ξ x (up Ξ ξ δ)) (up Ζ (wkm Ζ η) δ) =
      tr T X Ξ (tr T X Ζ x (up Ζ (wkm Ζ η) δ)) (up Ξ (up Ξ ξ η) δ).
    Proof.
      rewrite !tr_pair; apply tr_rel_pw.
      change (up Ξ ξ δ ⊗ up Ζ (wkm Ζ η) δ) with (up (Pair Ξ Ζ) (ξ ⊗ wkm Ζ η) δ).
      change (up Ζ (wkm Ζ η) δ ⊗ up Ξ (up Ξ ξ η) δ) with (up (Pair Ζ Ξ) (wkm Ζ η ⊗ up Ξ ξ η) δ).
      apply (pointwise_up (ξ ⊗ wkm Ζ η) (wkm Ζ η ⊗ up Ξ ξ η) δ).
      constructor; intros; cbn.
      now rewrite tr_wkm_wk, lk_wkm, tr_vr, lk_up_wk.
    Qed.

    Lemma tr_up₁_wkm_comm (η:Dom) (x:X) (ξ: Ξ) :
      tr T X Ζ (tr T X Ξ x (up₁ Ξ ξ)) (up₁ Ζ (wkm Ζ η)) =
      tr T X Ξ (tr T X Ζ x (up₁ Ζ (wkm Ζ η))) (up₁ Ξ (up Ξ ξ η)).
    Proof. exact (tr_up_wkm_comm 1 η x ξ). Qed.

    Lemma tr_wkm_comm (η:Dom) (x:X) (ξ: Ξ) :
      tr T X Ζ (tr T X Ξ x ξ) (wkm Ζ η) =
      tr T X Ξ (tr T X Ζ x (wkm Ζ η)) (up Ξ ξ η).
    Proof. generalize (tr_up_wkm_comm 0 η x ξ). now rewrite !up_zero. Qed.

    Lemma tr_up_wkm₁_comm (δ:Dom) (x:X) (ξ:Ξ) :
      tr T X Ζ (tr T X Ξ x (up Ξ ξ δ)) (up Ζ (wkm₁ Ζ) δ) =
      tr T X Ξ (tr T X Ζ x (up Ζ (wkm₁ Ζ) δ)) (up Ξ (up₁ Ξ ξ) δ).
    Proof. exact (tr_up_wkm_comm δ 1 x ξ). Qed.

    Lemma tr_up₁_wkm₁_comm (x:X) (ξ: Ξ) :
      tr T X Ζ (tr T X Ξ x (up₁ Ξ ξ)) (up₁ Ζ (wkm₁ Ζ)) =
      tr T X Ξ (tr T X Ζ x (up₁ Ζ (wkm₁ Ζ))) (up₁ Ξ (up₁ Ξ ξ)).
    Proof. exact (tr_up₁_wkm_comm 1 x ξ). Qed.

    Lemma tr_wkm₁_comm (x:X) (ξ: Ξ) :
      tr T X Ζ (tr T X Ξ x ξ) (wkm₁ Ζ) =
      tr T X Ξ (tr T X Ζ x (wkm₁ Ζ)) (up₁ Ξ ξ).
    Proof. exact (tr_wkm_comm 1 x ξ). Qed.

  End TrWkmComm.

  Section TrWkmBeta.

    Context
      {T: Type} `{Vr T, Wk T, Tr T T, !WkVr T, !TrVr T, !TrWk T T}
      {X: Type} `{Tr T X, !TrPair T X, !TrRel T X, !TrIdm T X}
      {Ξ: Type} `{Lk T Ξ, Up Ξ, Wkm Ξ, !UpHom Ξ, !LkUp T Ξ, !LkWkm T Ξ}
      {Ζ: Type} `{Lk T Ζ, Up Ζ, Beta T Ζ, !UpHom Ζ, !LkUp T Ζ, !LkBeta T Ζ}.

    Lemma tr_up_wkm₁_beta₁ (δ : Dom) (t: T) (x: X) :
      tr T X Ζ (tr T X Ξ x (up Ξ (wkm₁ Ξ) δ)) (up Ζ (beta₁ T Ζ t) δ) = x.
    Proof.
      rewrite tr_pair, <- (tr_idm (Ξ := unit)), <- (up_idm δ).
      apply tr_rel_pw.
      change (up Ξ (wkm₁ Ξ) δ ⊗ up Ζ (beta₁ T Ζ t) δ)
        with (up (Pair Ξ Ζ) (wkm₁ Ξ ⊗ beta₁ T Ζ t) δ).
      apply (pointwise_up (wkm₁ Ξ ⊗ beta₁ T Ζ t) tt δ).
      constructor; intros; cbn.
      now rewrite lk_wkm₁, tr_vr, lk_beta₁_suc.
    Qed.

    Lemma tr_up₁_wkm₁_beta₁ (t: T) (x: X) :
      tr T X Ζ (tr T X Ξ x (up₁ Ξ (wkm₁ Ξ))) (up₁ Ζ (beta₁ T Ζ t)) = x.
    Proof. exact (tr_up_wkm₁_beta₁ 1 t x). Qed.

    Lemma tr_wkm₁_beta₁ (t: T) (x: X) :
      tr T X Ζ (tr T X Ξ x (wkm₁ Ξ)) (beta₁ T Ζ t) = x.
    Proof. generalize (tr_up_wkm₁_beta₁ 0 t x). now rewrite !up_zero. Qed.

  End TrWkmBeta.

  Section TrBetaComm.

    Context
      {T: Type} `{Vr T, Wk T, Tr T T, !WkVr T, !TrVr T, !TrWk T T,
                  !TrWkmWk T T, !TrPair T T, !TrRel T T, !TrIdm T T}
      {X: Type} `{Tr T X, !TrPair T X, !TrRel T X}
      {Ξ: Type} `{Lk T Ξ, Up Ξ, Beta T Ξ, !UpHom Ξ, !LkUp T Ξ, !LkBeta T Ξ}
      {Ζ: Type} `{Lk T Ζ, Up Ζ, !UpHom Ζ, !LkUp T Ζ}.

    Lemma tr_up_beta₁_comm (δ:Dom) (t:T) (x:X) (ζ:Ζ) :
      tr T X Ζ (tr T X Ξ x (up Ξ (beta₁ T Ξ t) δ)) (up Ζ ζ δ) =
      tr T X Ξ (tr T X Ζ x (up Ζ (up₁ Ζ ζ) δ)) (up Ξ (beta₁ T Ξ (tr T T Ζ t ζ)) δ).
    Proof.
      rewrite !tr_pair; apply tr_rel_pw.
      change (up Ξ (beta₁ T Ξ t) δ ⊗ up Ζ ζ δ)
        with (up (Pair Ξ Ζ) (beta₁ T Ξ t ⊗ ζ) δ).
      change (up Ζ (up₁ Ζ ζ) δ ⊗ up Ξ (beta₁ T Ξ (tr T T Ζ t ζ)) δ)
        with (up (Pair Ζ Ξ) (up₁ Ζ ζ ⊗ beta₁ T Ξ (tr T T Ζ t ζ)) δ).
      apply (pointwise_up (beta₁ T Ξ t ⊗ ζ) (up₁ Ζ ζ ⊗ beta₁ T Ξ (tr T T Ζ t ζ)) δ).
      constructor; intros; cbn.
      destruct i; cbn.
      - now rewrite lk_up₁_zero, tr_vr, !lk_beta₁_zero.
      - now rewrite lk_up₁_suc, lk_beta₁_suc, tr_vr,
          <- (tr_wkm₁_wk₁ (Ξ := Shifts)), tr_wkm₁_beta₁.
    Qed.

    Lemma tr_up₁_beta₁_comm (t:T) (x:X) (ζ:Ζ) :
      tr T X Ζ (tr T X Ξ x (up₁ Ξ (beta₁ T Ξ t))) (up₁ Ζ ζ) =
      tr T X Ξ (tr T X Ζ x (up₁ Ζ (up₁ Ζ ζ))) (up₁ Ξ (beta₁ T Ξ (tr T T Ζ t ζ))).
    Proof. exact (tr_up_beta₁_comm 1 t x ζ). Qed.

    Lemma tr_beta₁_comm (t:T) (x:X) (ζ:Ζ) :
      tr T X Ζ (tr T X Ξ x (beta₁ T Ξ t)) ζ =
      tr T X Ξ (tr T X Ζ x (up₁ Ζ ζ)) (beta₁ T Ξ (tr T T Ζ t ζ)).
    Proof. generalize (tr_up_beta₁_comm 0 t x ζ). now rewrite !up_zero. Qed.

  End TrBetaComm.

End Pointful.
