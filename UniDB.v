Require Export UniDB.Inst.
Require Export UniDB.Inst.Subst.
Require Export UniDB.Lemmas.Core.
Require Export UniDB.Morph.Depth.
Require Export UniDB.Morph.Pair.
Require Export UniDB.Morph.Reg.
Require Export UniDB.Morph.Shift.
Require Export UniDB.Morph.Shifts.
Require Export UniDB.Morph.Unit.
Require Export UniDB.Morph.Weaken.
Require Export UniDB.Scoping.Core.
Require Export UniDB.Scoping.Subst.
Require Export UniDB.Spec.Core.
Require Export UniDB.Spec.Subst.
Require Export UniDB.Tactics.Core.
Require Export UniDB.Tactics.Subst.
Require Export UniDB.Tactics.Morph.

Reserved Notation "ξ ↑₁"
  (at level 8, left associativity, format "ξ ↑₁").
Reserved Notation "x ↑ δ"
  (at level 53, left associativity).
Reserved Notation "ξ ⊙ ζ"
  (at level 46, left associativity).
Reserved Notation "ξ ⊡ ζ"
  (at level 46, left associativity).
Reserved Notation "ξ · x"
  (at level 55, left associativity).
Reserved Notation "ξ ≃ ζ"
  (at level 20, no associativity).
Reserved Notation "ξ ≅ ζ"
  (at level 20, no associativity).

Notation "ξ ↑₁" := (up₁ _ ξ).
Notation "x ↑ δ" := (up _ x δ).
Notation "ξ ⊙ ζ" := (comp _ ξ ζ).
Notation "ξ ⊡ ζ" := (hcomp ξ ζ).
Notation "ξ · x" := (snoc _ _ ξ x).
Notation "ξ ≃ ζ" := (Pointwise _ _ _ ξ ζ).
Notation "ξ ≅ ζ" := (Extended _ _ _ ξ ζ).


Reserved Notation "t '[' ξ ']'"
  (at level 8, left associativity, format "t [ ξ ]").
Notation "x '[' ξ ']'" := (tr _ _ _ x ξ).

Reserved Notation "⟨ ξ : γ => δ ⟩" (at level 0, ξ at level 98, γ at level 98, δ at level 98).
Notation "⟨ ξ : γ => δ ⟩" := (WsSub γ δ ξ).

Ltac usimpl :=
  repeat
    (repeat unidb_simpl_context_core;
     repeat unidb_simpl_conc_core;
     repeat unidb_simpl_scoping;
     repeat unidb_simpl_conc_subst;
     repeat unidb_fold_morph;
     repeat unidb_rewrite_core;
     repeat unidb_rewrite_subst).
