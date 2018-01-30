Require Import UniDB.
Require Import List.

(******************************************************************************)

Inductive Tm : Set :=
  | var (i : Ix)
  | abs (t : Tm)
  | app (t1 t2 : Tm).

Section WsTm.

  Inductive WsTm (γ : Dom) : Tm → Prop :=
    | ws_var {i} (wi : γ ∋ i): ⟨ γ ⊢ var i ⟩
    | ws_abs {t} (wt : ⟨ S γ ⊢ t ⟩): ⟨ γ ⊢ abs t ⟩
    | ws_app {t1 t2} (wt1 : ⟨ γ ⊢ t1 ⟩) (wt2 : ⟨ γ ⊢ t2 ⟩):
        ⟨ γ ⊢ app t1 t2 ⟩
  where "⟨ γ ⊢ t ⟩" := (WsTm γ t).

  Global Instance iWsTm : Ws Tm := WsTm.

End WsTm.

Fixpoint trTm {Ξ : Type} `{Lk Tm Ξ, Up Ξ} (t : Tm) (ξ : Ξ) : Tm :=
  match t with
  | var i     => lk Tm Ξ ξ i
  | abs t     => abs (trTm t ξ↑₁)
  | app t1 t2 => app (trTm t1 ξ) (trTm t2 ξ)
  end.

Instance UniDBTm : UniDBVar Tm :=
  {| VrT := var; TrT := @trTm |}.
Instance UnidebTmLemmas : UniDBVarLemmas Tm.
Proof. unidb_derive_instance. Qed.

Instance UniDBTms : UniDBTerm Tm (list Tm) :=
  {| TrTX := fun Ξ lkTΞ upΞ ts ξ => map (fun t => tr Tm Tm Ξ t ξ) ts
  |}.

(******************************************************************************)

Definition subTm {X : Type} {trTmX : Tr Tm X} (s : Tm) (x : X) : X :=
  tr Tm X (Reg Tm) x (beta₁ Tm (Reg Tm) s).

Inductive Eval : Tm → Tm → Prop :=
  | e_app₁ {t₁ t₁' t₂ : Tm} :
      Eval t₁ t₁' → Eval (app t₁ t₂) (app t₁' t₂)
  | e_app₂ {t₁ t₂ t₂' : Tm} :
      Eval t₂ t₂' → Eval (app t₁ t₂) (app t₁ t₂')
  | e_abs  {t t' : Tm} :
      Eval t t' → Eval (abs t) (abs t')
  | e_beta₁ {s : Tm} {t : Tm} :
      Eval (app (abs t) s) (subTm s t).

(******************************************************************************)
