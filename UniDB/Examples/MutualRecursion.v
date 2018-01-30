Require Import UniDB.

Inductive Tm : Set :=
  | var (i : Ix)
  | abs (t : Tm)
  | app (t : Tm) (ts: Tms)
with Tms : Set :=
  | tnil
  | tcons (t : Tm) (ts : Tms).

Section Tr.
  Context {Ξ : Type} `{Lk Tm Ξ, Up Ξ}.

  Fixpoint trTm (t : Tm) (ξ : Ξ) {struct t} : Tm :=
    match t with
      | var i    => lk Tm Ξ ξ i
      | abs t    => abs (trTm t ξ↑₁)
      | app t ts => app (trTm t ξ) (trTms ts ξ)
    end
  with trTms (ts : Tms) (ξ : Ξ) {struct ts} : Tms :=
    match ts with
      | tnil       => tnil
      | tcons t ts => tcons (trTm t ξ) (trTms ts ξ)
    end.

End Tr.

Instance UniDBTm : UniDBVar Tm :=
  {| VrT := var; TrT := @trTm |}.
Instance iTrTmTms : Tr Tm Tms := @trTms.

Section TrRel.

  Context
    {Ξ : Type} {lkTΞ : Lk Tm Ξ} {upΞ : Up Ξ} {upHomΞ : UpHom Ξ}
    {Ζ : Type} {lkTΖ : Lk Tm Ζ} {upΖ : Up Ζ} {upHomΖ : UpHom Ζ}.

  Lemma trrel_tm (t : Tm) :
    ∀ {ξ : Ξ} {ζ : Ζ} (hyp : Extended Tm Ξ Ζ ξ ζ), trTm t ξ = trTm t ζ
  with trrel_tms (ts : Tms) :
    ∀ {ξ : Ξ} {ζ : Ζ} (hyp : Extended Tm Ξ Ζ ξ ζ), trTms ts ξ = trTms ts ζ.
  Proof.
    - unidb_derive_trrel Tm Ξ Ζ t.
    - unidb_derive_trrel Tm Ξ Ζ ts.
  Qed.

End TrRel.
Instance iTrRelTm : TrRel Tm Tm := @trrel_tm.
Instance iTrRelTms : TrRel Tm Tms := @trrel_tms.

Section TrPair.

  Context
    {Ξ : Type} {lkTΞ : Lk Tm Ξ} {upΞ : Up Ξ} (* {upHomΞ : UpHom Ξ} *)
    {Ζ : Type} {lkTΖ : Lk Tm Ζ} {upΖ : Up Ζ} (* {upHomΖ : UpHom Ζ} *).

  Lemma trpair_tm (t : Tm) :
    ∀ (ξ : Ξ) (ζ : Ζ), tr Tm Tm Ζ (tr Tm Tm Ξ t ξ) ζ = tr Tm Tm _ t (ξ ⊗ ζ)
  with trpair_tms (ts : Tms) :
    ∀ (ξ : Ξ) (ζ : Ζ), tr Tm Tms Ζ (tr Tm Tms Ξ ts ξ) ζ = tr Tm Tms _ ts (ξ ⊗ ζ).
  Proof.
    - unidb_derive_trpair t.
    - unidb_derive_trpair ts.
  Qed.

End TrPair.

Instance iTrPairTm : TrPair Tm Tm := fun _ _ _ _ _ _ _ _ => trpair_tm.
Instance iTrPairTms : TrPair Tm Tms := fun _ _ _ _ _ _ _ _ => trpair_tms.

Section TrIdmUnit.

  Lemma tridm_unit_tm (t : Tm) :
    tr Tm Tm unit t tt = t
  with tridm_unit_tms (ts : Tms) :
    tr Tm Tms unit ts tt = ts.
  Proof.
    - induction t; now cbn; f_equal.
    - induction ts; now cbn; f_equal.
  Qed.
End TrIdmUnit.

Instance iTrIdmTm : TrIdmUnit Tm Tm := tridm_unit_tm.
Instance iTrIdmTms : TrIdmUnit Tm Tms := tridm_unit_tms.

Instance UnidebTmLemmas : UniDBVarLemmas Tm.
Proof. unidb_derive_instance. Qed.

(* Compose a substitution from a list of terms. *)
Fixpoint beta (ts : Tms) : Reg Tm :=
  match ts with
  | tnil       => idm (Reg Tm)
  | tcons t ts => beta₁ Tm (Reg Tm) t ⊙ beta ts
  end.

Definition subTms {X: Type} `{Tr Tm X} (ts : Tms) (x : X) : X :=
  tr Tm X (Reg Tm) x (beta ts).

Inductive Eval : Tm → Tm → Prop :=
  | e_app₁ {t t' ts} :
      Eval t t' → Eval (app t ts) (app t' ts)
  | e_app₂ {t ts ts'} :
      Evals ts ts' → Eval (app t ts) (app t ts')
  | e_abs  {t t'} :
      Eval t t' → Eval (abs t) (abs t')
  | e_beta {t ts} :
      Eval (app (abs t) ts) (subTms ts t)
with Evals : Tms → Tms → Prop :=
  | e_tcons₁ {t t' ts} :
      Eval t t' → Evals (tcons t ts) (tcons t' ts)
  | e_tcons₂ {t ts ts'} :
      Evals ts ts' → Evals (tcons t ts) (tcons t ts').

(******************************************************************************)
