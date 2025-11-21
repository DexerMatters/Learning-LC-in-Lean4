import LearningLC.DeBruijn
import LearningLC.STLC.Basic

open Term

def rename {Γ Δ}
  (ρ : ∀ {A}, Γ ∋ A → Δ ∋ A)
  --------------------------
  : ∀ {A}, Γ ⊢ A → Δ ⊢ A
:= fun M => match M with
  | ′v       => ′(ρ v)
  | λ. t     => λ. (rename (Ix.ext ρ) t)
  | t1 ⋅ t2   => (rename ρ t1) ⋅ (rename ρ t2)
  | mu t     => mu (rename (Ix.ext ρ) t)
  | succ t   => succ (rename ρ t)
  | zero     => zero
  | cases e1 e2 e3 => cases (rename ρ e1) (rename ρ e2) (rename (Ix.ext ρ) e3)

def exts {Γ Δ}
  (σ : ∀ {A}, Γ ∋ A → Δ ⊢ A)
  ---------------------------------------
  : ∀ {A B}, (B :: Γ) ∋ A → (B :: Δ) ⊢ A
:= fun x => match x with
  | Ix.here    => ′Ix.here
  | Ix.there v => rename Ix.there (σ v)

def subst {Γ Δ}
  (σ : ∀ {A}, Γ ∋ A → Δ ⊢ A)
  --------------------------
  : ∀ {A}, Γ ⊢ A → Δ ⊢ A
:= fun M => match M with
  | ′v       => σ v
  | λ. t     => λ. (subst (exts σ) t)
  | t1 ⋅ t2   => (subst σ t1) ⋅ (subst σ t2)
  | mu t     => mu (subst (exts σ) t)
  | succ t   => succ (subst σ t)
  | zero     => zero
  | cases e1 e2 e3 => cases (subst σ e1) (subst σ e2) (subst (exts σ) e3)

def subst_here {Γ A}
  (N : Γ ⊢ A)
  ----------------
  : ∀ {B}, (A :: Γ) ⊢ B → Γ ⊢ B
:= by
  apply subst
  intro A
  intro
  | Ix.here    => exact N
  | Ix.there v => exact ′v

inductive IsValue : {Γ : List Ty} → Γ ⊢ A → Prop where
  | vlam {Γ A B} (M : A :: Γ ⊢ B) :
      IsValue (λ. M)
  | vzero :
      IsValue zero
  | vsucc {Γ} {N : Γ ⊢ Ty.nat} :
      IsValue N →
      IsValue (succ N)

inductive Eval : {Γ : List Ty} → Γ ⊢ A → Γ ⊢ A → Prop where
  | lam_beta {Γ} {A B} {M : A :: Γ ⊢ B} {N : Γ ⊢ A}:
      IsValue N →
      ---------------------------------
      Eval ((λ. M) ⋅ N) (subst_here N M)
  | mu_unfold {Γ} {A} {M : A :: Γ ⊢ A} :
      Eval (mu M) (subst_here (mu M) M)
  | app_left {Γ} {A B} {M1 M2 : Γ ⊢ Ty.arrow A B} {N : Γ ⊢ A} :
      Eval M1 M2 →
      ---------------------
      Eval (M1 ⋅ N) (M2 ⋅ N)
  | app_right {Γ} {A B} {M : Γ ⊢ Ty.arrow A B} {N1 N2 : Γ ⊢ A} :
    IsValue M → Eval N1 N2 →
    -------------------------
    Eval (M ⋅ N1) (M ⋅ N2)
  | succ_step {Γ} {N N' : Γ ⊢ Ty.nat}:
    Eval N N' →
    -----------------------
    Eval (succ N) (succ N')
  | cases_beta_zero {Γ} {A}
    {M : Γ ⊢ Ty.nat} {P : Γ ⊢ A} {Q : Ty.nat :: Γ ⊢ A} :
    -----------------------------------------------------
    Eval (cases zero P Q) P
  | cases_beta_succ {Γ} {A}
    {M : Γ ⊢ Ty.nat} {P : Γ ⊢ A} {Q : Ty.nat :: Γ ⊢ A} :
    ----------------------------------------------------
    IsValue M →
    Eval (cases (succ M) P Q) (subst_here M Q)
  | cases_step {Γ} {A}
    {M1 M2 : Γ ⊢ Ty.nat} {P : Γ ⊢ A} {Q : Ty.nat :: Γ ⊢ A} :
    Eval M1 M2 →
    ---------------------------------------------------------
    Eval (cases M1 P Q) (cases M2 P Q)

infix:50 " ⇒ " => Eval

-- Refectivity and transitivity of multi-step evaluation
inductive MultiEval : {Γ : List Ty} → Γ ⊢ A → Γ ⊢ A → Prop where
  | refl {Γ} {A} {M : Γ ⊢ A} :
      MultiEval M M
  | step {Γ} {A} {M1 M2 M3 : Γ ⊢ A} :
      M1 ⇒ M2 →
      MultiEval M2 M3 →
      MultiEval M1 M3

infix:50 " ⇒* " => MultiEval

theorem cannot_reduce_value {Γ A} : ∀ M : Γ ⊢ A, IsValue M → ¬ ∃ N, M ⇒ N := by
  intro M V
  induction V
  case vlam =>
    intro ⟨N, h⟩
    cases h
  case vzero =>
    intro ⟨N, h⟩
    cases h
  case vsucc N ih =>
    intro ⟨N0, h⟩
    cases h with
    | succ_step h' =>
      apply ih
      exact ⟨_, h'⟩


theorem progress: ∀ M : ∅ ⊢ A, (IsValue M ∨ ∃ N, M ⇒ N) := by
  open Eval IsValue in
  intro M
  match M with
  | λ. _ =>
    left; apply vlam
  | mu M' =>
    right; exact ⟨subst_here (mu M') M', mu_unfold ⟩
  | zero =>
    left; apply vzero
  | succ N =>
    match progress N with
    | .inl hN =>
      left; apply vsucc hN
    | .inr ⟨N', h⟩ =>
      right; exact ⟨succ N', succ_step h⟩
  | L ⋅ N =>
    right;
    match progress L with
    | .inr ⟨L', hL⟩ =>
      exact ⟨L' ⋅ N, app_left hL⟩
    | .inl vL =>
      match progress N with
      | .inr ⟨N', hN⟩ =>
        exact ⟨L ⋅ N', app_right vL hN⟩
      | .inl vN =>
        match vL with
        | vlam M' =>
          exact ⟨subst_here N M', lam_beta vN⟩
  | cases M P Q =>
    right;
    match progress M with
    | .inr ⟨M', hM⟩ => exact ⟨cases M' P Q, cases_step hM⟩
    | .inl hM =>
      cases hM
      case vzero =>
        exists P
        apply cases_beta_zero
        exact zero
      case vsucc n ih =>
        exact ⟨subst_here n Q, cases_beta_succ ih⟩
