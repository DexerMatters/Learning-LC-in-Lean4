import LearningLC.SystemF.Basic

open Term Ty

def List.shift {Δ} {Γ : List (Ty Δ)} : List (Ty (Δ + 1)) :=
  Γ.map (Ty.shift)

-- Extend the context for lambda terms
def ext {Δ Γ Δ' Γ'}
  {Ρ : Fin Δ → Fin Δ'}
  (ρ : ∀ {A}, Γ ∋ A → Γ' ∋ (A.rename Ρ))
  : ∀ {B A : Ty Δ}, (B :: Γ) ∋ A → (B.rename Ρ :: Γ') ∋ (A.rename Ρ)
:= fun x => match x with
  | Ix.here => Ix.here
  | Ix.there v => Ix.there (ρ v)

-- Extend the context for type abstractions
def ext_meta
  {Δ Δ'}
  {Γ : List (Ty Δ)}
  {Γ' : List (Ty Δ')}
  {Ρ : Fin Δ → Fin Δ'}
  : ∀ {A}, Γ.shift ∋ A → Γ'.shift ∋ (A.rename (Ty.ext Ρ) )
:= by
  intro A x
  generalize Γ.shift = Γ_shift at *
  generalize Γ'.shift = Γ'_shift at *




def rename {Δ Γ Δ' Γ'}
  (Ρ : Fin Δ → Fin Δ') (ρ : ∀ {A}, Γ ∋ A → Γ' ∋ (Ty.rename Ρ A))
  ---------------------------------------------------------------
: ∀ {A}, Δ ; Γ ⊢ A → Δ' ; Γ' ⊢ (Ty.rename Ρ A)
:= fun M =>
  match M with
  | .var v       => .var (ρ v)
  | .lam A t     => .lam (Ty.rename Ρ A) (rename Ρ (ext ρ) t)
  | .app t1 t2   => .app (rename Ρ ρ t1) (rename Ρ ρ t2)
  | .tlam t      => .tlam (rename (Ty.ext Ρ) (ext_meta ρ) t)

  | .tapp t U    => sorry
  | .zero        => .zero
  | .succ t      => .succ (rename Ρ ρ t)
  | .cases e1 e2 e3 => .cases (rename Ρ ρ e1) (rename Ρ ρ e2) (rename Ρ (ext ρ) e3)
  | .mu t        => .mu (rename Ρ (ext ρ) t)
