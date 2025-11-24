import LearningLC.SystemF.Basic

open Term Ty

def exts {Δ Γ Δ' Γ'}
  (Ρ : Fin Δ → Fin Δ') (ρ : ∀ {A}, Γ ∋ A → Γ' ∋ (Ty.rename Ρ A))
  -----------------------------------------------------------------
  : ∀ {B A}, (B :: Γ) ∋ A → (Ty.rename Ρ B :: Γ') ∋ (Ty.rename Ρ A)
:= fun x => match x with
  | Ix.here => Ix.here
  | Ix.there v => Ix.there (ρ v)

def ext_shift {Δ Γ Δ' Γ'}
  (Ρ : Fin Δ → Fin Δ') (ρ : ∀ {A}, Γ ∋ A → Γ' ∋ (Ty.rename Ρ A))
  ---------------------------------------------------------------------
  : ∀ {A}, (Γ.map Ty.shift) ∋ A → (Γ'.map Ty.shift) ∋ (Ty.rename (Ty.ext Ρ) A)
:= sorry

def rename {Δ Γ Δ' Γ'}
  (Ρ : Fin Δ → Fin Δ') (ρ : ∀ {A}, Γ ∋ A → Γ' ∋ (Ty.rename Ρ A))
  ---------------------------------------------------------------
: ∀ {A}, Δ ; Γ ⊢ A → Δ' ; Γ' ⊢ (Ty.rename Ρ A)
:= fun M =>
  match M with
  | .var v       => .var (ρ v)
  | .lam A t     => .lam (Ty.rename Ρ A) (rename Ρ (exts Ρ ρ) t)
  | .app t1 t2   => .app (rename Ρ ρ t1) (rename Ρ ρ t2)
  | .tlam t      => .tlam (rename (Ty.ext Ρ) (ext_shift Ρ ρ) t)

  | .tapp t U    => .tapp (rename Ρ ρ t) (Ty.rename Ρ U)
  | .zero        => .zero
  | .succ t      => .succ (rename Ρ ρ t)
  | .cases e1 e2 e3 => .cases (rename Ρ ρ e1) (rename Ρ ρ e2) (rename Ρ (exts Ρ ρ) e3)
  | .mu t        => .mu (rename Ρ (exts Ρ ρ) t)
