import LearningLC.SystemF.Basic

open Context Ty Term

def Term.ext {Δ Δ'} {Γ : Context Δ} {Γ' : Context Δ'}
  (R : Fin Δ → Fin Δ')
  (ρ: ∀ {A}, Γ ∋ A → Γ' ∋ A.rename R)
  ------------------------------------------------
  : ∀ {A B}, (B :: Γ) ∋ A → (B.rename R :: Γ') ∋ A.rename R
  | _, _, Var.here      => Var.here
  | _, _, Var.there v   => Var.there (ρ v)

def Term.extₜ {Δ Δ'} {Γ : Context Δ} {Γ' : Context Δ'}
  (R : Fin Δ → Fin Δ')
  (ρ: ∀ {A}, Γ ∋ A → Γ' ∋ A.rename R)
  -------------------------------------
  : ∀ {A}, exts Γ ∋ A → exts Γ' ∋ A.rename (Ty.ext R)
  | _, Var.hereₜ        => Var.hereₜ
  | _, Var.thereₜ v     => Var.thereₜ (ρ v)

def Term.rename {Δ Δ'} {Γ : Context Δ} {Γ' : Context Δ'}
  (R : Fin Δ → Fin Δ')
  (ρ : ∀ {A}, Γ ∋ A → Γ' ∋ A.rename R)
  -----------------------------
: ∀ {A}, Δ; Γ ⊢ A → Δ'; Γ' ⊢ (A.rename R)
:= fun {A} t => match t with
  | .var v => .var (ρ v)
  | .lam t1 => .lam (.rename R (ext R ρ) t1)
  | .app t1 t2 => .app (.rename R ρ t1) (.rename R ρ t2)
  | .tlam t1 => .tlam (.rename (Ty.ext R) (extₜ R ρ) t1)
  | .tapp t1 B => .tapp (.rename R ρ t1) (B.rename R)
  | .mu t1 => .mu (.rename R (ext R ρ) t1)
  | .succ t1 => .succ (.rename R ρ t1)
  | .zero => .zero
  | .cases t1 t2 t3 =>
      .cases (.rename R ρ t1)
             (.rename R ρ t2)
             (.rename R (ext R ρ) t3)

def Term.exts {Δ Δ'} {Γ : Context Δ} {Γ' : Context Δ'}
  (S : Fin Δ → Ty Δ')
  (σ : ∀ {A}, Γ ∋ A → Term Δ' Γ' (A.subst S))
  ------------------------------------------------
  : ∀ {A B}, (B :: Γ) ∋ A → Term Δ' (B.subst S :: Γ') (A.subst S)
:= fun {A B} v => match v with
  | Var.here      => .var .here
  | Var.there v   => .var (.there (σ v))

def Term.subst {Δ Δ'} {Γ : Context Δ} {Γ' : Context Δ'}
  (S : Fin Δ → Ty Δ')
  (σ : ∀ {A}, Γ ∋ A → Term Δ' Γ' (A.subst S))
  -------------------------------------
  : ∀ {A}, Δ; Γ ⊢ A → Δ'; Γ' ⊢ A.subst S
:= fun {A} t => match t with
  | .var v => σ v
  | .lam t1 => .lam (Term.subst S (Term.exts S σ) t1)
  | .app t1 t2 => .app (Term.subst S σ t1) (Term.subst S σ t2)
