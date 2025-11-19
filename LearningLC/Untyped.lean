import LearningLC.DeBruijn

declare_syntax_cat lambda

universe u

inductive Ty : Type u where
  | unit : Ty

inductive Typing : List Ty → Ty → Type u where
  | unit {Γ} : Typing Γ .unit
  | var {Γ} :
      Γ ∋ .unit
    ----------------
    → Typing Γ .unit
  | lam {Γ} :
      Typing (.unit :: Γ) τ₂
    ------------------------
    → Typing Γ (.unit)
  | app {Γ} :
      Typing Γ (.unit) → Typing Γ (.unit)
    -------------------------------------
    → Typing Γ (.unit)

infix:60 "⊢" => Typing


notation:60 " λ. " e:60 => Typing.lam e
notation:55 e1:50 " ⋅ " e2:55 => Typing.app e1 e2
notation:60 " • " => Typing.unit
prefix:90 " ′ " => Typing.var


def rename {Γ Δ}
  (ρ : ∀ {A}, Γ ∋ A → Δ ∋ A)
  ------------------------
  : ∀ {A}, Γ ⊢ A → Δ ⊢ A
:= by intro _; intro
  | •        => exact •
  | ′v       => exact ′(ρ v)
  | λ. t     => exact λ. (rename (Ix.ext ρ) t)
  | t1 ⋅ t2  => exact (rename ρ t1) ⋅ (rename ρ t2)


def exts {Γ Δ}
  (σ : ∀ {A}, Γ ∋ A → Δ ⊢ A)
  ------------------------
  : ∀ {A B}, (B :: Γ) ∋ A → (B :: Δ) ⊢ A
:= by intro _ _; intro
  | Ix.here    => exact ′Ix.here;
  | Ix.there v => exact rename Ix.there (σ v)

def subst {Γ Δ}
  (σ : ∀ {A}, Γ ∋ A → Δ ⊢ A)
  ------------------------
  : ∀ {A}, Γ ⊢ A → Δ ⊢ A
:= by intro _; intro
  | •        => exact •
  | ′v       => exact σ v
  | λ. t     => exact λ. (subst (exts σ) t)
  | t1 ⋅ t2  => exact (subst σ t1) ⋅ (subst σ t2)

inductive Value : {Γ : List Ty} → Γ ⊢ A → Type u where
  | unit :
    ----------------
    Value Typing.unit
  | lam {Γ} {M : .unit :: Γ ⊢ .unit} :
    ------------------------
    Value (λ. M)

inductive Step : {Γ : List Ty} → Γ ⊢ A → Γ ⊢ A → Type u where
  | ξ₁ {Γ} {M N₁ N₂ : Γ ⊢ .unit} :
      Step N₁ N₂
    ------------------------
    → Step (M ⋅ N₁) (M ⋅ N₂)
  | ξ₂ {Γ} {M₁ M₂ N : Γ ⊢ .unit} :
      Step M₁ M₂
    ------------------------
    → Step (M₁ ⋅ N) (M₂ ⋅ N)
  | β {Γ} {M : .unit :: Γ ⊢ .unit} {N : Γ ⊢ .unit} :
    --------------------------------------
    Step ((λ. M) ⋅ N) (subst (fun _ => N) M)
  | ζ {Γ} {M N : .unit :: Γ ⊢ .unit} :
      Step M N
    ------------------------
    → Step (λ. M) (λ. N)

infix:40 " ⟶ " => Step

inductive Progress (M : Γ ⊢ A) : Prop where
  | value : Value M → Progress M
  | step {N : Γ ⊢ A} : (M ⟶ N) → Progress M

/- Proofs of Progress and Preservation would go here -/

theorem progress (M : ∅ ⊢ A) : Progress M :=
  match M with
  | •       => .value Value.unit
  | ′v      => by contradiction
  | λ. M'   => .value (Value.lam)
  | M₁ ⋅ M₂ => by
    have p1 := progress M₁
    have p2 := progress M₂
    cases p1
    case step

-- macro "#" n:num : term => `(Typing.var (Ix.fromNat (a := Ty.unit) $n (by simp)))

-- example : [] ⊢ .unit :=
--   (λ. #0) ⋅ •

-- example : [] ⊢ .unit :=
--   (λ. (λ. #1 ⋅ #0)) ⋅ (λ. •)
