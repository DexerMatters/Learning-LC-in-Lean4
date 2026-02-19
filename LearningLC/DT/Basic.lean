-- Weaker representation of types
inductive Tyₜ : Type
| unit : Tyₜ
| prod : Tyₜ → Tyₜ → Tyₜ

-- Weaker representation of terms
inductive Tmₜ : Type
| unit : Tmₜ
| pair : Tmₜ → Tmₜ → Tmₜ
| var : Nat → Tmₜ

abbrev Cxₜ := List Tyₜ

-- Weaker representation of substitutions
inductive Sbₜ : Type
| bang : Sbₜ
| id : Sbₜ
| proj : Sbₜ
| ext : Sbₜ → Tyₜ → Tmₜ → Sbₜ

-- Weaker substitution on raw types.
def subst_ty : Sbₜ → Tyₜ → Tyₜ
  | _, .unit     => .unit
  | γ, .prod A B => .prod (subst_ty γ A) (subst_ty γ B)

def subst_tm : Sbₜ → Tmₜ → Tmₜ
  | _, .unit     => .unit
  | γ, .pair M N => .pair (subst_tm γ M) (subst_tm γ N)
  | γ, .var n    =>
    match γ with
    | .bang => .var n
    | .id => .var n
    | .proj => .var (n + 1)
    | .ext γ' A M' =>
      if n = 0 then M'
      else subst_tm γ' (.var (n - 1))

mutual

-- Well-formed contexts
inductive Cx : Cxₜ → Type
| nil : Cx []
| cons {Γ} {t : Tyₜ} :
    Ty Γ t → Cx Γ
  ----------------
  → Cx (t :: Γ)

-- Well-formed types
inductive Ty : Cxₜ → Tyₜ → Type
| unit {Γ} : Cx Γ → Ty Γ Tyₜ.unit
| prod {Γ} {A B : Tyₜ} :
    Ty Γ A → Ty Γ B
  -------------------------
  → Ty Γ (Tyₜ.prod A B)

-- Well-formed terms
inductive Tm : Cxₜ → Tmₜ → Tyₜ → Type
| unit {Γ} : Cx Γ → Tm Γ Tmₜ.unit Tyₜ.unit
| pair {Γ} {M N : Tmₜ} {A B : Tyₜ} :
    Tm Γ M A → Tm Γ N B
  -------------------------------------
  → Tm Γ (Tmₜ.pair M N) (Tyₜ.prod A B)
| q {Γ} {A : Tyₜ} :
    Ty Γ A
  -----------------------------------------------------
  → Tm (A :: Γ) (Tmₜ.var 0) (subst_ty .proj A)

inductive Sb : (Γ Δ : Cxₜ) → Sbₜ → Type
| bang {Γ} : Cx Γ → Sb Γ [] .bang
| id {Γ} : Cx Γ → Sb Γ Γ .id
| proj {Γ} {A : Tyₜ} : Cx (A :: Γ) → Sb (A :: Γ) Γ .proj
| ext {Γ Δ γ} {A : Tyₜ} {M : Tmₜ} :
    Sb Δ Γ γ → Ty Γ A → Tm Δ M (subst_ty γ A)
  -------------------------------------------
  → Sb Δ (A :: Γ) (Sbₜ.ext γ A M)
end
