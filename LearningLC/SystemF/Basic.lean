import LearningLC.SystemF.Type

universe u


def Context (Δ : Nat) : Type u := List (Ty Δ)

def Context.shift {Δ} (Γ : Context Δ) : Context (Δ + 1) :=
  Γ.map Ty.shift

infixl:60 " :: " => Context.cons

inductive Var {Δ} : Context Δ → Ty Δ → Type u where
  | here {Γ A} : Var (A :: Γ) A
  | there {Γ A B} : Var Γ B → Var (A :: Γ) B

infix:60 "∋" => Var

inductive Term : (Δ : Nat) → Context Δ → Ty Δ → Type u where
  | var {Γ A} :
      Γ ∋ A
    ----------
    → Term Δ Γ A
  | lam {Γ A B} :
      Term Δ (A :: Γ) B
    -----------------------
    → Term Δ Γ (Ty.tyArr A B)
  | app {Γ A B} :
      Term Δ Γ (Ty.tyArr A B) → Term Δ Γ A
    ----------------------------------
    → Term Δ Γ B
  | tlam {Γ A} :
      Term (Δ + 1) (Context.shift Γ) A
    ---------------------------
    → Term Δ Γ (Ty.tyForall A)
  | tapp {Δ Γ A A'} :
      Term Δ Γ (Ty.tyForall A) → (B : Ty Δ)
    -----------------------------------------
    → Term Δ Γ A'
  | mu {Δ Γ A} :
      Term Δ (A :: Γ) A
    -----------------
    → Term Δ Γ A
  | succ {Δ Γ} : Term Δ Γ Ty.tyNat → Term Δ Γ Ty.tyNat
  | zero {Δ Γ} : Term Δ Γ Ty.tyNat
  | cases {Δ Γ A} :
      Term Δ Γ (@Ty.tyNat Δ) → Term Δ Γ A → Term Δ ((@Ty.tyNat Δ) :: Γ) A
      --------------------------------------------------------------------
      → Term Δ Γ A


notation:60 e1:60 " ; " e2:60 " ⊢ " A:60 => Term e1 e2 A
