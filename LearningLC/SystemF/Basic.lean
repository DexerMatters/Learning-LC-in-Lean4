import LearningLC.SystemF.Type

universe u


inductive Context : (Δ : Nat) → Type u where
  | nil : Context 0
  | cons {Δ} (A : Ty Δ) (Γ : Context Δ) : Context Δ
  | exts {Δ} (Γ : Context Δ) : Context (Δ + 1)

open Context

infixl:60 " :: " => Context.cons

inductive Var : Context Δ → Ty Δ → Type u where
  | here {Γ A} : Var (A :: Γ) A
  | there {Γ A B} : Var Γ B → Var (A :: Γ) B
  | hereₜ {Γ} {A : Ty (Δ + 1)} : Var (exts Γ) A
  | thereₜ {Γ} {A : Ty Δ} {A' : Ty (Δ + 1)} : Var Γ A → Var (exts Γ) A'

infix:60 "∋" => Var


inductive Term : (Δ : Nat) → Context Δ → Ty Δ → Type u where
  | var {Δ Γ A} :
      Γ ∋ A
    ----------
    → Term Δ Γ A
  | lam {Δ Γ A B} :
      Term Δ (A :: Γ) B
    -----------------------
    → Term Δ Γ (Ty.tyArr A B)
  | app {Δ Γ A B} :
      Term Δ Γ (Ty.tyArr A B) → Term Δ Γ A
    ----------------------------------
    → Term Δ Γ B
  | tlam {Δ Γ A} :
      Term (Δ + 1) (exts Γ) A
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
      Term Δ Γ Ty.tyNat → Term Δ Γ A → Term Δ (Ty.tyNat :: Γ) A
      ---------------------------------------------------------
      → Term Δ Γ A



notation:60 e1:60 " ; " e2:60 " ⊢ " A:60 => Term e1 e2 A
