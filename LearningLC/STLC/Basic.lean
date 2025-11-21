import LearningLC.DeBruijn

universe u

inductive Ty : Type u where
  | nat : Ty
  | arrow : Ty → Ty → Ty

inductive Term : List Ty → Ty → Type u where
  | var {Γ A} :
      Γ ∋ A
    ----------
    → Term Γ A
  | lam {Γ A B} :
      Term (A :: Γ) B
    -----------------------
    → Term Γ (Ty.arrow A B)
  | app {Γ A B} :
      Term Γ (Ty.arrow A B) → Term Γ A
    ----------------------------------
    → Term Γ B
  | mu {Γ A} :
      Term (A :: Γ) A
    -----------------
    → Term Γ A
  | succ {Γ} : Term Γ Ty.nat → Term Γ Ty.nat
  | zero {Γ} : Term Γ Ty.nat
  | cases {Γ A} :
      Term Γ Ty.nat → Term Γ A → Term (Ty.nat :: Γ) A
      ------------------------------------------------
      → Term Γ A


infix:60 "⊢" => Term

notation:60 " λ. " e:60 => Term.lam e
notation:55 e1:50 " ⋅ " e2:55 => Term.app e1 e2
notation:60 " • " => Term.unit
notation:60 " case " e1:60 "{zero=>" e2:60 ",succ=>" e3:60 " }" => Term.case e1 e2 e3
prefix:90 " ′ " => Term.var

macro "#" n:num : term => `(Term.var (Ix.fromNat (a := Ty.nat) $n (by simp)))
