import LearningLC.DeBruijn

inductive Ty : Nat → Type u where
  | tyVar {Δ} : Fin Δ → Ty Δ
  | tyNat {Δ} : Ty Δ
  | tyArr {Δ} : Ty Δ → Ty Δ → Ty Δ
  | tyForall {Δ} : Ty (Δ + 1) → Ty Δ

def Ty.ext {Δ Δ'}
  (ρ : Fin Δ → Fin Δ')
  : Fin (Δ + 1) → Fin (Δ' + 1)
:= fun x => match x with
  | 0         => 0
  | ⟨k+1, hk⟩ => Fin.succ (ρ ⟨k, by omega⟩)

def Ty.rename {Δ Δ'}
  (ρ : Fin Δ → Fin Δ')
  : Ty Δ → Ty Δ'
:= fun A => match A with
  | .tyVar x      => .tyVar (ρ x)
  | .tyNat        => .tyNat
  | .tyArr A B    => .tyArr (Ty.rename ρ A) (Ty.rename ρ B)
  | .tyForall A   => .tyForall (Ty.rename (Ty.ext ρ) A)

def Ty.shift {Δ} : Ty Δ → Ty (Δ + 1) := Ty.rename (fun x => Fin.succ x)

def Ty.subst {Δ} (U : Ty Δ) : Ty (Δ + 1) → Ty Δ
  | .tyVar x      =>
    match x with
      | 0         => U
      | ⟨k+1, hk⟩ => .tyVar ⟨k, Nat.lt_of_succ_lt_succ hk⟩
  | .tyNat        => .tyNat
  | .tyArr A B    => .tyArr (.subst U A) (.subst U B)
  | .tyForall A   => .tyForall (.subst (.shift U) A)



inductive Term : (Δ : Nat) → List (Ty Δ) → Ty Δ → Type u where
  | var {Δ Γ A} :
      Γ ∋ A
    ----------
    → Term Δ Γ A
  | lam {Δ Γ B} :
      (A : Ty Δ) → Term Δ (A :: Γ) B
    ---------------------------------
    → Term Δ Γ (Ty.tyArr A B)
  | app {Δ Γ A B} :
      Term Δ Γ (Ty.tyArr A B) → Term Δ Γ A
    ---------------------------------------
    → Term Δ Γ B
  | tlam {Δ Γ A} :
      Term (Δ + 1) (Γ.map Ty.shift) A
    --------------------------------
    → Term Δ Γ (Ty.tyForall A)
  | tapp {Δ Γ A} :
      Term Δ Γ (Ty.tyForall A) → (U : Ty Δ)
    ---------------------------------------
    → Term Δ Γ (Ty.subst U A)
  | mu {Δ Γ A} :
      Term Δ (A :: Γ) A
    -------------------
    → Term Δ Γ A
  | succ {Δ Γ} : Term Δ Γ Ty.tyNat → Term Δ Γ Ty.tyNat
  | zero {Δ Γ} : Term Δ Γ Ty.tyNat
  | cases {Δ Γ A} :
      Term Δ Γ Ty.tyNat → Term Δ Γ A → Term Δ (Ty.tyNat :: Γ) A
      ---------------------------------------------------------
      → Term Δ Γ A


notation:60 e1:90 ";" e2:90 "⊢" e3:50 => Term e1 e2 e3

notation:60 " λ:" ty:0 "." e:50 => Term.lam ty e
notation:55 e1:50 " ⋅ " e2:55 => Term.app e1 e2
notation:60 " case " e1:60 "{zero=>" e2:60 ",succ=>" e3:60 " }" => Term.cases e1 e2 e3
notation:60 " Λ. " e:60 => Term.tlam e
notation:55 e " ⟨ " U:55 " ⟩ " => Term.tapp e U
prefix:90 " ′ " => Term.var
