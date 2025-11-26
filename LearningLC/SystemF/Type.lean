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

def Ty.exts {Δ Δ'} (σ : Fin Δ → Ty Δ') : Fin (Δ + 1) → Ty (Δ' + 1)
  | 0 => Ty.tyVar 0
  | ⟨k+1, hk⟩ => Ty.shift (σ ⟨k, by omega⟩)

def Ty.subst {Δ Δ'} (σ : Fin Δ → Ty Δ') : Ty Δ → Ty Δ'
  | .tyVar x      => σ x
  | .tyNat        => .tyNat
  | .tyArr A B    => .tyArr (Ty.subst σ A) (Ty.subst σ B)
  | .tyForall A   => .tyForall (Ty.subst (Ty.exts σ) A)

def Ty.subst₀ {Δ} (U : Ty Δ) : Ty (Δ + 1) → Ty Δ :=
  Ty.subst (fun x => match x with
    | 0         => U
    | ⟨k+1, hk⟩ => Ty.tyVar ⟨k, by omega⟩)
