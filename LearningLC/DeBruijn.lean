inductive Ix {α : Type u} : List α → α → Type u where
  | here {Γ α} : Ix (α :: Γ) α
  | there {Γ α₁ α₂} : Ix Γ α₂ → Ix (α₁ :: Γ) α₂

infix:60 "∋" => Ix

def Ix.ext {α : Type u} {Δ Δ' : List α}
  (ρ: ∀ {a}, Δ ∋ a → Δ' ∋ a)
  -------------------------------------
  : ∀ {a β}, (β :: Δ) ∋ a → (β :: Δ') ∋ a
  | _, _, Ix.here      => Ix.here
  | _, _, Ix.there v   => Ix.there (ρ v)


def Ix.toNat {α : Type u} {Γ : List α} {a : α} : Ix Γ a → Nat
  | Ix.here => 0
  | Ix.there i => i.toNat + 1

def Ix.fromNat {α : Type u} {Γ : List α} {a : α} (n : Nat) (h : n < Γ.length ∧ Γ[n]? = some a) : Ix Γ a :=
  match Γ, n with
  | b :: _, 0 =>
      have : a = b := by
        have ⟨_, h2⟩ := h
        simp at h2
        exact h2.symm
      this ▸ Ix.here
  | _ :: Γ', n + 1 => Ix.there (Ix.fromNat n (by
      have ⟨h1, h2⟩ := h
      constructor
      · simp at h1; omega
      · simpa using h2))


example : (Ix.here : Ix [Nat, Nat, Nat] Nat).toNat = 0 := rfl
example : (Ix.there Ix.here : Ix [Nat, Nat, Nat] Nat).toNat = 1 := rfl
example : (Ix.there (Ix.there Ix.here) : Ix [Nat, Nat, Nat] Nat).toNat = 2 := rfl
