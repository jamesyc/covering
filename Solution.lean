module

public import Covering.Main

public section

/-!
# Proved statements

Comparator checks that these declarations have exactly the statements in `Challenge.lean` and
use only the standard axioms. They are the main theorems of `Covering/Main.lean`, which state
Theorem 1.1 and Corollary 5.2 of the paper for ordinary finite families of finite sets.
-/

/-- `C(24, 14, 4) ≥ 20`. -/
theorem Covering.Palomar.covering_24_14_4_lower_bound (𝒯 : Finset (Finset (Fin 24)))
    (hk : ∀ B ∈ 𝒯, B.card = 14)
    (hcov : ∀ S : Finset (Fin 24), S.card = 4 → ∃ B ∈ 𝒯, S ⊆ B) :
    20 ≤ 𝒯.card :=
  Covering.covering_24_14_4 𝒯 hk hcov

/-- `C(25, 15, 5) ≥ 34`. -/
theorem Covering.Palomar.covering_25_15_5_lower_bound (𝒯 : Finset (Finset (Fin 25)))
    (hk : ∀ B ∈ 𝒯, B.card = 15)
    (hcov : ∀ S : Finset (Fin 25), S.card = 5 → ∃ B ∈ 𝒯, S ⊆ B) :
    34 ≤ 𝒯.card :=
  Covering.covering_25_15_5 𝒯 hk hcov

#print axioms Covering.Palomar.covering_24_14_4_lower_bound
#print axioms Covering.Palomar.covering_25_15_5_lower_bound
