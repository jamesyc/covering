module

public import Mathlib.Data.Finset.Card

public section

/-!
# Lower bounds for the covering numbers C(24,14,4) and C(25,15,5)

A `(v, k, t)` covering design is a family of `k`-element subsets (blocks) of a `v`-element set
such that every `t`-element subset is contained in at least one block. The covering number
`C(v, k, t)` is the least number of blocks in such a design.

The two theorems below say that `C(24, 14, 4) ≥ 20` and `C(25, 15, 5) ≥ 34`. The point set is
`Fin v`, a family of blocks is a `Finset` of `Finset`s, and no other definitions are used.
-/

/-- Every family of 14-element subsets of a 24-element set that covers every 4-element subset
has at least 20 members. That is, `C(24, 14, 4) ≥ 20`. -/
theorem Covering.Palomar.covering_24_14_4_lower_bound (𝒯 : Finset (Finset (Fin 24)))
    (hk : ∀ B ∈ 𝒯, B.card = 14)
    (hcov : ∀ S : Finset (Fin 24), S.card = 4 → ∃ B ∈ 𝒯, S ⊆ B) :
    20 ≤ 𝒯.card := by
  sorry

/-- Every family of 15-element subsets of a 25-element set that covers every 5-element subset
has at least 34 members. That is, `C(25, 15, 5) ≥ 34`. -/
theorem Covering.Palomar.covering_25_15_5_lower_bound (𝒯 : Finset (Finset (Fin 25)))
    (hk : ∀ B ∈ 𝒯, B.card = 15)
    (hcov : ∀ S : Finset (Fin 25), S.card = 5 → ∃ B ∈ 𝒯, S ⊆ B) :
    34 ≤ 𝒯.card := by
  sorry
