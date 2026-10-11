module

public import Covering.Components.IncidenceIdentity
public import Covering.Quadruple.NoQuadruple
public import Covering.Remaining.Exclusion
public import Covering.Bounds
public import Covering.Finset

@[expose] public section

/-!
# Main theorems

`covering_24_14_4` and `covering_25_15_5` state Theorem 1.1 and Corollary 5.2 for
ordinary families of finite sets. They assume only the block size and the
covering property.
-/

open Finset
open scoped BigOperators

namespace Covering
open Remaining Bounds Quadruple

/-- No `(24,14,4)` cover has exactly nineteen blocks. -/
theorem exact_nineteen_excluded : ExactNineteenExcluded := by
  intro T hr hc hlen
  obtain ⟨g⟩ := exists_balanced_quadruple T hr hc hlen
  exact no_balanced_quadruple T hr hc hlen g

/-- Indexed-family version: repeated blocks are allowed. -/
theorem indexed_C24_14_4 (T : Family 24)
    (hr : ∀ R, R ∈ T → ValidBlock 14 R) (hc : IsCovering 4 T) :
    20 ≤ T.length :=
  c24_lower_twenty exact_nineteen_excluded T hr hc

/-- The 25-point bound follows by taking one-point derivatives. -/
theorem indexed_C25_15_5 (T : Family 25)
    (hr : ∀ R, R ∈ T → ValidBlock 15 R) (hc : IsCovering 5 T) :
    34 ≤ T.length :=
  c25_lower_thirty_four exact_nineteen_excluded T hr hc

/-- Main theorem, in the usual finite-set formulation. -/
theorem covering_24_14_4 (𝒯 : Finset (Finset (Fin 24)))
    (hk : ∀ B ∈ 𝒯, B.card = 14)
    (hcov : ∀ S : Finset (Fin 24), S.card = 4 → ∃ B ∈ 𝒯, S ⊆ B) :
    20 ≤ 𝒯.card :=
  Covering.finset_lower_bound indexed_C24_14_4 𝒯 hk hcov

/-- The paper's corollary, in the usual finite-set formulation. -/
theorem covering_25_15_5 (𝒯 : Finset (Finset (Fin 25)))
    (hk : ∀ B ∈ 𝒯, B.card = 15)
    (hcov : ∀ S : Finset (Fin 25), S.card = 5 → ∃ B ∈ 𝒯, S ⊆ B) :
    34 ≤ 𝒯.card :=
  Covering.finset_lower_bound indexed_C25_15_5 𝒯 hk hcov

#print axioms covering_24_14_4
#print axioms covering_25_15_5

end Covering