import A19PhysicalCounts
open Finset
open scoped BigOperators
namespace Covering.NormalizedBridge20261003.A19Physical
open PointDegree

lemma low_card_one_high (T : Family 24) (p : Fin 24) (hp : degree T p = 13)
    (hrest : ∀ q, q ≠ p → degree T q = 11) : Fintype.card (LowPoint T) = 23 := by
  classical
  have hi : ∀ q, degree T q = 11 ↔ q ≠ p := by
    intro q
    constructor
    · intro h hqp
      subst q
      omega
    · exact hrest q
  have hf : (univ.filter fun q => degree T q = 11) = univ.erase p := by
    ext q; simp [hi]
  simp [LowPoint, Fintype.card_subtype, hf]

lemma low_card_two_high (T : Family 24) (p q : Fin 24) (hpq : p ≠ q)
    (hp : degree T p = 12) (hq : degree T q = 12)
    (hrest : ∀ r, r ≠ p → r ≠ q → degree T r = 11) : Fintype.card (LowPoint T) = 22 := by
  classical
  have hi : ∀ r, degree T r = 11 ↔ r ≠ p ∧ r ≠ q := by
    intro r
    constructor
    · intro h
      constructor
      · intro hr; subst r; omega
      · intro hr; subst r; omega
    · rintro ⟨hrp, hrq⟩
      exact hrest r hrp hrq
  have hf : (univ.filter fun r => degree T r = 11) = (univ.erase p).erase q := by
    ext r; simp [hi, and_comm]
  simp [LowPoint, Fintype.card_subtype, hf, hpq, Ne.symm hpq]

lemma low_card_cases (T : Family 24) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (hcover : IsCovering 4 T) (hlen : T.length = 19) :
    Fintype.card (LowPoint T) = 23 ∨ Fintype.card (LowPoint T) = 22 := by
  rcases degree_patterns T hrows hcover hlen with ⟨p, hp, hrest⟩ | ⟨p, q, hpq, hp, hq, hrest⟩
  · exact Or.inl (low_card_one_high T p hp hrest)
  · exact Or.inr (low_card_two_high T p q hpq hp hq hrest)

end Covering.NormalizedBridge20261003.A19Physical
#print axioms Covering.NormalizedBridge20261003.A19Physical.low_card_one_high
#print axioms Covering.NormalizedBridge20261003.A19Physical.low_card_two_high
#print axioms Covering.NormalizedBridge20261003.A19Physical.low_card_cases
