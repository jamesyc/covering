import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Prod

/-! Explicit two-point coordinates for a fixed-point-free involution on twenty
physical points. This does not depend on the graph, spectral, or color modules. -/
namespace InvolutionPairCoordinates

/-- Choose the smaller point in each two-point orbit. -/
abbrev Representatives (σ : Fin 20 → Fin 20) := {p : Fin 20 // p < σ p}

/-- The representative has index zero; its partner has index one. -/
def encode (σ : Fin 20 → Fin 20) (x : Representatives σ × Fin 2) : Fin 20 :=
  if x.2 = 0 then x.1 else σ x.1

lemma fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by omega

/-- Involutivity prevents overlap between distinct chosen two-point orbits. -/
lemma encode_injective (σ : Fin 20 → Fin 20) (hinv : Function.Involutive σ) :
    Function.Injective (encode σ) := by
  rintro ⟨p, i⟩ ⟨q, j⟩ h
  rcases fin_two_cases i with rfl | rfl <;>
    rcases fin_two_cases j with rfl | rfl
  · simp only [encode] at h
    exact Prod.ext (Subtype.ext h) rfl
  · simp [encode] at h
    have hp := p.property
    rw [h, hinv] at hp
    exact (lt_asymm q.property hp).elim
  · simp [encode] at h
    have hq := q.property
    rw [← h, hinv] at hq
    exact (lt_asymm p.property hq).elim
  · simp [encode] at h
    exact Prod.ext (Subtype.ext (hinv.injective h)) rfl

/-- Fixed-point-freeness ensures every point belongs to a selected orbit. -/
lemma encode_surjective (σ : Fin 20 → Fin 20) (hinv : Function.Involutive σ)
    (hfree : ∀ p, σ p ≠ p) : Function.Surjective (encode σ) := by
  intro p
  by_cases hp : p < σ p
  · exact ⟨(⟨p, hp⟩, 0), by simp [encode]⟩
  · have hsp : σ p < p := lt_of_le_of_ne (le_of_not_gt hp) (hfree p)
    have hr : σ p < σ (σ p) := by simpa only [hinv p] using hsp
    exact ⟨(⟨σ p, hr⟩, 1), by simp [encode, hinv p]⟩

noncomputable def representativePairs (σ : Fin 20 → Fin 20)
    (hinv : Function.Involutive σ) (hfree : ∀ p, σ p ≠ p) :
    (Representatives σ × Fin 2) ≃ Fin 20 :=
  Equiv.ofBijective (encode σ) ⟨encode_injective σ hinv, encode_surjective σ hinv hfree⟩

/-- Twenty physical points give exactly ten representatives; this is proved
from the explicit bijection, not assumed as a cardinality premise. -/
theorem representatives_card (σ : Fin 20 → Fin 20) (hinv : Function.Involutive σ)
    (hfree : ∀ p, σ p ≠ p) : Fintype.card (Representatives σ) = 10 := by
  have hc : Fintype.card (Representatives σ) * 2 = 20 := by
    simpa using Fintype.card_congr (representativePairs σ hinv hfree)
  omega

/-- A chosen relabeling of the ten two-point orbits by Fin 10. -/
noncomputable def coordinates (σ : Fin 20 → Fin 20)
    (hinv : Function.Involutive σ) (hfree : ∀ p, σ p ≠ p) :
    (Fin 10 × Fin 2) ≃ Fin 20 :=
  (Equiv.prodCongr (Fintype.equivFinOfCardEq (representatives_card σ hinv hfree)).symm
    (Equiv.refl (Fin 2))).trans (representativePairs σ hinv hfree)

/-- The two coordinates in each class are precisely involution partners. -/
theorem coordinates_partner (σ : Fin 20 → Fin 20) (hinv : Function.Involutive σ)
    (hfree : ∀ p, σ p ≠ p) (i : Fin 10) :
    coordinates σ hinv hfree (i, 1) = σ (coordinates σ hinv hfree (i, 0)) := by
  rfl

theorem coordinates_partner_reverse (σ : Fin 20 → Fin 20) (hinv : Function.Involutive σ)
    (hfree : ∀ p, σ p ≠ p) (i : Fin 10) :
    σ (coordinates σ hinv hfree (i, 1)) = coordinates σ hinv hfree (i, 0) := by
  rw [coordinates_partner, hinv]

/-- Exact existential interface for the regular20 physical twin involution. -/
theorem exists_paired_coordinates (σ : Fin 20 → Fin 20) (hinv : Function.Involutive σ)
    (hfree : ∀ p, σ p ≠ p) :
    ∃ e : (Fin 10 × Fin 2) ≃ Fin 20, ∀ i, e (i, 1) = σ (e (i, 0)) :=
  ⟨coordinates σ hinv hfree, coordinates_partner σ hinv hfree⟩

#print axioms InvolutionPairCoordinates.fin_two_cases
#print axioms InvolutionPairCoordinates.encode_injective
#print axioms InvolutionPairCoordinates.encode_surjective
#print axioms InvolutionPairCoordinates.representatives_card
#print axioms InvolutionPairCoordinates.coordinates_partner
#print axioms InvolutionPairCoordinates.coordinates_partner_reverse
#print axioms InvolutionPairCoordinates.exists_paired_coordinates
end InvolutionPairCoordinates
