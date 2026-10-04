import ProviderSides
open Matrix Finset
open scoped BigOperators
namespace Covering.NormalizedBridge20261003.ExceptionBranch
open PointDegree SideLift CrossGrid OmissionSlots

lemma not_partner_of_sign (σ : Fin 22 → Fin 22) (z : Fin 22 → ℝ)
    (ha : ∀ p, z (σ p) = -z p) (p q : Fin 22) (hp : z p = 1)
    (hq : z q = 0 ∨ z q = 1) : q ≠ σ p := by
  intro h
  have hh := ha p
  rw [← h, hp] at hh
  rcases hq with hq | hq <;> rw [hq] at hh <;> norm_num at hh

lemma positive_side_forbids_partner (σ : Fin 22 → Fin 22) (A B C : Block 22)
    (hAB : Covering.Disjoint A B) (hABC : Covering.Disjoint (A ++ B) C)
    (ha : ∀ p, signedVector A B (σ p) = -signedVector A B p)
    (p : Fin 22) (hp : p ∈ A) (q : Fin 22) (hq : q ∈ A ++ C) : q ≠ σ p := by
  have hpB : p ∉ B := hAB p hp
  apply not_partner_of_sign σ (signedVector A B) ha p q
  · simp [signedVector, hp, hpB]
  · rcases List.mem_append.mp hq with hqA | hqC
    · right
      have hqB : q ∉ B := hAB q hqA
      simp [signedVector, hqA, hqB]
    · left
      have hqA : q ∉ A := fun h => hABC q (List.mem_append.mpr (Or.inl h)) hqC
      have hqB : q ∉ B := fun h => hABC q (List.mem_append.mpr (Or.inr h)) hqC
      simp [signedVector, hqA, hqB]

lemma balanced_sides_obstruction (F R : Family 22) (hlen : R.length = 8)
    (σ : Fin 22 → Fin 22)
    (hpairF : ∀ p q, pairDegree F p q = if p = q ∨ q = σ p then 6 else 3)
    (hanti : ∀ z : Fin 22 → ℝ,
      (CoveringMatrixIncidence.incidence F).transpose *ᵥ z = 0 → ∀ p, z (σ p) = -z p)
    (A B C D : Block 22) (hA : A.Nodup) (hC : C.Nodup)
    (hAlen : 3 ≤ A.length) (hClen : 3 ≤ C.length)
    (hAB : Covering.Disjoint A B) (hCD : Covering.Disjoint C D)
    (hcross : Covering.Disjoint (A ++ B) (C ++ D))
    (hkAB : (CoveringMatrixIncidence.incidence F).transpose *ᵥ signedVector A B = 0)
    (hkCD : (CoveringMatrixIncidence.incidence F).transpose *ᵥ signedVector C D = 0)
    (high : Fin 22) (hh : degree R high = 6)
    (hnot : high ∉ (A ++ B) ++ (C ++ D))
    (hdegree : ∀ p, p ∈ A ++ C → degree R p = 5)
    (hsumPair : ∀ p, p ∈ A ++ C → ∀ q, q ∈ A ++ C → p ≠ q →
      pairDegree F p q + pairDegree R p q = 6)
    (hsumHigh : ∀ p, p ∈ A ++ C → pairDegree F p high + pairDegree R p high = 6) : False := by
  have hantA := hanti (signedVector A B) hkAB
  have hantC := hanti (signedVector C D) hkCD
  have hAC : Covering.Disjoint A C := fun p hp hq =>
    hcross p (List.mem_append.mpr (Or.inl hp)) (List.mem_append.mpr (Or.inl hq))
  have hABC : Covering.Disjoint (A ++ B) C :=
    fun p hp hq => hcross p hp (List.mem_append.mpr (Or.inl hq))
  have hCDA : Covering.Disjoint (C ++ D) A :=
    fun p hp hq => hcross p (List.mem_append.mpr (Or.inl hq)) hp
  have hforbid : ∀ p, p ∈ A ++ C → ∀ q, q ∈ A ++ C → q ≠ σ p := by
    intro p hp q hq
    rcases List.mem_append.mp hp with hpA | hpC
    · exact positive_side_forbids_partner σ A B C hAB hABC hantA p hpA q hq
    · have hq' : q ∈ C ++ A := by simpa [List.mem_append, or_comm] using hq
      exact positive_side_forbids_partner σ C D A hCD hCDA hantC p hpC q hq'
  have hhiA : high ∉ A := fun h => hnot (List.mem_append.mpr (Or.inl
    (List.mem_append.mpr (Or.inl h))))
  have hhiB : high ∉ B := fun h => hnot (List.mem_append.mpr (Or.inl
    (List.mem_append.mpr (Or.inr h))))
  have hhiC : high ∉ C := fun h => hnot (List.mem_append.mpr (Or.inr
    (List.mem_append.mpr (Or.inl h))))
  have hhiD : high ∉ D := fun h => hnot (List.mem_append.mpr (Or.inr
    (List.mem_append.mpr (Or.inr h))))
  have hforbidHigh : ∀ p, p ∈ A ++ C → high ≠ σ p := by
    intro p hp
    rcases List.mem_append.mp hp with hpA | hpC
    · apply not_partner_of_sign σ (signedVector A B) hantA p high
      · have hpB : p ∉ B := hAB p hpA
        simp [signedVector, hpA, hpB]
      · left; simp [signedVector, hhiA, hhiB]
    · apply not_partner_of_sign σ (signedVector C D) hantC p high
      · have hpD : p ∉ D := hCD p hpC
        simp [signedVector, hpC, hpD]
      · left; simp [signedVector, hhiC, hhiD]
  have hn : (A ++ C).Nodup := List.nodup_append.mpr ⟨hA, hC, by
    intro x hx y hy hxy
    subst y
    exact hAC x hx hy⟩
  let S := (A ++ C).toFinset
  have hScard : 6 ≤ S.card := by
    rw [show S = (A ++ C).toFinset from rfl, List.toFinset_card_of_nodup hn, List.length_append]
    omega
  apply OmissionSlots.eight_slot_obstruction R hlen S hScard high hh
  · intro p hp
    exact hdegree p (List.mem_toFinset.mp hp)
  · intro p hp q hq hpq
    have hp' := List.mem_toFinset.mp hp
    have hq' := List.mem_toFinset.mp hq
    have hf : pairDegree F p q = 3 := by
      rw [hpairF, if_neg (not_or.mpr ⟨hpq, hforbid p hp' q hq'⟩)]
    have hs := hsumPair p hp' q hq' hpq
    omega
  · intro p hp
    have hp' := List.mem_toFinset.mp hp
    have hph : p ≠ high := by
      intro h; subst p
      rcases List.mem_append.mp hp' with ha | hc
      · exact hhiA ha
      · exact hhiC hc
    have hf : pairDegree F p high = 3 := by
      rw [hpairF, if_neg (not_or.mpr ⟨hph, hforbidHigh p hp'⟩)]
    have hs := hsumHigh p hp'
    omega

end Covering.NormalizedBridge20261003.ExceptionBranch
#print axioms Covering.NormalizedBridge20261003.ExceptionBranch.balanced_sides_obstruction
