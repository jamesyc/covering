module

public import WeightedComponentSupports

@[expose] public section

open Finset
open scoped BigOperators
namespace ComponentOrderDichotomy
variable {α : Type*} [DecidableEq α]

lemma classify (s : Finset α) (f : α → ℕ) (hcard : 3 ≤ s.card)
    (hmin : ∀ a ∈ s, 2 ≤ f a) (heven : ∀ a ∈ s, Even (f a))
    (htotal : ∑ a ∈ s, f a ≤ 16) :
    (∃ a ∈ s, f a = 4) ∨
    (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ f a = 2 ∧ f b = 2) ∨
    (∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ s = {a, b, c} ∧
      f a = 2 ∧ f b = 6 ∧ (f c = 6 ∨ f c = 8)) := by
  classical
  by_cases hfour : ∃ a ∈ s, f a = 4
  · exact Or.inl hfour
  by_cases htwo : ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ f a = 2 ∧ f b = 2
  · exact Or.inr (Or.inl htwo)
  have hlarge : ∀ a ∈ s, f a ≠ 2 → 6 ≤ f a := by
    intro a ha hn
    have hlo := hmin a ha
    have h4 : f a ≠ 4 := fun h => hfour ⟨a, ha, h⟩
    obtain ⟨k, hk⟩ := heven a ha
    omega
  have ha : ∃ a ∈ s, f a = 2 := by
    by_contra hn
    push_neg at hn
    have hge : (∑ _a ∈ s, (6 : ℕ)) ≤ ∑ a ∈ s, f a :=
      Finset.sum_le_sum (fun a ha => hlarge a ha (hn a ha))
    simp at hge
    omega
  obtain ⟨a, ha, ha2⟩ := ha
  have hrest : ∀ b ∈ s.erase a, 6 ≤ f b := by
    intro b hb
    have hbs := (mem_erase.mp hb).2
    have hba := (mem_erase.mp hb).1
    apply hlarge b hbs
    intro hb2
    exact htwo ⟨a, ha, b, hbs, Ne.symm hba, ha2, hb2⟩
  have hsum := s.sum_erase_add f ha
  have ht : (∑ b ∈ s.erase a, f b) + 2 ≤ 16 := by
    rw [← ha2, hsum]
    exact htotal
  have hge : (∑ _b ∈ s.erase a, (6 : ℕ)) ≤ ∑ b ∈ s.erase a, f b :=
    Finset.sum_le_sum hrest
  simp at hge
  have hecard := Finset.card_erase_of_mem ha
  have hcard2 : (s.erase a).card = 2 := by omega
  obtain ⟨b, c, hbc, hpair⟩ := Finset.card_eq_two.mp hcard2
  have hb : b ∈ s.erase a := by rw [hpair]; simp
  have hc : c ∈ s.erase a := by rw [hpair]; simp
  have hba := (mem_erase.mp hb).1
  have hca := (mem_erase.mp hc).1
  have hb6 := hrest b hb
  have hc6 := hrest c hc
  obtain ⟨k, hk⟩ := heven b (mem_erase.mp hb).2
  obtain ⟨l, hl⟩ := heven c (mem_erase.mp hc).2
  rw [hpair, Finset.sum_pair hbc] at ht
  have hs : s = {a, b, c} := by
    have h := Finset.insert_erase ha
    rw [hpair] at h
    exact h.symm
  have hbsize : f b = 6 ∨ f b = 8 := by omega
  have hcsize : f c = 6 ∨ f c = 8 := by omega
  right; right
  rcases hbsize with hbEq | hbEq
  · exact ⟨a, b, c, Ne.symm hba, Ne.symm hca, hbc, hs, ha2, hbEq, hcsize⟩
  · have hcEq : f c = 6 := by omega
    refine ⟨a, c, b, Ne.symm hca, Ne.symm hba, Ne.symm hbc, ?_, ha2, hcEq, Or.inr hbEq⟩
    simpa only [Finset.pair_comm b c] using hs

end ComponentOrderDichotomy
#print axioms ComponentOrderDichotomy.classify
