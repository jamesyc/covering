module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
# Component sizes

Section 5.1: without balanced quadruples the component sizes are one 2 and at least two of size at least 6.
-/

open Finset
open scoped BigOperators
namespace Covering.Components
variable {α : Type*} [DecidableEq α]

lemma classify_components (s : Finset α) (f : α → ℕ) (hcard : 3 ≤ s.card)
    (hmin : ∀ a ∈ s, 2 ≤ f a) (heven : ∀ a ∈ s, Even (f a))
    (htotal : ∑ a ∈ s, f a ≤ 16) :
    (∃ a ∈ s, f a = 4) ∨
    (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ f a = 2 ∧ f b = 2) ∨
    (∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ f a = 2 ∧ 6 ≤ f b ∧ 6 ≤ f c) := by
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
    push Not at hn
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
  have hecard := Finset.card_erase_of_mem ha
  obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.mp
    (show 1 < (s.erase a).card by omega)
  exact Or.inr (Or.inr ⟨a, ha, b, (mem_erase.mp hb).2,
    c, (mem_erase.mp hc).2, Ne.symm (mem_erase.mp hb).1,
    Ne.symm (mem_erase.mp hc).1, hbc, ha2, hrest b hb, hrest c hc⟩)


/-- Section 5.1: once balanced quadruples are excluded, the components consist of
    one of size two and two of size at least six. -/
theorem remaining_component_sizes {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) (hcard : 3 ≤ s.card)
    (hmin : ∀ a ∈ s, 2 ≤ f a) (heven : ∀ a ∈ s, Even (f a))
    (htotal : ∑ a ∈ s, f a ≤ 16)
    (hfour : ¬ ∃ a ∈ s, f a = 4)
    (htwo : ¬ ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ f a = 2 ∧ f b = 2) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ f a = 2 ∧ 6 ≤ f b ∧ 6 ≤ f c := by
  rcases classify_components s f hcard hmin heven htotal with h | h | h
  · exact (hfour h).elim
  · exact (htwo h).elim
  · exact h

end Covering.Components