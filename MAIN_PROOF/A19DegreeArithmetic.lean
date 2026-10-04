import MatrixFoundation
open Finset
open scoped BigOperators
namespace A19DegreeArithmetic
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite natural excess budget of two has exactly the two possible patterns. -/
theorem sum_two_pattern (e : V → ℕ) (he : ∑ i, e i = 2) :
    (∃ p, e p = 2 ∧ ∀ q, q ≠ p → e q = 0) ∨
    (∃ p q, p ≠ q ∧ e p = 1 ∧ e q = 1 ∧ ∀ r, r ≠ p → r ≠ q → e r = 0) := by
  classical
  have hle : ∀ i, e i ≤ 2 := by
    intro i
    have h := Finset.single_le_sum (fun j (_ : j ∈ (univ : Finset V)) => Nat.zero_le (e j))
      (mem_univ i)
    simpa [he] using h
  by_cases htwo : ∃ p, e p = 2
  · left
    obtain ⟨p, hp⟩ := htwo
    refine ⟨p, hp, ?_⟩
    have hs := (univ : Finset V).sum_erase_add e (mem_univ p)
    have hz : ∑ i ∈ univ.erase p, e i = 0 := by omega
    intro q hq
    have hqmem : q ∈ (univ : Finset V).erase p := by simp [hq]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le (e i))).mp hz q hqmem
  · have hsmall : ∀ i, e i = 0 ∨ e i = 1 := by
      intro i
      have hi := hle i
      have hn : e i ≠ 2 := fun h => htwo ⟨i, h⟩
      omega
    let s := univ.filter (fun i => e i = 1)
    have hcard : s.card = 2 := by
      calc
        s.card = ∑ i, if e i = 1 then 1 else 0 := by simp [s]
        _ = ∑ i, e i := by
          apply Finset.sum_congr rfl
          intro i _
          rcases hsmall i with h | h <;> simp [h]
        _ = 2 := he
    obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp hcard
    have hsiff : ∀ i, e i = 1 ↔ i = p ∨ i = q := by
      intro i
      have hmem : i ∈ s ↔ i = p ∨ i = q := by rw [hs]; simp
      simpa [s] using hmem
    right
    refine ⟨p, q, hpq, (hsiff p).mpr (Or.inl rfl), (hsiff q).mpr (Or.inr rfl), ?_⟩
    intro r hrp hrq
    rcases hsmall r with h | h
    · exact h
    · exact False.elim ((hsiff r).mp h |>.elim hrp hrq)

theorem degree_patterns (D : Fin 24 → ℕ) (hfloor : ∀ p, 11 ≤ D p)
    (htotal : ∑ p, D p = 266) :
    (∃ p, D p = 13 ∧ ∀ q, q ≠ p → D q = 11) ∨
    (∃ p q, p ≠ q ∧ D p = 12 ∧ D q = 12 ∧
      ∀ r, r ≠ p → r ≠ q → D r = 11) := by
  let e := fun p => D p - 11
  have hpoint : ∀ p, e p + 11 = D p := fun p => Nat.sub_add_cancel (hfloor p)
  have hsum : (∑ p, e p) + 264 = 266 := by
    have h := Finset.sum_congr rfl (fun p (_ : p ∈ (univ : Finset (Fin 24))) => hpoint p)
    simpa [Finset.sum_add_distrib, htotal] using h
  have he : ∑ p, e p = 2 := by omega
  rcases sum_two_pattern e he with ⟨p, hp, hrest⟩ | ⟨p, q, hpq, hp, hq, hrest⟩
  · left
    refine ⟨p, ?_, ?_⟩
    · have h := hpoint p; omega
    · intro q hq
      have h := hpoint q
      have hz := hrest q hq
      omega
  · right
    refine ⟨p, q, hpq, ?_, ?_, ?_⟩
    · have h := hpoint p; omega
    · have h := hpoint q; omega
    · intro r hrp hrq
      have h := hpoint r
      have hz := hrest r hrp hrq
      omega

end A19DegreeArithmetic
#print axioms A19DegreeArithmetic.sum_two_pattern
#print axioms A19DegreeArithmetic.degree_patterns
