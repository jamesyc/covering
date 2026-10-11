module

public import Covering.Basic.ExcessPatterns
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Degree patterns

With total excess two, either one point has degree thirteen or two points have degree twelve.
-/

open Finset
open scoped BigOperators
namespace Covering.DegreeArithmetic
variable {V : Type*} [Fintype V] [DecidableEq V]

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
  rcases Covering.FiniteExcess.sum_two_pattern e he with ⟨p, hp, hrest⟩ | ⟨p, q, hpq, hp, hq, hrest⟩
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

end Covering.DegreeArithmetic
