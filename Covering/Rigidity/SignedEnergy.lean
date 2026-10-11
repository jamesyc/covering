module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Row energy

Lemma 2.2 in arithmetic form: a row of deviations with sum three has energy at most nine, and energy five if it has a negative entry.
-/
open Matrix Finset
open scoped BigOperators
namespace Covering.RowEnergy
/-- The hypotheses of Lemma 2.2: a symmetric array with zero diagonal and row sums
three, in which a negative entry is `-1` and the rest of its row is `0` or `1`. -/
structure SignedData (W : Matrix (Fin 22) (Fin 22) ℝ) : Prop where
  symmetric : ∀ i j, W i j=W j i
  diagonal : ∀ i, W i i=0
  row_sum : ∀ i, ∑ j, W i j=3
  negative_row : ∀ i j, W i j<0 → W i j = -1 ∧
    ∀ k, k≠j → W i k=0 ∨ W i k=1

def energy (W : Matrix (Fin 22) (Fin 22) ℝ) (i : Fin 22) : ℝ :=
  ∑ j, (W i j)^2

lemma negative_energy (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W)
    (i j : Fin 22) (hj : W i j<0) : energy W i=5 := by
  obtain ⟨hj,hh⟩ := h.negative_row i j hj
  have he (k : Fin 22) : (W i k)^2=W i k+(if k=j then 2 else 0) := by
    by_cases hk : k=j
    · subst k; norm_num [hj]
    · rcases hh k hk with hk' | hk' <;> norm_num [hk,hk']
  unfold energy
  simp_rw [he]
  rw [Finset.sum_add_distrib,h.row_sum i]
  norm_num

lemma energy_le_nine (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W)
    (i : Fin 22) : energy W i≤9 := by
  by_cases hn : ∃ j, W i j<0
  · obtain ⟨j,hj⟩ := hn
    rw [negative_energy W h i j hj]
    norm_num
  · have hp : ∀ j, 0≤W i j := fun j => le_of_not_gt (fun hj => hn ⟨j,hj⟩)
    have hh := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := W i)
      (fun j _ => hp j)
    change (∑ j, (W i j)^2)≤9
    calc
      _ ≤ (∑ j, W i j)^2 := hh
      _ = 9 := by rw [h.row_sum i]; norm_num

end Covering.RowEnergy
