module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

open Matrix Finset
open scoped BigOperators
namespace MatrixFoundation
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem trace_square_eigenvalues (K : Matrix n n ℝ) (hK : K.IsHermitian) :
    (K * K).trace = ∑ i, (hK.eigenvalues i)^2 := by
  conv_lhs => rw [hK.spectral_theorem, ← map_mul]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    one_mul, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp [pow_two]

theorem trace_sq_le_rank_mul_trace_square (K : Matrix n n ℝ) (hK : K.IsHermitian) :
    K.trace ^ 2 ≤ (K.rank : ℝ) * (K * K).trace := by
  classical
  let s : Finset n := univ.filter (fun i => hK.eigenvalues i ≠ 0)
  have hs : (∑ i ∈ s, hK.eigenvalues i) = ∑ i, hK.eigenvalues i := by
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with h <;> simp_all
  have hs2 : (∑ i ∈ s, (hK.eigenvalues i)^2) = ∑ i, (hK.eigenvalues i)^2 := by
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with h <;> simp_all
  have hr : K.rank = s.card := by
    rw [hK.rank_eq_card_non_zero_eigs]
    simp [s, Fintype.card_subtype]
  have ht : K.trace = ∑ i, hK.eigenvalues i := by simpa using hK.trace_eq_sum_eigenvalues
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) hK.eigenvalues
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hs, hs2,
    ← ht, ← hr, ← trace_square_eigenvalues K hK] using hc

theorem trace_square_ge_396 (K : Matrix n n ℝ) (hK : K.IsHermitian)
    (ht : K.trace = 66) (hr : K.rank ≤ 11) : 396 ≤ (K * K).trace := by
  have hc := trace_sq_le_rank_mul_trace_square K hK
  have hn : 0 ≤ (K * K).trace := by
    rw [trace_square_eigenvalues K hK]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hr' : (K.rank : ℝ) ≤ 11 := by exact_mod_cast hr
  have hm := mul_le_mul_of_nonneg_right hr' hn
  rw [ht] at hc
  linarith

theorem sandwich_rank_le_eleven (M : Matrix n (Fin 11) ℝ)
    (H : Matrix (Fin 11) (Fin 11) ℝ) : (M * H * M.transpose).rank ≤ 11 := by
  exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)).trans M.rank_le_card_width

end MatrixFoundation

#print axioms MatrixFoundation.trace_square_eigenvalues
#print axioms MatrixFoundation.trace_sq_le_rank_mul_trace_square

#print axioms MatrixFoundation.trace_square_ge_396
#print axioms MatrixFoundation.sandwich_rank_le_eleven
