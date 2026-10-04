module

public import MatrixFoundation

@[expose] public section

open Matrix Finset
open scoped BigOperators
namespace RowSumFactorization
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
def ones (n m : Type*) : Matrix n m ℝ := fun _ _ => 1

theorem ones_sandwich (M : Matrix n m ℝ) (r : ℝ)
    (hM : ∀ i, ∑ j, M i j = r) :
    M * ones m m * M.transpose = r ^ 2 • ones n n := by
  ext i j
  simp only [Matrix.mul_apply, ones, Matrix.transpose_apply, Matrix.smul_apply,
    smul_eq_mul, mul_one]
  simp only [hM, ← Finset.mul_sum]
  ring

theorem row_sum_factorization (M : Matrix n m ℝ) (r t : ℝ)
    (hM : ∀ i, ∑ j, M i j = r) :
    M * M.transpose - (t * r ^ 2) • ones n n =
      M * (1 - t • ones m m) * M.transpose := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, ones_sandwich M r hM, smul_smul]

theorem six_row_factorization (M : Matrix n (Fin 11) ℝ)
    (hM : ∀ i, ∑ j, M i j = 6) :
    M * M.transpose - (3 : ℝ) • ones n n =
      M * (1 - (1 / 12 : ℝ) • ones (Fin 11) (Fin 11)) * M.transpose := by
  convert row_sum_factorization M 6 (1 / 12) hM using 1 <;> norm_num

theorem six_row_rank_le_eleven (M : Matrix n (Fin 11) ℝ)
    (hM : ∀ i, ∑ j, M i j = 6) :
    (M * M.transpose - (3 : ℝ) • ones n n).rank ≤ 11 := by
  rw [six_row_factorization M hM]
  exact MatrixFoundation.sandwich_rank_le_eleven _ _
end RowSumFactorization
#print axioms RowSumFactorization.ones_sandwich
#print axioms RowSumFactorization.row_sum_factorization
#print axioms RowSumFactorization.six_row_factorization
#print axioms RowSumFactorization.six_row_rank_le_eleven
