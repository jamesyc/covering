module

public import Covering.Kernel.Gram
public import Covering.Kernel.Regular

@[expose] public section

/-!
# Incidence factorizations

When the Gram matrix factors through an incidence matrix, kernel vectors give balanced columns (equation (11)).
-/

open Matrix Finset
open scoped BigOperators
namespace WeightedKernelComponents.System
open WeightedSignlessKernel
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable (S : System V)

omit [DecidableEq B] in
lemma components_from_incidence (hd : S.d ≠ 0) (c : ℝ) (hc : 0 ≤ c)
    (M : Matrix V B ℝ) (hGram : S.gram c = M * M.transpose) :
    Fintype.card V - Fintype.card B ≤ Nat.card {a // S.BalancedBipartite a} := by
  apply S.balanced_components_of_rank_le hd c hc
  rw [hGram]
  exact (Matrix.rank_mul_le_left _ _).trans M.rank_le_card_width

omit [DecidableEq B] in
lemma incidence_transpose_kernel (hd : S.d ≠ 0) (c : ℝ) (hc : 0 ≤ c)
    (M : Matrix V B ℝ) (hGram : S.gram c = M * M.transpose)
    {x : V → ℝ} (hx : x ∈ S.kernel) : M.transpose *ᵥ x = 0 := by
  have hxG := (S.gram_kernel_iff hd c hc x).mpr hx
  have hxM : x ∈ (M * M.transpose).mulVecLin.ker := by
    change (M * M.transpose) *ᵥ x = 0
    rw [← hGram]
    exact hxG
  change x ∈ M.transpose.mulVecLin.ker
  rw [← Matrix.ker_mulVecLin_transpose_mul_self M.transpose]
  simpa only [Matrix.transpose_transpose] using hxM

omit [DecidableEq B] in
lemma incidence_column_balance (hd : S.d ≠ 0) (c : ℝ) (hc : 0 ≤ c)
    (M : Matrix V B ℝ) (hGram : S.gram c = M * M.transpose)
    {x : V → ℝ} (hx : x ∈ S.kernel) (b : B) : ∑ i, M i b * x i = 0 := by
  have h := congrFun (S.incidence_transpose_kernel hd c hc M hGram hx) b
  simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using h

end WeightedKernelComponents.System
