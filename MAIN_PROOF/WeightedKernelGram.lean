import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import WeightedKernelBalanced
import RowSumFactorization
open Matrix Finset
open scoped BigOperators
namespace WeightedKernelComponents.System
open WeightedSignlessKernel RowSumFactorization
variable {V : Type*} [Fintype V] [DecidableEq V] (S : System V)

lemma Q_posSemidef : S.Q.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change S.Qᴴ = S.Q
    ext i j
    by_cases h : i = j
    · subst j; simp [Q, signless, Matrix.conjTranspose_apply]
    · simp [Q, signless, Matrix.conjTranspose_apply, Matrix.one_apply, h, Ne.symm h,
        S.symmetric]
  · intro x
    simp only [star_trivial, dotProduct]
    rw [Q, energy_identity S.W S.symmetric S.d x]
    apply add_nonneg
    · exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (sub_nonneg.mpr (S.degree_le i)) (sq_nonneg _)
    · apply div_nonneg
      · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (S.nonnegative i j) (sq_nonneg _)
      · norm_num

def gram (c : ℝ) : Matrix V V ℝ := S.Q + c • ones V V

lemma gram_mulVec_apply (c : ℝ) (x : V → ℝ) (i : V) :
    (S.gram c *ᵥ x) i = (S.Q *ᵥ x) i + c * ∑ j, x j := by
  rw [gram, Matrix.add_mulVec, Matrix.smul_mulVec]
  simp [ones, Matrix.mulVec, dotProduct]

lemma gram_kernel_iff (hd : S.d ≠ 0) (c : ℝ) (hc : 0 ≤ c) (x : V → ℝ) :
    S.gram c *ᵥ x = 0 ↔ x ∈ S.kernel := by
  constructor
  · intro hx
    have hz : (∑ i, x i * (S.gram c *ᵥ x) i) = 0 := by rw [hx]; simp
    have he : (∑ i, x i * (S.gram c *ᵥ x) i) =
        (∑ i, x i * (S.Q *ᵥ x) i) + c * (∑ i, x i)^2 := by
      simp_rw [S.gram_mulVec_apply, mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul]
      ring
    rw [he] at hz
    have hn : 0 ≤ ∑ i, x i * (S.Q *ᵥ x) i := by
      simpa [dotProduct] using S.Q_posSemidef.dotProduct_mulVec_nonneg x
    have hp : 0 ≤ c * (∑ i, x i)^2 := mul_nonneg hc (sq_nonneg _)
    have hq : ∑ i, x i * (S.Q *ᵥ x) i = 0 := by linarith
    apply S.Q_posSemidef.dotProduct_mulVec_zero_iff.mp
    simpa [dotProduct] using hq
  · intro hx
    have hz := S.sum_kernel_eq_zero hd hx
    have hq : S.Q *ᵥ x = 0 := hx
    ext i
    rw [S.gram_mulVec_apply, hz, hq]
    simp

lemma gram_kernel_eq (hd : S.d ≠ 0) (c : ℝ) (hc : 0 ≤ c) :
    (S.gram c).mulVecLin.ker = S.kernel := by
  ext x
  exact S.gram_kernel_iff hd c hc x

lemma card_sub_rank_le_balanced_components (hd : S.d ≠ 0) (c : ℝ) (hc : 0 ≤ c) :
    Fintype.card V - (S.gram c).rank ≤ Nat.card {a // S.BalancedBipartite a} := by
  have hr := (S.gram c).mulVecLin.finrank_range_add_finrank_ker
  rw [← Matrix.rank, S.gram_kernel_eq hd c hc, Module.finrank_pi] at hr
  have hb := S.nullity_le_balanced_bipartite_components hd
  omega

lemma balanced_components_of_rank_le (hd : S.d ≠ 0) (c : ℝ) (hc : 0 ≤ c)
    (r : ℕ) (hr : (S.gram c).rank ≤ r) :
    Fintype.card V - r ≤ Nat.card {a // S.BalancedBipartite a} := by
  have h := S.card_sub_rank_le_balanced_components hd c hc
  omega

end WeightedKernelComponents.System
#print axioms WeightedKernelComponents.System.Q_posSemidef
#print axioms WeightedKernelComponents.System.gram_kernel_iff
#print axioms WeightedKernelComponents.System.card_sub_rank_le_balanced_components
#print axioms WeightedKernelComponents.System.balanced_components_of_rank_le
