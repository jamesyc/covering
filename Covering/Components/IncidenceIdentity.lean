module

public import Covering.Kernel.Gram

@[expose] public section

/-!
# The incidence-vector identity

Equation (8). The squared norm is written as a sum of squared coordinates.
The double sum runs over ordered pairs and is halved, which equals the paper's
sum over unordered pairs because the weights are symmetric with zero diagonal.
-/

open Matrix Finset
open scoped BigOperators

namespace Covering.Nineteen
open WeightedSignlessKernel WeightedKernelComponents

variable {V B : Type*} [Fintype V] [DecidableEq V]
    [Fintype B] [DecidableEq B]

/-- Combine the rank-one term with the signless energy identity. -/
theorem gram_energy (S : System V) (c : ℝ) (a : V → ℝ) :
    (∑ p, a p * (S.gram c *ᵥ a) p) =
      c * (∑ p, a p) ^ 2 +
      (∑ p, (S.d - rowSum S.W p) * a p ^ 2) +
      (∑ p, ∑ q, S.W p q * (a p + a q) ^ 2) / 2 := by
  have hg : (∑ p, a p * (S.gram c *ᵥ a) p) =
      (∑ p, a p * (S.Q *ᵥ a) p) + c * (∑ p, a p) ^ 2 := by
    simp_rw [S.gram_mulVec_apply, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul]
    ring
  rw [hg, System.Q, energy_identity S.W S.symmetric S.d a]
  ring

omit [DecidableEq V] [DecidableEq B] in
/-- A coordinate double count identifies a squared norm with its Gram form. -/
theorem coordinate_gram_identity (M : Matrix V B ℝ) (a : V → ℝ) :
    (∑ b, (∑ p, M p b * a p) ^ 2) =
      ∑ p, a p * ((M * M.transpose) *ᵥ a) p := by
  simp only [Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply, dotProduct]
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro b _
  ring

omit [DecidableEq B] in
/-- The paper's single incidence-vector identity, with general constants. -/
theorem incidence_vector_energy (S : System V) (c : ℝ)
    (M : Matrix V B ℝ) (hGram : S.gram c = M * M.transpose) (a : V → ℝ) :
    (∑ b, (∑ p, M p b * a p) ^ 2) =
      c * (∑ p, a p) ^ 2 +
      (∑ p, (S.d - rowSum S.W p) * a p ^ 2) +
      (∑ p, ∑ q, S.W p q * (a p + a q) ^ 2) / 2 := by
  rw [coordinate_gram_identity, ← hGram]
  exact gram_energy S c a

omit [DecidableEq B] in
/-- Specialization to the low-point excess five and baseline codegree six. -/
theorem low_incidence_energy (S : System V) (hd : S.d = 5)
    (M : Matrix V B ℝ) (hGram : S.gram 6 = M * M.transpose) (a : V → ℝ) :
    (∑ b, (∑ p, M p b * a p) ^ 2) =
      6 * (∑ p, a p) ^ 2 +
      (∑ p, (5 - rowSum S.W p) * a p ^ 2) +
      (∑ p, ∑ q, S.W p q * (a p + a q) ^ 2) / 2 := by
  simpa only [hd] using incidence_vector_energy S 6 M hGram a

end Covering.Nineteen