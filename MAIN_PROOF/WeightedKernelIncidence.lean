module

public import WeightedKernelGram
public import WeightedKernelClassification

@[expose] public section

open Matrix Finset
open scoped BigOperators
namespace WeightedKernelComponents.System
open WeightedSignlessKernel
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable (S : System V)

lemma components_from_incidence (hd : S.d ≠ 0) (c : ℝ) (hc : 0 ≤ c)
    (M : Matrix V B ℝ) (hGram : S.gram c = M * M.transpose) :
    Fintype.card V - Fintype.card B ≤ Nat.card {a // S.BalancedBipartite a} := by
  apply S.balanced_components_of_rank_le hd c hc
  rw [hGram]
  exact (Matrix.rank_mul_le_left _ _).trans M.rank_le_card_width

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

lemma incidence_column_balance (hd : S.d ≠ 0) (c : ℝ) (hc : 0 ≤ c)
    (M : Matrix V B ℝ) (hGram : S.gram c = M * M.transpose)
    {x : V → ℝ} (hx : x ∈ S.kernel) (b : B) : ∑ i, M i b * x i = 0 := by
  have h := congrFun (S.incidence_transpose_kernel hd c hc M hGram hx) b
  simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using h

lemma zero_outside_of_full_sum {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℝ) (ha : ∀ i, 0 ≤ a i) (s : Finset P)
    (hs : ∑ i ∈ s, a i = ∑ i, a i) {j : P} (hj : j ∉ s) : a j = 0 := by
  have hsplit := s.sum_add_sum_compl a
  have hzero : (∑ i ∈ sᶜ, a i) = 0 := by linarith
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).mp hzero j
    (Finset.mem_compl.mpr hj)

open scoped Classical in
lemma distinct_component_supports_disjoint {a b : S.graph.ConnectedComponent} (h : a ≠ b) :
    Disjoint (univ.filter fun i => S.graph.connectedComponentMk i = a)
      (univ.filter fun i => S.graph.connectedComponentMk i = b) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact h (hi.symm.trans hj)

end WeightedKernelComponents.System
#print axioms WeightedKernelComponents.System.components_from_incidence
#print axioms WeightedKernelComponents.System.incidence_transpose_kernel
#print axioms WeightedKernelComponents.System.incidence_column_balance
#print axioms WeightedKernelComponents.System.zero_outside_of_full_sum
#print axioms WeightedKernelComponents.System.distinct_component_supports_disjoint
