module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import SmallCutConnectivity

@[expose] public section

/-! A spectrum-free consumer from concrete quotient H-matrix identities to
an actual cubic graph and its exact common-neighbor conditions. -/
namespace QuotientMatrixGraph
open Matrix Finset SimpleGraph
open scoped BigOperators

def ones (m n : Type*) : Matrix m n ℝ := fun _ _ => 1

structure Data (I : Type*) [Fintype I] [DecidableEq I] where
  C : Matrix I (Fin 10) ℝ
  row_sum : ∀ i, ∑ j, C i j = 5
  col_sum : ∀ j, ∑ i, C i j = 3
  row_gram : C * C.transpose = (3 : ℝ) • (1 : Matrix I I ℝ) + (2 : ℝ) • ones I I
  diagonal : ∀ j, (C.transpose * C) j j = 3
  off_diagonal : ∀ u v, u ≠ v → (C.transpose * C) u v = 1 ∨ (C.transpose * C) u v = 2

namespace Data
variable {I : Type*} [Fintype I] [DecidableEq I] (D : Data I)

def gram : Matrix (Fin 10) (Fin 10) ℝ := D.C.transpose * D.C

def adjacency : Matrix (Fin 10) (Fin 10) ℝ :=
  D.gram - (2 : ℝ) • (1 : Matrix (Fin 10) (Fin 10) ℝ) - ones (Fin 10) (Fin 10)

lemma gram_symmetric (u v : Fin 10) : D.gram u v = D.gram v u := by
  simp only [gram, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma gram_row_sum (u : Fin 10) : ∑ v, D.gram u v = 15 := by
  simp only [gram, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, D.row_sum]
  rw [← Finset.sum_mul, D.col_sum]
  norm_num

lemma ones_sandwich : D.C.transpose * ones I I * D.C =
    (9 : ℝ) • ones (Fin 10) (Fin 10) := by
  ext u v
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ones, Matrix.smul_apply,
    smul_eq_mul, mul_one]
  simp only [D.col_sum, ← Finset.mul_sum]
  norm_num

lemma gram_square : D.gram * D.gram =
    (3 : ℝ) • D.gram + (18 : ℝ) • ones (Fin 10) (Fin 10) := by
  calc
    D.gram * D.gram = D.C.transpose * (D.C * D.C.transpose) * D.C := by
      simp only [gram, Matrix.mul_assoc]
    _ = D.C.transpose * ((3 : ℝ) • (1 : Matrix I I ℝ) + (2 : ℝ) • ones I I) * D.C := by
      rw [D.row_gram]
    _ = (3 : ℝ) • D.gram + (18 : ℝ) • ones (Fin 10) (Fin 10) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one]
      rw [D.ones_sandwich]
      norm_num [gram, smul_smul]

lemma gram_mul_ones : D.gram * ones (Fin 10) (Fin 10) =
    (15 : ℝ) • ones (Fin 10) (Fin 10) := by
  ext u v
  simp [Matrix.mul_apply, ones, D.gram_row_sum]

lemma ones_mul_gram : ones (Fin 10) (Fin 10) * D.gram =
    (15 : ℝ) • ones (Fin 10) (Fin 10) := by
  ext u v
  simp only [Matrix.mul_apply, ones, one_mul, Matrix.smul_apply, smul_eq_mul, mul_one]
  simp_rw [D.gram_symmetric _ v]
  exact D.gram_row_sum v

lemma ones_square : ones (Fin 10) (Fin 10) * ones (Fin 10) (Fin 10) =
    (10 : ℝ) • ones (Fin 10) (Fin 10) := by
  ext u v
  norm_num [Matrix.mul_apply, ones]

/-- The adjacency polynomial comes from Gram multiplication and row sums alone. -/
theorem adjacency_polynomial : D.adjacency * D.adjacency + D.adjacency -
    (2 : ℝ) • (1 : Matrix (Fin 10) (Fin 10) ℝ) = ones (Fin 10) (Fin 10) := by
  simp only [adjacency, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  rw [D.gram_square, D.gram_mul_ones, D.ones_mul_gram, ones_square]
  ext u v
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, ones]
  ring

lemma adjacency_apply (u v : Fin 10) :
    D.adjacency u v = D.gram u v - (if u = v then 2 else 0) - 1 := by
  simp [adjacency, Matrix.one_apply, ones, mul_ite]

lemma adjacency_diagonal (u : Fin 10) : D.adjacency u u = 0 := by
  norm_num [D.adjacency_apply, gram, D.diagonal]

lemma adjacency_row_sum (u : Fin 10) : ∑ v, D.adjacency u v = 3 := by
  simp only [D.adjacency_apply, Finset.sum_sub_distrib]
  rw [D.gram_row_sum]
  norm_num

/-- Zero-one entries, symmetry, and zero diagonal are derived, not supplied. -/
theorem isAdjMatrix : D.adjacency.IsAdjMatrix where
  zero_or_one u v := by
    by_cases huv : u = v
    · subst v; exact Or.inl (D.adjacency_diagonal u)
    · rcases D.off_diagonal u v huv with h | h
      · left; norm_num [D.adjacency_apply, huv, gram, h]
      · right; norm_num [D.adjacency_apply, huv, gram, h]
  symm := by
    ext u v
    simp only [Matrix.transpose_apply, D.adjacency_apply]
    rw [D.gram_symmetric v u]
    simp only [eq_comm]
  apply_diag := D.adjacency_diagonal

/-- The actual simple graph attached to the quotient incidence matrix. -/
def graph : SimpleGraph (Fin 10) := D.isAdjMatrix.toGraph

noncomputable instance graph_decidable : DecidableRel D.graph.Adj := by
  classical
  unfold graph
  infer_instance

lemma graph_adj (u v : Fin 10) : D.graph.Adj u v ↔ D.adjacency u v = 1 := Iff.rfl

/-- The constructed edges are exactly quotient H-codegree two. -/
lemma graph_adj_iff_gram_two (u v : Fin 10) : D.graph.Adj u v ↔ D.gram u v = 2 := by
  rw [D.graph_adj]
  by_cases huv : u = v
  · subst v
    norm_num [D.adjacency_diagonal, gram, D.diagonal]
  · rw [D.adjacency_apply]
    simp only [ite_eq_right huv, sub_zero]
    constructor <;> intro h <;> linarith

lemma graph_adjMatrix : D.graph.adjMatrix ℝ = D.adjacency := by
  classical
  exact D.isAdjMatrix.adjMatrix_toGraph_eq

/-- The constructed graph is cubic. -/
theorem graph_degree (u : Fin 10) : D.graph.degree u = 3 := by
  classical
  have hp := congrArg (fun M : Matrix (Fin 10) (Fin 10) ℝ => M u u) D.adjacency_polynomial
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply_eq, D.adjacency_diagonal, ones] at hp
  have haa : (D.adjacency * D.adjacency) u u = 3 := by linarith
  have hg := D.graph.adjMatrix_mul_self_apply_self (α := ℝ) u
  rw [D.graph_adjMatrix] at hg
  have hdegree : (D.graph.degree u : ℝ) = 3 := hg.symm.trans haa
  exact_mod_cast hdegree

/-- A concrete finite set of common neighbors. -/
noncomputable def common (u v : Fin 10) : Finset (Fin 10) :=
  (D.graph.neighborFinset u).filter (fun w => D.graph.Adj w v)

lemma mem_common (u v w : Fin 10) : w ∈ D.common u v ↔ w ∈ D.graph.commonNeighbors u v := by
  classical
  simp [common, SimpleGraph.mem_commonNeighbors, SimpleGraph.adj_comm]

lemma common_card (u v : Fin 10) :
    ((D.common u v).card : ℝ) = (D.adjacency * D.adjacency) u v := by
  classical
  rw [← D.graph_adjMatrix]
  simp [SimpleGraph.adjMatrix_apply, common]
  congr 1
  ext w
  simp [SimpleGraph.adj_comm, and_comm]

lemma common_card_add_adjacency {u v : Fin 10} (huv : u ≠ v) :
    ((D.common u v).card : ℝ) + D.adjacency u v = 1 := by
  have hp := congrArg (fun M : Matrix (Fin 10) (Fin 10) ℝ => M u v) D.adjacency_polynomial
  simpa only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply_ne huv, mul_zero, sub_zero, ones, ← D.common_card] using hp

/-- Adjacent vertices have no common neighbor. -/
theorem adjacent_common_empty (u v : Fin 10) (huv : D.graph.Adj u v) :
    D.graph.commonNeighbors u v = ∅ := by
  classical
  have hp := D.common_card_add_adjacency huv.ne
  rw [(D.graph_adj u v).mp huv] at hp
  have hc : (D.common u v).card = 0 := by exact_mod_cast (show ((D.common u v).card : ℝ) = 0 by linarith)
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hm := (D.mem_common u v w).mpr hw
  rw [Finset.card_eq_zero.mp hc] at hm
  exact Finset.notMem_empty w hm

/-- Distinct nonadjacent vertices have exactly one common neighbor. -/
theorem nonadjacent_unique_common (u v : Fin 10) (huv : u ≠ v) (hn : ¬D.graph.Adj u v) :
    ∃! w, w ∈ D.graph.commonNeighbors u v := by
  classical
  have haz : D.adjacency u v = 0 := D.isAdjMatrix.apply_ne_one_iff u v |>.mp hn
  have hp := D.common_card_add_adjacency huv
  rw [haz, add_zero] at hp
  have hc : (D.common u v).card = 1 := by exact_mod_cast hp
  have he := Finset.card_eq_one_iff_existsUnique.mp hc
  simpa only [D.mem_common] using he

/-- End-to-end graph consumer: connectivity follows for the constructed graph. -/
theorem graph_connected_delete_two (R : Finset (Fin 10)) (hR : R.card ≤ 2) :
    (D.graph.induce {x | x ∉ R}).Connected :=
  SmallCutConnectivity.cubic_ten_connected_delete_le_two D.graph D.graph_degree
    D.adjacent_common_empty D.nonadjacent_unique_common R hR

#print axioms QuotientMatrixGraph.Data.gram_symmetric
#print axioms QuotientMatrixGraph.Data.gram_row_sum
#print axioms QuotientMatrixGraph.Data.ones_sandwich
#print axioms QuotientMatrixGraph.Data.gram_square
#print axioms QuotientMatrixGraph.Data.gram_mul_ones
#print axioms QuotientMatrixGraph.Data.ones_mul_gram
#print axioms QuotientMatrixGraph.Data.ones_square
#print axioms QuotientMatrixGraph.Data.adjacency_polynomial
#print axioms QuotientMatrixGraph.Data.adjacency_apply
#print axioms QuotientMatrixGraph.Data.adjacency_diagonal
#print axioms QuotientMatrixGraph.Data.adjacency_row_sum
#print axioms QuotientMatrixGraph.Data.isAdjMatrix
#print axioms QuotientMatrixGraph.Data.graph_adj
#print axioms QuotientMatrixGraph.Data.graph_adj_iff_gram_two
#print axioms QuotientMatrixGraph.Data.graph_adjMatrix
#print axioms QuotientMatrixGraph.Data.graph_degree
#print axioms QuotientMatrixGraph.Data.mem_common
#print axioms QuotientMatrixGraph.Data.common_card
#print axioms QuotientMatrixGraph.Data.common_card_add_adjacency
#print axioms QuotientMatrixGraph.Data.adjacent_common_empty
#print axioms QuotientMatrixGraph.Data.nonadjacent_unique_common
#print axioms QuotientMatrixGraph.Data.graph_connected_delete_two
end Data
end QuotientMatrixGraph
