module

public import PhysicalIncidenceMatrix
public import QuotientMatrixGraph
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! The actual quotient matrix of an H family, using the canonical physical
incidence adapter and one common physical pairing equivalence. -/
namespace PhysicalQuotientMatrix
open Matrix Finset Covering Covering.PointDegree Covering.SideLift Covering.CrossGrid
open CoveringMatrixIncidence
open Covering.NormalizedBridge20261003.Regular22Incidence
open scoped BigOperators

/-- Every paired value occurs twice in the full physical sum. -/
lemma sum_doubled (e : (Fin 10 × Fin 2) ≃ Fin 20) (f : Fin 20 → ℝ)
    (hp : ∀ i, f (e (i, 0)) = f (e (i, 1))) :
    (∑ p : Fin 20, f p) = 2 * ∑ i : Fin 10, f (e (i, 0)) := by
  rw [← e.sum_comp f]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, ← hp]
  rw [Finset.sum_add_distrib]
  ring

/-- The one canonical representative-incidence constructor; no replacement
family, row deduplication, or alternate incidence definition is introduced. -/
def quotient (H : Family 20) (e : (Fin 10 × Fin 2) ≃ Fin 20) :
    Matrix (Fin H.length) (Fin 10) ℝ :=
  (incidenceOn H (fun i => e (i, 0))).transpose

lemma quotient_apply (H : Family 20) (e : (Fin 10 × Fin 2) ≃ Fin 20)
    (j : Fin H.length) (i : Fin 10) : quotient H e j i = incidence H (e (i, 0)) j := rfl

lemma paired_incidence (H : Family 20) (e : (Fin 10 × Fin 2) ≃ Fin 20)
    (hpair : ∀ i R, R ∈ H → (e (i, 0) ∈ R ↔ e (i, 1) ∈ R))
    (j : Fin H.length) (i : Fin 10) :
    incidence H (e (i, 0)) j = incidence H (e (i, 1)) j := by
  simp only [incidence, hpair i (H.get j) (List.get_mem H j)]

lemma quotient_row_sum (H : Family 20) (e : (Fin 10 × Fin 2) ≃ Fin 20)
    (hrows : ∀ R, R ∈ H → ValidBlock 10 R)
    (hpair : ∀ i R, R ∈ H → (e (i, 0) ∈ R ↔ e (i, 1) ∈ R))
    (j : Fin H.length) : ∑ i, quotient H e j i = 5 := by
  have hd := sum_doubled e (fun p => incidence H p j) (paired_incidence H e hpair j)
  rw [column_sum H hrows j] at hd
  change (10 : ℝ) = 2 * ∑ i, quotient H e j i at hd
  linarith

lemma quotient_col_sum (H : Family 20) (e : (Fin 10 × Fin 2) ≃ Fin 20)
    (hdegree : ∀ p, degree H p = 3) (i : Fin 10) :
    ∑ j, quotient H e j i = 3 := by
  change (∑ j, incidenceOn H (fun u => e (u, 0)) i j) = 3
  rw [restricted_row_sum, hdegree]
  norm_num

/-- The full physical row product counts the actual list intersection. -/
lemma physical_row_product_sum (H : Family 20)
    (hrows : ∀ R, R ∈ H → ValidBlock 10 R) (j k : Fin H.length) :
    (∑ p : Fin 20, incidence H p j * incidence H p k) =
      ((hits (H.get j) (H.get k)).length : ℝ) := by
  have he (p : Fin 20) : incidence H p j * incidence H p k =
      if p ∈ hits (H.get j) (H.get k) then (1 : ℝ) else 0 := by
    simp only [incidence, mem_hits]
    by_cases hj : p ∈ H.get j <;> by_cases hk : p ∈ H.get k <;>
      simp only [List.get_eq_getElem] at hj hk ⊢ <;> simp [hj, hk]
  simp_rw [he]
  exact full_support_count _ (hits_nodup _ _ (hrows _ (List.get_mem H j)).1)

lemma quotient_row_gram_doubled (H : Family 20) (e : (Fin 10 × Fin 2) ≃ Fin 20)
    (hrows : ∀ R, R ∈ H → ValidBlock 10 R)
    (hpair : ∀ i R, R ∈ H → (e (i, 0) ∈ R ↔ e (i, 1) ∈ R))
    (j k : Fin H.length) :
    ((hits (H.get j) (H.get k)).length : ℝ) =
      2 * (quotient H e * (quotient H e).transpose) j k := by
  have hd := sum_doubled e (fun p => incidence H p j * incidence H p k) (by
    intro i
    rw [paired_incidence H e hpair j i, paired_incidence H e hpair k i])
  rw [physical_row_product_sum H hrows j k] at hd
  exact hd

/-- Physical row intersections four become quotient row intersections two. -/
lemma quotient_row_gram (H : Family 20) (e : (Fin 10 × Fin 2) ≃ Fin 20)
    (hrows : ∀ R, R ∈ H → ValidBlock 10 R)
    (hpair : ∀ i R, R ∈ H → (e (i, 0) ∈ R ↔ e (i, 1) ∈ R))
    (hinter : ∀ j k : Fin H.length, j ≠ k → (hits (H.get j) (H.get k)).length = 4) :
    quotient H e * (quotient H e).transpose =
      (3 : ℝ) • (1 : Matrix (Fin H.length) (Fin H.length) ℝ) +
      (2 : ℝ) • QuotientMatrixGraph.ones (Fin H.length) (Fin H.length) := by
  ext j k
  have hd := quotient_row_gram_doubled H e hrows hpair j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    QuotientMatrixGraph.ones]
  by_cases hjk : j = k
  · subst k
    rw [hits_eq_self _ _ (fun p hp => hp), (hrows _ (List.get_mem H j)).2] at hd
    norm_num at hd ⊢
    linarith
  · rw [hinter j k hjk] at hd
    norm_num [hjk] at hd ⊢
    linarith

/-- Quotient point Gram entries remain the codegrees of the selected actual
physical representatives, by the accepted canonical adapter. -/
lemma quotient_point_gram (H : Family 20) (e : (Fin 10 × Fin 2) ≃ Fin 20)
    (u v : Fin 10) : ((quotient H e).transpose * quotient H e) u v =
      (pairDegree H (e (u, 0)) (e (v, 0)) : ℝ) :=
  restricted_gram H (fun i => e (i, 0)) u v

/-- Instantiate every matrixgraph input from actual physical row/point facts. -/
noncomputable def data (H : Family 20) (e : (Fin 10 × Fin 2) ≃ Fin 20)
    (hrows : ∀ R, R ∈ H → ValidBlock 10 R)
    (hdegree : ∀ p, degree H p = 3)
    (hpair : ∀ i R, R ∈ H → (e (i, 0) ∈ R ↔ e (i, 1) ∈ R))
    (hinter : ∀ j k : Fin H.length, j ≠ k → (hits (H.get j) (H.get k)).length = 4)
    (hcodegree : ∀ u v : Fin 10, u ≠ v →
      pairDegree H (e (u, 0)) (e (v, 0)) = 1 ∨ pairDegree H (e (u, 0)) (e (v, 0)) = 2) :
    QuotientMatrixGraph.Data (Fin H.length) where
  C := quotient H e
  row_sum := quotient_row_sum H e hrows hpair
  col_sum := quotient_col_sum H e hdegree
  row_gram := quotient_row_gram H e hrows hpair hinter
  diagonal u := by rw [quotient_point_gram, pair_diagonal, hdegree]; norm_num
  off_diagonal u v huv := by
    rw [quotient_point_gram]
    rcases hcodegree u v huv with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num

lemma representatives_distinct (e : (Fin 10 × Fin 2) ≃ Fin 20)
    {u v : Fin 10} (huv : u ≠ v) : e (u, 0) ≠ e (v, 0) := by
  intro h
  exact huv (congrArg Prod.fst (e.injective h))

lemma representative_not_partner (σ : Fin 20 → Fin 20)
    (e : (Fin 10 × Fin 2) ≃ Fin 20) (he : ∀ i, e (i, 1) = σ (e (i, 0)))
    (u v : Fin 10) : e (v, 0) ≠ σ (e (u, 0)) := by
  intro h
  have hp : (v, (0 : Fin 2)) = (u, 1) := e.injective (h.trans (he u).symm)
  exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd hp)

/-- Direct interface to the actual common physical twin involution. Only one
H family and one paired equivalence e are used throughout the construction. -/
noncomputable def dataOfCoordinates (H : Family 20) (σ : Fin 20 → Fin 20)
    (e : (Fin 10 × Fin 2) ≃ Fin 20) (he : ∀ i, e (i, 1) = σ (e (i, 0)))
    (hrows : ∀ R, R ∈ H → ValidBlock 10 R)
    (hdegree : ∀ p, degree H p = 3)
    (htwins : ∀ p R, R ∈ H → (p ∈ R ↔ σ p ∈ R))
    (hinter : ∀ j k : Fin H.length, j ≠ k → (hits (H.get j) (H.get k)).length = 4)
    (hcodegree : ∀ p q, p ≠ q → q ≠ σ p → pairDegree H p q = 1 ∨ pairDegree H p q = 2) :
    QuotientMatrixGraph.Data (Fin H.length) :=
  data H e hrows hdegree
    (fun i R hR => by rw [he i]; exact htwins (e (i, 0)) R hR)
    hinter (fun u v huv => hcodegree _ _ (representatives_distinct e huv)
      (representative_not_partner σ e he u v))

#print axioms PhysicalQuotientMatrix.sum_doubled
#print axioms PhysicalQuotientMatrix.quotient_apply
#print axioms PhysicalQuotientMatrix.paired_incidence
#print axioms PhysicalQuotientMatrix.quotient_row_sum
#print axioms PhysicalQuotientMatrix.quotient_col_sum
#print axioms PhysicalQuotientMatrix.physical_row_product_sum
#print axioms PhysicalQuotientMatrix.quotient_row_gram_doubled
#print axioms PhysicalQuotientMatrix.quotient_row_gram
#print axioms PhysicalQuotientMatrix.quotient_point_gram
#print axioms PhysicalQuotientMatrix.data
#print axioms PhysicalQuotientMatrix.representatives_distinct
#print axioms PhysicalQuotientMatrix.representative_not_partner
#print axioms PhysicalQuotientMatrix.dataOfCoordinates
end PhysicalQuotientMatrix
