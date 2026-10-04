import Regular22RankConsequences
import Regular22TwinBalance

open Matrix Finset
open scoped BigOperators
namespace CoveringMatrixRegular22
open Covering Covering.PointDegree Covering.SideLift CoveringMatrixIncidence

lemma row_gram_entry {n : Nat} (F : Family n)
    (hrows : ∀ R, R ∈ F → R.Nodup) (i j : Fin F.length) :
    ((incidence F).transpose*incidence F) i j=
      ((CrossGrid.hits (F.get i) (F.get j)).length : ℝ) := by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,incidence]
  have he (p : Fin n) :
      (if p ∈ F.get i then (1:ℝ) else 0)*(if p ∈ F.get j then 1 else 0)=
      ((if p ∈ F.get i ∧ p ∈ F.get j then 1 else 0 : Nat) : ℝ) := by
    by_cases hi : p ∈ F.get i <;> by_cases hj : p ∈ F.get j <;>
      simp only [List.get_eq_getElem] at hi hj ⊢ <;> simp [hi,hj]
  simp_rw [he]
  rw [fin_nat_sum (fun p : Fin n => if p ∈ F.get i ∧ p ∈ F.get j then 1 else 0)]
  exact_mod_cast Covering.NormalizedBridge20261003.LinearTriples.pair_presence_sum
    (List.finRange n) (F.get i) (F.get j) (List.nodup_finRange n)
    (hrows (F.get i) (List.get_mem F i)) (fun p _ => by simp)

/-- Row intersections obtained from the physical incidence matrix, without a quotient. -/
theorem regular22_row_gram (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (hlen : F.length=11) (hregular : ∀ p, degree F p=6) :
    (incidence F).transpose*incidence F=
      (6:ℝ) • (1 : Matrix (Fin F.length) (Fin F.length) ℝ)+
      (6:ℝ) • RowSumFactorization.ones (Fin F.length) (Fin F.length) := by
  let M := incidence F
  let C : Matrix (Fin F.length) (Fin F.length) ℝ :=
    (6:ℝ) • 1+(6:ℝ) • RowSumFactorization.ones (Fin F.length) (Fin F.length)
  obtain ⟨σ,hne,_,hpair,htwin⟩ := regular22_physical_twins F hrows hcover hlen hregular
  have hMC : M*(M.transpose*M)=M*C := by
    rw [← Matrix.mul_assoc]
    ext p j
    have hsame : M (σ p) j=M p j := by
      change (if σ p ∈ F.get j then (1:ℝ) else 0)=(if p ∈ F.get j then 1 else 0)
      simp only [(htwin p (F.get j) (List.get_mem F j)).symm]
    have hcol : (∑ q, M q j)=12 := by rw [column_sum F hrows j]; norm_num
    have hrow : (∑ k, M p k)=6 := by
      change (∑ k, incidence F p k)=6
      rw [row_sum,hregular]
      norm_num
    have hleft : ((M*M.transpose)*M) p j=6*M p j+36 := by
      change ((M*M.transpose) *ᵥ (fun q => M q j)) p=6*M p j+36
      rw [twin_gram_action F σ hne hpair,hsame,hcol]
      ring
    rw [hleft]
    simp [C,Matrix.mul_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,
      RowSumFactorization.ones,smul_eq_mul,mul_add,mul_ite,Finset.sum_add_distrib,
      ← Finset.sum_mul,hrow]
    ring
  have hinj := physical_column_map_injective F hrows hcover hlen hregular
  ext i j
  have hh : M.mulVecLin (fun k => (M.transpose*M) k j)=M.mulVecLin (fun k => C k j) := by
    ext p
    change (M*(M.transpose*M)) p j=(M*C) p j
    exact congrFun (congrFun hMC p) j
  exact congrFun (hinj hh) i

theorem regular22_row_intersection_six (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (hlen : F.length=11) (hregular : ∀ p, degree F p=6)
    (i j : Fin F.length) (hij : i≠j) : (CrossGrid.hits (F.get i) (F.get j)).length=6 := by
  have h := congrFun (congrFun (regular22_row_gram F hrows hcover hlen hregular) i) j
  rw [row_gram_entry F (fun R hR => (hrows R hR).1) i j] at h
  have hh : ((CrossGrid.hits (F.get i) (F.get j)).length : ℝ)=6 := by
    simpa [Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,hij,
      RowSumFactorization.ones] using h
  exact_mod_cast hh

#print axioms regular22_row_gram
#print axioms regular22_row_intersection_six
end CoveringMatrixRegular22
