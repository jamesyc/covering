import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import FormalResume20261003.Regular22TwoProviderV1

open Matrix Finset
open scoped BigOperators

set_option autoImplicit false

namespace CoveringMatrixIncidence

variable {α V : Type*}

open Covering Covering.PointDegree Covering.SideLift

/-- Each column is one actual row slot; no deduplication or witness replacement. -/
def incidence {n : Nat} (F : Family n) : Matrix (Fin n) (Fin F.length) ℝ :=
  fun p j => if p ∈ F.get j then 1 else 0

lemma sum_get (L : List α) (f : α → ℝ) :
    (∑ j : Fin L.length, f (L.get j))=(L.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map L f

lemma indicator_count (L : List α) (P : α → Prop) [DecidablePred P] :
    (L.map (fun a => if P a then (1:ℝ) else 0)).sum=(L.filter P).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases ha : P a <;> simp [ha,ih,add_comm]

lemma row_sum {n : Nat} (F : Family n) (p : Fin n) :
    (∑ j, incidence F p j)=(degree F p : ℝ) := by
  unfold incidence
  rw [sum_get F (fun R : Block n => if p ∈ R then (1:ℝ) else 0),indicator_count]
  rfl

lemma gram_entry {n : Nat} (F : Family n) (p q : Fin n) :
    (incidence F*(incidence F).transpose) p q=(pairDegree F p q : ℝ) := by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,incidence]
  have he (R : Block n) :
      (if p ∈ R then (1:ℝ) else 0)*(if q ∈ R then 1 else 0)=
      if p ∈ R ∧ q ∈ R then 1 else 0 := by
    by_cases hp : p ∈ R <;> by_cases hq : q ∈ R <;> simp [hp,hq]
  simp_rw [he]
  rw [sum_get F (fun R : Block n => if p ∈ R ∧ q ∈ R then (1:ℝ) else 0),indicator_count]
  rfl

lemma full_support_count {n : Nat} (R : Block n) (hR : R.Nodup) :
    (∑ p : Fin n, if p ∈ R then (1:ℝ) else 0)=R.length := by
  rw [Fin.sum_univ_def,indicator_count]
  have hh := Covering.NormalizedBridge20261003.LinearTriples.supported_hits_length
    (List.finRange n) R (List.nodup_finRange n) hR (fun p _ => by simp)
  exact_mod_cast hh

lemma column_sum {n k : Nat} (F : Family n)
    (hrows : ∀ R, R ∈ F → ValidBlock k R) (j : Fin F.length) :
    (∑ p, incidence F p j)=(k : ℝ) := by
  have hv := hrows (F.get j) (List.get_mem F j)
  unfold incidence
  rw [full_support_count (F.get j) hv.1,hv.2]

lemma fin_nat_sum {n : Nat} (f : Fin n → Nat) :
    (∑ p, (f p : ℝ))=(((List.finRange n).map f).sum : ℝ) := by
  exact_mod_cast Fin.sum_univ_def f

/-- Actual point restriction, used for the degree-eleven low-point subtype. -/
def incidenceOn {n : Nat} (F : Family n) (e : V → Fin n) : Matrix V (Fin F.length) ℝ :=
  (incidence F).submatrix e id

lemma restricted_row_sum {n : Nat} (F : Family n) (e : V → Fin n) (p : V) :
    (∑ j, incidenceOn F e p j)=(degree F (e p) : ℝ) :=
  row_sum F (e p)

lemma restricted_gram {n : Nat} (F : Family n) (e : V → Fin n) (p q : V) :
    (incidenceOn F e*(incidenceOn F e).transpose) p q=(pairDegree F (e p) (e q) : ℝ) :=
  gram_entry F (e p) (e q)

#print axioms row_sum
#print axioms gram_entry
#print axioms column_sum
#print axioms restricted_gram

end CoveringMatrixIncidence
