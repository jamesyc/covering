import MatrixFoundation
import Mathlib.Algebra.BigOperators.Fin
import A19PhysicalFloors
import A19DegreeArithmetic
open Finset
open scoped BigOperators
namespace Covering.NormalizedBridge20261003.A19Physical
open PointDegree SideLift CrossGrid TwinCap.CliqueIncidence

lemma fin_sum_eq_list_sum {n : ℕ} (f : Fin n → ℕ) :
    (∑ p, f p) = ((List.finRange n).map f).sum := by
  exact Fin.sum_univ_def f

lemma total_degree (T : Family 24) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (hlen : T.length = 19) : ∑ p, degree T p = 266 := by
  rw [fin_sum_eq_list_sum, incidence_on_eq]
  have hh : ∀ R, R ∈ T → (hits (List.finRange 24) R).length = 14 := by
    intro R hR
    have hv := hrows R hR
    rw [LinearTriples.supported_hits_length (List.finRange 24) R
      (List.nodup_finRange 24) hv.1 (fun q _ => by simp)]
    exact hv.2
  rw [List.map_congr_left hh, sum_map_const, hlen]

lemma degree_patterns (T : Family 24) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (hcover : IsCovering 4 T) (hlen : T.length = 19) :
    (∃ p, degree T p = 13 ∧ ∀ q, q ≠ p → degree T q = 11) ∨
    (∃ p q, p ≠ q ∧ degree T p = 12 ∧ degree T q = 12 ∧
      ∀ r, r ≠ p → r ≠ q → degree T r = 11) :=
  A19DegreeArithmetic.degree_patterns (degree T) (point_floor_eleven T hrows hcover)
    (total_degree T hrows hlen)

abbrev LowPoint (T : Family 24) := {p : Fin 24 // degree T p = 11}

def fullExcess (T : Family 24) : Matrix (Fin 24) (Fin 24) ℝ :=
  fun p q => if p = q then 0 else (pairDegree T p q : ℝ) - 6

def lowExcess (T : Family 24) : Matrix (LowPoint T) (LowPoint T) ℝ :=
  (fullExcess T).submatrix Subtype.val Subtype.val

lemma fullExcess_symmetric (T : Family 24) (p q : Fin 24) :
    fullExcess T p q = fullExcess T q p := by
  by_cases h : p = q
  · subst q; rfl
  · simp [fullExcess, h, Ne.symm h, Regular22Incidence.pair_symmetric T p q]

lemma fullExcess_diagonal (T : Family 24) (p : Fin 24) : fullExcess T p p = 0 := by
  simp [fullExcess]

lemma fullExcess_nonnegative (T : Family 24) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (hcover : IsCovering 4 T) (p q : Fin 24) : 0 ≤ fullExcess T p q := by
  by_cases h : p = q
  · simp [fullExcess, h]
  · have hp := pair_floor_six T hrows hcover p q h
    simp only [fullExcess, if_neg h]
    have hp' : (6 : ℝ) ≤ pairDegree T p q := by exact_mod_cast hp
    linarith

lemma fullExcess_entry (T : Family 24) (p q : Fin 24) :
    fullExcess T p q = (pairDegree T p q : ℝ) - 6 -
      (if p = q then (degree T p : ℝ) - 6 else 0) := by
  by_cases h : p = q
  · subst q
    simp [fullExcess, Regular22Incidence.pair_diagonal]
  · simp [fullExcess, h]

lemma fullExcess_row_sum (T : Family 24) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (p : Fin 24) : ∑ q, fullExcess T p q = 13 * (degree T p : ℝ) - 138 := by
  have hnat : (∑ q, pairDegree T p q) = degree T p * 14 := by
    rw [fin_sum_eq_list_sum]
    exact Regular22Incidence.pair_row_sum T hrows p
  have hreal : (∑ q, (pairDegree T p q : ℝ)) = (degree T p : ℝ) * 14 := by
    exact_mod_cast hnat
  simp_rw [fullExcess_entry, Finset.sum_sub_distrib]
  rw [hreal]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

lemma fullExcess_low_row_sum (T : Family 24) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (p : LowPoint T) : ∑ q, fullExcess T p.val q = 5 := by
  rw [fullExcess_row_sum T hrows, p.property]
  norm_num

lemma fullExcess_low_entry_le_five (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (p : LowPoint T) (q : Fin 24) : fullExcess T p.val q ≤ 5 := by
  have h := Finset.single_le_sum (fun r (_ : r ∈ (univ : Finset (Fin 24))) =>
    fullExcess_nonnegative T hrows hcover p.val r) (mem_univ q)
  rw [fullExcess_low_row_sum T hrows p] at h
  exact h

lemma lowExcess_row_le_five (T : Family 24) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (hcover : IsCovering 4 T) (p : LowPoint T) : ∑ q, lowExcess T p q ≤ 5 := by
  classical
  have hs := Fintype.sum_subtype_add_sum_subtype (fun q => degree T q = 11)
    (fun q => fullExcess T p.val q)
  have hn : 0 ≤ ∑ q : {q : Fin 24 // ¬ degree T q = 11}, fullExcess T p.val q.val :=
    Finset.sum_nonneg (fun q _ => fullExcess_nonnegative T hrows hcover p.val q.val)
  have hf := fullExcess_low_row_sum T hrows p
  change (∑ q : LowPoint T, fullExcess T p.val q.val) ≤ 5
  linarith

end Covering.NormalizedBridge20261003.A19Physical
#print axioms Covering.NormalizedBridge20261003.A19Physical.point_floor_eleven
#print axioms Covering.NormalizedBridge20261003.A19Physical.total_degree
#print axioms Covering.NormalizedBridge20261003.A19Physical.degree_patterns
#print axioms Covering.NormalizedBridge20261003.A19Physical.fullExcess_nonnegative
#print axioms Covering.NormalizedBridge20261003.A19Physical.fullExcess_row_sum
#print axioms Covering.NormalizedBridge20261003.A19Physical.lowExcess_row_le_five
#print axioms Covering.NormalizedBridge20261003.A19Physical.fullExcess_low_entry_le_five
