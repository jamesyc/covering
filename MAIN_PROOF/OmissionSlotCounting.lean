import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import FormalResume20261003.SixPointTriplesV1
import campaign_next15.lean.d0_lift.SlotPairsV2
open Finset
open scoped BigOperators
namespace Covering.NormalizedBridge20261003.OmissionSlots
open PointDegree SideLift CrossGrid LinearTriples

lemma nat_sum_get (L : List α) (f : α → ℕ) :
    (∑ j : Fin L.length, f (L.get j)) = (L.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map L f

def missing {n : ℕ} (R : Family n) (p : Fin n) : Block R.length :=
  (List.finRange R.length).filter (fun j => p ∉ R[j.val])

lemma mem_missing {n : ℕ} (R : Family n) (p : Fin n) (j : Fin R.length) :
    j ∈ missing R p ↔ p ∉ R[j.val] := by simp [missing]

lemma missing_nodup {n : ℕ} (R : Family n) (p : Fin n) : (missing R p).Nodup :=
  (List.nodup_finRange _).filter _

lemma presence_sum {n : ℕ} (R : Family n) (p : Fin n) :
    (∑ j : Fin R.length, if p ∈ R[j.val] then 1 else 0) = degree R p := by
  have h := nat_sum_get R (fun A => if p ∈ A then 1 else 0)
  rw [sum_indicator_eq_filter_length] at h
  simpa only [List.get_eq_getElem, degree, pairDegree] using h

lemma pair_sum {n : ℕ} (R : Family n) (p q : Fin n) :
    (∑ j : Fin R.length, if p ∈ R[j.val] ∧ q ∈ R[j.val] then 1 else 0) = pairDegree R p q := by
  have h := nat_sum_get R (fun A => if p ∈ A ∧ q ∈ A then 1 else 0)
  rw [sum_indicator_eq_filter_length] at h
  simpa only [List.get_eq_getElem, degree, pairDegree] using h

lemma absence_sum {n : ℕ} (R : Family n) (p : Fin n) :
    (∑ j : Fin R.length, if p ∉ R[j.val] then 1 else 0) = (missing R p).length := by
  rw [Fin.sum_univ_def, sum_indicator_eq_filter_length]
  rfl

lemma missing_length_add_degree {n : ℕ} (R : Family n) (p : Fin n) :
    (missing R p).length + degree R p = R.length := by
  have he : ∀ j : Fin R.length,
      (if p ∉ R[j.val] then 1 else 0) + (if p ∈ R[j.val] then 1 else 0) = 1 := by
    intro j; by_cases h : p ∈ R[j.val] <;> simp [h]
  have hs := Finset.sum_congr rfl (fun j (_ : j ∈ (univ : Finset (Fin R.length))) => he j)
  simp only [Finset.sum_add_distrib] at hs
  rw [absence_sum, presence_sum] at hs
  simpa using hs

lemma both_absence_sum {n : ℕ} (R : Family n) (p q : Fin n) :
    (∑ j : Fin R.length, if p ∉ R[j.val] ∧ q ∉ R[j.val] then 1 else 0) =
      (hits (missing R p) (missing R q)).length := by
  have h := LinearTriples.pair_presence_sum (List.finRange R.length) (missing R p) (missing R q)
    (List.nodup_finRange _) (missing_nodup R p) (fun j _ => by simp)
  rw [← Fin.sum_univ_def] at h
  simpa only [mem_missing] using h

lemma missing_pair_count {n : ℕ} (R : Family n) (p q : Fin n) :
    (hits (missing R p) (missing R q)).length + degree R p + degree R q =
      R.length + pairDegree R p q := by
  have he : ∀ j : Fin R.length,
      (if p ∉ R[j.val] ∧ q ∉ R[j.val] then 1 else 0) +
        (if p ∈ R[j.val] then 1 else 0) + (if q ∈ R[j.val] then 1 else 0) =
      1 + (if p ∈ R[j.val] ∧ q ∈ R[j.val] then 1 else 0) := by
    intro j
    by_cases hp : p ∈ R[j.val] <;> by_cases hq : q ∈ R[j.val] <;> simp [hp, hq]
  have hs := Finset.sum_congr rfl (fun j (_ : j ∈ (univ : Finset (Fin R.length))) => he j)
  simp only [Finset.sum_add_distrib] at hs
  rw [both_absence_sum, presence_sum, presence_sum, pair_sum] at hs
  simpa using hs

lemma eight_slot_obstruction {n : ℕ} (R : Family n) (hlen : R.length = 8)
    (S : Finset (Fin n)) (hS : 6 ≤ S.card) (high : Fin n)
    (hh : degree R high = 6)
    (hdegree : ∀ p ∈ S, degree R p = 5)
    (hpair : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → pairDegree R p q = 3)
    (hhigh : ∀ p ∈ S, pairDegree R p high = 3) : False := by
  let P := missing R high
  let F : Family R.length := S.toList.map (missing R)
  have hP : ValidBlock 2 P := by
    refine ⟨missing_nodup R high, ?_⟩
    have h := missing_length_add_degree R high
    dsimp [P]
    omega
  have hrows : ∀ D, D ∈ F → ValidBlock 3 D := by
    intro D hD
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hD
    have hpS : p ∈ S := by simpa using hp
    refine ⟨missing_nodup R p, ?_⟩
    have hd := hdegree p hpS
    have h := missing_length_add_degree R p
    omega
  have havoid : ∀ D, D ∈ F → Covering.Disjoint D P := by
    intro D hD
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hD
    have hpS : p ∈ S := by simpa using hp
    have hd := hdegree p hpS
    have hph := hhigh p hpS
    have hc := missing_pair_count R p high
    have hz : (hits (missing R p) P).length = 0 := by dsimp [P]; omega
    have hn : hits (missing R p) P = [] := List.eq_nil_of_length_eq_zero hz
    intro j hj hjP
    have hmem := (mem_hits _ _ _).mpr ⟨hj, hjP⟩
    rw [hn] at hmem
    exact List.not_mem_nil hmem
  have hpairOrig : S.toList.Pairwise
      (fun p q => (hits (missing R p) (missing R q)).length = 1) := by
    have hnodup : S.toList.Pairwise (fun p q => p ≠ q) := S.nodup_toList
    apply hnodup.imp_of_mem
    intro p q hp hq hpq
    have hpS : p ∈ S := by simpa using hp
    have hqS : q ∈ S := by simpa using hq
    have hdp := hdegree p hpS
    have hdq := hdegree q hqS
    have hpq' := hpair p hpS q hqS hpq
    have h := missing_pair_count R p q
    omega
  have hpairs : F.Pairwise (fun A B => (hits A B).length = 1) :=
    List.pairwise_map.mpr hpairOrig
  have hbound := LinearTriples.cardinality_le_four (complement P) F (complement_nodup P)
    (by rw [complement_length P hP]; omega)
    (fun D hD => ⟨hrows D hD, fun j hj => (mem_complement P j).mpr
      (fun hjP => havoid D hD j hj hjP)⟩) hpairs
  have hlenF : F.length = S.card := by simp [F]
  omega

end Covering.NormalizedBridge20261003.OmissionSlots
#print axioms Covering.NormalizedBridge20261003.OmissionSlots.missing_length_add_degree
#print axioms Covering.NormalizedBridge20261003.OmissionSlots.missing_pair_count
#print axioms Covering.NormalizedBridge20261003.OmissionSlots.eight_slot_obstruction
