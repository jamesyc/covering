module

public import Covering.Basic.HitSums

@[expose] public section

/-!
# Point covers

Incidence counts for families that cover every point, or every cross pair between two sets.
-/

namespace Covering.PointCover

open CrossGrid HitSums

def CrossCover {n : Nat} (X Y : Block n) (F : Family n) : Prop :=
  ∀ x, x ∈ X → ∀ y, y ∈ Y → ∃ R, R ∈ F ∧ x ∈ R ∧ y ∈ R

def PointCover {n : Nat} (W : Block n) (F : Family n) : Prop :=
  ∀ x, x ∈ W → ∃ R, R ∈ F ∧ x ∈ R

theorem incidence_on_eq {n : Nat} (X : Block n) (F : Family n) :
    (X.map (PointDegree.degree F)).sum = (F.map (fun R => (hits X R).length)).sum := by
  have hdegree (p : Fin n) : PointDegree.degree F p =
      (F.map (fun R => if p ∈ R then 1 else 0)).sum :=
    (PointDegree.sum_indicator_eq_filter_length F (fun R => p ∈ R)).symm
  rw [show PointDegree.degree F =
    (fun p => (F.map (fun R => if p ∈ R then 1 else 0)).sum) from funext hdegree]
  rw [Weighted.sum_map_swap]
  simp only [PointDegree.sum_indicator_eq_filter_length,hits]

theorem point_cover_incidence {n : Nat} (Z : Block n) (F : Family n)
    (hc : PointCover Z F) : Z.length ≤ (F.map (fun R => (hits Z R).length)).sum := by
  have hlo := Weighted.sum_map_le Z (fun _ => 1) (PointDegree.degree F) (by
    intro z hz
    obtain ⟨R,hR,hzR⟩ := hc z hz
    have hh := Weighted.term_le_sum_map F (fun T => if z ∈ T then 1 else 0) R hR
    rw [PointDegree.sum_indicator_eq_filter_length] at hh
    simpa [hzR,PointDegree.degree] using hh)
  simpa only [PointDegree.sum_map_const,Nat.mul_one,incidence_on_eq] using hlo

end Covering.PointCover
