module

public import FormalResume20261003.Regular22MatchingV1
public import FormalResume20261003.SixPointTriplesV1

@[expose] public section

/-! Physical incidence inputs for the separate regular22 matrix argument.
No linear-algebra or spectral conclusion is asserted in this module. -/
namespace Covering.NormalizedBridge20261003.Regular22Incidence

open PointSplit PointDegree SideLift CrossGrid TwinCap.CliqueIncidence Regular22Matching

theorem pair_symmetric {n : Nat} (F : Family n) (p q : Fin n) :
    pairDegree F p q=pairDegree F q p := by simp only [pairDegree,and_comm]

theorem pair_diagonal {n : Nat} (F : Family n) (p : Fin n) :
    pairDegree F p p=degree F p := by simp only [pairDegree,and_self,degree]

theorem pair_le_point {n : Nat} (F : Family n) (p q : Fin n) :
    pairDegree F p q≤degree F p := by
  rw [← degree_filtered_eq_pair]
  exact List.length_filter_le _ _

theorem pair_row_sum {n k : Nat} (F : Family n)
    (hrows : ∀ R, R ∈ F → ValidBlock k R) (p : Fin n) :
    ((List.finRange n).map (pairDegree F p)).sum=degree F p*k := by
  let T := F.filter (fun R => p ∈ R)
  have he : pairDegree F p=degree T := by
    funext q
    exact (degree_filtered_eq_pair F p q).symm
  rw [he,incidence_on_eq]
  have hh : ∀ R, R ∈ T → (hits (List.finRange n) R).length=k := by
    intro R hR
    have hv := hrows R (List.mem_filter.mp hR).1
    rw [LinearTriples.supported_hits_length (List.finRange n) R
      (List.nodup_finRange n) hv.1 (fun q _ => by simp)]
    exact hv.2
  rw [List.map_congr_left hh,sum_map_const]
  rfl

theorem pair_cover_point_floor_two (F : Family 21)
    (hrows : ∀ R, R ∈ F → ValidBlock 11 R) (hcover : IsCovering 2 F)
    (p : Fin 21) : 2≤degree F p := by
  let e := swapPoint p (Fin.last 20)
  have he : ∀ x, e (e x)=x := swapPoint_involutive p (Fin.last 20)
  let G := relabelFamily e F
  have hGrows := valid_rows_relabel F e e he hrows
  have hGcover : IsCovering 2 G := (isCovering_relabel_iff e e he he F).mpr hcover
  have hcount := point_cover_count (through G)
    (fun R hR => Nat.le_of_eq (through_valid G hGrows R hR).2)
    (covering_split G hGcover).1
  have hlen : (through G).length=degree F p := by
    rw [through_length]
    exact degree_swap_right F p (Fin.last 20)
  rw [hlen] at hcount
  omega

theorem triple_pair_floor_two (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (p q : Fin 22) (hpq : p≠q) : 2≤pairDegree F p q := by
  let e := swapPoint p (Fin.last 21)
  have he : ∀ x, e (e x)=x := swapPoint_involutive p (Fin.last 21)
  have heLast : e (Fin.last 21)=p := swapPoint_right p (Fin.last 21)
  let G := relabelFamily e F
  have hGrows := valid_rows_relabel F e e he hrows
  have hGcover : IsCovering 3 G := (isCovering_relabel_iff e e he he F).mpr hcover
  have hne : e q≠Fin.last 21 := by
    intro hh
    have hh' := congrArg e hh
    rw [he,heLast] at hh'
    exact hpq hh'.symm
  obtain ⟨r,hr⟩ := cast_of_ne_last (e q) hne
  have hlo := pair_cover_point_floor_two (through G) (through_valid G hGrows)
    (covering_split G hGcover).1 r
  rw [degree_through,hr,pair_degree_relabel e e he he,heLast,he] at hlo
  exact hlo

/-- Equality in the pair/point incidence bound is literal row-slot containment. -/
theorem pair_equal_point_containment {n : Nat} (F : Family n) (p q : Fin n)
    (he : pairDegree F p q=degree F p) :
    ∀ R, R ∈ F → p ∈ R → q ∈ R := by
  let T := F.filter (fun R => p ∈ R)
  have hl : (T.filter (fun R => q ∈ R)).length=T.length := by
    change degree T q=degree F p
    rw [degree_filtered_eq_pair]
    exact he
  intro R hR hp
  have hh := List.length_filter_eq_length_iff.mp hl R
    (List.mem_filter.mpr ⟨hR,by simpa using hp⟩)
  exact of_decide_eq_true hh

/-- Saturating both endpoint degrees gives identical physical incidence columns. -/
theorem pair_equal_degrees_twins {n : Nat} (F : Family n) (p q : Fin n)
    (hp : pairDegree F p q=degree F p) (hq : pairDegree F p q=degree F q) :
    ∀ R, R ∈ F → (p ∈ R ↔ q ∈ R) := by
  intro R hR
  constructor
  · exact pair_equal_point_containment F p q hp R hR
  · apply pair_equal_point_containment F q p _ R hR
    rw [pair_symmetric]
    exact hq

/-- Actual integer pair-codegree data available before any matrix argument. -/
structure PairData (F : Family 22) : Prop where
  symmetric : ∀ p q, pairDegree F p q=pairDegree F q p
  diagonal : ∀ p, pairDegree F p p=6
  off_diagonal_bounds : ∀ p q, p≠q → 2≤pairDegree F p q ∧ pairDegree F p q≤6
  row_sum : ∀ p, ((List.finRange 22).map (pairDegree F p)).sum=72
  two_matching : ∀ u v w, u≠v → u≠w → pairDegree F u v=2 → pairDegree F u w=2 → v=w

theorem physical_pair_data (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (hregular : ∀ p, degree F p=6) : PairData F := by
  refine ⟨pair_symmetric F,?_,?_,?_,?_⟩
  · intro p
    rw [pair_diagonal,hregular]
  · intro p q hpq
    refine ⟨triple_pair_floor_two F hrows hcover p q hpq,?_⟩
    rw [← hregular p]
    exact pair_le_point F p q
  · intro p
    rw [pair_row_sum F hrows p,hregular]
  · intro u v w huv huw hv hw
    exact codegree_two_matching F hrows hcover u v w huv huw (hregular u) hv hw

end Covering.NormalizedBridge20261003.Regular22Incidence
