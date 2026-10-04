module

public import campaign_next15.lean.d0_lift.SlotPairsV2
public import FormalResume20261003.SlotDegreesV1

@[expose] public section

/-! New reconstruction of the generic physical pair-floor proof. Historical
post-archive acceptance is not evidence for this source until fresh checking. -/
namespace Covering.NormalizedBridge20261003

open PointSplit PointDegree SideLift

theorem triple_point_floor_six (F : Family 23)
    (hrows : ∀ R, R ∈ F → ValidBlock 13 R) (hcover : IsCovering 3 F)
    (p : Fin 23) : 6≤degree F p := by
  let e := swapPoint p (Fin.last 22)
  have he : ∀ q, e (e q)=q := swapPoint_involutive p (Fin.last 22)
  let G := relabelFamily e F
  have hGrows : ∀ R, R ∈ G → ValidBlock 13 R := by
    intro R hR
    obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
    exact (validBlock_relabel_iff e e he S).mpr (hrows S hS)
  have hGcover : IsCovering 3 G := (isCovering_relabel_iff e e he he F).mpr hcover
  have hlo := PairLowerBound.pair_cover_22_12_ge_six (through G)
    (through_valid G hGrows) (covering_split G hGcover).1
  have hlen : (through G).length=degree F p := by
    rw [through_length]
    exact degree_swap_right F p (Fin.last 22)
  simpa only [hlen] using hlo

theorem triple_cover_23_13_ge_eleven (F : Family 23)
    (hrows : ∀ R, R ∈ F → ValidBlock 13 R) (hcover : IsCovering 3 F) : 11≤F.length := by
  have hlo := Weighted.sum_map_le (List.finRange 23) (fun _ => 6) (degree F)
    (fun p _ => triple_point_floor_six F hrows hcover p)
  have hi := incidence_le F
  have hu := Weighted.sum_map_le_length_mul F List.length 13
    (fun R hR => Nat.le_of_eq (hrows R hR).2)
  simp only [sum_map_const,List.length_finRange] at hlo
  omega

theorem pair_floor_last (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (q : Fin 23) : 6≤pairDegree T (Fin.last 23) q.castSucc := by
  rw [← degree_through T q]
  exact triple_point_floor_six (through T) (through_valid T hrows)
    (covering_split T hcover).1 q

/-- Any two distinct physical points in a24-point14-row four-cover occur
together in at least six actual row slots. Repeated rows remain legal. -/
theorem pair_floor_six (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (p q : Fin 24) (hpq : p≠q) : 6≤pairDegree T p q := by
  let e := swapPoint p (Fin.last 23)
  have he : ∀ x, e (e x)=x := swapPoint_involutive p (Fin.last 23)
  have helast : e (Fin.last 23)=p := swapPoint_right p (Fin.last 23)
  let G := relabelFamily e T
  have hGrows : ∀ R, R ∈ G → ValidBlock 14 R := by
    intro R hR
    obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
    exact (validBlock_relabel_iff e e he S).mpr (hrows S hS)
  have hGcover : IsCovering 4 G := (isCovering_relabel_iff e e he he T).mpr hcover
  have hnorm (x : Fin 24) : x≠Fin.last 23 → 6≤pairDegree G (Fin.last 23) x := by
    refine Fin.lastCases ?_ (fun r _ => pair_floor_last G hGrows hGcover r) x
    intro hx
    exact False.elim (hx rfl)
  have hq : e q≠Fin.last 23 := by
    intro hx
    have hh := congrArg e hx
    rw [he,helast] at hh
    exact hpq hh.symm
  have hlo := hnorm (e q) hq
  rw [pair_degree_relabel e e he he,helast,he] at hlo
  exact hlo

end Covering.NormalizedBridge20261003
