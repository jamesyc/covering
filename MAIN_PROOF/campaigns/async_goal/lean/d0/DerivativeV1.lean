module

public import campaigns.async_goal.lean.PairLowerBoundV4
public import rounds.round_06.lean.PointSplit

@[expose] public section

namespace Covering.D0.Derivative

/-- A local23-point triple cover, not a hypothesis about global Target. -/
theorem triple_cover_degree_ge_six (F : Family 23)
    (hrows : ∀ R, R ∈ F → ValidBlock 13 R) (hcover : IsCovering 3 F)
    (p : Fin 23) : 6 ≤ PointDegree.degree F p := by
  let e := PointDegree.swapPoint p (Fin.last 22)
  have he : ∀ x, e (e x) = x := PointDegree.swapPoint_involutive p (Fin.last 22)
  let G := relabelFamily e F
  have hgrows : ∀ R, R ∈ G → ValidBlock 13 R := by
    intro R hR
    obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
    exact (validBlock_relabel_iff e e he S).mpr (hrows S hS)
  have hgcover : IsCovering 3 G := (isCovering_relabel_iff e e he he F).mpr hcover
  have htraceRows := PointSplit.through_valid G hgrows
  have htraceCover := (PointSplit.covering_split G hgcover).1
  have hlow := PairLowerBound.pair_cover_22_12_ge_six (PointSplit.through G)
    htraceRows htraceCover
  have hdegree : (PointSplit.through G).length = PointDegree.degree F p := by
    rw [PointSplit.through_length]
    change PointDegree.degree (relabelFamily e F) (Fin.last 22) = PointDegree.degree F p
    exact PointDegree.degree_swap_right F p (Fin.last 22)
  simpa only [hdegree] using hlow

theorem degree_lift_outside (H E : Family 22) (p : Fin 22) :
    PointDegree.degree (PointSplit.lift H E) p.castSucc =
      PointDegree.degree H p + PointDegree.degree E p := by
  simp [PointDegree.degree,PointSplit.lift,List.filter_append,List.filter_map,
    Function.comp_def]

/-- Exact local derivative inequality for mixed12-core/13-extension traces. -/
theorem mixed_point_degree_ge_six (H E : Family 22)
    (hH : ∀ R, R ∈ H → ValidBlock 12 R)
    (hE : ∀ R, R ∈ E → ValidBlock 13 R)
    (hpairs : IsCovering 2 H) (htriples : IsCovering 3 (H ++ E))
    (p : Fin 22) : 6 ≤ PointDegree.degree H p + PointDegree.degree E p := by
  have hvalid : ∀ R, R ∈ PointSplit.lift H E → ValidBlock 13 R := by
    intro R hR
    rcases List.mem_append.mp hR with hR | hR
    · obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
      exact PointSplit.valid_cone S (hH S hS)
    · obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
      exact PointSplit.valid_embed S (hE S hS)
  have hcover : IsCovering 3 (PointSplit.lift H E) :=
    (PointSplit.covering_lift_iff H E).mpr ⟨hpairs,htriples⟩
  simpa only [degree_lift_outside] using
    triple_cover_degree_ge_six (PointSplit.lift H E) hvalid hcover p.castSucc

end Covering.D0.Derivative
