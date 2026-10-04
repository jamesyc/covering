import rounds.round_06.lean.PointSplit
import rounds.round_06.theory.PointDegree
import Statements.Target

namespace Covering.PointSplit

/-- The original target is exactly a mixed 24-point construction with at most
24 fourteen-rows. The other rows have size15 and the total budget stays41. -/
theorem target_iff_mixed_degree24 :
    Target ↔ ∃ A B : Family 24, Mixed 14 4 41 A B ∧ A.length ≤ 24 := by
  constructor
  · rintro ⟨F, hF⟩
    obtain ⟨G, hG, hdegree⟩ := PointDegree.design25_normalize_last F hF
    refine ⟨through G, away G, design_to_mixed G hG, ?_⟩
    simpa only [through_length, PointDegree.degree] using hdegree
  · rintro ⟨A, B, h, _⟩
    exact mixed_to_design A B h

/-- Search-facing form: A covers all four-sets; only its five-set residuals
need to be covered by B. Every clause remains unrestricted on the24 points. -/
theorem target_iff_residual_degree24 :
    Target ↔ ∃ A B : Family 24,
      A.length ≤ 24 ∧ A.length + B.length ≤ 41 ∧
      (∀ T, T ∈ A → ValidBlock 14 T) ∧
      (∀ T, T ∈ B → ValidBlock 15 T) ∧
      IsCovering 4 A ∧ ResidualCovered 5 A B := by
  rw [target_iff_mixed_degree24]
  constructor
  · rintro ⟨A, B, ⟨hlen, hA, hB, h4, h5⟩, h24⟩
    exact ⟨A, B, h24, hlen, hA, hB, h4,
      (covering_append_iff_residual A B).mp h5⟩
  · rintro ⟨A, B, h24, hlen, hA, hB, h4, h5⟩
    exact ⟨A, B, ⟨hlen, hA, hB, h4,
      (covering_append_iff_residual A B).mpr h5⟩, h24⟩

end Covering.PointSplit
