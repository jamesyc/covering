import FormalResume20261003.PairFloorV1
import FormalResume20261003.Regular22IncidenceV1

namespace Covering.NormalizedBridge20261003.A19Physical
open PointSplit PointDegree

theorem point_floor_eleven (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (p : Fin 24) : 11 ≤ degree T p := by
  let e := swapPoint p (Fin.last 23)
  have he : ∀ q, e (e q) = q := swapPoint_involutive p (Fin.last 23)
  let G := relabelFamily e T
  have hGrows : ∀ R, R ∈ G → ValidBlock 14 R := by
    intro R hR
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hR
    exact (validBlock_relabel_iff e e he S).mpr (hrows S hS)
  have hGcover : IsCovering 4 G := (isCovering_relabel_iff e e he he T).mpr hcover
  have hlo := triple_cover_23_13_ge_eleven (through G)
    (through_valid G hGrows) (covering_split G hGcover).1
  have hlen : (through G).length = degree T p := by
    rw [through_length]
    exact degree_swap_right T p (Fin.last 23)
  simpa only [hlen] using hlo

end Covering.NormalizedBridge20261003.A19Physical
#print axioms Covering.NormalizedBridge20261003.A19Physical.point_floor_eleven
