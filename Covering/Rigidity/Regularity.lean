module
public import Covering.PairCover.PairFloor
public import Covering.Basic.PairDegree
@[expose] public section

/-!
# Regularity of eleven-block covers

Every point of an eleven-block `(22,12,3)` cover has degree six (Section 2.1).
-/

namespace Covering.Rigidity
open PointDegree SideLift

/-- Retaining, rather than deleting, the fixed point gives a pair cover on 22 points. -/
theorem through_covers_pairs (F : Family 22) (hc : IsCovering 3 F) (p : Fin 22) :
    IsCovering 2 (F.filter (fun R => p ∈ R)) := by
  intro S hS
  have hs : (support (p :: S)).length ≤ 3 := by
    have h : (support (p :: S)).length ≤ (p :: S).length := support_length_le (p :: S)
    have hl := hS.2
    simp only [List.length_cons] at h
    omega
  obtain ⟨Q, hQ, hsQ⟩ := exists_valid_extension (p :: S) hs (by decide : 3 ≤ 22)
  obtain ⟨R, hR, hQR⟩ := hc Q hQ
  refine ⟨R, List.mem_filter.mpr ⟨hR, ?_⟩, ?_⟩
  · have hpR := hQR p (hsQ p (by simp))
    simpa using hpR
  · intro q hq
    exact hQR q (hsQ q (by simp [hq]))

/-- Every eleven-block (22,12,3) covering is six-regular. -/
theorem eleven_block_regular (F : Family 22)
    (hr : ∀ R, R ∈ F → ValidBlock 12 R) (hc : IsCovering 3 F)
    (hlen : F.length = 11) : ∀ p, degree F p = 6 := by
  have hlo (p : Fin 22) : 6 ≤ degree F p :=
    PairLowerBound.pair_cover_22_12_ge_six (F.filter (fun R => p ∈ R))
      (fun R hR => hr R (List.mem_filter.mp hR).1) (through_covers_pairs F hc p)
  have hi := incidence_le F
  have hu := Weighted.sum_map_le_length_mul F List.length 12
    (fun R hR => Nat.le_of_eq (hr R hR).2)
  rw [hlen] at hu
  have he := pointwise_eq_of_sum_le (List.finRange 22) (fun _ => 6) (degree F)
    (fun p _ => hlo p) (by rw [sum_map_const, List.length_finRange]; omega)
  intro p
  exact (he p (by simp)).symm

end Covering.Rigidity