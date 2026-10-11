module

public import Covering.Quadruple.Completion
public import Covering.PairCover.NineteenGrid

@[expose] public section

/-!
# Degrees from the completion

Equation (14). The completion is built first; its two new points are twins, so
each old point has codegree three with a new point and hence `H`-degree three.
-/

namespace Covering.Quadruple
open PointSplit PointDegree TwoPointSplit SideLift
open Floors Covering.Completions

/-- Pair coverage implies point coverage without a regularity calculation. -/
lemma pair_cover_has_points (H : Family 20) (hHc : IsCovering 2 H) :
    IsCovering 1 H := by
  apply Covering.Matching.point_cover_of_providers H
  intro p
  obtain ⟨q, hpq⟩ : ∃ q : Fin 20, p ≠ q := by
    by_cases hp : p = 0
    · refine ⟨1, ?_⟩
      rw [hp]
      decide
    · exact ⟨0, hp⟩
  obtain ⟨R, hR, hs⟩ := hHc [p, q] (by simp [ValidBlock, hpq])
  exact ⟨R, hR, hs p (by simp)⟩

/-- Once the completion is a triple cover, twins force both old degrees. -/
theorem completion_degrees_from_rigidity (H E : Family 20)
    (hHl : H.length = 6)
    (hrows : ∀ R, R ∈ extended H E → ValidBlock 12 R)
    (hcover : IsCovering 3 (extended H E))
    (hlen : (extended H E).length = 11) :
    ∀ p, degree H p = 3 ∧ degree E p = 3 := by
  classical
  have hd := Covering.Rigidity.eleven_block_regular (extended H E) hrows hcover hlen
  obtain ⟨σ, _hne, _hinv, hpair, _htwin⟩ :=
    Covering.Rigidity.eleven_block_rigidity (extended H E) hrows hcover hlen
  have hab : pairDegree (extended H E) anchorFirst anchorSecond = 6 := by
    simp only [extended, liftFour, anchorFirst, anchorSecond,
      pair_lift_last_old, degree_lift_last]
    exact hHl
  have hneab : anchorFirst ≠ anchorSecond := by decide
  have hanchor : σ anchorFirst = anchorSecond := by
    by_contra h
    have h' : anchorSecond ≠ σ anchorFirst := Ne.symm h
    have hp := hpair anchorFirst anchorSecond
    simp only [hneab, h', or_self, ite_false] at hp
    omega
  intro p
  have hp := p.isLt
  have hfirst : anchorFirst ≠ old p := by
    intro h
    have hv := congrArg Fin.val h
    change 21 = p.val at hv
    omega
  have hsecond : old p ≠ anchorSecond := by
    intro h
    have hv := congrArg Fin.val h
    change p.val = 20 at hv
    omega
  have hcodeg : pairDegree (extended H E) anchorFirst (old p) = 3 := by
    rw [hpair]
    simp only [hfirst, hanchor, hsecond, or_self, ite_false]
  have hcount : pairDegree (extended H E) anchorFirst (old p) = degree H p := by
    simp only [extended, liftFour, anchorFirst, old,
      pair_lift_last_old, degree_lift_old]
    simp [degree]
  have hdH : degree H p = 3 := hcount.symm.trans hcodeg
  have hh := hd (old p)
  change degree (lift (lift H []) (lift [] E)) p.castSucc.castSucc = 6 at hh
  rw [degree_lift_old, degree_lift_old, degree_lift_old, hdH] at hh
  simp only [show degree ([] : Family 20) p = 0 from rfl,
    Nat.add_zero, Nat.zero_add] at hh
  exact ⟨hdH, by omega⟩

/-- The paper's completion argument uses only sizes and coverage as inputs. -/
theorem completion_from_rigidity (H E : Family 20)
    (hHl : H.length = 6) (hEl : E.length = 5)
    (hHr : ∀ R, R ∈ H → ValidBlock 10 R)
    (hEr : ∀ R, R ∈ E → ValidBlock 12 R)
    (hHc : IsCovering 2 H) (hEc : IsCovering 3 (H ++ E)) : Completion H E := by
  have hpH := pair_cover_has_points H hHc
  have hextr : ∀ R, R ∈ extended H E → ValidBlock 12 R :=
    lift_valid _ _ (lift_valid H [] hHr (by simp)) (lift_valid [] E (by simp) hEr)
  have hextc : IsCovering 3 (extended H E) := by
    apply (covering_liftFour_iff H [] [] E).mpr
    exact ⟨hpH, by simpa using hHc, by simpa using hHc, by simpa using hEc⟩
  have hextl : (extended H E).length = 11 := by
    simp [extended, liftFour, lift_length, hHl, hEl]
  have hd := completion_degrees_from_rigidity H E hHl hextr hextc hextl
  exact ⟨hHl, hEl, hHr, hEr, fun p => (hd p).1, fun p => (hd p).2, hHc, hEc⟩

end Covering.Quadruple