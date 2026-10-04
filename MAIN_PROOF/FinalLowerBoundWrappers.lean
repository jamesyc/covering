module

public import rounds.round_06.lean.PointSplit
public import rounds.round_06.theory.PointDegree

@[expose] public section

/-! Conditional final wrappers. The exact nineteen-row contradiction is an
explicit input until the independently checked terminal branches are composed.
All statements count actual list slots and allow repeated rows. -/
namespace Covering.FinalLowerBoundWrappers
open PointDegree

def padWith {n : Nat} (F : Family n) (R : Block n) (b : Nat) : Family n :=
  F ++ List.replicate (b - F.length) R

theorem padWith_length {n : Nat} (F : Family n) (R : Block n) (b : Nat)
    (h : F.length ≤ b) : (padWith F R b).length = b := by
  simp only [padWith, List.length_append, List.length_replicate]
  omega

theorem padWith_valid {n k : Nat} (F : Family n) (R : Block n) (b : Nat)
    (hrows : ∀ A, A ∈ F → ValidBlock k A) (hR : ValidBlock k R) :
    ∀ A, A ∈ padWith F R b → ValidBlock k A := by
  intro A hA
  rcases List.mem_append.mp hA with hA | hA
  · exact hrows A hA
  · have he : A = R := (List.mem_replicate.mp hA).2
    simpa only [he] using hR

theorem padWith_cover {n t : Nat} (F : Family n) (R : Block n) (b : Nat)
    (hcover : IsCovering t F) : IsCovering t (padWith F R b) := by
  intro A hA
  obtain ⟨B, hB, hAB⟩ := hcover A hA
  exact ⟨B, List.mem_append.mpr (Or.inl hB), hAB⟩

def ExactNineteenExcluded : Prop :=
  ∀ T : Family 24, (∀ R, R ∈ T → ValidBlock 14 R) →
    IsCovering 4 T → T.length = 19 → False

theorem no_at_most_nineteen (hexact : ExactNineteenExcluded) (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (hlen : T.length ≤ 19) : False := by
  obtain ⟨R, hR, _⟩ := hcover [0, 1, 2, 3] (by constructor <;> decide)
  exact hexact (padWith T R 19) (padWith_valid T R 19 hrows (hrows R hR))
    (padWith_cover T R 19 hcover) (padWith_length T R 19 hlen)

theorem c24_lower_twenty (hexact : ExactNineteenExcluded) (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T) :
    20 ≤ T.length := by
  apply Classical.byContradiction
  intro h
  exact no_at_most_nineteen hexact T hrows hcover (by omega)

theorem point_degree_twenty_of_c24
    (h24 : ∀ T : Family 24, (∀ R, R ∈ T → ValidBlock 14 R) →
      IsCovering 4 T → 20 ≤ T.length)
    (F : Family 25) (hrows : ∀ R, R ∈ F → ValidBlock 15 R)
    (hcover : IsCovering 5 F) (p : Fin 25) : 20 ≤ degree F p := by
  let e := swapPoint p (Fin.last 24)
  have he : ∀ x, e (e x) = x := swapPoint_involutive p (Fin.last 24)
  let G := relabelFamily e F
  have hgrows : ∀ R, R ∈ G → ValidBlock 15 R := by
    intro R hR
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hR
    exact (validBlock_relabel_iff e e he S).mpr (hrows S hS)
  have hgcover : IsCovering 5 G := (isCovering_relabel_iff e e he he F).mpr hcover
  have hlow := h24 (PointSplit.through G) (PointSplit.through_valid G hgrows)
    (PointSplit.covering_split G hgcover).1
  have hdegree : (PointSplit.through G).length = degree F p := by
    rw [PointSplit.through_length]
    change degree (relabelFamily e F) (Fin.last 24) = degree F p
    exact degree_swap_right F p (Fin.last 24)
  simpa only [hdegree] using hlow

theorem c25_lower_thirty_four_of_c24
    (h24 : ∀ T : Family 24, (∀ R, R ∈ T → ValidBlock 14 R) →
      IsCovering 4 T → 20 ≤ T.length)
    (F : Family 25) (hrows : ∀ R, R ∈ F → ValidBlock 15 R)
    (hcover : IsCovering 5 F) : 34 ≤ F.length := by
  have hp := point_degree_twenty_of_c24 h24 F hrows hcover
  have hlo := Weighted.sum_map_le (List.finRange 25) (fun _ => 20) (degree F)
    (fun p _ => hp p)
  simp only [sum_map_const, List.length_finRange] at hlo
  have hi := incidence_le F
  have hu := Weighted.sum_map_le_length_mul F List.length 15
    (fun R hR => Nat.le_of_eq (hrows R hR).2)
  omega

theorem c25_lower_thirty_four (hexact : ExactNineteenExcluded) (F : Family 25)
    (hrows : ∀ R, R ∈ F → ValidBlock 15 R) (hcover : IsCovering 5 F) : 34 ≤ F.length :=
  c25_lower_thirty_four_of_c24 (c24_lower_twenty hexact) F hrows hcover

theorem no_design24_budget19 (hexact : ExactNineteenExcluded) :
    ¬ ∃ T : Family 24, Design 14 4 19 T := by
  rintro ⟨T, hT⟩
  exact no_at_most_nineteen hexact T hT.1.2.1 hT.2 hT.1.1

theorem no_design25_budget33 (hexact : ExactNineteenExcluded) :
    ¬ ∃ F : Family 25, Design 15 5 33 F := by
  rintro ⟨F, hF⟩
  have h := c25_lower_thirty_four hexact F hF.1.2.1 hF.2
  have hle := hF.1.1
  omega

end Covering.FinalLowerBoundWrappers
#print axioms Covering.FinalLowerBoundWrappers.no_at_most_nineteen
#print axioms Covering.FinalLowerBoundWrappers.c24_lower_twenty
#print axioms Covering.FinalLowerBoundWrappers.point_degree_twenty_of_c24
#print axioms Covering.FinalLowerBoundWrappers.c25_lower_thirty_four_of_c24
#print axioms Covering.FinalLowerBoundWrappers.c25_lower_thirty_four
#print axioms Covering.FinalLowerBoundWrappers.no_design24_budget19
#print axioms Covering.FinalLowerBoundWrappers.no_design25_budget33
