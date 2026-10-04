module

public import Statements.Model

@[expose] public section

namespace Covering

theorem publicLabel_range {n : Nat} (p : Fin n) :
    1 ≤ publicLabel p ∧ publicLabel p ≤ n := by
  have hp := p.isLt
  unfold publicLabel
  omega

theorem publicLabel_injective {n : Nat} (p q : Fin n)
    (h : publicLabel p = publicLabel q) : p = q := by
  apply Fin.ext
  unfold publicLabel at h
  omega

theorem exists_point_of_label {n : Nat} (label : Nat)
    (h : 1 ≤ label ∧ label ≤ n) : ∃ p : Fin n, publicLabel p = label := by
  refine ⟨⟨label - 1, by omega⟩, ?_⟩
  simp only [publicLabel]
  omega

theorem subset_refl {n : Nat} (B : Block n) : Subset B B := by
  intro x hx
  exact hx

theorem subset_trans {n : Nat} {A B C : Block n}
    (hAB : Subset A B) (hBC : Subset B C) : Subset A C := by
  intro x hx
  exact hBC x (hAB x hx)

theorem mem_complement {n : Nat} (B : Block n) (x : Fin n) :
    x ∈ complement B ↔ x ∉ B := by
  simp [complement]

/-- Containment in a block is exactly disjointness from its complement. -/
theorem subset_iff_disjoint_complement {n : Nat} (T B : Block n) :
    Subset T B ↔ Disjoint T (complement B) := by
  constructor
  · intro h x hx hxc
    exact (mem_complement B x).mp hxc (h x hx)
  · intro h x hx
    by_cases hb : x ∈ B
    · exact hb
    · exact False.elim (h x hx ((mem_complement B x).mpr hb))

theorem covers_iff_complement_disjoint {n : Nat} (F : Family n) (T : Block n) :
    Covers F T ↔ ∃ B, B ∈ F ∧ Disjoint T (complement B) := by
  simp only [Covers, subset_iff_disjoint_complement]

theorem covers_append {n : Nat} (F G : Family n) (T : Block n) :
    Covers (F ++ G) T ↔ Covers F T ∨ Covers G T := by
  constructor
  · rintro ⟨B, hB, hT⟩
    rcases List.mem_append.mp hB with hF | hG
    · exact Or.inl ⟨B, hF, hT⟩
    · exact Or.inr ⟨B, hG, hT⟩
  · rintro (⟨B, hB, hT⟩ | ⟨B, hB, hT⟩)
    · exact ⟨B, List.mem_append.mpr (Or.inl hB), hT⟩
    · exact ⟨B, List.mem_append.mpr (Or.inr hB), hT⟩

/-- Exact residual replacement rule. The old removed blocks are irrelevant:
only the holes left by the kept family must be covered by the added family. -/
theorem covering_append_iff_residual {n t : Nat} (kept added : Family n) :
    IsCovering t (kept ++ added) ↔ ResidualCovered t kept added := by
  constructor
  · intro h T hT hhole
    exact (covers_append kept added T).mp (h T hT) |>.resolve_left hhole
  · intro h T hT
    apply (covers_append kept added T).mpr
    by_cases hc : Covers kept T
    · exact Or.inl hc
    · exact Or.inr (h T hT hc)

/-- The exact design rule includes admissibility of the final family,
preventing overlap/duplicates or wrong block sizes from being hidden. -/
theorem design_append_iff {n k t budget : Nat} (kept added : Family n) :
    Design k t budget (kept ++ added) ↔
      Admissible k budget (kept ++ added) ∧ ResidualCovered t kept added := by
  simp only [Design, covering_append_iff_residual]

theorem universe_contains {n : Nat} (T : Block n) :
    Subset T (List.finRange n) := by
  intro x _
  simp

theorem universe_covers {n t : Nat} :
    IsCovering t [List.finRange n] := by
  intro T _
  exact ⟨List.finRange n, by simp, universe_contains T⟩

end Covering
