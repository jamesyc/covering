module

public import Covering.Basic.Model

@[expose] public section

/-!
# Elementary facts about blocks

Small lemmas on complements, subsets and coverage of concatenated families.
-/

namespace Covering

theorem subset_trans {n : Nat} {A B C : Block n}
    (hAB : Subset A B) (hBC : Subset B C) : Subset A C := by
  intro x hx
  exact hBC x (hAB x hx)

theorem mem_complement {n : Nat} (B : Block n) (x : Fin n) :
    x ∈ complement B ↔ x ∉ B := by
  simp [complement]

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

end Covering
