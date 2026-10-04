import Statements.Shadow
import Foundations.Basic

namespace Covering

theorem covers_sameSet_iff {n : Nat} (G : Family n) {T R : Block n}
    (h : SameSet T R) : Covers G T ↔ Covers G R := by
  constructor
  · rintro ⟨B, hB, hTB⟩
    exact ⟨B, hB, subset_trans h.2 hTB⟩
  · rintro ⟨B, hB, hRB⟩
    exact ⟨B, hB, subset_trans h.1 hRB⟩

/-- Exact three-row bridge. The universal coordinates are ordered and may
repeat. No size, validity, nonemptiness, or distinctness premise is needed. -/
theorem covers_three_iff_ordered_shadow {n : Nat} (T A B C : Block n) :
    Covers [A, B, C] T ↔
      ∀ u, u ∈ T → ∀ v, v ∈ T → ∀ w, w ∈ T →
        u ∈ A ∨ v ∈ B ∨ w ∈ C := by
  constructor
  · rintro ⟨R, hR, hsub⟩ u hu v hv w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact Or.inl (hsub u hu)
    · exact Or.inr (Or.inl (hsub v hv))
    · exact Or.inr (Or.inr (hsub w hw))
  · intro h
    by_cases hA : Subset T A
    · exact ⟨A, by simp, hA⟩
    by_cases hB : Subset T B
    · exact ⟨B, by simp, hB⟩
    by_cases hC : Subset T C
    · exact ⟨C, by simp, hC⟩
    simp only [Subset, Classical.not_forall] at hA hB hC
    obtain ⟨u, hu, hAu⟩ := hA
    obtain ⟨v, hv, hBv⟩ := hB
    obtain ⟨w, hw, hCw⟩ := hC
    rcases h u hu v hv w hw with ha | hb | hc
    · exact False.elim (hAu ha)
    · exact False.elim (hBv hb)
    · exact False.elim (hCw hc)

theorem representatives_three_iff_shadow {n : Nat} (H : Family n) (A B C : Block n) :
    (∀ R, R ∈ H → Covers [A, B, C] R) ↔
      ∀ u v w, Shadow3 H u v w → u ∈ A ∨ v ∈ B ∨ w ∈ C := by
  constructor
  · intro h u v w
    rintro ⟨R, hR, hu, hv, hw⟩
    exact (covers_three_iff_ordered_shadow R A B C).mp (h R hR) u hu v hv w hw
  · intro h R hR
    apply (covers_three_iff_ordered_shadow R A B C).mpr
    intro u hu v hv w hw
    exact h u v w ⟨R, hR, hu, hv, hw⟩

theorem residualCovered_iff_representatives {n t : Nat} (K H G : Family n)
    (sound : ∀ R, R ∈ H → ValidBlock t R ∧ ¬ Covers K R)
    (complete : ∀ T, ValidBlock t T → ¬ Covers K T →
      ∃ R, R ∈ H ∧ SameSet T R) :
    ResidualCovered t K G ↔ ∀ R, R ∈ H → Covers G R := by
  constructor
  · intro h R hR
    exact h R (sound R hR).1 (sound R hR).2
  · intro h T hT hhole
    obtain ⟨R, hR, hsame⟩ := complete T hT hhole
    exact (covers_sameSet_iff G hsame).mpr (h R hR)

/-- SAT lifting requires both sound and complete residual representation;
all final-family admissibility checks are kept in the conclusion. -/
theorem design_append_three_iff_shadow {n k t budget : Nat}
    (K H : Family n) (A B C : Block n)
    (sound : ∀ R, R ∈ H → ValidBlock t R ∧ ¬ Covers K R)
    (complete : ∀ T, ValidBlock t T → ¬ Covers K T →
      ∃ R, R ∈ H ∧ SameSet T R) :
    Design k t budget (K ++ [A, B, C]) ↔
      Admissible k budget (K ++ [A, B, C]) ∧
      (∀ u v w, Shadow3 H u v w → u ∈ A ∨ v ∈ B ∨ w ∈ C) := by
  rw [design_append_iff,
    residualCovered_iff_representatives K H [A, B, C] sound complete,
    representatives_three_iff_shadow]

/-- The necessary direction needs only sound witnessed clauses, not complete
enumeration. It does not assert soundness of an encoding or a solver trace. -/
theorem shadow_necessary_of_covering {n t : Nat}
    (K H : Family n) (A B C : Block n)
    (sound : ∀ R, R ∈ H → ValidBlock t R ∧ ¬ Covers K R)
    (h : IsCovering t (K ++ [A, B, C])) :
    ∀ u v w, Shadow3 H u v w → u ∈ A ∨ v ∈ B ∨ w ∈ C := by
  apply (representatives_three_iff_shadow H A B C).mp
  intro R hR
  exact (covering_append_iff_residual K [A, B, C]).mp h
    R (sound R hR).1 (sound R hR).2

end Covering
