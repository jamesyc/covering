module
public import Covering.Basic.TwoPointDerivative
public import Covering.Basic.PointCover
public import Covering.PairCover.PairFloor
@[expose] public section

/-!
# The nine-by-ten grid

Lemma A.5: three eleven-sets cannot cover all cross pairs of a 9 + 10 partition.
-/

namespace Covering.Matching
open PointSplit TwoPointSplit CrossGrid PointCover

theorem point_cover_of_providers {n : Nat} (F : Family n)
    (h : ∀ p : Fin n, ∃ R, R ∈ F ∧ p ∈ R) : IsCovering 1 F := by
  intro S hS
  cases S with
  | nil => simp [ValidBlock] at hS
  | cons p tail =>
    have ht : tail = [] := List.length_eq_zero_iff.mp (by
      have hh := hS.2
      simp only [List.length_cons] at hh
      omega)
    subst tail
    obtain ⟨R, hR, hp⟩ := h p
    refine ⟨R, hR, ?_⟩
    intro q hq
    have he : q = p := by simpa using hq
    simpa [he] using hp

/-- Lemma A.5: a cover of the 9-by-10 grid by three eleven-sets would give a
    five-block `(22,12,2)` cover. -/
theorem no_cross_cover_nineteen (R Y : Block 19) (D : Family 19)
    (hR : ValidBlock 9 R) (hY : ValidBlock 10 Y)
    (hp : ∀ p : Fin 19, p ∈ R ∨ p ∈ Y)
    (hDlen : D.length = 3) (hD : ∀ Q, Q ∈ D → ValidBlock 11 Q)
    (hcross : CrossCover R Y D) : False := by
  let A : Family 20 := [cone R, embed Y]
  let B : Family 20 := D.map cone
  let C : Family 20 := A ++ B
  have hRA : cone R ∈ C := by simp [C, A]
  have hYA : embed Y ∈ C := by simp [C, A]
  have hDB (Q : Block 19) (hQ : Q ∈ D) : cone Q ∈ C :=
    List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨Q, hQ, rfl⟩))
  obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos (show 0 < R.length by rw [hR.2]; decide)
  have hw (p : Fin 20) : ∃ Q, Q ∈ C ∧ Fin.last 19 ∈ Q ∧ p ∈ Q := by
    refine Fin.lastCases ?_ (fun p => ?_) p
    · exact ⟨cone R, hRA, by simp [cone], by simp [cone]⟩
    · rcases hp p with hpR | hpY
      · exact ⟨cone R, hRA, by simp [cone], (mem_cone R p).mpr hpR⟩
      · obtain ⟨Q, hQ, _, hpQ⟩ := hcross r hr p hpY
        exact ⟨cone Q, hDB Q hQ, by simp [cone], (mem_cone Q p).mpr hpQ⟩
  have hpair (p q : Fin 20) : ∃ Q, Q ∈ C ∧ p ∈ Q ∧ q ∈ Q := by
    revert q
    refine Fin.lastCases ?_ (fun p q => ?_) p
    · intro q
      exact hw q
    · refine Fin.lastCases ?_ (fun q => ?_) q
      · obtain ⟨Q, hQ, hwQ, hpQ⟩ := hw p.castSucc
        exact ⟨Q, hQ, hpQ, hwQ⟩
      · rcases hp p with hpR | hpY <;> rcases hp q with hqR | hqY
        · exact ⟨cone R, hRA, (mem_cone R p).mpr hpR, (mem_cone R q).mpr hqR⟩
        · obtain ⟨Q, hQ, hpQ, hqQ⟩ := hcross p hpR q hqY
          exact ⟨cone Q, hDB Q hQ, (mem_cone Q p).mpr hpQ, (mem_cone Q q).mpr hqQ⟩
        · obtain ⟨Q, hQ, hqQ, hpQ⟩ := hcross q hqR p hpY
          exact ⟨cone Q, hDB Q hQ, (mem_cone Q p).mpr hpQ, (mem_cone Q q).mpr hqQ⟩
        · exact ⟨embed Y, hYA, (mem_embed Y p).mpr hpY, (mem_embed Y q).mpr hqY⟩
  have hC : IsCovering 2 C := by
    intro S hS
    obtain ⟨p, q, rfl⟩ := PairLowerBound.list_of_length_two S hS.2
    obtain ⟨Q, hQ, hpQ, hqQ⟩ := hpair p q
    refine ⟨Q, hQ, ?_⟩
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption
  have hA : IsCovering 1 A := point_cover_of_providers A (by
    intro p
    refine Fin.lastCases ?_ (fun p => ?_) p
    · exact ⟨cone R, by simp [A], by simp [cone]⟩
    · rcases hp p with hpR | hpY
      · exact ⟨cone R, by simp [A], (mem_cone R p).mpr hpR⟩
      · exact ⟨embed Y, by simp [A], (mem_embed Y p).mpr hpY⟩)
  have hA0 : IsCovering 0 A := by
    intro S hS
    have he : S = [] := List.length_eq_zero_iff.mp hS.2
    subst S
    exact ⟨cone R, by simp [A], by simp [Covering.Subset]⟩
  have hAr : ∀ Q, Q ∈ A → ValidBlock 10 Q := by
    intro Q hQ
    simp only [A, List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl
    · exact valid_cone R hR
    · exact valid_embed Y hY
  have hBr : ∀ Q, Q ∈ B → ValidBlock 12 Q := by
    intro Q hQ
    change Q ∈ D.map cone at hQ
    obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hQ
    exact valid_cone U (hD U hU)
  let F : Family 22 := liftFour A [] [] B
  have hFr : ∀ Q, Q ∈ F → ValidBlock 12 Q :=
    lift_valid _ _ (lift_valid A [] hAr (by simp)) (lift_valid [] B (by simp) hBr)
  have hFc : IsCovering 2 F := by
    apply (covering_liftFour_iff A [] [] B).mpr
    exact ⟨hA0, by simpa using hA, by simpa using hA, by simpa [C] using hC⟩
  have hFl : F.length = 5 := by simp [F, liftFour, lift_length, A, B, hDlen]
  exact PairLowerBound.no_five_pair_cover F hFl hFr hFc

end Covering.Matching