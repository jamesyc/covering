module

public import FinalCoveringBounds
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
Independent fidelity check, written outside the archived proof.

The textbook definition of a (v,k,t) covering design: a set of k-subsets of a
v-set such that every t-subset lies in some block. We state the two bounds in
that form with Mathlib `Finset`s and derive them from the archived endpoints.
If the archived `ValidBlock` / `IsCovering` meant something stronger than the
textbook notions, these derivations would not go through.
-/

theorem textbook_C24_14_4 (𝒯 : Finset (Finset (Fin 24)))
    (hk : ∀ B ∈ 𝒯, B.card = 14)
    (hcov : ∀ S : Finset (Fin 24), S.card = 4 → ∃ B ∈ 𝒯, S ⊆ B) :
    20 ≤ 𝒯.card := by
  classical
  let F : Covering.Family 24 := 𝒯.toList.map (fun B => B.toList)
  have hrows : ∀ R, R ∈ F → Covering.ValidBlock 14 R := by
    intro R hR
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hR
    show B.toList.Nodup ∧ B.toList.length = 14
    exact ⟨Finset.nodup_toList B, by rw [Finset.length_toList]; exact hk B (Finset.mem_toList.mp hB)⟩
  have hcover : Covering.IsCovering 4 F := by
    intro T hT
    have hT' : T.Nodup ∧ T.length = 4 := hT
    obtain ⟨B, hB, hsub⟩ :=
      hcov T.toFinset (by rw [List.toFinset_card_of_nodup hT'.1]; exact hT'.2)
    show ∃ R, R ∈ F ∧ ∀ x, x ∈ T → x ∈ R
    exact ⟨B.toList, List.mem_map.mpr ⟨B, Finset.mem_toList.mpr hB, rfl⟩,
      fun x hx => Finset.mem_toList.mpr (hsub (List.mem_toFinset.mpr hx))⟩
  have h := Covering.FinalCoveringBounds.c24_14_4_lower_twenty F hrows hcover
  simpa [F, List.length_map, Finset.length_toList] using h

theorem textbook_C25_15_5 (𝒯 : Finset (Finset (Fin 25)))
    (hk : ∀ B ∈ 𝒯, B.card = 15)
    (hcov : ∀ S : Finset (Fin 25), S.card = 5 → ∃ B ∈ 𝒯, S ⊆ B) :
    34 ≤ 𝒯.card := by
  classical
  let F : Covering.Family 25 := 𝒯.toList.map (fun B => B.toList)
  have hrows : ∀ R, R ∈ F → Covering.ValidBlock 15 R := by
    intro R hR
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hR
    show B.toList.Nodup ∧ B.toList.length = 15
    exact ⟨Finset.nodup_toList B, by rw [Finset.length_toList]; exact hk B (Finset.mem_toList.mp hB)⟩
  have hcover : Covering.IsCovering 5 F := by
    intro T hT
    have hT' : T.Nodup ∧ T.length = 5 := hT
    obtain ⟨B, hB, hsub⟩ :=
      hcov T.toFinset (by rw [List.toFinset_card_of_nodup hT'.1]; exact hT'.2)
    show ∃ R, R ∈ F ∧ ∀ x, x ∈ T → x ∈ R
    exact ⟨B.toList, List.mem_map.mpr ⟨B, Finset.mem_toList.mpr hB, rfl⟩,
      fun x hx => Finset.mem_toList.mpr (hsub (List.mem_toFinset.mpr hx))⟩
  have h := Covering.FinalCoveringBounds.c25_15_5_lower_thirty_four F hrows hcover
  simpa [F, List.length_map, Finset.length_toList] using h

-- What the archived endpoints actually say, and the definitions they use.
#check @Covering.FinalCoveringBounds.c24_14_4_lower_twenty
#check @Covering.FinalCoveringBounds.c25_15_5_lower_thirty_four
#print Covering.ValidBlock
#print Covering.Covers
#print Covering.IsCovering
#print Covering.Subset

#print axioms textbook_C24_14_4
#print axioms textbook_C25_15_5
