module

public import Covering.Basic.Model
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
# Finite-set formulation

Transfers bounds for indexed families to the usual formulation: a `Finset` of
`k`-element `Finset`s covering every `t`-element `Finset`.
-/

/-- Transfer any indexed-family lower bound to the usual finite-set formulation. -/
lemma Covering.finset_lower_bound {v k t b : ℕ}
    (bound : ∀ F : Covering.Family v,
      (∀ R, R ∈ F → Covering.ValidBlock k R) → Covering.IsCovering t F → b ≤ F.length)
    (𝒯 : Finset (Finset (Fin v)))
    (hk : ∀ B ∈ 𝒯, B.card = k)
    (hcov : ∀ S : Finset (Fin v), S.card = t → ∃ B ∈ 𝒯, S ⊆ B) :
    b ≤ 𝒯.card := by
  classical
  let F : Covering.Family v := 𝒯.toList.map (fun B => B.toList)
  have hrows : ∀ R, R ∈ F → Covering.ValidBlock k R := by
    intro R hR
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hR
    show B.toList.Nodup ∧ B.toList.length = k
    exact ⟨Finset.nodup_toList B, by rw [Finset.length_toList]; exact hk B (Finset.mem_toList.mp hB)⟩
  have hcover : Covering.IsCovering t F := by
    intro T hT
    have hT' : T.Nodup ∧ T.length = t := hT
    obtain ⟨B, hB, hsub⟩ :=
      hcov T.toFinset (by rw [List.toFinset_card_of_nodup hT'.1]; exact hT'.2)
    show ∃ R, R ∈ F ∧ ∀ x, x ∈ T → x ∈ R
    exact ⟨B.toList, List.mem_map.mpr ⟨B, Finset.mem_toList.mpr hB, rfl⟩,
      fun x hx => Finset.mem_toList.mpr (hsub (List.mem_toFinset.mpr hx))⟩
  have h := bound F hrows hcover
  simpa [F, List.length_map, Finset.length_toList] using h

