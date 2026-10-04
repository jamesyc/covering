module

public import Foundations.Shadow

@[expose] public section

namespace Covering

/-- Distinct-point support in universe order; input rows may contain duplicates. -/
def support {n : Nat} (B : Block n) : Block n :=
  (List.finRange n).filter (fun p => p ∈ B)

theorem mem_support {n : Nat} (B : Block n) (x : Fin n) :
    x ∈ support B ↔ x ∈ B := by simp [support]

theorem support_nodup {n : Nat} (B : Block n) : (support B).Nodup := by
  exact (List.nodup_finRange n).filter _

theorem support_sameSet {n : Nat} (B : Block n) : SameSet B (support B) := by
  constructor <;> intro x hx
  · exact (mem_support B x).mpr hx
  · exact (mem_support B x).mp hx

theorem support_length_of_nodup {n : Nat} (B : Block n) (h : B.Nodup) :
    (support B).length = B.length := by
  apply Nat.le_antisymm
  · exact (support_nodup B).length_le_of_subset (fun _ hx => (mem_support B _).mp hx)
  · exact h.length_le_of_subset (fun _ hx => (mem_support B _).mpr hx)

theorem complement_nodup {n : Nat} (B : Block n) : (complement B).Nodup := by
  exact (List.nodup_finRange n).filter _

theorem support_add_complement_length {n : Nat} (B : Block n) :
    (support B).length + (complement B).length = n := by
  have h := (List.filter_append_perm (fun p : Fin n => decide (p ∈ B)) (List.finRange n)).length_eq
  simpa [support, complement] using h

theorem complement_length {n k : Nat} (B : Block n) (h : ValidBlock k B) :
    (complement B).length = n - k := by
  have hs := support_add_complement_length B
  rw [support_length_of_nodup B h.1, h.2] at hs
  omega

/-- Finite padding, with no ordering or candidate-pool restriction. -/
theorem exists_valid_extension {n k : Nat} (B : Block n)
    (hB : (support B).length ≤ k) (hk : k ≤ n) :
    ∃ C, ValidBlock k C ∧ Subset B C := by
  let S := support B
  have hS : S.length ≤ k := hB
  let P := (complement S).take (k - S.length)
  refine ⟨S ++ P, ⟨?_, ?_⟩, ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨support_nodup B, (complement_nodup S).take, ?_⟩
    intro x hx y hy hxy
    subst y
    exact (mem_complement S x).mp (List.mem_of_mem_take hy) hx
  · have hlen := complement_length S ⟨support_nodup B, rfl⟩
    dsimp [P]
    rw [List.length_append, List.length_take, hlen, Nat.min_eq_left (by omega)]
    omega
  · intro x hx
    exact List.mem_append.mpr (Or.inl ((mem_support B x).mpr hx))

/-- Extensional duplicate removal preserves coverage and never adds a row. -/
theorem exists_distinct_subcover {n : Nat} (F : Family n) :
    ∃ G : Family n, G.length ≤ F.length ∧
      (∀ B, B ∈ G → B ∈ F) ∧ Distinct G ∧
      (∀ T, Covers G T ↔ Covers F T) := by
  classical
  induction F with
  | nil =>
    refine ⟨[], by simp, ?_, List.Pairwise.nil, ?_⟩
    · simp
    · intro T; rfl
  | cons B F ih =>
    rcases ih with ⟨G, hlen, hmem, hdist, hcov⟩
    by_cases he : ∃ C, C ∈ G ∧ SameSet B C
    · rcases he with ⟨C, hC, hBC⟩
      refine ⟨G, by simp; omega, ?_, hdist, ?_⟩
      · intro D hD; exact List.mem_cons_of_mem _ (hmem D hD)
      · intro T
        constructor
        · rintro ⟨D, hD, hTD⟩
          exact ⟨D, List.mem_cons_of_mem _ (hmem D hD), hTD⟩
        · rintro ⟨D, hD, hTD⟩
          rcases List.mem_cons.mp hD with hD | hD
          · subst D; exact ⟨C, hC, subset_trans hTD hBC.1⟩
          · exact (hcov T).mpr ⟨D, hD, hTD⟩
    · refine ⟨B :: G, by simp; omega, ?_, ?_, ?_⟩
      · intro D hD
        rcases List.mem_cons.mp hD with hD | hD
        · exact List.mem_cons.mpr (Or.inl hD)
        · exact List.mem_cons_of_mem _ (hmem D hD)
      · apply List.pairwise_cons.mpr
        exact ⟨fun C hC hBC => he ⟨C, hC, hBC⟩, hdist⟩
      · intro T
        constructor
        · rintro ⟨D, hD, hTD⟩
          rcases List.mem_cons.mp hD with hD | hD
          · exact ⟨D, List.mem_cons.mpr (Or.inl hD), hTD⟩
          · exact ⟨D, List.mem_cons_of_mem _ (hmem D hD), hTD⟩
        · rintro ⟨D, hD, hTD⟩
          rcases List.mem_cons.mp hD with hD | hD
          · exact ⟨D, List.mem_cons.mpr (Or.inl hD), hTD⟩
          · rcases (hcov T).mpr ⟨D, hD, hTD⟩ with ⟨E, hE, hTE⟩
            exact ⟨E, List.mem_cons_of_mem _ hE, hTE⟩

/-- The distinct-point union of all occurrences assigned the indicated color. -/
def classUnion {n r : Nat} (H : Family n) (c : Fin H.length → Fin r)
    (j : Fin r) : Block n :=
  (List.finRange n).filter (fun p => ∃ i : Fin H.length, c i = j ∧ p ∈ H.get i)

theorem mem_classUnion {n r : Nat} (H : Family n) (c : Fin H.length → Fin r)
    (j : Fin r) (x : Fin n) :
    x ∈ classUnion H c j ↔ ∃ i : Fin H.length, c i = j ∧ x ∈ H.get i := by
  simp [classUnion]

theorem classUnion_nodup {n r : Nat} (H : Family n) (c : Fin H.length → Fin r)
    (j : Fin r) : (classUnion H c j).Nodup := by
  exact (List.nodup_finRange n).filter _

/-- Exact unrestricted finite union-capacity equivalence. Empty demand rows,
repeated rows and repeated points are permitted; the row budget is at most r. -/
theorem admissible_cover_iff_capacity {n k r : Nat} (H : Family n) (hk : k ≤ n) :
    (∃ G : Family n, Admissible k r G ∧ ∀ T, T ∈ H → Covers G T) ↔
    (∃ c : Fin H.length → Fin r, ∀ j, (classUnion H c j).length ≤ k) := by
  classical
  constructor
  · rintro ⟨G, hG, hcover⟩
    have hchoose : ∀ i : Fin H.length, ∃ j : Fin G.length,
        Subset (H.get i) (G.get j) := by
      intro i
      rcases hcover (H.get i) (List.get_mem H i) with ⟨B, hB, hsub⟩
      rcases List.mem_iff_get.mp hB with ⟨j, hj⟩
      exact ⟨j, hj.symm ▸ hsub⟩
    let a : Fin H.length → Fin G.length := fun i => Classical.choose (hchoose i)
    have ha : ∀ i, Subset (H.get i) (G.get (a i)) :=
      fun i => Classical.choose_spec (hchoose i)
    let c : Fin H.length → Fin r := fun i => Fin.castLE hG.1 (a i)
    refine ⟨c, ?_⟩
    intro j
    by_cases he : ∃ i, c i = j
    · rcases he with ⟨i₀, hi₀⟩
      have hsub : Subset (classUnion H c j) (G.get (a i₀)) := by
        intro x hx
        rcases (mem_classUnion H c j x).mp hx with ⟨i, hi, hx⟩
        have heq : a i = a i₀ := by
          apply Fin.ext
          have hv := congrArg (fun x : Fin r => x.val) (hi.trans hi₀.symm)
          exact hv
        rw [← heq]
        exact ha i x hx
      have hlen := (classUnion_nodup H c j).length_le_of_subset (fun _ hx => hsub _ hx)
      have hb := hG.2.1 (G.get (a i₀)) (List.get_mem G (a i₀))
      rw [hb.2] at hlen
      exact hlen
    · have hempty : classUnion H c j = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x hx
        rcases (mem_classUnion H c j x).mp hx with ⟨i, hi, _⟩
        exact he ⟨i, hi⟩
      simp [hempty]
  · rintro ⟨c, hc⟩
    have hext : ∀ j : Fin r, ∃ B, ValidBlock k B ∧ Subset (classUnion H c j) B := by
      intro j
      apply exists_valid_extension _ _ hk
      rw [support_length_of_nodup _ (classUnion_nodup H c j)]
      exact hc j
    let b : Fin r → Block n := fun j => Classical.choose (hext j)
    have hb : ∀ j, ValidBlock k (b j) ∧ Subset (classUnion H c j) (b j) :=
      fun j => Classical.choose_spec (hext j)
    let F := (List.finRange r).map b
    rcases exists_distinct_subcover F with ⟨G, hlen, hmem, hdist, hcov⟩
    refine ⟨G, ⟨?_, ?_, hdist⟩, ?_⟩
    · have hf : F.length = r := by simp [F]
      omega
    · intro B hB
      rcases List.mem_map.mp (hmem B hB) with ⟨j, _, rfl⟩
      exact (hb j).1
    · intro T hT
      apply (hcov T).mpr
      rcases List.mem_iff_get.mp hT with ⟨i, rfl⟩
      refine ⟨b (c i), List.mem_map.mpr ⟨c i, by simp, rfl⟩, ?_⟩
      intro x hx
      apply (hb (c i)).2 x
      exact (mem_classUnion H c (c i) x).mpr ⟨i, rfl, hx⟩

/-- Exact capacity characterization of a fixed kept family's residual problem. -/
theorem residual_completion_iff_capacity {n k t r : Nat} (K H : Family n)
    (hk : k ≤ n)
    (sound : ∀ R, R ∈ H → ValidBlock t R ∧ ¬ Covers K R)
    (complete : ∀ T, ValidBlock t T → ¬ Covers K T →
      ∃ R, R ∈ H ∧ SameSet T R) :
    (∃ G, Admissible k r G ∧ ResidualCovered t K G) ↔
    (∃ c : Fin H.length → Fin r, ∀ j, (classUnion H c j).length ≤ k) := by
  simp only [residualCovered_iff_representatives K H _ sound complete]
  exact admissible_cover_iff_capacity H hk

/-- Valid rows and coverage can always be normalized to extensional distinctness. -/
theorem exists_design_of_valid_cover {n k t budget : Nat} (F : Family n)
    (hlen : F.length ≤ budget)
    (hvalid : ∀ B, B ∈ F → ValidBlock k B) (hcover : IsCovering t F) :
    ∃ G : Family n, Design k t budget G := by
  rcases exists_distinct_subcover F with ⟨G, hGlen, hmem, hdist, hcov⟩
  refine ⟨G, ⟨by omega, fun B hB => hvalid B (hmem B hB), hdist⟩, ?_⟩
  intro T hT
  exact (hcov T).mpr (hcover T hT)

/-- Positive residual lifting needs complete representatives. Any extra demands
are harmless. Normalize the entire append, including collisions with kept rows. -/
theorem exists_design_of_capacity {n k t r budget : Nat} (K H : Family n)
    (hk : k ≤ n) (hK : ∀ B, B ∈ K → ValidBlock k B)
    (hbudget : K.length + r ≤ budget)
    (complete : ∀ T, ValidBlock t T → ¬ Covers K T →
      ∃ R, R ∈ H ∧ SameSet T R)
    (capacity : ∃ c : Fin H.length → Fin r, ∀ j, (classUnion H c j).length ≤ k) :
    ∃ F : Family n, Design k t budget F := by
  rcases (admissible_cover_iff_capacity H hk).mpr capacity with ⟨G, hG, hcov⟩
  apply exists_design_of_valid_cover (K ++ G)
  · simp only [List.length_append]
    have hsize := hG.1
    omega
  · intro B hB
    rcases List.mem_append.mp hB with hB | hB
    · exact hK B hB
    · exact hG.2.1 B hB
  · apply (covering_append_iff_residual K G).mpr
    intro T hT hhole
    rcases complete T hT hhole with ⟨R, hR, hsame⟩
    exact (covers_sameSet_iff G hsame).mpr (hcov R hR)

/-- Negative residual lifting requires only sound witnesses, not completeness. -/
theorem no_residual_completion_of_no_capacity {n k t r : Nat} (K H : Family n)
    (hk : k ≤ n)
    (sound : ∀ R, R ∈ H → ValidBlock t R ∧ ¬ Covers K R)
    (impossible : ¬ ∃ c : Fin H.length → Fin r,
      ∀ j, (classUnion H c j).length ≤ k) :
    ¬ ∃ G, Admissible k r G ∧ ResidualCovered t K G := by
  rintro ⟨G, hG, hres⟩
  apply impossible
  apply (admissible_cover_iff_capacity H hk).mp
  exact ⟨G, hG, fun R hR => hres R (sound R hR).1 (sound R hR).2⟩

theorem validBlock_length_le {n k : Nat} (B : Block n) (h : ValidBlock k B) : k ≤ n := by
  have hs := h.1.length_le_of_subset (l₂ := List.finRange n) (fun _ _ => List.mem_finRange _)
  simpa [h.2] using hs

end Covering
