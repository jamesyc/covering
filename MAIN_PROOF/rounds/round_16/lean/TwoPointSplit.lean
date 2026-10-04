import rounds.round_06.lean.GlobalTarget

namespace Covering.TwoPointSplit

open PointSplit

/-- Four membership types for two distinguished points, in order 11,10,01,00. -/
def liftFour {n : Nat} (C D E F : Family n) : Family (n+1+1) :=
  lift (lift C D) (lift E F)

@[simp] theorem through_append {n : Nat} (A B : Family (n+1)) :
    through (A ++ B) = through A ++ through B := by
  simp [through, List.filter_append, List.map_append]

@[simp] theorem away_append {n : Nat} (A B : Family (n+1)) :
    away (A ++ B) = away A ++ away B := by
  simp [away, List.filter_append, List.map_append]

@[simp] theorem lift_length {n : Nat} (A B : Family n) :
    (lift A B).length = A.length + B.length := by simp [lift]

theorem lift_valid {n k : Nat} (A B : Family n)
    (ha : ∀ T, T ∈ A → ValidBlock k T)
    (hb : ∀ T, T ∈ B → ValidBlock (k+1) T) :
    ∀ T, T ∈ lift A B → ValidBlock (k+1) T := by
  intro T ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨U, hu, rfl⟩ := List.mem_map.mp ht
    exact valid_cone U (ha U hu)
  · obtain ⟨U, hu, rfl⟩ := List.mem_map.mp ht
    exact valid_embed U (hb U hu)

/-- Interleaving the two point-split lifts affects row order only, not coverage. -/
theorem covers_shuffle {n : Nat} (C D E F : Family n) (T : Block (n+1)) :
    Covers (lift C D ++ lift E F) T ↔ Covers (lift (C ++ E) (D ++ F)) T := by
  simp only [lift, List.map_append, covers_append]
  simp only [or_assoc, or_left_comm]

theorem covering_shuffle {n t : Nat} (C D E F : Family n) :
    IsCovering t (lift C D ++ lift E F) ↔
      IsCovering t (lift (C ++ E) (D ++ F)) := by
  constructor
  · intro h T ht; exact (covers_shuffle C D E F T).mp (h T ht)
  · intro h T ht; exact (covers_shuffle C D E F T).mpr (h T ht)

/-- Exact four-stratum coverage test. All families are free variables. -/
theorem covering_liftFour_iff {n t : Nat} (C D E F : Family n) :
    IsCovering (t+1+1) (liftFour C D E F) ↔
      IsCovering t C ∧ IsCovering (t+1) (C ++ D) ∧
      IsCovering (t+1) (C ++ E) ∧
      IsCovering (t+1+1) ((C ++ E) ++ (D ++ F)) := by
  rw [liftFour, covering_lift_iff, covering_lift_iff, covering_shuffle,
    covering_lift_iff]
  exact and_assoc

/-- Search-facing global two-point model. Raw repeated rows can be deduplicated
when lifted; no chosen prefix, group, candidate pool, or near-cover is assumed. -/
def FourProfile (C D E F : Family 23) : Prop :=
  C.length + D.length ≤ 24 ∧
  C.length + D.length + (E.length + F.length) ≤ 41 ∧
  (∀ T, T ∈ C → ValidBlock 13 T) ∧
  (∀ T, T ∈ D → ValidBlock 14 T) ∧
  (∀ T, T ∈ E → ValidBlock 14 T) ∧
  (∀ T, T ∈ F → ValidBlock 15 T) ∧
  IsCovering 3 C ∧ IsCovering 4 (C ++ D) ∧
  IsCovering 4 (C ++ E) ∧ IsCovering 5 ((C ++ E) ++ (D ++ F))

/-- Global equivalence with the unchanged canonical Target. The ≤24 bound is
inherited from the proved low-degree normalization, not an experimental rule. -/
theorem target_iff_four_profile :
    Target ↔ ∃ C D E F : Family 23, FourProfile C D E F := by
  rw [target_iff_mixed_degree24]
  constructor
  · rintro ⟨A, B, ⟨hlen, ha, hb, h4, h5⟩, h24⟩
    obtain ⟨h3, h4a⟩ := covering_split A h4
    obtain ⟨h4b, h5b⟩ := covering_split (A ++ B) h5
    refine ⟨through A, away A, through B, away B, ?_⟩
    refine ⟨?_, ?_, through_valid A ha, away_valid A ha,
      through_valid B hb, away_valid B hb, h3, h4a, ?_, ?_⟩
    · simpa only [split_length] using h24
    · simpa only [split_length] using hlen
    · simpa only [through_append] using h4b
    · simpa only [through_append, away_append] using h5b
  · rintro ⟨C, D, E, F, h⟩
    obtain ⟨h24, hlen, hc, hd, he, hf, h3, h4a, h4b, h5⟩ := h
    refine ⟨lift C D, lift E F, ?_, by simpa only [lift_length] using h24⟩
    refine ⟨by simpa only [lift_length] using hlen, lift_valid C D hc hd,
      lift_valid E F he hf, (covering_lift_iff C D).mpr ⟨h3, h4a⟩, ?_⟩
    exact (covering_shuffle C D E F).mpr
      ((covering_lift_iff (C ++ E) (D ++ F)).mpr ⟨h4b, h5⟩)

/-- Both slices must use the SAME point permutation. -/
theorem mixed_relabel {n k t budget : Nat} (A B : Family n)
    (e d : Fin n → Fin n) (hde : ∀ p, d (e p) = p)
    (hed : ∀ p, e (d p) = p) (h : Mixed k t budget A B) :
    Mixed k t budget (relabelFamily e A) (relabelFamily e B) := by
  obtain ⟨hl, ha, hb, hc, hab⟩ := h
  refine ⟨by simpa only [relabelFamily, List.length_map] using hl, ?_, ?_,
    (isCovering_relabel_iff e d hde hed A).mpr hc, ?_⟩
  · intro T ht
    obtain ⟨U, hu, rfl⟩ := List.mem_map.mp ht
    exact (validBlock_relabel_iff e d hde U).mpr (ha U hu)
  · intro T ht
    obtain ⟨U, hu, rfl⟩ := List.mem_map.mp ht
    exact (validBlock_relabel_iff e d hde U).mpr (hb U hu)
  · have hh := (isCovering_relabel_iff e d hde hed (A ++ B)).mpr hab
    simpa only [relabelFamily, List.map_append] using hh

/-- The first normalized slice has at most24 rows, each of size14 on24 points.
Its total incidence is at most336 < 24*15, so a second pivot occurs in at most14
of them. Swapping that pivot in BOTH A and B introduces no structural restriction. -/
theorem target_iff_four_profile_core14 :
    Target ↔ ∃ C D E F : Family 23, FourProfile C D E F ∧ C.length ≤ 14 := by
  constructor
  · intro ht
    obtain ⟨A, B, h, h24⟩ := target_iff_mixed_degree24.mp ht
    obtain ⟨p, hp⟩ := PointDegree.exists_degree_le (k := 14) (cap := 14) A h24
      (fun T ht => Nat.le_of_eq (h.2.1 T ht).2) (by decide)
    let e := PointDegree.swapPoint p (Fin.last 23)
    have he : ∀ x, e (e x) = x := PointDegree.swapPoint_involutive p (Fin.last 23)
    let A' := relabelFamily e A
    let B' := relabelFamily e B
    have hm : Mixed 14 4 41 A' B' := mixed_relabel A B e e he he h
    have ha24 : A'.length ≤ 24 := by simpa [A', relabelFamily] using h24
    have hcore : (through A').length ≤ 14 := by
      have hs : PointDegree.degree A' (Fin.last 23) ≤ 14 := by
        simpa only [A', e, PointDegree.degree_swap_right] using hp
      simpa only [through_length, PointDegree.degree] using hs
    obtain ⟨hlen, ha, hb, h4, h5⟩ := hm
    obtain ⟨h3, h4a⟩ := covering_split A' h4
    obtain ⟨h4b, h5b⟩ := covering_split (A' ++ B') h5
    refine ⟨through A', away A', through B', away B', ?_, hcore⟩
    refine ⟨?_, ?_, through_valid A' ha, away_valid A' ha,
      through_valid B' hb, away_valid B' hb, h3, h4a, ?_, ?_⟩
    · simpa only [split_length] using ha24
    · simpa only [split_length] using hlen
    · simpa only [through_append] using h4b
    · simpa only [through_append, away_append] using h5b
  · rintro ⟨C, D, E, F, h, _⟩
    exact target_iff_four_profile.mpr ⟨C, D, E, F, h⟩

end Covering.TwoPointSplit
