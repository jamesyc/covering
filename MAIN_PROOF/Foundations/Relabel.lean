module

public import Foundations.Basic

@[expose] public section

namespace Covering

theorem relabelBlock_inverse {n : Nat} (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p) = p) (B : Block n) :
    relabelBlock d (relabelBlock e B) = B := by
  simp only [relabelBlock, List.map_map]
  exact List.map_id'' hde B

theorem pointMap_injective {n : Nat} (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p) = p) (p q : Fin n) (h : e p = e q) : p = q := by
  calc
    p = d (e p) := (hde p).symm
    _ = d (e q) := congrArg d h
    _ = q := hde q

theorem mem_relabelBlock_iff {n : Nat} (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p) = p) (hed : ∀ p, e (d p) = p)
    (B : Block n) (x : Fin n) :
    x ∈ relabelBlock e B ↔ d x ∈ B := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    simpa only [hde] using hy
  · intro hx
    exact List.mem_map.mpr ⟨d x, hx, hed x⟩

theorem subset_relabelBlock_iff {n : Nat} (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p) = p) (hed : ∀ p, e (d p) = p)
    (T B : Block n) :
    Subset T (relabelBlock e B) ↔ Subset (relabelBlock d T) B := by
  constructor
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact (mem_relabelBlock_iff e d hde hed B x).mp (h x hx)
  · intro h x hx
    exact (mem_relabelBlock_iff e d hde hed B x).mpr
      (h (d x) (List.mem_map_of_mem hx))

theorem subset_relabel_iff {n : Nat} (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p) = p) (hed : ∀ p, e (d p) = p)
    (A B : Block n) :
    Subset (relabelBlock e A) (relabelBlock e B) ↔ Subset A B := by
  rw [subset_relabelBlock_iff e d hde hed, relabelBlock_inverse e d hde]

theorem sameSet_relabel_iff {n : Nat} (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p) = p) (hed : ∀ p, e (d p) = p)
    (A B : Block n) :
    SameSet (relabelBlock e A) (relabelBlock e B) ↔ SameSet A B := by
  simp only [SameSet, subset_relabel_iff e d hde hed]

theorem validBlock_relabel_iff {n k : Nat} (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p) = p) (B : Block n) :
    ValidBlock k (relabelBlock e B) ↔ ValidBlock k B := by
  unfold ValidBlock relabelBlock
  rw [List.length_map]
  constructor
  · rintro ⟨hn, hlen⟩
    exact ⟨List.Pairwise.of_map e (fun _ _ hne heq => hne (congrArg e heq)) hn, hlen⟩
  · rintro ⟨hn, hlen⟩
    exact ⟨List.Pairwise.map e
      (fun a b hne heq => hne (pointMap_injective e d hde a b heq)) hn, hlen⟩

theorem distinct_relabel_iff {n : Nat} (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p) = p) (hed : ∀ p, e (d p) = p)
    (F : Family n) : Distinct (relabelFamily e F) ↔ Distinct F := by
  unfold Distinct relabelFamily
  rw [List.pairwise_map]
  constructor
  · intro h
    exact h.imp (fun {A B} hn hs => hn ((sameSet_relabel_iff e d hde hed A B).mpr hs))
  · intro h
    exact h.imp (fun {A B} hn hs => hn ((sameSet_relabel_iff e d hde hed A B).mp hs))

theorem covers_relabel_iff {n : Nat} (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p) = p) (hed : ∀ p, e (d p) = p)
    (F : Family n) (T : Block n) :
    Covers (relabelFamily e F) T ↔ Covers F (relabelBlock d T) := by
  constructor
  · rintro ⟨B, hB, hsub⟩
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
    exact ⟨A, hA, (subset_relabelBlock_iff e d hde hed T A).mp hsub⟩
  · rintro ⟨A, hA, hsub⟩
    exact ⟨relabelBlock e A, List.mem_map_of_mem hA,
      (subset_relabelBlock_iff e d hde hed T A).mpr hsub⟩

theorem admissible_relabel_iff {n k budget : Nat} (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p) = p) (hed : ∀ p, e (d p) = p)
    (F : Family n) :
    Admissible k budget (relabelFamily e F) ↔ Admissible k budget F := by
  constructor
  · rintro ⟨hlen, hvalid, hdistinct⟩
    refine ⟨?_, ?_, (distinct_relabel_iff e d hde hed F).mp hdistinct⟩
    · simpa only [relabelFamily, List.length_map] using hlen
    · intro B hB
      exact (validBlock_relabel_iff e d hde B).mp
        (hvalid (relabelBlock e B) (List.mem_map_of_mem hB))
  · rintro ⟨hlen, hvalid, hdistinct⟩
    refine ⟨?_, ?_, (distinct_relabel_iff e d hde hed F).mpr hdistinct⟩
    · simpa only [relabelFamily, List.length_map] using hlen
    · intro B hB
      obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
      exact (validBlock_relabel_iff e d hde A).mpr (hvalid A hA)

theorem isCovering_relabel_iff {n t : Nat} (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p) = p) (hed : ∀ p, e (d p) = p)
    (F : Family n) :
    IsCovering t (relabelFamily e F) ↔ IsCovering t F := by
  constructor
  · intro h T hT
    have himage := h (relabelBlock e T) ((validBlock_relabel_iff e d hde T).mpr hT)
    have hpull := (covers_relabel_iff e d hde hed F (relabelBlock e T)).mp himage
    simpa only [relabelBlock_inverse e d hde] using hpull
  · intro h T hT
    apply (covers_relabel_iff e d hde hed F T).mpr
    exact h (relabelBlock d T) ((validBlock_relabel_iff d e hed T).mpr hT)

/-- One fixed global point bijection preserves the complete design predicate,
including final row sizes, extensional distinctness, budget, and all tests. -/
theorem design_relabel_iff {n k t budget : Nat} (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p) = p) (hed : ∀ p, e (d p) = p)
    (F : Family n) :
    Design k t budget (relabelFamily e F) ↔ Design k t budget F := by
  simp only [Design, admissible_relabel_iff e d hde hed,
    isCovering_relabel_iff e d hde hed]

theorem residualCovered_relabel_iff {n t : Nat} (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p) = p) (hed : ∀ p, e (d p) = p)
    (K G : Family n) :
    ResidualCovered t (relabelFamily e K) (relabelFamily e G) ↔ ResidualCovered t K G := by
  rw [← covering_append_iff_residual, ← covering_append_iff_residual]
  have happend : relabelFamily e K ++ relabelFamily e G = relabelFamily e (K ++ G) := by
    simp only [relabelFamily, List.map_append]
  rw [happend, isCovering_relabel_iff e d hde hed]

end Covering
