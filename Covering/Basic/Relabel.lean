module

public import Covering.Basic.Facts

@[expose] public section

/-!
# Relabelling points

Coverage, block validity and degrees are invariant under a permutation of the points.
-/

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

end Covering
