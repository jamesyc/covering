module

public import Covering.Basic.Model
public import Covering.Basic.Facts

@[expose] public section

/-!
# Supports and complements

The duplicate-free support of a block and its complement, with length identities.
-/

namespace Covering

/-- The set of points of a block, without repetition, in increasing order. -/
def support {n : Nat} (B : Block n) : Block n :=
  (List.finRange n).filter (fun p => p ∈ B)

theorem mem_support {n : Nat} (B : Block n) (x : Fin n) :
    x ∈ support B ↔ x ∈ B := by simp [support]

theorem support_nodup {n : Nat} (B : Block n) : (support B).Nodup := by
  exact (List.nodup_finRange n).filter _

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

end Covering
