module

public import Covering.Basic.Facts

@[expose] public section

/-!
# Sums over lists

Monotonicity and exchange lemmas for sums of natural-number weights over list positions.
-/

namespace Covering.Weighted

instance decidableSubset {n : Nat} (T B : Block n) : Decidable (Subset T B) := by
  unfold Subset
  infer_instance

theorem sum_map_le {α : Type} (L : List α) (f g : α → Nat)
    (h : ∀ a, a ∈ L → f a ≤ g a) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    apply Nat.add_le_add
    · exact h a (by simp)
    · exact ih (fun b hb => h b (by simp [hb]))

theorem sum_map_add {α : Type} (L : List α) (f g : α → Nat) :
    (L.map (fun a => f a + g a)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem sum_map_zero {α : Type} (L : List α) :
    (L.map (fun _ => (0 : Nat))).sum = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih => simpa using ih

theorem sum_map_le_length_mul {α : Type} (L : List α) (f : α → Nat) (cap : Nat)
    (h : ∀ a, a ∈ L → f a ≤ cap) :
    (L.map f).sum ≤ L.length * cap := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem term_le_sum_map {α : Type} (L : List α) (f : α → Nat) (a : α)
    (h : a ∈ L) : f a ≤ (L.map f).sum := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | ht
    · omega
    · have := ih ht
      omega

theorem sum_map_swap {α β : Type} (L : List α) (M : List β) (f : α → β → Nat) :
    (L.map (fun a => (M.map (f a)).sum)).sum =
      (M.map (fun b => (L.map (fun a => f a b)).sum)).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil]; exact (sum_map_zero M).symm
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [sum_map_add, ih]

end Covering.Weighted
