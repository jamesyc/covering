module

public import Foundations.Basic

@[expose] public section

/-!
Nonnegative integer weighted counting for the canonical covering model.
Weights are attached to list occurrences. Neither distinct demands nor distinct
added rows are needed for the weighted noncompletion implication.
-/

namespace Covering.Weighted

instance decidableSubset {n : Nat} (T B : Block n) : Decidable (Subset T B) := by
  unfold Subset
  infer_instance

/-- Total weight, including every listed demand occurrence. -/
def weightTotal {n : Nat} (D : List (Block n × Nat)) : Nat :=
  (D.map Prod.snd).sum

/-- Weight of the listed demands contained in one canonical block. -/
def rowLoad {n : Nat} (D : List (Block n × Nat)) (B : Block n) : Nat :=
  (D.map (fun d => if Subset d.1 B then d.2 else 0)).sum

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

/-- A cover pays each demand's weight in at least one row; repeated coverage
can only increase the sum on the right. -/
theorem weightTotal_le_sum_rowLoad {n : Nat} (D : List (Block n × Nat))
    (G : Family n) (hcover : ∀ d, d ∈ D → Covers G d.1) :
    weightTotal D ≤ (G.map (rowLoad D)).sum := by
  unfold weightTotal rowLoad
  rw [← sum_map_swap D G (fun d B => if Subset d.1 B then d.2 else 0)]
  apply sum_map_le
  intro d hd
  obtain ⟨B, hB, hsub⟩ := hcover d hd
  have h := term_le_sum_map G (fun B => if Subset d.1 B then d.2 else 0) B hB
  simpa only [if_pos hsub] using h

/-- Uniform unrestricted row caps bound the total weight of every covered
list of demands. No distinctness assumption is used. -/
theorem weightTotal_le_budget_mul_cap {n k budget cap : Nat}
    (D : List (Block n × Nat)) (G : Family n)
    (hlen : G.length ≤ budget)
    (hvalid : ∀ B, B ∈ G → ValidBlock k B)
    (hcap : ∀ B, ValidBlock k B → rowLoad D B ≤ cap)
    (hcover : ∀ d, d ∈ D → Covers G d.1) :
    weightTotal D ≤ budget * cap := by
  calc
    weightTotal D ≤ (G.map (rowLoad D)).sum := weightTotal_le_sum_rowLoad D G hcover
    _ ≤ G.length * cap := sum_map_le_length_mul G (rowLoad D) cap
      (fun B hB => hcap B (hvalid B hB))
    _ ≤ budget * cap := Nat.mul_le_mul_right cap hlen

/-- Sound residual witnesses and an unrestricted row cap exclude every
admissible completion when the total weight exceeds the row budget times cap. -/
theorem no_residual_completion {n k t budget cap : Nat}
    (D : List (Block n × Nat)) (kept : Family n)
    (hsound : ∀ d, d ∈ D → ValidBlock t d.1 ∧ ¬ Covers kept d.1)
    (hcap : ∀ B, ValidBlock k B → rowLoad D B ≤ cap)
    (hweight : budget * cap < weightTotal D) :
    ¬ ∃ G : Family n, Admissible k budget G ∧ ResidualCovered t kept G := by
  rintro ⟨G, hadm, hres⟩
  have hle := weightTotal_le_budget_mul_cap D G hadm.1 hadm.2.1 hcap
    (fun d hd => hres d.1 (hsound d hd).1 (hsound d hd).2)
  omega

/-- The same obstruction stated directly as failure of an appended covering. -/
theorem no_covering_append {n k t budget cap : Nat}
    (D : List (Block n × Nat)) (kept : Family n)
    (hsound : ∀ d, d ∈ D → ValidBlock t d.1 ∧ ¬ Covers kept d.1)
    (hcap : ∀ B, ValidBlock k B → rowLoad D B ≤ cap)
    (hweight : budget * cap < weightTotal D) :
    ∀ G : Family n, Admissible k budget G → ¬ IsCovering t (kept ++ G) := by
  intro G hadm hcover
  exact no_residual_completion D kept hsound hcap hweight
    ⟨G, hadm, (covering_append_iff_residual kept G).mp hcover⟩

end Covering.Weighted
