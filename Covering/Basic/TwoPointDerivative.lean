module

public import Covering.Basic.Derivative
public import Covering.Basic.Degree
public import Covering.Basic.Model

@[expose] public section

/-!
# Two-point derivatives

The derivative through a pair of points, obtained by splitting twice.
-/

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

/-- Reordering the blocks of the two splits does not change coverage. -/
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

end Covering.TwoPointSplit
