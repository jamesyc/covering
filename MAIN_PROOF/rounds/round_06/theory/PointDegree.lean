module

public import rounds.round_05.theory.WeightedCounting
public import Foundations.Relabel

@[expose] public section

/-! A global incidence normalization: a small uniform family has a low-degree
point. No candidate pool, symmetry, or fixed-row hypothesis is imposed. -/
namespace Covering.PointDegree

/-- Number of row occurrences containing the point. -/
def degree {n : Nat} (F : Family n) (p : Fin n) : Nat :=
  (F.filter (fun B => p ∈ B)).length

theorem sum_indicator_eq_filter_length {α : Type} (L : List α) (P : α → Prop)
    [DecidablePred P] :
    (L.map (fun a => if P a then 1 else 0)).sum = (L.filter P).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases h : P a
    · simp [h, ih, Nat.add_comm]
    · simp [h, ih]

theorem support_length_le {n : Nat} (B : Block n) :
    ((List.finRange n).filter (fun p => p ∈ B)).length ≤ B.length := by
  apply List.Nodup.length_le_of_subset
    (List.Nodup.sublist (List.filter_sublist) (List.nodup_finRange n))
  intro p hp
  exact (List.mem_filter.mp hp).2 |> of_decide_eq_true

theorem incidence_le {n : Nat} (F : Family n) :
    ((List.finRange n).map (degree F)).sum ≤ (F.map List.length).sum := by
  have hdegree (p : Fin n) : degree F p =
      (F.map (fun B => if p ∈ B then 1 else 0)).sum :=
    (sum_indicator_eq_filter_length F (fun B => p ∈ B)).symm
  rw [show degree F = (fun p => (F.map (fun B => if p ∈ B then 1 else 0)).sum) from funext hdegree]
  rw [Weighted.sum_map_swap]
  apply Weighted.sum_map_le
  intro B _
  rw [sum_indicator_eq_filter_length]
  exact support_length_le B

theorem sum_map_const {α : Type} (L : List α) (c : Nat) :
    (L.map (fun _ => c)).sum = L.length * c := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, Nat.succ_mul, Nat.add_comm]

/-- Strict incidence inequality forces a point of degree at most cap.
Rows may even contain repetitions; only the length upper bound is needed. -/
theorem exists_degree_le {n k budget cap : Nat} (F : Family n)
    (hlen : F.length ≤ budget)
    (hrow : ∀ B, B ∈ F → B.length ≤ k)
    (hgap : k * budget < n * (cap + 1)) :
    ∃ p : Fin n, degree F p ≤ cap := by
  apply Classical.byContradiction
  intro h
  have hlower : n * (cap + 1) ≤ ((List.finRange n).map (degree F)).sum := by
    have hs := Weighted.sum_map_le (List.finRange n) (fun _ => cap + 1) (degree F)
      (by
        intro p _
        have hp : ¬ degree F p ≤ cap := fun hc => h ⟨p, hc⟩
        omega)
    simpa only [sum_map_const, List.length_finRange] using hs
  have hupper := Weighted.sum_map_le_length_mul F List.length k hrow
  have hi := incidence_le F
  have hm : F.length * k ≤ budget * k := Nat.mul_le_mul_right k hlen
  rw [Nat.mul_comm budget k] at hm
  omega

theorem admissible25_degree_le24 (F : Family 25)
    (h : Admissible 15 41 F) : ∃ p : Fin 25, degree F p ≤ 24 := by
  apply exists_degree_le F h.1
  · intro B hB
    exact Nat.le_of_eq (h.2.1 B hB).2
  · decide

/-- A single global transposition, also valid when p=q. -/
def swapPoint {n : Nat} (p q x : Fin n) : Fin n :=
  if x = p then q else if x = q then p else x

theorem swapPoint_involutive {n : Nat} (p q x : Fin n) :
    swapPoint p q (swapPoint p q x) = x := by
  by_cases hpq : p = q
  · subst q
    by_cases hxp : x = p <;> simp [swapPoint, hxp]
  · by_cases hxp : x = p
    · subst x
      simp [swapPoint, hpq, Ne.symm hpq]
    · by_cases hxq : x = q
      · subst x
        simp [swapPoint, hpq, Ne.symm hpq]
      · simp [swapPoint, hxp, hxq]

theorem swapPoint_right {n : Nat} (p q : Fin n) : swapPoint p q q = p := by
  by_cases hpq : p = q
  · subst q; simp [swapPoint]
  · simp [swapPoint, Ne.symm hpq]

theorem degree_relabel {n : Nat} (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p) = p) (hed : ∀ p, e (d p) = p)
    (F : Family n) (q : Fin n) :
    degree (relabelFamily e F) q = degree F (d q) := by
  simp only [degree, relabelFamily, List.filter_map, List.length_map]
  congr 1
  apply congrArg (fun f => F.filter f)
  funext B
  simp only [Function.comp_apply,
    mem_relabelBlock_iff e d hde hed B q]

theorem degree_swap_right {n : Nat} (F : Family n) (p q : Fin n) :
    degree (relabelFamily (swapPoint p q) F) q = degree F p := by
  rw [degree_relabel (swapPoint p q) (swapPoint p q)
    (swapPoint_involutive p q) (swapPoint_involutive p q), swapPoint_right]

/-- Any target-parameter design can be globally relabeled so that its last
point belongs to at most24 rows; all canonical admissibility remains intact. -/
theorem design25_normalize_last (F : Family 25) (h : Design 15 5 41 F) :
    ∃ G : Family 25, Design 15 5 41 G ∧ degree G (Fin.last 24) ≤ 24 := by
  obtain ⟨p, hp⟩ := admissible25_degree_le24 F h.1
  let e := swapPoint p (Fin.last 24)
  have he : ∀ x, e (e x) = x := swapPoint_involutive p (Fin.last 24)
  refine ⟨relabelFamily e F, (design_relabel_iff e e he he F).mpr h, ?_⟩
  simpa only [e, degree_swap_right] using hp

end Covering.PointDegree
