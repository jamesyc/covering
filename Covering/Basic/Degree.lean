module

public import Covering.Basic.ListSums
public import Covering.Basic.Relabel

@[expose] public section

/-!
# Point degrees

The degree of a point is the number of blocks containing it. The total degree of
a family of `k`-blocks is `k` times its length, so some point has degree at most
the average (equation (1) of the paper).
-/

namespace Covering.PointDegree

/-- The number of blocks containing the point. -/
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

/-- A family of at most `budget` blocks of size at most `k` with
`k * budget < n * (cap + 1)` has a point of degree at most `cap`. -/
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
      simp [swapPoint, Ne.symm hpq]
    · by_cases hxq : x = q
      · subst x
        simp [swapPoint, Ne.symm hpq]
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

end Covering.PointDegree
