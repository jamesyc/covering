import campaigns.async_goal.lean.CrossGridV3

namespace Covering.D0.WeightedProvider

open CrossGrid

def rowWeight {n : Nat} (P R : Block n) : Nat := if Subset P R then 2 else 1

def providers {n : Nat} (E : Family n) (c b : Fin n) : Family n :=
  E.filter (fun R => c ∈ R ∧ b ∈ R)

def cellLoad {n : Nat} (P : Block n) (E : Family n) (c b : Fin n) : Nat :=
  ((providers E c b).map (rowWeight P)).sum

def weightedArea {n : Nat} (P C B : Block n) (E : Family n) : Nat :=
  (E.map (fun R => rowWeight P R * (hits C R).length * (hits B R).length)).sum

def ThreePartCover {n : Nat} (P C B : Block n) (E : Family n) : Prop :=
  ∀ p, p ∈ P → ∀ c, c ∈ C → ∀ b, b ∈ B →
    ∃ R, R ∈ E ∧ p ∈ R ∧ c ∈ R ∧ b ∈ R

theorem rowWeight_pos {n : Nat} (P R : Block n) : 1 ≤ rowWeight P R := by
  unfold rowWeight
  split <;> omega

theorem full_iff_hits_length {n : Nat} (P R : Block n) :
    Subset P R ↔ (hits P R).length = P.length := by
  simp only [hits,List.length_filter_eq_length_iff,decide_eq_true_eq,Subset]

/-- Covering every point of a nonempty P requires weight at least two:
a sole provider must contain all of P and so has weight two. -/
theorem point_cover_weight_ge_two {n : Nat} (P : Block n) (L : Family n)
    (hne : 0 < P.length)
    (hcover : ∀ p, p ∈ P → ∃ R, R ∈ L ∧ p ∈ R) :
    2 ≤ (L.map (rowWeight P)).sum := by
  classical
  apply Classical.byContradiction
  intro hn
  have hlen : L.length ≤ (L.map (rowWeight P)).sum := by
    have hh := Weighted.sum_map_le L (fun _ => 1) (rowWeight P)
      (fun R _ => rowWeight_pos P R)
    simpa only [PointDegree.sum_map_const,Nat.mul_one] using hh
  have hsmall : L.length ≤ 1 := by omega
  cases L with
  | nil =>
    obtain ⟨p,hp⟩ := exists_mem_of_length_pos P hne
    obtain ⟨R,hR,_⟩ := hcover p hp
    simp at hR
  | cons R L =>
    have hzero : L.length = 0 := by simp only [List.length_cons] at hsmall; omega
    have he := List.length_eq_zero_iff.mp hzero
    subst L
    have hfull : Subset P R := by
      intro p hp
      obtain ⟨S,hS,hpS⟩ := hcover p hp
      have hSR : S = R := by simpa using hS
      simpa only [hSR] using hpS
    simp [rowWeight,hfull] at hn

theorem provider_weight_ge_two {n : Nat} (P C B : Block n) (E : Family n)
    (hne : 0 < P.length) (hcover : ThreePartCover P C B E)
    (c b : Fin n) (hc : c ∈ C) (hb : b ∈ B) : 2 ≤ cellLoad P E c b := by
  apply point_cover_weight_ge_two P (providers E c b) hne
  intro p hp
  obtain ⟨R,hR,hpR,hcR,hbR⟩ := hcover p hp c hc b hb
  exact ⟨R,List.mem_filter.mpr ⟨hR,by simp [hcR,hbR]⟩,hpR⟩

theorem sum_filter_map_eq {α : Type} (L : List α) (q : α → Bool) (f : α → Nat) :
    ((L.filter q).map f).sum = (L.map (fun x => if q x then f x else 0)).sum := by
  induction L with
  | nil => simp
  | cons x L ih => cases h : q x <;> simp [h,ih]

theorem cellLoad_eq_sum {n : Nat} (P : Block n) (E : Family n) (c b : Fin n) :
    cellLoad P E c b =
      (E.map (fun R => if c ∈ R ∧ b ∈ R then rowWeight P R else 0)).sum := by
  unfold cellLoad providers
  simpa using sum_filter_map_eq E (fun R => decide (c ∈ R ∧ b ∈ R)) (rowWeight P)

theorem sum_constant_hits {n : Nat} (X R : Block n) (w : Nat) :
    (X.map (fun x => if x ∈ R then w else 0)).sum = w * (hits X R).length := by
  induction X with
  | nil => simp [hits]
  | cons x X ih =>
    by_cases hx : x ∈ R <;> simp [hits,hx,ih,Nat.mul_add,Nat.add_comm]

theorem single_row_grid_mass {n : Nat} (C B R : Block n) (w : Nat) :
    (C.map (fun c => (B.map (fun b => if c ∈ R ∧ b ∈ R then w else 0)).sum)).sum =
      w * (hits C R).length * (hits B R).length := by
  have hinner (c : Fin n) :
      (B.map (fun b => if c ∈ R ∧ b ∈ R then w else 0)).sum =
        if c ∈ R then w * (hits B R).length else 0 := by
    by_cases hc : c ∈ R
    · simpa only [hc,true_and,if_pos] using sum_constant_hits B R w
    · simp [hc,Weighted.sum_map_zero]
  simp only [hinner]
  rw [sum_constant_hits]
  exact Nat.mul_right_comm w (hits B R).length (hits C R).length

/-- Concrete double counting of actual row memberships, including repetitions. -/
theorem grid_mass_eq_weightedArea {n : Nat} (P C B : Block n) (E : Family n) :
    (C.map (fun c => (B.map (fun b => cellLoad P E c b)).sum)).sum =
      weightedArea P C B E := by
  simp only [cellLoad_eq_sum]
  have hswap (c : Fin n) :
      (B.map (fun b => (E.map (fun R =>
        if c ∈ R ∧ b ∈ R then rowWeight P R else 0)).sum)).sum =
      (E.map (fun R => (B.map (fun b =>
        if c ∈ R ∧ b ∈ R then rowWeight P R else 0)).sum)).sum :=
    Weighted.sum_map_swap B E _
  simp only [hswap]
  rw [Weighted.sum_map_swap]
  simp only [single_row_grid_mass,weightedArea]

/-- Each C-B cell receives weighted load at least two. No row-shape premise. -/
theorem weighted_area_lower_bound {n : Nat} (P C B : Block n) (E : Family n)
    (hne : 0 < P.length) (hcover : ThreePartCover P C B E) :
    C.length * B.length * 2 ≤ weightedArea P C B E := by
  have hinner (c : Fin n) (hc : c ∈ C) :
      B.length * 2 ≤ (B.map (fun b => cellLoad P E c b)).sum := by
    have hh := Weighted.sum_map_le B (fun _ => 2) (fun b => cellLoad P E c b)
      (fun b hb => provider_weight_ge_two P C B E hne hcover c b hc hb)
    simpa only [PointDegree.sum_map_const] using hh
  have hh := Weighted.sum_map_le C (fun _ => B.length*2)
    (fun c => (B.map (fun b => cellLoad P E c b)).sum) hinner
  rw [PointDegree.sum_map_const,grid_mass_eq_weightedArea] at hh
  simpa only [Nat.mul_assoc] using hh

end Covering.D0.WeightedProvider
