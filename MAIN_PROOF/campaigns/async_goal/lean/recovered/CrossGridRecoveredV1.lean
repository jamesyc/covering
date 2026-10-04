import rounds.round_06.theory.PointDegree
import Foundations.Capacity

/-! Newly reconstructed after workspace loss. This is not the frozen CrossGridV3
source and has not inherited its prior acceptance. Fresh build/review required. -/
namespace Covering.CrossGrid

def hits {n : Nat} (X R : Block n) : Block n := X.filter (fun x => x ∈ R)

theorem mem_hits {n : Nat} (X R : Block n) (x : Fin n) :
    x ∈ hits X R ↔ x ∈ X ∧ x ∈ R := by simp [hits]

theorem hits_nodup {n : Nat} (X R : Block n) (hX : X.Nodup) :
    (hits X R).Nodup := hX.filter _

theorem hits_eq_self {n : Nat} (X R : Block n) (h : Subset X R) : hits X R=X := by
  apply List.filter_eq_self.mpr
  intro x hx
  exact decide_eq_true (h x hx)

theorem hits_le_row {n : Nat} (X R : Block n) (hX : X.Nodup) :
    (hits X R).length≤R.length :=
  (hits_nodup X R hX).length_le_of_subset (fun x hx => ((mem_hits X R x).mp hx).2)

theorem disjoint_hits_sum_le {n : Nat} (X Y R : Block n)
    (hX : X.Nodup) (hY : Y.Nodup) (hXY : Disjoint X Y) :
    (hits X R).length+(hits Y R).length≤R.length := by
  have hn : (hits X R++hits Y R).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hits_nodup X R hX,hits_nodup Y R hY,?_⟩
    intro x hx y hy hxy
    subst y
    exact hXY x ((mem_hits X R x).mp hx).1 ((mem_hits Y R x).mp hy).1
  have hs : Subset (hits X R++hits Y R) R := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact ((mem_hits X R x).mp h).2
    · exact ((mem_hits Y R x).mp h).2
  simpa only [List.length_append] using hn.length_le_of_subset hs

theorem cover_two_count {n : Nat} (X R S : Block n)
    (h : ∀ x, x ∈ X → x ∈ R ∨ x ∈ S) :
    X.length≤(hits X R).length+(hits X S).length := by
  have hh := Weighted.sum_map_le X (fun _ => 1)
    (fun x => (if x ∈ R then 1 else 0)+(if x ∈ S then 1 else 0)) (by
      intro x hx
      rcases h x hx with hr | hs
      · simp [hr]
      · simp [hs])
  simpa only [PointDegree.sum_map_const,Weighted.sum_map_add,
    PointDegree.sum_indicator_eq_filter_length,Nat.mul_one,hits] using hh

def CrossTwo {n : Nat} (X Y R S : Block n) : Prop :=
  ∀ x, x ∈ X → ∀ y, y ∈ Y → (x ∈ R ∧ y ∈ R) ∨ (x ∈ S ∧ y ∈ S)


theorem exists_mem_of_length_pos {n : Nat} (X : Block n) (h : 0<X.length) :
    ∃ x, x ∈ X := List.exists_mem_of_ne_nil X (List.length_pos_iff.mp h)

theorem crossTwo_swap_sides {n : Nat} (X Y R S : Block n) (h : CrossTwo X Y R S) :
    CrossTwo Y X R S := by
  intro y hy x hx
  rcases h x hx y hy with hr | hs
  · exact Or.inl hr.symm
  · exact Or.inr hs.symm

theorem crossTwo_swap_rows {n : Nat} (X Y R S : Block n) (h : CrossTwo X Y R S) :
    CrossTwo X Y S R := by
  intro x hx y hy
  exact (h x hx y hy).symm

theorem crossTwo_x_covered {n : Nat} (X Y R S : Block n) (hy : 0<Y.length)
    (h : CrossTwo X Y R S) : ∀ x, x ∈ X → x ∈ R ∨ x ∈ S := by
  obtain ⟨y,hyY⟩ := exists_mem_of_length_pos Y hy
  intro x hx
  rcases h x hx y hyY with hr | hs
  · exact Or.inl hr.1
  · exact Or.inr hs.1

theorem crossTwo_force_right {n : Nat} (X Y R S : Block n) (h : CrossTwo X Y R S)
    (x : Fin n) (hx : x ∈ X) (hxR : x ∉ R) : Subset Y S := by
  intro y hy
  rcases h x hx y hy with hr | hs
  · exact False.elim (hxR hr.1)
  · exact hs.2

/-- Generic capacity argument; both sides must be nonempty. -/
theorem crossTwo_capacity_disjunction {n k : Nat} (X Y R S : Block n)
    (hX : X.Nodup) (hY : Y.Nodup) (hXY : Disjoint X Y)
    (hx : 0<X.length) (hy : 0<Y.length) (hR : R.length≤k) (hS : S.length≤k)
    (hcross : CrossTwo X Y R S) :
    X.length+Y.length≤k ∨ 2*X.length+Y.length≤2*k ∨ X.length+2*Y.length≤2*k := by
  obtain ⟨x0,hx0⟩ := List.exists_mem_of_ne_nil X (List.length_pos_iff.mp hx)
  obtain ⟨y0,hy0⟩ := List.exists_mem_of_ne_nil Y (List.length_pos_iff.mp hy)
  have hXcover : ∀ x, x ∈ X → x ∈ R ∨ x ∈ S := by
    intro x hx
    rcases hcross x hx y0 hy0 with hr | hs
    · exact Or.inl hr.1
    · exact Or.inr hs.1
  have hYcover : ∀ y, y ∈ Y → y ∈ R ∨ y ∈ S := by
    intro y hy
    rcases hcross x0 hx0 y hy with hr | hs
    · exact Or.inl hr.2
    · exact Or.inr hs.2
  have hcapR := disjoint_hits_sum_le X Y R hX hY hXY
  have hcapS := disjoint_hits_sum_le X Y S hX hY hXY
  by_cases hxR : Subset X R
  · by_cases hyR : Subset Y R
    · have hxEq := hits_eq_self X R hxR
      have hyEq := hits_eq_self Y R hyR
      rw [hxEq,hyEq] at hcapR
      exact Or.inl (by omega)
    · obtain ⟨y,hy⟩ := Classical.not_forall.mp hyR
      obtain ⟨hyY,hyR⟩ := Classical.not_imp.mp hy
      have hxS : Subset X S := by
        intro x hx
        rcases hcross x hx y hyY with hr | hs
        · exact False.elim (hyR hr.2)
        · exact hs.1
      have hh := cover_two_count Y R S hYcover
      rw [hits_eq_self X R hxR] at hcapR
      rw [hits_eq_self X S hxS] at hcapS
      exact Or.inr (Or.inl (by omega))
  · obtain ⟨x,hx⟩ := Classical.not_forall.mp hxR
    obtain ⟨hxX,hxR⟩ := Classical.not_imp.mp hx
    have hyS : Subset Y S := by
      intro y hy
      rcases hcross x hxX y hy with hr | hs
      · exact False.elim (hxR hr.1)
      · exact hs.2
    by_cases hxS : Subset X S
    · rw [hits_eq_self X S hxS,hits_eq_self Y S hyS] at hcapS
      exact Or.inl (by omega)
    · obtain ⟨x',hx'⟩ := Classical.not_forall.mp hxS
      obtain ⟨hx'X,hx'S⟩ := Classical.not_imp.mp hx'
      have hyR : Subset Y R := by
        intro y hy
        rcases hcross x' hx'X y hy with hr | hs
        · exact hr.2
        · exact False.elim (hx'S hs.1)
      have hh := cover_two_count X R S hXcover
      rw [hits_eq_self Y R hyR] at hcapR
      rw [hits_eq_self Y S hyS] at hcapS
      exact Or.inr (Or.inr (by omega))

theorem crossTwo_impossible {n : Nat} (X Y R S : Block n)
    (hX : X.Nodup) (hY : Y.Nodup) (hXY : Disjoint X Y)
    (hx : 8≤X.length) (hy : 10≤Y.length)
    (hR : R.length≤12) (hS : S.length≤12) (hcross : CrossTwo X Y R S) : False := by
  have hh := crossTwo_capacity_disjunction X Y R S hX hY hXY
    (by omega) (by omega) hR hS hcross
  omega

end Covering.CrossGrid
