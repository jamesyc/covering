import campaigns.async_goal.lean.d0.WeightedProviderV2

/-! Physical clique-incidence obstructions for the degree-four twin-cap proof.
This module proves only the graph stage, not the full multiplicity-six bound.
All counts are of actual list memberships; repeated row slots remain legal. -/
namespace Covering.TwinCap.CliqueIncidence

open CrossGrid D0.WeightedProvider

def CrossCover {n : Nat} (X Y : Block n) (F : Family n) : Prop :=
  ∀ x, x ∈ X → ∀ y, y ∈ Y → ∃ R, R ∈ F ∧ x ∈ R ∧ y ∈ R

def PointCover {n : Nat} (W : Block n) (F : Family n) : Prop :=
  ∀ x, x ∈ W → ∃ R, R ∈ F ∧ x ∈ R

def outside {n : Nat} (W X Y : Block n) : Block n :=
  W.filter (fun x => x ∉ X ∧ x ∉ Y)

theorem sum_map_mul_left {α : Type} (L : List α) (a : Nat) (f : α → Nat) :
    (L.map (fun x => a*f x)).sum = a*(L.map f).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [ih,Nat.mul_add]

theorem incidence_on_eq {n : Nat} (X : Block n) (F : Family n) :
    (X.map (PointDegree.degree F)).sum = (F.map (fun R => (hits X R).length)).sum := by
  have hdegree (p : Fin n) : PointDegree.degree F p =
      (F.map (fun R => if p ∈ R then 1 else 0)).sum :=
    (PointDegree.sum_indicator_eq_filter_length F (fun R => p ∈ R)).symm
  rw [show PointDegree.degree F =
    (fun p => (F.map (fun R => if p ∈ R then 1 else 0)).sum) from funext hdegree]
  rw [Weighted.sum_map_swap]
  simp only [PointDegree.sum_indicator_eq_filter_length,hits]

theorem point_cover_incidence {n : Nat} (Z : Block n) (F : Family n)
    (hc : PointCover Z F) : Z.length ≤ (F.map (fun R => (hits Z R).length)).sum := by
  have hlo := Weighted.sum_map_le Z (fun _ => 1) (PointDegree.degree F) (by
    intro z hz
    obtain ⟨R,hR,hzR⟩ := hc z hz
    have hh := Weighted.term_le_sum_map F (fun T => if z ∈ T then 1 else 0) R hR
    rw [PointDegree.sum_indicator_eq_filter_length] at hh
    simpa [hzR,PointDegree.degree] using hh)
  simpa only [PointDegree.sum_map_const,Nat.mul_one,incidence_on_eq] using hlo

/-- Every actual cross-pair contributes at least one row occurrence. -/
theorem cross_cover_area {n : Nat} (X Y : Block n) (F : Family n)
    (hc : CrossCover X Y F) :
    X.length*Y.length ≤ (F.map (fun R => (hits X R).length*(hits Y R).length)).sum := by
  let d := fun x y => (F.map (fun R => if x ∈ R ∧ y ∈ R then 1 else 0)).sum
  have hcell (x : Fin n) (hx : x ∈ X) (y : Fin n) (hy : y ∈ Y) : 1 ≤ d x y := by
    obtain ⟨R,hR,hxR,hyR⟩ := hc x hx y hy
    have hh := Weighted.term_le_sum_map F (fun R => if x ∈ R ∧ y ∈ R then 1 else 0) R hR
    simpa [d,hxR,hyR] using hh
  have hinner (x : Fin n) (hx : x ∈ X) : Y.length ≤ (Y.map (d x)).sum := by
    have hh := Weighted.sum_map_le Y (fun _ => 1) (d x) (hcell x hx)
    simpa only [PointDegree.sum_map_const,Nat.mul_one] using hh
  have hlo := Weighted.sum_map_le X (fun _ => Y.length)
    (fun x => (Y.map (d x)).sum) hinner
  rw [PointDegree.sum_map_const] at hlo
  have hswap (x : Fin n) :
      (Y.map (fun y => (F.map (fun R => if x ∈ R ∧ y ∈ R then 1 else 0)).sum)).sum =
      (F.map (fun R => (Y.map (fun y => if x ∈ R ∧ y ∈ R then 1 else 0)).sum)).sum :=
    Weighted.sum_map_swap Y F _
  dsimp [d] at hlo
  simp only [hswap] at hlo
  rw [Weighted.sum_map_swap] at hlo
  simpa only [single_row_grid_mass,Nat.one_mul] using hlo

/-- Three disjoint physical parts cannot charge more incidences than row length. -/
theorem three_hits_le {n : Nat} (X Y Z R : Block n)
    (hn : (X ++ (Y ++ Z)).Nodup) :
    (hits X R).length+(hits Y R).length+(hits Z R).length ≤ R.length := by
  have hh := hits_le_row (X ++ (Y ++ Z)) R hn
  simpa [hits,Nat.add_assoc] using hh

theorem rectangle_five (a b : Nat) (hs : a+b ≤ 5) : 5*(a*b) ≤ 6*(a+b) := by
  have ha : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 := by omega
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem rectangle_four (a b : Nat) (hs : a+b ≤ 4) : a*b ≤ a+b := by
  have ha : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 := by omega
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega

/-- Mixed pair and point demands, with all row loads derived from memberships. -/
theorem cross_point_cost {n k beta gamma : Nat} (X Y Z : Block n) (F : Family n)
    (hn : (X ++ (Y ++ Z)).Nodup) (hp : PointCover Z F) (hc : CrossCover X Y F)
    (hr : ∀ R, R ∈ F → R.length ≤ k)
    (rect : ∀ a b : Nat, a+b ≤ k → beta*(a*b) ≤ gamma*(a+b)) :
    beta*(X.length*Y.length)+gamma*Z.length ≤ F.length*(gamma*k) := by
  have ha := cross_cover_area X Y F hc
  have hz := point_cover_incidence Z F hp
  have hb := Weighted.sum_map_le_length_mul F
    (fun R => beta*((hits X R).length*(hits Y R).length)+gamma*(hits Z R).length)
    (gamma*k) (by
      intro R hR
      have htotal := three_hits_le X Y Z R hn
      have hrR := hr R hR
      have hrect := rect (hits X R).length (hits Y R).length (by omega)
      calc
        beta*((hits X R).length*(hits Y R).length)+gamma*(hits Z R).length
            ≤ gamma*((hits X R).length+(hits Y R).length)+gamma*(hits Z R).length :=
          Nat.add_le_add_right hrect _
        _ = gamma*((hits X R).length+(hits Y R).length+(hits Z R).length) := by
          simp only [Nat.mul_add,Nat.add_assoc]
        _ ≤ gamma*k := Nat.mul_le_mul_left gamma (by omega))
  rw [Weighted.sum_map_add,sum_map_mul_left,sum_map_mul_left] at hb
  exact Nat.le_trans (Nat.add_le_add (Nat.mul_le_mul_left beta ha)
    (Nat.mul_le_mul_left gamma hz)) hb

theorem outside_partition {n : Nat} (W X Y : Block n)
    (hW : W.Nodup) (hX : X.Nodup) (hY : Y.Nodup) (hXY : Disjoint X Y)
    (hxW : Subset X W) (hyW : Subset Y W) :
    (X ++ (Y ++ outside W X Y)).Nodup ∧
      X.length+Y.length+(outside W X Y).length = W.length := by
  let Z := outside W X Y
  have hZ : Z.Nodup := hW.filter _
  have hYZ : (Y ++ Z).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hY,hZ,?_⟩
    intro x hx y hy he
    subst y
    exact (of_decide_eq_true (List.mem_filter.mp hy).2).2 hx
  have hall : (X ++ (Y ++ Z)).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hX,hYZ,?_⟩
    intro x hx y hy he
    subst y
    rcases List.mem_append.mp hy with hy | hz
    · exact hXY x hx hy
    · exact (of_decide_eq_true (List.mem_filter.mp hz).2).1 hx
  have hf : Subset (X ++ (Y ++ Z)) W := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hxW x hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hyW x hx
      · exact (List.mem_filter.mp hx).1
  have hb : Subset W (X ++ (Y ++ Z)) := by
    intro x hx
    by_cases hxX : x ∈ X
    · simp [hxX]
    · by_cases hxY : x ∈ Y
      · simp [hxY]
      · have hxZ : x ∈ Z := List.mem_filter.mpr ⟨hx,by simp [hxX,hxY]⟩
        simp [hxZ]
  have he := Nat.le_antisymm (hall.length_le_of_subset hf) (hW.length_le_of_subset hb)
  refine ⟨hall,?_⟩
  simpa [List.length_append,Nat.add_assoc,Z] using he

theorem five_clique_cross_bound {n : Nat} (W X Y : Block n) (F : Family n)
    (hW : W.Nodup) (hX : X.Nodup) (hY : Y.Nodup) (hXY : Disjoint X Y)
    (hxW : Subset X W) (hyW : Subset Y W)
    (hp : PointCover W F) (hc : CrossCover X Y F)
    (hr : ∀ R, R ∈ F → R.length ≤ 5) :
    5*(X.length*Y.length)+6*W.length ≤ 30*F.length+6*(X.length+Y.length) := by
  obtain ⟨hn,hlen⟩ := outside_partition W X Y hW hX hY hXY hxW hyW
  have hcost := cross_point_cost X Y (outside W X Y) F hn
    (fun z hz => hp z (List.mem_filter.mp hz).1) hc hr rectangle_five
  omega

theorem four_clique_cross_bound {n : Nat} (W X Y : Block n) (F : Family n)
    (hW : W.Nodup) (hX : X.Nodup) (hY : Y.Nodup) (hXY : Disjoint X Y)
    (hxW : Subset X W) (hyW : Subset Y W)
    (hp : PointCover W F) (hc : CrossCover X Y F)
    (hr : ∀ R, R ∈ F → R.length ≤ 4) :
    X.length*Y.length+W.length ≤ 4*F.length+X.length+Y.length := by
  obtain ⟨hn,hlen⟩ := outside_partition W X Y hW hX hY hXY hxW hyW
  have hcost := cross_point_cost (beta:=1) (gamma:=1) X Y (outside W X Y) F hn
    (fun z hz => hp z (List.mem_filter.mp hz).1) hc hr
    (fun a b h => by simpa using rectangle_four a b h)
  omega

end Covering.TwinCap.CliqueIncidence
