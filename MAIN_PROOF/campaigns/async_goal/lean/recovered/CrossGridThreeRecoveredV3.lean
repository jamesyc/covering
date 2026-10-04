module

public import campaigns.async_goal.lean.recovered.CrossGridRecoveredV1

@[expose] public section

/-! New reconstruction, not the previously accepted CrossGridThreeV3 bytes. -/
namespace Covering.CrossGrid

def CrossThree {n : Nat} (X Y R S T : Block n) : Prop :=
  ∀ x, x ∈ X → ∀ y, y ∈ Y →
    (x ∈ R ∧ y ∈ R) ∨ (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)

theorem crossThree_symm {n : Nat} (X Y R S T : Block n) (h : CrossThree X Y R S T) :
    CrossThree Y X R S T := by
  intro y hy x hx
  rcases h x hx y hy with hr | hs | ht
  · exact Or.inl hr.symm
  · exact Or.inr (Or.inl hs.symm)
  · exact Or.inr (Or.inr ht.symm)

theorem crossThree_swap {n : Nat} (X Y R S T : Block n) (h : CrossThree X Y R S T) :
    CrossThree X Y S R T := by
  intro x hx y hy
  rcases h x hx y hy with hr | hs | ht
  · exact Or.inr (Or.inl hr)
  · exact Or.inl hs
  · exact Or.inr (Or.inr ht)

theorem crossThree_rotate {n : Nat} (X Y R S T : Block n) (h : CrossThree X Y R S T) :
    CrossThree X Y T R S := by
  intro x hx y hy
  rcases h x hx y hy with hr | hs | ht
  · exact Or.inr (Or.inl hr)
  · exact Or.inr (Or.inr hs)
  · exact Or.inl ht

theorem incidence_le_on {n : Nat} (X : Block n) (F : Family n) (hn : X.Nodup) :
    (X.map (PointDegree.degree F)).sum≤(F.map List.length).sum := by
  have heq (x : Fin n) : PointDegree.degree F x=
      (F.map (fun R => if x ∈ R then 1 else 0)).sum :=
    (PointDegree.sum_indicator_eq_filter_length F (fun R => x ∈ R)).symm
  rw [show PointDegree.degree F=(fun x => (F.map (fun R => if x ∈ R then 1 else 0)).sum)
    from funext heq,Weighted.sum_map_swap]
  apply Weighted.sum_map_le
  intro R hR
  rw [PointDegree.sum_indicator_eq_filter_length]
  exact hits_le_row X R hn

theorem exists_degree_le_on {n k budget cap : Nat} (X : Block n) (F : Family n)
    (hn : X.Nodup) (hlen : F.length≤budget)
    (hrows : ∀ R, R ∈ F → R.length≤k)
    (hgap : k*budget<X.length*(cap+1)) :
    ∃ x, x ∈ X ∧ PointDegree.degree F x≤cap := by
  apply Classical.byContradiction
  intro hnone
  have hlo := Weighted.sum_map_le X (fun _ => cap+1) (PointDegree.degree F) (by
    intro x hx
    have hh : ¬PointDegree.degree F x≤cap := fun h => hnone ⟨x,hx,h⟩
    omega)
  rw [PointDegree.sum_map_const] at hlo
  have hinc := incidence_le_on X F hn
  have hup := Weighted.sum_map_le_length_mul F List.length k hrows
  have hm := Nat.mul_le_mul_right k hlen
  rw [Nat.mul_comm budget k] at hm
  omega

theorem crossThree_unique_impossible {n : Nat} (X Y R S T : Block n)
    (hX : X.Nodup) (hY : Y.Nodup) (hXY : Disjoint X Y)
    (hx : 10≤X.length) (hy : 10≤Y.length)
    (hR : R.length≤12) (hS : S.length≤12) (hT : T.length≤12)
    (hcross : CrossThree X Y R S T) (x : Fin n) (hxX : x ∈ X)
    (hxS : x ∉ S) (hxT : x ∉ T) : False := by
  have hYR : Subset Y R := by
    intro y hy
    rcases hcross x hxX y hy with hr | hs | ht
    · exact hr.2
    · exact False.elim (hxS hs.1)
    · exact False.elim (hxT ht.1)
  let Z := X.filter (fun z => z ∉ R)
  have hsplit : (hits X R).length+Z.length=X.length := by
    have hh := (List.filter_append_perm (fun z : Fin n => decide (z ∈ R)) X).length_eq
    simpa [hits,Z] using hh
  have hcap := disjoint_hits_sum_le X Y R hX hY hXY
  rw [hits_eq_self Y R hYR] at hcap
  have hZlen : 8≤Z.length := by omega
  have hZ : Z.Nodup := hX.filter _
  have hZY : Disjoint Z Y := by
    intro z hz hy
    exact hXY z (List.mem_filter.mp hz).1 hy
  have htwo : CrossTwo Z Y S T := by
    intro z hz y hy
    have hzX := (List.mem_filter.mp hz).1
    have hzR : z ∉ R := of_decide_eq_true (List.mem_filter.mp hz).2
    rcases hcross z hzX y hy with hr | hs | ht
    · exact False.elim (hzR hr.1)
    · exact Or.inl hs
    · exact Or.inr ht
  exact crossTwo_impossible Z Y S T hZ hY hZY hZlen hy hS hT htwo

theorem crossThree_lowdegree_impossible {n : Nat} (X Y R S T : Block n)
    (hX : X.Nodup) (hY : Y.Nodup) (hXY : Disjoint X Y)
    (hx : 10≤X.length) (hy : 10≤Y.length)
    (hR : R.length≤12) (hS : S.length≤12) (hT : T.length≤12)
    (hcross : CrossThree X Y R S T) (x : Fin n) (hxX : x ∈ X)
    (hdeg : PointDegree.degree [R,S,T] x≤1) : False := by
  by_cases hxR : x ∈ R
  · have hxS : x ∉ S := by
      intro hh
      by_cases ht : x ∈ T <;> simp [PointDegree.degree,hxR,hh,ht] at hdeg
    have hxT : x ∉ T := by
      intro hh
      simp [PointDegree.degree,hxR,hxS,hh] at hdeg
    exact crossThree_unique_impossible X Y R S T hX hY hXY hx hy hR hS hT hcross x hxX hxS hxT
  · by_cases hxS : x ∈ S
    · have hxT : x ∉ T := by
        intro hh
        simp [PointDegree.degree,hxR,hxS,hh] at hdeg
      exact crossThree_unique_impossible X Y S R T hX hY hXY hx hy hS hR hT
        (crossThree_swap X Y R S T hcross) x hxX hxR hxT
    · exact crossThree_unique_impossible X Y T R S hX hY hXY hx hy hT hR hS
        (crossThree_rotate X Y R S T hcross) x hxX hxR hxS

theorem crossThree_impossible {n : Nat} (X Y R S T : Block n)
    (hX : X.Nodup) (hY : Y.Nodup) (hXY : Disjoint X Y)
    (hx : 10≤X.length) (hy : 10≤Y.length)
    (hR : R.length≤12) (hS : S.length≤12) (hT : T.length≤12)
    (hcross : CrossThree X Y R S T) : False := by
  have hn : (X++Y).Nodup := List.nodup_append.mpr ⟨hX,hY,by
    intro x hx y hy hxy
    subst y
    exact hXY x hx hy⟩
  have hrows : ∀ U, U ∈ [R,S,T] → U.length≤12 := by
    intro U hU
    simp at hU
    rcases hU with rfl | rfl | rfl <;> assumption
  obtain ⟨x,hxXY,hdeg⟩ := exists_degree_le_on (X++Y) [R,S,T] hn
    (show [R,S,T].length≤3 by simp) hrows (show 12*3<(X++Y).length*(1+1) by
      simp only [List.length_append]; omega)
  rcases List.mem_append.mp hxXY with hxX | hxY
  · exact crossThree_lowdegree_impossible X Y R S T hX hY hXY hx hy hR hS hT hcross x hxX hdeg
  · have hYX : Disjoint Y X := fun x hy hx => hXY x hx hy
    exact crossThree_lowdegree_impossible Y X R S T hY hX hYX hy hx hR hS hT
      (crossThree_symm X Y R S T hcross) x hxY hdeg

end Covering.CrossGrid
