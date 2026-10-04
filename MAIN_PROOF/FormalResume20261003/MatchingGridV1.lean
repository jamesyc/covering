import campaigns.async_goal.lean.recovered.CrossGridThreeRecoveredV3
import campaigns.async_goal.lean.twin_cap.CliqueIncidenceV2
import campaigns.async_goal.lean.recovered.PairLowerBoundRecoveredV4

namespace Covering.NormalizedBridge20261003.MatchingGrid

open CrossGrid PointDegree TwinCap.CliqueIncidence

theorem grid_unique_impossible {n : Nat} (X Y R S T : Block n)
    (hX : X.Nodup) (hY : Y.Nodup) (hXY : Disjoint X Y)
    (hx : 9≤X.length) (hy : 9≤Y.length) (hxylen : 19≤X.length+Y.length)
    (hR : R.length≤11) (hS : S.length≤11) (hT : T.length≤11)
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
  have hh := crossTwo_capacity_disjunction Z Y S T hZ hY hZY
    (by omega) (by omega) hS hT htwo
  omega

theorem grid_lowdegree_impossible {n : Nat} (X Y R S T : Block n)
    (hX : X.Nodup) (hY : Y.Nodup) (hXY : Disjoint X Y)
    (hx : 9≤X.length) (hy : 9≤Y.length) (hxylen : 19≤X.length+Y.length)
    (hR : R.length≤11) (hS : S.length≤11) (hT : T.length≤11)
    (hcross : CrossThree X Y R S T) (x : Fin n) (hxX : x ∈ X)
    (hdeg : PointDegree.degree [R,S,T] x≤1) : False := by
  by_cases hxR : x ∈ R
  · have hxS : x ∉ S := by
      intro hh
      by_cases ht : x ∈ T <;> simp [PointDegree.degree,hxR,hh,ht] at hdeg
    have hxT : x ∉ T := by
      intro hh
      simp [PointDegree.degree,hxR,hxS,hh] at hdeg
    exact grid_unique_impossible X Y R S T hX hY hXY hx hy hxylen hR hS hT hcross x hxX hxS hxT
  · by_cases hxS : x ∈ S
    · have hxT : x ∉ T := by
        intro hh
        simp [PointDegree.degree,hxR,hxS,hh] at hdeg
      exact grid_unique_impossible X Y S R T hX hY hXY hx hy hxylen hS hR hT
        (crossThree_swap X Y R S T hcross) x hxX hxR hxT
    · exact grid_unique_impossible X Y T R S hX hY hXY hx hy hxylen hT hR hS
        (crossThree_rotate X Y R S T hcross) x hxX hxR hxS

theorem grid_three_impossible {n : Nat} (X Y R S T : Block n)
    (hX : X.Nodup) (hY : Y.Nodup) (hXY : Disjoint X Y)
    (hx : 9≤X.length) (hy : 9≤Y.length) (hxylen : 19≤X.length+Y.length)
    (hR : R.length≤11) (hS : S.length≤11) (hT : T.length≤11)
    (hcross : CrossThree X Y R S T) : False := by
  have hn : (X++Y).Nodup := List.nodup_append.mpr ⟨hX,hY,by
    intro x hx y hy hxy
    subst y
    exact hXY x hx hy⟩
  have hrows : ∀ U, U ∈ [R,S,T] → U.length≤11 := by
    intro U hU
    simp at hU
    rcases hU with rfl | rfl | rfl <;> assumption
  obtain ⟨x,hxXY,hdeg⟩ := exists_degree_le_on (X++Y) [R,S,T] hn
    (show [R,S,T].length≤3 by simp) hrows (show 11*3<(X++Y).length*(1+1) by
      simp only [List.length_append]; omega)
  rcases List.mem_append.mp hxXY with hxX | hxY
  · exact grid_lowdegree_impossible X Y R S T hX hY hXY hx hy hxylen hR hS hT hcross x hxX hdeg
  · have hYX : Disjoint Y X := fun x hy hx => hXY x hx hy
    exact grid_lowdegree_impossible Y X R S T hY hX hYX hy hx (by omega) hR hS hT
      (crossThree_symm X Y R S T hcross) x hxY hdeg

theorem no_three_rows {n : Nat} (X Y : Block n) (F : Family n)
    (hX : X.Nodup) (hY : Y.Nodup) (hXY : Disjoint X Y)
    (hx : 9≤X.length) (hy : 9≤Y.length) (hxy : 19≤X.length+Y.length)
    (hF : F.length=3) (hrows : ∀ R, R ∈ F → R.length≤11)
    (hcover : CrossCover X Y F) : False := by
  obtain ⟨R,S,T,rfl⟩ := PairLowerBound.list_of_length_three F hF
  apply grid_three_impossible X Y R S T hX hY hXY hx hy hxy
    (hrows R (by simp)) (hrows S (by simp)) (hrows T (by simp))
  intro x hx y hy
  obtain ⟨Q,hQ,hxQ,hyQ⟩ := hcover x hx y hy
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl
  · exact Or.inl ⟨hxQ,hyQ⟩
  · exact Or.inr (Or.inl ⟨hxQ,hyQ⟩)
  · exact Or.inr (Or.inr ⟨hxQ,hyQ⟩)

end Covering.NormalizedBridge20261003.MatchingGrid
