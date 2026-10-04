import Regular20Twins

namespace CoveringMatrixRegular20
open Covering Covering.PointSplit Covering.PointDegree Covering.TwoPointSplit Covering.SideLift

lemma extended_eq (H E : Family 20) : extended H E=
    H.map (fun R => cone (cone R))++E.map (fun R => embed (embed R)) := by
  simp [extended,liftFour,lift,List.map_append,List.map_map,Function.comp_def]

def Hslot (H E : Family 20) (i : Fin H.length) : Fin (extended H E).length :=
  ⟨i.val,by rw [extended_eq,List.length_append,List.length_map,List.length_map]; omega⟩

lemma Hslot_injective (H E : Family 20) : Function.Injective (Hslot H E) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun z : Fin (extended H E).length => z.val) hij

lemma Hslot_get (H E : Family 20) (i : Fin H.length) :
    (extended H E).get (Hslot H E i)=cone (cone (H.get i)) := by
  simp [Hslot,List.get_eq_getElem,extended_eq,List.getElem_append,i.isLt]

lemma hits_cone_length {n : Nat} (R S : Block n) :
    (CrossGrid.hits (cone R) (cone S)).length=(CrossGrid.hits R S).length+1 := by
  unfold CrossGrid.hits
  change ((Fin.last n::embed R).filter (fun p => decide (p ∈ cone S))).length=
    (R.filter (fun p => decide (p ∈ S))).length+1
  simp only [List.filter_cons]
  simp [List.filter_map,embed,Function.comp_def]

/-- Intersections of actual H row slots, before choosing quotient coordinates. -/
theorem H_row_intersection_four (H E : Family 20) (h : Completion H E)
    (i j : Fin H.length) (hij : i≠j) : (CrossGrid.hits (H.get i) (H.get j)).length=4 := by
  have hh := CoveringMatrixRegular22.regular22_row_intersection_six (extended H E)
    (extended_rows H E h) (extended_cover H E h) (extended_length H E h)
    (extended_degree H E h) (Hslot H E i) (Hslot H E j)
    (fun he => hij (Hslot_injective H E he))
  rw [Hslot_get,Hslot_get,hits_cone_length,hits_cone_length] at hh
  omega

#print axioms H_row_intersection_four
end CoveringMatrixRegular20
