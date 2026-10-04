import Regular22RowGram

namespace CoveringMatrixRegular20
open Covering Covering.PointSplit Covering.PointDegree Covering.TwoPointSplit Covering.SideLift
open Covering.NormalizedBridge20261003

structure Completion (H E : Family 20) : Prop where
  H_length : H.length=6
  E_length : E.length=5
  H_rows : ∀ R, R ∈ H → ValidBlock 10 R
  E_rows : ∀ R, R ∈ E → ValidBlock 12 R
  H_degree : ∀ p, degree H p=3
  E_degree : ∀ p, degree E p=3
  H_cover : IsCovering 2 H
  all_cover : IsCovering 3 (H++E)

/-- Pair coverage and exact row incidence already force the H degrees. -/
lemma H_regular_from_pairs (H : Family 20) (hlen : H.length=6)
    (hrows : ∀ R, R ∈ H → ValidBlock 10 R) (hcover : IsCovering 2 H) :
    ∀ p, degree H p=3 := by
  have hlo (p : Fin 20) : 3≤degree H p := by
    let e := swapPoint p (Fin.last 19)
    have he : ∀ q, e (e q)=q := swapPoint_involutive p (Fin.last 19)
    let G := relabelFamily e H
    have hGrows := Regular22Matching.valid_rows_relabel H e e he hrows
    have hGcover : IsCovering 2 G := (isCovering_relabel_iff e e he he H).mpr hcover
    have hc := Regular22Matching.point_cover_count (through G)
      (fun R hR => Nat.le_of_eq (through_valid G hGrows R hR).2)
      (covering_split G hGcover).1
    have hd : (through G).length=degree H p := by
      rw [through_length]
      exact degree_swap_right H p (Fin.last 19)
    rw [hd] at hc
    omega
  have hi := incidence_le H
  have hu := Weighted.sum_map_le_length_mul H List.length 10
    (fun R hR => Nat.le_of_eq (hrows R hR).2)
  rw [hlen] at hu
  have he := pointwise_eq_of_sum_le (List.finRange 20) (fun _ => 3) (degree H)
    (fun p _ => hlo p) (by
      rw [sum_map_const,List.length_finRange]
      omega)
  intro p
  exact (he p (by simp)).symm

def extended (H E : Family 20) : Family 22 := liftFour H [] [] E

def old (p : Fin 20) : Fin 22 := p.castSucc.castSucc
def anchorFirst : Fin 22 := Fin.last 21
def anchorSecond : Fin 22 := (Fin.last 20).castSucc

lemma old_injective : Function.Injective old := by
  intro p q hpq
  exact Fin.castSucc_inj.mp (Fin.castSucc_inj.mp hpq)

lemma H_points (H E : Family 20) (h : Completion H E) : IsCovering 1 H := by
  intro S hS
  obtain ⟨p,rfl⟩ := Regular22Matching.list_of_length_one S hS.2
  have hlen : 0<(H.filter (fun R => p ∈ R)).length := by
    change 0<degree H p
    rw [h.H_degree p]
    decide
  obtain ⟨R,hR⟩ := List.exists_mem_of_length_pos hlen
  obtain ⟨hRH,hpR⟩ := List.mem_filter.mp hR
  have hpR : p ∈ R := of_decide_eq_true hpR
  refine ⟨R,hRH,?_⟩
  intro q hq
  have hqp : q=p := List.mem_singleton.mp hq
  subst q
  exact hpR

lemma extended_length (H E : Family 20) (h : Completion H E) : (extended H E).length=11 := by
  simp [extended,liftFour,lift_length,h.H_length,h.E_length]

lemma extended_rows (H E : Family 20) (h : Completion H E) :
    ∀ R, R ∈ extended H E → ValidBlock 12 R :=
  lift_valid _ _ (lift_valid H [] h.H_rows (by simp)) (lift_valid [] E (by simp) h.E_rows)

lemma extended_cover (H E : Family 20) (h : Completion H E) : IsCovering 3 (extended H E) := by
  apply (covering_liftFour_iff H [] [] E).mpr
  exact ⟨H_points H E h,by simpa using h.H_cover,by simpa using h.H_cover,
    by simpa using h.all_cover⟩

lemma extended_degree (H E : Family 20) (h : Completion H E) :
    ∀ p, degree (extended H E) p=6 := by
  intro p
  refine Fin.lastCases ?_ (fun q => ?_) p
  · change degree (lift (lift H []) (lift [] E)) (Fin.last 21)=6
    rw [degree_lift_last,lift_length,h.H_length]
    rfl
  · refine Fin.lastCases ?_ (fun r => ?_) q
    · change degree (lift (lift H []) (lift [] E)) (Fin.last 20).castSucc=6
      rw [degree_lift_old,degree_lift_last,degree_lift_last,h.H_length]
      rfl
    · change degree (lift (lift H []) (lift [] E)) r.castSucc.castSucc=6
      rw [degree_lift_old,degree_lift_old,degree_lift_old,h.H_degree,h.E_degree]
      simp [degree]

lemma pair_lift_old {n : Nat} (A B : Family n) (p q : Fin n) :
    pairDegree (lift A B) p.castSucc q.castSucc=pairDegree A p q+pairDegree B p q := by
  simp [pairDegree,lift,List.filter_append,List.filter_map,Function.comp_def]

lemma pair_lift_last_old {n : Nat} (A B : Family n) (p : Fin n) :
    pairDegree (lift A B) (Fin.last n) p.castSucc=degree A p := by
  simp [pairDegree,degree,lift,List.filter_append,List.filter_map,Function.comp_def]

lemma old_pair (H E : Family 20) (p q : Fin 20) :
    pairDegree (extended H E) (old p) (old q)=pairDegree H p q+pairDegree E p q := by
  simp only [extended,liftFour,old,pair_lift_old]
  simp [pairDegree]

lemma first_old_pair (H E : Family 20) (h : Completion H E) (p : Fin 20) :
    pairDegree (extended H E) anchorFirst (old p)=3 := by
  simp only [extended,liftFour,anchorFirst,old,pair_lift_last_old,degree_lift_old]
  rw [h.H_degree p]
  simp [degree]

lemma second_old_pair (H E : Family 20) (h : Completion H E) (p : Fin 20) :
    pairDegree (extended H E) anchorSecond (old p)=3 := by
  simp only [extended,liftFour,anchorSecond,old,pair_lift_old,pair_lift_last_old]
  rw [h.H_degree p]
  simp [degree]

lemma anchor_pair (H E : Family 20) (h : Completion H E) :
    pairDegree (extended H E) anchorFirst anchorSecond=6 := by
  simp only [extended,liftFour,anchorFirst,anchorSecond,pair_lift_last_old,degree_lift_last]
  exact h.H_length

lemma H_row_lift_mem (H E : Family 20) (R : Block 20) (hR : R ∈ H) :
    cone (cone R) ∈ extended H E :=
  List.mem_append.mpr (Or.inl (List.mem_map_of_mem
    (List.mem_append.mpr (Or.inl (List.mem_map_of_mem hR)))))

lemma E_row_lift_mem (H E : Family 20) (R : Block 20) (hR : R ∈ E) :
    embed (embed R) ∈ extended H E :=
  List.mem_append.mpr (Or.inr (List.mem_map_of_mem
    (List.mem_append.mpr (Or.inr (List.mem_map_of_mem hR)))))

end CoveringMatrixRegular20
