module

public import Covering.Rigidity.Twins

@[expose] public section

/-!
# Completions

Adding two points to the blocks of `H` gives an eleven-block `(22,12,3)` cover.
-/

namespace Covering.Completions
open Covering Covering.PointSplit Covering.PointDegree Covering.TwoPointSplit Covering.SideLift
open Covering.Floors

structure Completion (H E : Family 20) : Prop where
  H_length : H.length=6
  E_length : E.length=5
  H_rows : ∀ R, R ∈ H → ValidBlock 10 R
  E_rows : ∀ R, R ∈ E → ValidBlock 12 R
  H_degree : ∀ p, degree H p=3
  E_degree : ∀ p, degree E p=3
  H_cover : IsCovering 2 H
  all_cover : IsCovering 3 (H++E)

def extended (H E : Family 20) : Family 22 := liftFour H [] [] E

def old (p : Fin 20) : Fin 22 := p.castSucc.castSucc
def anchorFirst : Fin 22 := Fin.last 21
def anchorSecond : Fin 22 := (Fin.last 20).castSucc

lemma old_injective : Function.Injective old := by
  intro p q hpq
  exact Fin.castSucc_inj.mp (Fin.castSucc_inj.mp hpq)

lemma H_points (H E : Family 20) (h : Completion H E) : IsCovering 1 H := by
  intro S hS
  obtain ⟨p,rfl⟩ := Matching.list_of_length_one S hS.2
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

lemma H_row_lift_mem (H E : Family 20) (R : Block 20) (hR : R ∈ H) :
    cone (cone R) ∈ extended H E :=
  List.mem_append.mpr (Or.inl (List.mem_map_of_mem
    (List.mem_append.mpr (Or.inl (List.mem_map_of_mem hR)))))

lemma E_row_lift_mem (H E : Family 20) (R : Block 20) (hR : R ∈ E) :
    embed (embed R) ∈ extended H E :=
  List.mem_append.mpr (Or.inr (List.mem_map_of_mem
    (List.mem_append.mpr (Or.inr (List.mem_map_of_mem hR)))))

end Covering.Completions
