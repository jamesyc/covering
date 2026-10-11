module

public import Covering.Basic.PointCover

@[expose] public section

/-!
# Linear families of triples

Lemma 5.1: a family of triples on at most six points in which any two triples meet
in exactly one point has at most four members.
-/

namespace Covering.LinearTriples

open CrossGrid PointDegree HitSums PointCover

theorem supported_hits_length {n : Nat} (W R : Block n)
    (hW : W.Nodup) (hR : R.Nodup) (hRW : Subset R W) :
    (hits W R).length=R.length := by
  apply Nat.le_antisymm (hits_le_row W R hW)
  apply hR.length_le_of_subset
  intro x hx
  exact (mem_hits W R x).mpr ⟨hRW x hx,hx⟩

theorem presence_sum {n : Nat} (W R : Block n)
    (hW : W.Nodup) (hR : R.Nodup) (hRW : Subset R W) :
    (W.map (fun x => if x ∈ R then 1 else 0)).sum=R.length := by
  rw [sum_constant_hits,Nat.one_mul]
  exact supported_hits_length W R hW hR hRW

theorem pair_presence_sum {n : Nat} (W R S : Block n)
    (hW : W.Nodup) (hR : R.Nodup) (hRW : Subset R W) :
    (W.map (fun x => if x ∈ R ∧ x ∈ S then 1 else 0)).sum=(hits R S).length := by
  have he : (fun x : Fin n => if x ∈ R ∧ x ∈ S then 1 else 0)=
      (fun x => if x ∈ hits R S then 1 else 0) := by
    funext x
    simp only [mem_hits]
  rw [he]
  exact presence_sum W (hits R S) hW (hR.filter _) (fun x hx => hRW x ((mem_hits R S x).mp hx).1)

/-- Three 3-subsets with pair intersections exactly one and a common point
need at least seven support points. This proof is direct incidence counting. -/
theorem three_common_point_impossible {n : Nat} (W R S T : Block n)
    (hW : W.Nodup) (hWlen : W.length≤6)
    (hR : ValidBlock 3 R) (hS : ValidBlock 3 S) (hT : ValidBlock 3 T)
    (hRW : Subset R W) (hSW : Subset S W) (hTW : Subset T W)
    (hRS : (hits R S).length=1) (hRT : (hits R T).length=1) (hST : (hits S T).length=1)
    (x : Fin n) (hxR : x ∈ R) (hxS : x ∈ S) (hxT : x ∈ T) : False := by
  have hp : 1≤(W.map (fun p => if p ∈ R ∧ p ∈ S ∧ p ∈ T then 1 else 0)).sum := by
    have hh := Weighted.term_le_sum_map W (fun p => if p ∈ R ∧ p ∈ S ∧ p ∈ T then 1 else 0) x (hRW x hxR)
    simpa only [hxR,hxS,hxT,and_self,ite_true] using hh
  have hpoint (p : Fin n) (_ : p ∈ W) :
      (if p ∈ R then 1 else 0)+(if p ∈ S then 1 else 0)+(if p ∈ T then 1 else 0)+
        (if p ∈ R ∧ p ∈ S ∧ p ∈ T then 1 else 0)≤
      1+(if p ∈ R ∧ p ∈ S then 1 else 0)+(if p ∈ R ∧ p ∈ T then 1 else 0)+
        (if p ∈ S ∧ p ∈ T then 1 else 0) := by
    by_cases hr : p ∈ R <;> by_cases hs : p ∈ S <;> by_cases ht : p ∈ T <;> simp [hr,hs,ht]
  have hh := Weighted.sum_map_le W
    (fun p => (if p ∈ R then 1 else 0)+(if p ∈ S then 1 else 0)+(if p ∈ T then 1 else 0)+
      (if p ∈ R ∧ p ∈ S ∧ p ∈ T then 1 else 0))
    (fun p => 1+(if p ∈ R ∧ p ∈ S then 1 else 0)+(if p ∈ R ∧ p ∈ T then 1 else 0)+
      (if p ∈ S ∧ p ∈ T then 1 else 0)) hpoint
  simp only [Weighted.sum_map_add,sum_map_const] at hh
  rw [presence_sum W R hW hR.1 hRW,presence_sum W S hW hS.1 hSW,
    presence_sum W T hW hT.1 hTW,pair_presence_sum W R S hW hR.1 hRW,
    pair_presence_sum W R T hW hR.1 hRW,pair_presence_sum W S T hW hS.1 hSW] at hh
  rw [hR.2,hS.2,hT.2,hRS,hRT,hST] at hh
  omega

theorem three_prefix {α : Type} (L : List α) (h : 3≤L.length) :
    ∃ a b c Q, L=a::b::c::Q := by
  cases L with
  | nil => simp at h
  | cons a L =>
    cases L with
    | nil => simp at h
    | cons b L =>
      cases L with
      | nil => simp at h
      | cons c Q => exact ⟨a,b,c,Q,rfl⟩

theorem point_degree_le_two {n : Nat} (W : Block n) (F : Family n)
    (hW : W.Nodup) (hWlen : W.length≤6)
    (hrows : ∀ R, R ∈ F → ValidBlock 3 R ∧ Subset R W)
    (hpairs : F.Pairwise (fun R S => (hits R S).length=1)) (x : Fin n) : degree F x≤2 := by
  apply Classical.byContradiction
  intro hn
  let P := F.filter (fun R => x ∈ R)
  obtain ⟨R,S,T,Q,hP⟩ := three_prefix P (by change 3≤degree F x; omega)
  have hRp : R ∈ P := by rw [hP]; simp
  have hSp : S ∈ P := by rw [hP]; simp
  have hTp : T ∈ P := by rw [hP]; simp
  have hRm : R ∈ F ∧ x ∈ R := by simpa only [P,List.mem_filter,decide_eq_true_eq] using hRp
  have hSm : S ∈ F ∧ x ∈ S := by simpa only [P,List.mem_filter,decide_eq_true_eq] using hSp
  have hTm : T ∈ F ∧ x ∈ T := by simpa only [P,List.mem_filter,decide_eq_true_eq] using hTp
  have hPairP : P.Pairwise (fun R S => (hits R S).length=1) := hpairs.filter _
  rw [hP] at hPairP
  have hRS := (List.pairwise_cons.mp hPairP).1 S (by simp)
  have hRT := (List.pairwise_cons.mp hPairP).1 T (by simp)
  have hST := (List.pairwise_cons.mp (List.pairwise_cons.mp hPairP).2).1 T (by simp)
  exact three_common_point_impossible W R S T hW hWlen
    (hrows R hRm.1).1 (hrows S hSm.1).1 (hrows T hTm.1).1
    (hrows R hRm.1).2 (hrows S hSm.1).2 (hrows T hTm.1).2
    hRS hRT hST x hRm.2 hSm.2 hTm.2

/-- The incidence count behind Lemma 5.1. -/
theorem incidence_bound {n : Nat} (W : Block n) (F : Family n)
    (hW : W.Nodup) (hWlen : W.length≤6)
    (hrows : ∀ R, R ∈ F → ValidBlock 3 R ∧ Subset R W)
    (hpairs : F.Pairwise (fun R S => (hits R S).length=1)) : 3*F.length≤2*W.length := by
  have hu := Weighted.sum_map_le_length_mul W (degree F) 2
    (fun x _ => point_degree_le_two W F hW hWlen hrows hpairs x)
  rw [incidence_on_eq] at hu
  have hm : F.map (fun R => (hits W R).length)=F.map (fun _ => 3) := by
    apply List.map_congr_left
    intro R hR
    exact (supported_hits_length W R hW (hrows R hR).1.1 (hrows R hR).2).trans (hrows R hR).1.2
  rw [hm,sum_map_const] at hu
  simpa only [Nat.mul_comm] using hu

/-- Lemma 5.1: triples on at most six points that pairwise meet in exactly one
point number at most four. (Repeated triples would meet in three points.) -/
theorem cardinality_le_four {n : Nat} (W : Block n) (F : Family n)
    (hW : W.Nodup) (hWlen : W.length≤6)
    (hrows : ∀ R, R ∈ F → ValidBlock 3 R ∧ Subset R W)
    (hpairs : F.Pairwise (fun R S => (hits R S).length=1)) : F.length≤4 := by
  have hh := incidence_bound W F hW hWlen hrows hpairs
  omega


/-- Lemma 5.1 as stated in the paper: no five triples on six points pairwise meet
    in exactly one point. -/
theorem five_triples_on_six_positions {n : Nat} (W : Block n) (F : Family n)
    (hW : ValidBlock 6 W) (hF : F.length = 5)
    (hrows : ∀ R, R ∈ F → ValidBlock 3 R ∧ Covering.Subset R W)
    (hpairs : F.Pairwise (fun R S => (hits R S).length = 1)) : False := by
  have h := cardinality_le_four
    W F hW.1 (Nat.le_of_eq hW.2) hrows hpairs
  omega

end Covering.LinearTriples
