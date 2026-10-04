import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import FormalResume20261003.Regular22TwoProviderV1

open Finset
open scoped BigOperators
namespace CoveringOutsideTrace
open Covering Covering.PointDegree Covering.SideLift Covering.CrossGrid
open Covering.NormalizedBridge20261003

abbrev Outside {n : Nat} (U : Block n) := {p : Fin n // p ∉ U.toFinset}

lemma outside_card {n k m : Nat} (U : Block n) (hU : ValidBlock k U) (hn : n=k+m) :
    Fintype.card (Outside U)=m := by
  rw [Fintype.card_subtype_compl,Fintype.card_coe,Fintype.card_fin,
    List.toFinset_card_of_nodup hU.1,hU.2]
  omega

noncomputable def coordinates {n k m : Nat} (U : Block n) (hU : ValidBlock k U)
    (hn : n=k+m) : Fin m ≃ Outside U :=
  (Fintype.equivFinOfCardEq (outside_card U hU hn)).symm

def point {n m : Nat} {U : Block n} (e : Fin m ≃ Outside U) (p : Fin m) : Fin n := (e p).val

def trace {n m : Nat} {U : Block n} (e : Fin m ≃ Outside U) (R : Block n) : Block m :=
  (List.finRange m).filter (fun p => point e p ∈ R)

def traces {n m : Nat} {U : Block n} (e : Fin m ≃ Outside U) (F : Family n) : Family m :=
  F.map (trace e)

lemma point_injective {n m : Nat} {U : Block n} (e : Fin m ≃ Outside U) :
    Function.Injective (point e) := by
  intro p q hpq
  exact e.injective (Subtype.ext hpq)

lemma point_not_mem {n m : Nat} {U : Block n} (e : Fin m ≃ Outside U) (p : Fin m) :
    point e p ∉ U := by
  intro hp
  exact (e p).property (List.mem_toFinset.mpr hp)

@[simp] lemma mem_trace {n m : Nat} {U : Block n} (e : Fin m ≃ Outside U)
    (R : Block n) (p : Fin m) : p ∈ trace e R ↔ point e p ∈ R := by simp [trace]

lemma trace_nodup {n m : Nat} {U : Block n} (e : Fin m ≃ Outside U) (R : Block n) :
    (trace e R).Nodup := (List.nodup_finRange m).filter _

lemma trace_length_partition {n m : Nat} {U : Block n} (e : Fin m ≃ Outside U)
    (hU : U.Nodup) (R : Block n) (hR : R.Nodup) :
    (trace e R).length+(hits U R).length=R.length := by
  let f : Fin n → Nat := fun p => if p ∈ R then 1 else 0
  have hall : (∑ p, f p)=R.length := by
    rw [Fin.sum_univ_def]
    exact LinearTriples.presence_sum (List.finRange n) R (List.nodup_finRange n)
      hR (fun p _ => by simp)
  have hin : (∑ p ∈ U.toFinset, f p)=(hits U R).length := by
    rw [List.sum_toFinset f hU]
    exact sum_indicator_eq_filter_length U (fun p => p ∈ R)
  have hout : (∑ p : Outside U, f p.val)=(trace e R).length := by
    rw [← e.sum_comp (fun p : Outside U => f p.val),Fin.sum_univ_def]
    change ((List.finRange m).map (fun p => if point e p ∈ R then 1 else 0)).sum=
      (trace e R).length
    rw [sum_indicator_eq_filter_length]
    rfl
  have houtSet : (∑ p ∈ U.toFinsetᶜ, f p)=(trace e R).length :=
    (Finset.sum_subtype (p := fun p : Fin n => p ∉ U.toFinset) U.toFinsetᶜ
      (fun p => by simp) f).trans hout
  have hs := U.toFinset.sum_add_sum_compl f
  rw [hin,houtSet,hall] at hs
  omega

lemma valid_trace {n m k c : Nat} {U : Block n} (e : Fin m ≃ Outside U)
    (hU : U.Nodup) (R : Block n) (hR : ValidBlock (k+c) R)
    (hc : (hits U R).length=c) : ValidBlock k (trace e R) := by
  have hh := trace_length_partition e hU R hR.1
  rw [hc,hR.2] at hh
  exact ⟨trace_nodup e R,by omega⟩

@[simp] lemma traces_length {n m : Nat} {U : Block n} (e : Fin m ≃ Outside U) (F : Family n) :
    (traces e F).length=F.length := by simp [traces]

lemma degree_traces {n m : Nat} {U : Block n} (e : Fin m ≃ Outside U) (F : Family n)
    (p : Fin m) : degree (traces e F) p=degree F (point e p) := by
  simp [degree,traces,List.filter_map,Function.comp_def]

lemma pair_degree_traces {n m : Nat} {U : Block n} (e : Fin m ≃ Outside U) (F : Family n)
    (p q : Fin m) : pairDegree (traces e F) p q=pairDegree F (point e p) (point e q) := by
  simp [pairDegree,traces,List.filter_map,Function.comp_def]

lemma valid_append_core {n m s t : Nat} {U : Block n} (e : Fin m ≃ Outside U)
    (P : Block n) (hP : ValidBlock s P) (hPU : Covering.Subset P U)
    (Q : Block m) (hQ : ValidBlock t Q) : ValidBlock (s+t) (P++Q.map (point e)) := by
  refine ⟨List.nodup_append.mpr ⟨hP.1,List.Nodup.map (point_injective e) hQ.1,?_⟩,?_⟩
  · intro x hx y hy hxy
    obtain ⟨p,_,hpy⟩ := List.mem_map.mp hy
    apply point_not_mem e p
    rw [hpy,← hxy]
    exact hPU x hx
  · simp only [List.length_append,List.length_map,hP.2,hQ.2]

lemma covering_from_core {n m s t : Nat} {U : Block n} (e : Fin m ≃ Outside U)
    (F : Family n) (P : Block n) (hP : ValidBlock s P) (hPU : Covering.Subset P U)
    (hcover : IsCovering (s+t) F) :
    IsCovering t (traces e (F.filter (fun R => Covering.Subset P R))) := by
  intro Q hQ
  obtain ⟨R,hR,hs⟩ := hcover (P++Q.map (point e)) (valid_append_core e P hP hPU Q hQ)
  have hPR : Covering.Subset P R := fun p hp => hs p (List.mem_append.mpr (Or.inl hp))
  refine ⟨trace e R,List.mem_map.mpr ⟨R,List.mem_filter.mpr ⟨hR,by simpa using hPR⟩,rfl⟩,?_⟩
  intro p hp
  apply (mem_trace e R p).mpr
  exact hs (point e p) (List.mem_append.mpr (Or.inr (List.mem_map_of_mem hp)))

#print axioms coordinates
#print axioms trace_length_partition
#print axioms degree_traces
#print axioms pair_degree_traces
#print axioms covering_from_core
end CoveringOutsideTrace
