module

public import TwinProviderTrace
public import OmissionSlotCounting

@[expose] public section

open Matrix Finset
open scoped BigOperators
namespace Covering.NormalizedBridge20261003.ExceptionBranch
open TwinFrame PointDegree SideLift CrossGrid A19Physical CoveringOutsideTrace

lemma trace_hits {n m : ℕ} {U : Block n} (e : Fin m ≃ Outside U) (A R : Block n) :
    hits (trace e A) (trace e R) = trace e (hits A R) := by
  simp [hits, CoveringOutsideTrace.trace, List.filter_filter, and_comm, Bool.and_comm]

lemma trace_length_disjoint {n m : ℕ} {U : Block n} (e : Fin m ≃ Outside U)
    (hU : U.Nodup) (A : Block n) (hA : A.Nodup) (hUA : Covering.Disjoint U A) :
    (trace e A).length = A.length := by
  have hempty : hits U A = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    have hn : p ∉ A := hUA p hp
    simpa using hn
  have h := trace_length_partition e hU A hA
  rw [hempty, List.length_nil, add_zero] at h
  exact h

lemma trace_hits_length {n m : ℕ} {U : Block n} (e : Fin m ≃ Outside U)
    (hU : U.Nodup) (A R : Block n) (hA : A.Nodup) (hUA : Covering.Disjoint U A) :
    (hits (trace e A) (trace e R)).length = (hits A R).length := by
  rw [trace_hits]
  exact trace_length_disjoint e hU (hits A R) (hA.filter _)
    (fun p hp hhit => hUA p hp ((mem_hits A R p).mp hhit).1)

def signedVector {n : ℕ} (A B : Block n) : Fin n → ℝ :=
  fun p => (if p ∈ A then 1 else 0) - (if p ∈ B then 1 else 0)

lemma real_hit_sum {n : ℕ} (A R : Block n) (hA : A.Nodup) :
    (∑ p : Fin n, (if p ∈ R then (1 : ℝ) else 0) * (if p ∈ A then 1 else 0)) =
      (hits A R).length := by
  have hn : (∑ p : Fin n, if p ∈ A ∧ p ∈ R then (1 : ℕ) else 0) =
      (hits A R).length := by
    rw [Fin.sum_univ_def]
    exact LinearTriples.pair_presence_sum (List.finRange n) A R (List.nodup_finRange _)
      hA (fun p _ => by simp)
  have hr : (∑ p : Fin n, if p ∈ A ∧ p ∈ R then (1 : ℝ) else 0) =
      (hits A R).length := by exact_mod_cast hn
  rw [← hr]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p ∈ R <;> by_cases ha : p ∈ A <;> simp [hp, ha]

lemma transpose_kernel_of_hit_balance {n : ℕ} (F : Family n) (A B : Block n)
    (hA : A.Nodup) (hB : B.Nodup)
    (hbalance : ∀ R, R ∈ F → (hits A R).length = (hits B R).length) :
    (CoveringMatrixIncidence.incidence F).transpose *ᵥ signedVector A B = 0 := by
  ext j
  change (∑ p : Fin n, (if p ∈ F.get j then (1 : ℝ) else 0) *
    ((if p ∈ A then 1 else 0) - (if p ∈ B then 1 else 0))) = 0
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, real_hit_sum A (F.get j) hA, real_hit_sum B (F.get j) hB,
    hbalance (F.get j) (List.get_mem F j), sub_self]

lemma trace_signed_kernel {n m : ℕ} {U : Block n} (e : Fin m ≃ Outside U)
    (hU : U.Nodup) (F : Family n) (A B : Block n) (hA : A.Nodup) (hB : B.Nodup)
    (hUA : Covering.Disjoint U A) (hUB : Covering.Disjoint U B)
    (hbalance : ∀ R, R ∈ F → (hits A R).length = (hits B R).length) :
    (CoveringMatrixIncidence.incidence (traces e F)).transpose *ᵥ
      signedVector (trace e A) (trace e B) = 0 := by
  apply transpose_kernel_of_hit_balance _ _ _ (trace_nodup e A) (trace_nodup e B)
  intro R hR
  obtain ⟨Arow, hArow, rfl⟩ := List.mem_map.mp hR
  rw [trace_hits_length e hU A Arow hA hUA, trace_hits_length e hU B Arow hB hUB]
  exact hbalance Arow hArow

noncomputable def partBlock {T : Family 24} (A : Finset (LowPoint T)) : Block 24 :=
  A.toList.map Subtype.val

lemma partBlock_nodup {T : Family 24} (A : Finset (LowPoint T)) : (partBlock A).Nodup :=
  List.Nodup.map Subtype.val_injective A.nodup_toList

lemma mem_partBlock {T : Family 24} (A : Finset (LowPoint T)) (x : Fin 24) :
    x ∈ partBlock A ↔ ∃ p ∈ A, p.val = x := by simp [partBlock]

lemma partBlock_length {T : Family 24} (A : Finset (LowPoint T)) :
    (partBlock A).length = A.card := by simp [partBlock]

lemma partBlock_hits {T : Family 24} (A : Finset (LowPoint T)) (R : Block 24) :
    (hits (partBlock A) R).length = (A.filter fun p => p.val ∈ R).card := by
  simp only [partBlock, hits, List.filter_map, List.length_map]
  rw [← List.toFinset_card_of_nodup (A.nodup_toList.filter _)]
  simp

lemma parts_balance_rows {T : Family 24} (A B : Finset (LowPoint T))
    (hbalance : ∀ j : Fin T.length,
      (A.filter fun p => p.val ∈ T.get j).card = (B.filter fun p => p.val ∈ T.get j).card) :
    ∀ R, R ∈ T → (hits (partBlock A) R).length = (hits (partBlock B) R).length := by
  intro R hR
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hR
  rw [partBlock_hits, partBlock_hits]
  exact hbalance j

lemma part_disjoint_removed {T : Family 24}
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (E : ExceptionalComponents T hrows hcover) (f : TwinFrame T)
    (hf : ∀ r : LowPoint T, (lowSystem T hrows hcover).graph.connectedComponentMk r = E.c2 ↔
      r = f.q ∨ r = f.mate)
    (c : (lowSystem T hrows hcover).graph.ConnectedComponent) (hc : c ≠ E.c2)
    (A : Finset (LowPoint T))
    (hA : ∀ r ∈ A, (lowSystem T hrows hcover).graph.connectedComponentMk r = c) :
    Covering.Disjoint f.removed (partBlock A) := by
  intro x hx hxA
  obtain ⟨r, hr, hrx⟩ := (mem_partBlock A x).mp hxA
  have hrc := hA r hr
  have hr2 : (lowSystem T hrows hcover).graph.connectedComponentMk r = E.c2 := by
    apply (hf r).mpr
    simp only [removed, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · exact Or.inl (Subtype.ext (hrx.trans hx))
    · exact Or.inr (Subtype.ext (hrx.trans hx))
  exact hc (hrc.symm.trans hr2)

end Covering.NormalizedBridge20261003.ExceptionBranch
#print axioms Covering.NormalizedBridge20261003.ExceptionBranch.trace_signed_kernel
#print axioms Covering.NormalizedBridge20261003.ExceptionBranch.partBlock_hits
#print axioms Covering.NormalizedBridge20261003.ExceptionBranch.part_disjoint_removed
