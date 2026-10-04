module

public import A19GadgetInterface

@[expose] public section

open Matrix Finset
open scoped BigOperators
namespace Covering.NormalizedBridge20261003.A19Physical
open PointDegree SideLift WeightedKernelComponents

lemma pair_from_two_component (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (c : (lowSystem T hrows hcover).graph.ConnectedComponent)
    (hc : (lowSystem T hrows hcover).BalancedBipartite c)
    (hsize : (lowSystem T hrows hcover).componentSize c = 2) :
    ∃ u v : LowPoint T, u ≠ v ∧
      (∀ r, (lowSystem T hrows hcover).graph.connectedComponentMk r = c ↔ r = u ∨ r = v) ∧
      (∀ R, R ∈ T → (if u.val ∈ R then (1 : ℕ) else 0) =
        (if v.val ∈ R then (1 : ℕ) else 0)) := by
  classical
  let S := lowSystem T hrows hcover
  obtain ⟨A, B, _, _, hdis, hcard, hcomp, hbalance, _⟩ :=
    component_slot_balance_with_edges T hrows hcover c hc
  have hsupp : S.componentVertices c = A ∪ B := by
    ext r
    simpa [System.componentVertices, S] using hcomp r
  have hA1 : A.card = 1 := by
    change (S.componentVertices c).card = 2 at hsize
    rw [hsupp, Finset.card_union_of_disjoint hdis, ← hcard] at hsize
    omega
  have hB1 : B.card = 1 := by omega
  obtain ⟨u, hA⟩ := Finset.card_eq_one.mp hA1
  obtain ⟨v, hB⟩ := Finset.card_eq_one.mp hB1
  have hu : u ∈ A := by rw [hA]; simp
  have hv : v ∈ B := by rw [hB]; simp
  have huv : u ≠ v := fun h => Finset.disjoint_left.mp hdis hu (h.symm ▸ hv)
  refine ⟨u, v, huv, ?_, ?_⟩
  · intro r
    simpa [hA, hB] using hcomp r
  · intro R hR
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hR
    have hsing (a : LowPoint T) :
        (({a} : Finset (LowPoint T)).filter fun r => r.val ∈ T.get j).card =
          (if a.val ∈ T.get j then 1 else 0) := by
      rw [Finset.filter_singleton]
      split_ifs <;> rfl
    have hb := hbalance j
    rw [hA, hB, hsing u, hsing v] at hb
    exact hb

lemma has_gadget_of_two_two_components (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (c d : (lowSystem T hrows hcover).graph.ConnectedComponent) (hcd : c ≠ d)
    (hc : (lowSystem T hrows hcover).BalancedBipartite c)
    (hd : (lowSystem T hrows hcover).BalancedBipartite d)
    (hsizec : (lowSystem T hrows hcover).componentSize c = 2)
    (hsized : (lowSystem T hrows hcover).componentSize d = 2) : HasGadget T := by
  classical
  let S := lowSystem T hrows hcover
  obtain ⟨u, s, hus, hcompc, hbalc⟩ := pair_from_two_component T hrows hcover c hc hsizec
  obtain ⟨v, t, hvt, hcompd, hbald⟩ := pair_from_two_component T hrows hcover d hd hsized
  have huc : S.graph.connectedComponentMk u = c := (hcompc u).mpr (Or.inl rfl)
  have hsc : S.graph.connectedComponentMk s = c := (hcompc s).mpr (Or.inr rfl)
  have hvd : S.graph.connectedComponentMk v = d := (hcompd v).mpr (Or.inl rfl)
  have htd : S.graph.connectedComponentMk t = d := (hcompd t).mpr (Or.inr rfl)
  have cross : ∀ a b : LowPoint T, S.graph.connectedComponentMk a = c →
      S.graph.connectedComponentMk b = d → a ≠ b := by
    intro a b ha hb heq
    subst b
    exact hcd (ha.symm.trans hb)
  have huv := cross u v huc hvd
  have hut := cross u t huc htd
  have hvs := Ne.symm (cross s v hsc hvd)
  have hst := cross s t hsc htd
  have hvnot : S.graph.connectedComponentMk v ≠ c := by rw [hvd]; exact Ne.symm hcd
  have hz : fullExcess T u.val v.val = 0 := S.component_closed c huc hvnot
  refine ⟨⟨u, v, s, t, ⟨huv, hus, hut, hvs, hvt, hst⟩,
    zero_excess_codegree_six T u.val v.val (fun h => huv (Subtype.ext h)) hz, ?_, ?_⟩⟩
  · intro R hR
    rw [hbalc R hR, hbald R hR]
  · intro x hxu hxv hxs hxt
    constructor
    · apply outside_component_codegree_six T hrows hcover c hc u huc x
      intro r hr hxr
      rcases (hcompc r).mp hr with rfl | rfl
      · exact hxu hxr
      · exact hxs hxr
    · apply outside_component_codegree_six T hrows hcover d hd v hvd x
      intro r hr hxr
      rcases (hcompd r).mp hr with rfl | rfl
      · exact hxv hxr
      · exact hxt hxr

end Covering.NormalizedBridge20261003.A19Physical
#print axioms Covering.NormalizedBridge20261003.A19Physical.pair_from_two_component
#print axioms Covering.NormalizedBridge20261003.A19Physical.has_gadget_of_two_two_components
