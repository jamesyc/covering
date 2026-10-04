module

public import A19ComponentParts
public import A19ComponentUnion

@[expose] public section

open Matrix Finset
open scoped BigOperators
namespace Covering.NormalizedBridge20261003.A19Physical
open PointDegree SideLift WeightedKernelComponents

/-- A physical four-point gadget, with the balance/closure data needed later. -/
structure GadgetData (T : Family 24) where
  u : LowPoint T
  v : LowPoint T
  s : LowPoint T
  t : LowPoint T
  distinct : u ≠ v ∧ u ≠ s ∧ u ≠ t ∧ v ≠ s ∧ v ≠ t ∧ s ≠ t
  pivot_codegree : pairDegree T u.val v.val = 6
  row_balance : ∀ R, R ∈ T →
    (if u.val ∈ R then (1 : ℕ) else 0) + (if v.val ∈ R then 1 else 0) =
    (if s.val ∈ R then 1 else 0) + (if t.val ∈ R then 1 else 0)
  outside_codegree : ∀ x : Fin 24,
    x ≠ u.val → x ≠ v.val → x ≠ s.val → x ≠ t.val →
    pairDegree T u.val x = 6 ∧ pairDegree T v.val x = 6

abbrev HasGadget (T : Family 24) : Prop := Nonempty (GadgetData T)

lemma GadgetData.common_contains {T : Family 24} (g : GadgetData T)
    (R : Block 24) (hR : R ∈ T) (hu : g.u.val ∈ R) (hv : g.v.val ∈ R) :
    g.s.val ∈ R ∧ g.t.val ∈ R := by
  have h := g.row_balance R hR
  by_cases hs : g.s.val ∈ R <;> by_cases ht : g.t.val ∈ R <;> simp_all

lemma GadgetData.neither_avoids {T : Family 24} (g : GadgetData T)
    (R : Block 24) (hR : R ∈ T) (hu : g.u.val ∉ R) (hv : g.v.val ∉ R) :
    g.s.val ∉ R ∧ g.t.val ∉ R := by
  have h := g.row_balance R hR
  by_cases hs : g.s.val ∈ R <;> by_cases ht : g.t.val ∈ R <;> simp_all

lemma GadgetData.distinct_physical {T : Family 24} (g : GadgetData T) :
    [g.u.val, g.v.val, g.s.val, g.t.val].Nodup := by
  rcases g.distinct with ⟨huv, hus, hut, hvs, hvt, hst⟩
  have lift_ne : ∀ a b : LowPoint T, a ≠ b → a.val ≠ b.val :=
    fun a b h he => h (Subtype.ext he)
  simp [lift_ne g.u g.v huv, lift_ne g.u g.s hus, lift_ne g.u g.t hut,
    lift_ne g.v g.s hvs, lift_ne g.v g.t hvt, lift_ne g.s g.t hst]

lemma GadgetData.common_row_count {T : Family 24} (g : GadgetData T) :
    (T.filter fun R => g.u.val ∈ R ∧ g.v.val ∈ R).length = 6 :=
  g.pivot_codegree

lemma GadgetData.exclusive_one {T : Family 24} (g : GadgetData T)
    (R : Block 24) (hR : R ∈ T) (hu : g.u.val ∈ R) (hv : g.v.val ∉ R) :
    (if g.s.val ∈ R then (1 : ℕ) else 0) + (if g.t.val ∈ R then 1 else 0) = 1 := by
  have h := g.row_balance R hR
  simpa [hu, hv] using h.symm

lemma zero_excess_codegree_six (T : Family 24) (p q : Fin 24) (hpq : p ≠ q)
    (hz : fullExcess T p q = 0) : pairDegree T p q = 6 := by
  simp only [fullExcess, if_neg hpq] at hz
  have h : (pairDegree T p q : ℝ) = 6 := by linarith
  exact_mod_cast h

lemma pair_filter_count {T : Family 24} (R : Block 24) (p q : LowPoint T) (hpq : p ≠ q) :
    (({p, q} : Finset (LowPoint T)).filter fun r => r.val ∈ R).card =
      (if p.val ∈ R then 1 else 0) + (if q.val ∈ R then 1 else 0) := by
  by_cases hp : p.val ∈ R <;> by_cases hq : q.val ∈ R <;> simp [Finset.filter_insert, Finset.filter_singleton, hp, hq, hpq]

lemma outside_component_codegree_six (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (c : (lowSystem T hrows hcover).graph.ConnectedComponent)
    (hc : (lowSystem T hrows hcover).BalancedBipartite c)
    (p : LowPoint T) (hp : (lowSystem T hrows hcover).graph.connectedComponentMk p = c)
    (x : Fin 24)
    (havoid : ∀ r : LowPoint T,
      (lowSystem T hrows hcover).graph.connectedComponentMk r = c → x ≠ r.val) :
    pairDegree T p.val x = 6 := by
  apply zero_excess_codegree_six T p.val x (Ne.symm (havoid p hp))
  by_contra hw
  obtain ⟨_, _, _, _, _, _, _, hreg, _, _⟩ := hc
  obtain ⟨hx, hcx⟩ := component_closed_in_all_points T hrows hcover c hreg p hp x hw
  exact havoid ⟨x, hx⟩ hcx rfl

lemma has_gadget_of_four_component (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (c : (lowSystem T hrows hcover).graph.ConnectedComponent)
    (hc : (lowSystem T hrows hcover).BalancedBipartite c)
    (hsize : (lowSystem T hrows hcover).componentSize c = 4) : HasGadget T := by
  classical
  let S := lowSystem T hrows hcover
  obtain ⟨A, B, _, _, hdis, hcard, hcomp, hbalance, hedge⟩ :=
    component_slot_balance_with_edges T hrows hcover c hc
  have hsupp : S.componentVertices c = A ∪ B := by
    ext r
    simpa [System.componentVertices, S] using hcomp r
  have hA2 : A.card = 2 := by
    change (S.componentVertices c).card = 4 at hsize
    rw [hsupp, Finset.card_union_of_disjoint hdis, ← hcard] at hsize
    omega
  have hB2 : B.card = 2 := by omega
  obtain ⟨u, v, huv, hA⟩ := Finset.card_eq_two.mp hA2
  obtain ⟨s, t, hst, hB⟩ := Finset.card_eq_two.mp hB2
  have hu : u ∈ A := by rw [hA]; simp
  have hv : v ∈ A := by rw [hA]; simp
  have hs : s ∈ B := by rw [hB]; simp
  have ht : t ∈ B := by rw [hB]; simp
  have hus : u ≠ s := fun h => Finset.disjoint_left.mp hdis hu (h.symm ▸ hs)
  have hut : u ≠ t := fun h => Finset.disjoint_left.mp hdis hu (h.symm ▸ ht)
  have hvs : v ≠ s := fun h => Finset.disjoint_left.mp hdis hv (h.symm ▸ hs)
  have hvt : v ≠ t := fun h => Finset.disjoint_left.mp hdis hv (h.symm ▸ ht)
  have huc : S.graph.connectedComponentMk u = c := (hcomp u).mpr (Or.inl hu)
  have hvc : S.graph.connectedComponentMk v = c := (hcomp v).mpr (Or.inl hv)
  have hz : fullExcess T u.val v.val = 0 := by
    by_contra hn
    have hadj : S.graph.Adj u v :=
      lt_of_le_of_ne (fullExcess_nonnegative T hrows hcover u.val v.val) (Ne.symm hn)
    rcases hedge u v huc hadj with h | h
    · exact Finset.disjoint_left.mp hdis hv h.2
    · exact Finset.disjoint_left.mp hdis hu h.1
  refine ⟨⟨u, v, s, t, ⟨huv, hus, hut, hvs, hvt, hst⟩,
    zero_excess_codegree_six T u.val v.val (fun h => huv (Subtype.ext h)) hz, ?_, ?_⟩⟩
  · intro R hR
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hR
    have h := hbalance j
    rw [hA, hB, pair_filter_count _ u v huv, pair_filter_count _ s t hst] at h
    exact h
  · intro x hxu hxv hxs hxt
    have avoid : ∀ r : LowPoint T, S.graph.connectedComponentMk r = c → x ≠ r.val := by
      intro r hr hxr
      have hm := (hcomp r).mp hr
      rw [hA, hB] at hm
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with (rfl | rfl) | (rfl | rfl)
      · exact hxu hxr
      · exact hxv hxr
      · exact hxs hxr
      · exact hxt hxr
    exact ⟨outside_component_codegree_six T hrows hcover c hc u huc x avoid,
      outside_component_codegree_six T hrows hcover c hc v hvc x avoid⟩

end Covering.NormalizedBridge20261003.A19Physical
#print axioms Covering.NormalizedBridge20261003.A19Physical.has_gadget_of_four_component
#print axioms Covering.NormalizedBridge20261003.A19Physical.GadgetData.common_contains
#print axioms Covering.NormalizedBridge20261003.A19Physical.GadgetData.neither_avoids
#print axioms Covering.NormalizedBridge20261003.A19Physical.GadgetData.distinct_physical
#print axioms Covering.NormalizedBridge20261003.A19Physical.GadgetData.exclusive_one
