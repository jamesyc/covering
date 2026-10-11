module

public import Covering.Quadruple.Basic
public import Covering.Components.Balance
public import Covering.Components.AtMostSixteen

@[expose] public section

/-!
# Quadruple data

The configuration attached to a balanced quadruple in a nineteen-block cover.
-/

open Matrix Finset
open scoped BigOperators
namespace Covering.Nineteen
open Covering.Floors
open PointDegree SideLift WeightedKernelComponents

/-- Derived codegree data, built from a balanced quadruple by `quadruple_of_balance`. -/
structure QuadrupleData (T : Family 24) where
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

/-- Builds the quadruple data from the balance equation alone. -/
def quadruple_of_balance (T : Family 24)
    (hr : ∀ R, R ∈ T → ValidBlock 14 R) (hc : IsCovering 4 T)
    (g : Covering.Quadruple.BalancedQuadruple T) : QuadrupleData T :=
  ⟨g.u,g.v,g.s,g.t,g.distinct,(g.codegrees hr hc).1,g.row_balance,(g.codegrees hr hc).2⟩

abbrev HasQuadruple (T : Family 24) : Prop := Nonempty (Covering.Quadruple.BalancedQuadruple T)

lemma QuadrupleData.distinct_points {T : Family 24} (g : QuadrupleData T) :
    [g.u.val, g.v.val, g.s.val, g.t.val].Nodup := by
  rcases g.distinct with ⟨huv, hus, hut, hvs, hvt, hst⟩
  have lift_ne : ∀ a b : LowPoint T, a ≠ b → a.val ≠ b.val :=
    fun a b h he => h (Subtype.ext he)
  simp [lift_ne g.u g.v huv, lift_ne g.u g.s hus, lift_ne g.u g.t hut,
    lift_ne g.v g.s hvs, lift_ne g.v g.t hvt, lift_ne g.s g.t hst]

lemma zero_excess_codegree_six (T : Family 24) (p q : Fin 24) (hpq : p ≠ q)
    (hz : fullExcess T p q = 0) : pairDegree T p q = 6 := by
  simp only [fullExcess, ite_eq_right hpq] at hz
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

lemma quadruple_of_size_four_component (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (c : (lowSystem T hrows hcover).graph.ConnectedComponent)
    (hc : (lowSystem T hrows hcover).BalancedBipartite c)
    (hsize : (lowSystem T hrows hcover).componentSize c = 4) : HasQuadruple T := by
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
  refine ⟨⟨u,v,s,t,⟨huv,hus,hut,hvs,hvt,hst⟩,?_⟩⟩
  intro R hR
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hR
  have h := hbalance j
  rw [hA,hB,pair_filter_count _ u v huv,pair_filter_count _ s t hst] at h
  exact h

end Covering.Nineteen
