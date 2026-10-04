import A19WeightedFrontend
open Matrix Finset
open scoped BigOperators
namespace Covering.NormalizedBridge20261003.A19Physical
open PointDegree WeightedKernelComponents

lemma component_slot_balance (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (c : (lowSystem T hrows hcover).graph.ConnectedComponent)
    (hc : (lowSystem T hrows hcover).BalancedBipartite c) :
    ∃ s t : Finset (LowPoint T),
      s.Nonempty ∧ t.Nonempty ∧ _root_.Disjoint s t ∧ s.card = t.card ∧
      (∀ p, (lowSystem T hrows hcover).graph.connectedComponentMk p = c ↔ p ∈ s ∨ p ∈ t) ∧
      (∀ j : Fin T.length,
        (s.filter fun p => p.val ∈ T.get j).card =
        (t.filter fun p => p.val ∈ T.get j).card) := by
  classical
  let S := lowSystem T hrows hcover
  obtain ⟨s, t, hsnonempty, htnonempty, hdis, hcard, hcomp, hreg, hedge, _⟩ := hc
  let x : LowPoint T → ℝ := fun p => if p ∈ s then 1 else if p ∈ t then -1 else 0
  have hs : ∀ p, p ∈ s → x p = 1 := by intro p hp; simp [x, hp]
  have ht : ∀ p, p ∈ t → x p = -1 := by
    intro p hp
    have hn : p ∉ s := fun h => Finset.disjoint_left.mp hdis h hp
    simp [x, hn, hp]
  have hout : ∀ p, S.graph.connectedComponentMk p ≠ c → x p = 0 := by
    intro p hp
    have hn : ¬ (p ∈ s ∨ p ∈ t) := fun h => hp ((hcomp p).mpr h)
    simp [x, (not_or.mp hn).1, (not_or.mp hn).2]
  have hx : x ∈ S.kernel := by
    rw [S.kernel_iff]
    constructor
    · intro p hp
      apply hout p
      intro hpcomp
      rw [hreg p hpcomp] at hp
      exact lt_irrefl _ hp
    · intro p q hpq
      by_cases hp : S.graph.connectedComponentMk p = c
      · rcases hedge p q hp hpq with h | h
        · rw [hs p h.1, ht q h.2]; norm_num
        · rw [ht p h.1, hs q h.2]
      · have hq : S.graph.connectedComponentMk q ≠ c := by
          intro hq
          exact hp ((SimpleGraph.ConnectedComponent.sound hpq.reachable).trans hq)
        rw [hout p hp, hout q hq]; simp
  have hxdef : ∀ p, x p = (if p ∈ s then (1 : ℝ) else 0) -
      (if p ∈ t then (1 : ℝ) else 0) := by
    intro p
    by_cases hs' : p ∈ s <;> by_cases ht' : p ∈ t
    · exact False.elim (Finset.disjoint_left.mp hdis hs' ht')
    · simp [x, hs', ht']
    · simp [x, hs', ht']
    · simp [x, hs', ht']
  refine ⟨s, t, hsnonempty, htnonempty, hdis, hcard, hcomp, ?_⟩
  intro j
  have hcol := S.incidence_column_balance (by norm_num [S, lowSystem]) 6 (by norm_num)
    (lowIncidence T) (low_gram_identity T hrows hcover) hx j
  simp_rw [hxdef, mul_sub, Finset.sum_sub_distrib] at hcol
  have hsum (a : Finset (LowPoint T)) :
      (∑ p, lowIncidence T p j * (if p ∈ a then (1 : ℝ) else 0)) =
        ((a.filter fun p => p.val ∈ T.get j).card : ℝ) := by
    simp only [mul_ite, mul_one, mul_zero]
    simp [lowIncidence, CoveringMatrixIncidence.incidenceOn, CoveringMatrixIncidence.incidence]
  rw [hsum s, hsum t] at hcol
  exact_mod_cast sub_eq_zero.mp hcol

end Covering.NormalizedBridge20261003.A19Physical
#print axioms Covering.NormalizedBridge20261003.A19Physical.component_slot_balance
