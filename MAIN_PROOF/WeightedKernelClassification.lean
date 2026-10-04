module

public import WeightedKernelDimension

@[expose] public section

open Matrix Finset
open scoped BigOperators
namespace WeightedKernelComponents.System
open WeightedSignlessKernel
variable {V : Type*} [Fintype V] [DecidableEq V] (S : System V)

def RegularComponent (c : S.graph.ConnectedComponent) : Prop :=
  ∀ i, S.graph.connectedComponentMk i = c → rowSum S.W i = S.d

def BipartiteComponent (c : S.graph.ConnectedComponent) : Prop :=
  ∃ s t : Finset V, Disjoint s t ∧
    (∀ i, S.graph.connectedComponentMk i = c ↔ i ∈ s ∨ i ∈ t) ∧
    (∀ i j, S.graph.connectedComponentMk i = c → S.graph.Adj i j →
      (i ∈ s ∧ j ∈ t) ∨ (i ∈ t ∧ j ∈ s))

lemma regular_bipartite_active (c : S.graph.ConnectedComponent)
    (hr : S.RegularComponent c) (hb : S.BipartiteComponent c) : S.Active c := by
  classical
  obtain ⟨s, t, hdis, hcomp, hedge⟩ := hb
  let x : V → ℝ := fun i => if i ∈ s then 1 else if i ∈ t then -1 else 0
  have hs : ∀ i, i ∈ s → x i = 1 := by intro i hi; simp [x, hi]
  have ht : ∀ i, i ∈ t → x i = -1 := by
    intro i hi
    have hn : i ∉ s := fun h => Finset.disjoint_left.mp hdis h hi
    simp [x, hi, hn]
  have hout : ∀ i, S.graph.connectedComponentMk i ≠ c → x i = 0 := by
    intro i hi
    have hnot : ¬ (i ∈ s ∨ i ∈ t) := fun h => hi ((hcomp i).mpr h)
    simp [x, (not_or.mp hnot).1, (not_or.mp hnot).2]
  have hx : x ∈ S.kernel := by
    rw [S.kernel_iff]
    constructor
    · intro i hi
      apply hout i
      intro hc
      rw [hr i hc] at hi
      exact lt_irrefl _ hi
    · intro i j hij
      by_cases hi : S.graph.connectedComponentMk i = c
      · rcases hedge i j hi hij with h | h
        · rw [hs i h.1, ht j h.2]; norm_num
        · rw [ht i h.1, hs j h.2]
      · have hj : S.graph.connectedComponentMk j ≠ c := by
          intro hj
          exact hi ((SimpleGraph.ConnectedComponent.sound hij.reachable).trans hj)
        rw [hout i hi, hout j hj]; simp
  refine ⟨⟨x, hx⟩, ?_⟩
  change x (S.representative c) ≠ 0
  rcases (hcomp _).mp (S.representative_mem c) with h | h
  · rw [hs _ h]; norm_num
  · rw [ht _ h]; norm_num

lemma active_iff_regular_bipartite (hd : S.d ≠ 0) (c : S.graph.ConnectedComponent) :
    S.Active c ↔ S.RegularComponent c ∧ S.BipartiteComponent c := by
  constructor
  · intro h
    obtain ⟨s, t, _, _, hdis, _, hcomp, hreg, hedge, _⟩ := S.active_balanced_bipartite hd c h
    exact ⟨hreg, ⟨s, t, hdis, hcomp, hedge⟩⟩
  · rintro ⟨hr, hb⟩
    exact S.regular_bipartite_active c hr hb

lemma active_iff_balanced_bipartite (hd : S.d ≠ 0) (c : S.graph.ConnectedComponent) :
    S.Active c ↔ S.BalancedBipartite c := by
  refine ⟨S.active_balanced_bipartite hd c, ?_⟩
  rintro ⟨s, t, _, _, hdis, _, hcomp, hreg, hedge, _⟩
  exact S.regular_bipartite_active c hreg ⟨s, t, hdis, hcomp, hedge⟩

lemma zero_on_nonbipartite_component (hd : S.d ≠ 0) (c : S.graph.ConnectedComponent)
    (hc : ¬ S.BipartiteComponent c) {x : V → ℝ} (hx : x ∈ S.kernel) {i : V}
    (hi : S.graph.connectedComponentMk i = c) : x i = 0 := by
  apply S.zero_on_inactive_component c _ hx hi
  intro ha
  exact hc ((S.active_iff_regular_bipartite hd c).mp ha).2

lemma nullity_eq_regular_bipartite_components (hd : S.d ≠ 0) :
    Module.finrank ℝ S.kernel =
      Nat.card {c // S.RegularComponent c ∧ S.BipartiteComponent c} := by
  rw [S.nullity_eq_active_components]
  exact Nat.card_congr (Equiv.subtypeEquivRight (S.active_iff_regular_bipartite hd))

lemma nullity_eq_balanced_bipartite_components (hd : S.d ≠ 0) :
    Module.finrank ℝ S.kernel = Nat.card {c // S.BalancedBipartite c} := by
  rw [S.nullity_eq_active_components]
  exact Nat.card_congr (Equiv.subtypeEquivRight (S.active_iff_balanced_bipartite hd))

end WeightedKernelComponents.System
#print axioms WeightedKernelComponents.System.regular_bipartite_active
#print axioms WeightedKernelComponents.System.active_iff_regular_bipartite
#print axioms WeightedKernelComponents.System.zero_on_nonbipartite_component
#print axioms WeightedKernelComponents.System.nullity_eq_regular_bipartite_components
#print axioms WeightedKernelComponents.System.nullity_eq_balanced_bipartite_components
