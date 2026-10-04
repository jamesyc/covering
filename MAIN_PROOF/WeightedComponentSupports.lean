module

public import WeightedKernelIncidence
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

@[expose] public section

open Matrix Finset
open scoped BigOperators
namespace WeightedKernelComponents.System
variable {V : Type*} [Fintype V] [DecidableEq V] (S : System V)

noncomputable def componentVertices (c : S.graph.ConnectedComponent) : Finset V := by
  classical
  exact univ.filter (fun i => S.graph.connectedComponentMk i = c)

noncomputable def componentSize (c : S.graph.ConnectedComponent) : ℕ :=
  (S.componentVertices c).card

noncomputable def goodComponents : Finset S.graph.ConnectedComponent := by
  classical
  exact univ.filter S.BalancedBipartite

noncomputable def goodVertices : Finset V := by
  classical
  exact univ.filter (fun i => S.BalancedBipartite (S.graph.connectedComponentMk i))

lemma mem_goodComponents (c : S.graph.ConnectedComponent) :
    c ∈ S.goodComponents ↔ S.BalancedBipartite c := by
  classical
  simp [goodComponents]

lemma mem_goodVertices (i : V) :
    i ∈ S.goodVertices ↔ S.BalancedBipartite (S.graph.connectedComponentMk i) := by
  classical
  simp [goodVertices]

lemma card_goodComponents : S.goodComponents.card = Nat.card {c // S.BalancedBipartite c} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

lemma component_size_even {c : S.graph.ConnectedComponent} (hc : S.BalancedBipartite c) :
    Even (S.componentSize c) := by
  classical
  obtain ⟨s, t, _, _, hdis, hcard, hcomp, _, _, _⟩ := hc
  have hv : S.componentVertices c = s ∪ t := by
    ext i
    simp [componentVertices, hcomp]
  rw [componentSize, hv, Finset.card_union_of_disjoint hdis, hcard]
  exact ⟨t.card, rfl⟩

lemma component_size_ge_two {c : S.graph.ConnectedComponent} (hc : S.BalancedBipartite c) :
    2 ≤ S.componentSize c := by
  classical
  obtain ⟨s, t, hs, _, hdis, hcard, hcomp, _, _, _⟩ := hc
  have hv : S.componentVertices c = s ∪ t := by
    ext i
    simp [componentVertices, hcomp]
  rw [componentSize, hv, Finset.card_union_of_disjoint hdis]
  have hs' := Finset.card_pos.mpr hs
  omega

lemma sum_component_sizes : (∑ c ∈ S.goodComponents, S.componentSize c) = S.goodVertices.card := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter (univ : Finset V) S.goodComponents
    S.graph.connectedComponentMk
  simpa [componentSize, componentVertices, goodVertices, S.mem_goodComponents] using h

lemma good_vertices_even : Even S.goodVertices.card := by
  rw [← S.sum_component_sizes]
  apply Finset.even_sum
  intro c hc
  exact S.component_size_even ((S.mem_goodComponents c).mp hc)

lemma good_vertex_regular (i : V) (hi : i ∈ S.goodVertices) :
    WeightedSignlessKernel.rowSum S.W i = S.d := by
  have h := (S.mem_goodVertices i).mp hi
  obtain ⟨_, _, _, _, _, _, _, hreg, _, _⟩ := h
  exact hreg i rfl

end WeightedKernelComponents.System
#print axioms WeightedKernelComponents.System.component_size_even
#print axioms WeightedKernelComponents.System.component_size_ge_two
#print axioms WeightedKernelComponents.System.sum_component_sizes
#print axioms WeightedKernelComponents.System.good_vertices_even
