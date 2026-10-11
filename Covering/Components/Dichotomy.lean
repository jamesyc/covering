module

public import Covering.Quadruple.FromTwoPairs
public import Covering.Components.Sizes

@[expose] public section

/-!
# Quadruple or remaining components

Proposition 3.2 splits into the two cases treated in Sections 4 and 5.
-/

open Matrix Finset
open scoped BigOperators
namespace Covering.Nineteen
open Covering.Floors
open PointDegree WeightedKernelComponents

open scoped Classical in
structure RemainingComponents (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T) where
  c2 : (lowSystem T hrows hcover).graph.ConnectedComponent
  largeFirst : (lowSystem T hrows hcover).graph.ConnectedComponent
  largeSecond : (lowSystem T hrows hcover).graph.ConnectedComponent
  distinct : c2 ≠ largeFirst ∧ c2 ≠ largeSecond ∧ largeFirst ≠ largeSecond
  good_two : (lowSystem T hrows hcover).BalancedBipartite c2
  good_first : (lowSystem T hrows hcover).BalancedBipartite largeFirst
  good_second : (lowSystem T hrows hcover).BalancedBipartite largeSecond
  size_two : (lowSystem T hrows hcover).componentSize c2 = 2
  size_first_ge_six : 6 ≤ (lowSystem T hrows hcover).componentSize largeFirst
  size_second_ge_six : 6 ≤ (lowSystem T hrows hcover).componentSize largeSecond

lemma quadruple_or_remaining_components (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T) (hlen : T.length = 19) :
    HasQuadruple T ∨ Nonempty (RemainingComponents T hrows hcover) := by
  classical
  let S := lowSystem T hrows hcover
  have hcard : 3 ≤ S.goodComponents.card := by
    rw [S.card_goodComponents]
    exact at_least_three_components T hrows hcover hlen
  have hmin : ∀ c ∈ S.goodComponents, 2 ≤ S.componentSize c := by
    intro c hc
    exact S.component_size_ge_two ((S.mem_goodComponents c).mp hc)
  have heven : ∀ c ∈ S.goodComponents, Even (S.componentSize c) := by
    intro c hc
    exact S.component_size_even ((S.mem_goodComponents c).mp hc)
  have htotal : (∑ c ∈ S.goodComponents, S.componentSize c) ≤ 16 := by
    rw [S.sum_component_sizes]
    exact good_vertices_le_sixteen T hrows hcover hlen
  rcases Covering.Components.classify_components S.goodComponents S.componentSize hcard hmin heven htotal with
    ⟨c, hc, hs⟩ | ⟨c, hc, d, hd, hcd, hcs, hds⟩ | ⟨a, ha, b, hb, c, hc, hab, hac, hbc, ha2, hb6, hc6⟩
  · left
    exact quadruple_of_size_four_component T hrows hcover c ((S.mem_goodComponents c).mp hc) hs
  · left
    exact quadruple_of_two_size_two_components T hrows hcover c d hcd
      ((S.mem_goodComponents c).mp hc) ((S.mem_goodComponents d).mp hd) hcs hds
  · right
    exact ⟨{
      c2 := a
      largeFirst := b
      largeSecond := c
      distinct := ⟨hab, hac, hbc⟩
      good_two := (S.mem_goodComponents a).mp ha
      good_first := (S.mem_goodComponents b).mp hb
      good_second := (S.mem_goodComponents c).mp hc
      size_two := ha2
      size_first_ge_six := hb6
      size_second_ge_six := hc6 }⟩

end Covering.Nineteen
