import A19TwoTwinGadget
import ComponentOrderDichotomy
open Matrix Finset
open scoped BigOperators
namespace Covering.NormalizedBridge20261003.A19Physical
open PointDegree WeightedKernelComponents

open scoped Classical in
structure ExceptionalComponents (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T) where
  c2 : (lowSystem T hrows hcover).graph.ConnectedComponent
  c6 : (lowSystem T hrows hcover).graph.ConnectedComponent
  cLarge : (lowSystem T hrows hcover).graph.ConnectedComponent
  distinct : c2 ≠ c6 ∧ c2 ≠ cLarge ∧ c6 ≠ cLarge
  all_components : (lowSystem T hrows hcover).goodComponents = {c2, c6, cLarge}
  size_two : (lowSystem T hrows hcover).componentSize c2 = 2
  size_six : (lowSystem T hrows hcover).componentSize c6 = 6
  size_large : (lowSystem T hrows hcover).componentSize cLarge = 6 ∨
    (lowSystem T hrows hcover).componentSize cLarge = 8
  high_points : ∃ p q : Fin 24, p ≠ q ∧ degree T p = 12 ∧ degree T q = 12 ∧
    ∀ r, r ≠ p → r ≠ q → degree T r = 11

lemma gadget_or_exceptional_components (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T) (hlen : T.length = 19) :
    HasGadget T ∨ Nonempty (ExceptionalComponents T hrows hcover) := by
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
  rcases ComponentOrderDichotomy.classify S.goodComponents S.componentSize hcard hmin heven htotal with
    ⟨c, hc, hs⟩ | ⟨c, hc, d, hd, hcd, hcs, hds⟩ | ⟨a, b, c, hab, hac, hbc, hall, ha, hb, hc⟩
  · left
    exact has_gadget_of_four_component T hrows hcover c ((S.mem_goodComponents c).mp hc) hs
  · left
    exact has_gadget_of_two_two_components T hrows hcover c d hcd
      ((S.mem_goodComponents c).mp hc) ((S.mem_goodComponents d).mp hd) hcs hds
  · right
    have hcount : S.goodComponents.card = 3 := by rw [hall]; simp [hab, hac, hbc]
    have hhigh : ∃ p q : Fin 24, p ≠ q ∧ degree T p = 12 ∧ degree T q = 12 ∧
        ∀ r, r ≠ p → r ≠ q → degree T r = 11 := by
      rcases degree_patterns T hrows hcover hlen with ⟨p, hp, hrest⟩ | hh
      · have h4 := at_least_four_components_of_one_high T hrows hcover hlen p hp hrest
        rw [← S.card_goodComponents, hcount] at h4
        omega
      · exact hh
    exact ⟨⟨a, b, c, ⟨hab, hac, hbc⟩, hall, ha, hb, hc, hhigh⟩⟩

end Covering.NormalizedBridge20261003.A19Physical
#print axioms Covering.NormalizedBridge20261003.A19Physical.gadget_or_exceptional_components
