module

public import GadgetPairGeometry
public import PhysicalQuotientMatrix
public import InvolutionPairCoordinates
public import HighPointDeletion

@[expose] public section

open Finset
open scoped BigOperators
namespace CoveringGadgetTrace
open Covering Covering.PointDegree Covering.SideLift
open Covering.NormalizedBridge20261003.A19Physical
open CoveringMatrixRegular20 CoveringGadgetColors PhysicalQuotientMatrix
noncomputable section

/-- The actual four-point balanced gadget is impossible in a nineteen-slot
24-point14-row four-cover. All completions, pairings, quotient graph, high-point
deletions, and omitted-row colors are derived from the original family. -/
theorem gadget_impossible (T : Family 24)
    (hrows : ∀ R, R∈T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (hlen : T.length=19) (g : GadgetData T) : False := by
  classical
  obtain ⟨hE,hF⟩ := actual_completions g hrows hcover
  obtain ⟨σ,hσE⟩ := old_twin_geometry (H g) (E g) hE
  obtain ⟨τ,hτF⟩ := old_twin_geometry (H g) (F g) hF
  have hστ := completions_share_pairing (H g) (E g) (F g) hE hF σ τ hσE hτF
  subst τ
  obtain ⟨e,he⟩ := InvolutionPairCoordinates.exists_paired_coordinates σ hσE.involution hσE.no_fixed
  let D := dataOfCoordinates (H g) σ e he hE.H_rows hE.H_degree hσE.H_twins
    (H_row_intersection_four (H g) (E g) hE)
    (nonpartner_H_codegree (H g) (E g) hE σ hσE)
  obtain ⟨a,b,hab,ha,hb,hrest⟩ := two_high_points (G g) (G_length g hlen)
    (G_rows g hrows) (G_floor g hrows hcover)
  have hlow : ∀ p, p∈HighPointDeletion.lowSupport a b → degree (G g) p=2 := by
    intro p hp
    simp only [HighPointDeletion.lowSupport,mem_filter,mem_univ,true_and] at hp
    exact hrest p hp.1 hp.2
  apply HighPointDeletion.physical_color_capacity_impossible D.graph D.graph_degree
    D.adjacent_common_empty D.nonadjacent_unique_common e a b (color (G g))
  · intro u v huv i j
    have hune : u.val≠v.val := D.graph.ne_of_adj huv
    have hrep : pairDegree (H g) (e (u.val,0)) (e (v.val,0))=2 := by
      have hh := (D.graph_adj_iff_gram_two u.val v.val).mp huv
      change ((quotient (H g) e).transpose*quotient (H g) e) u.val v.val=2 at hh
      rw [quotient_point_gram] at hh
      exact_mod_cast hh
    have hH : pairDegree (H g) (e (u.val,i)) (e (v.val,j))=2 := by
      rw [paired_codegree (H g) σ e he hσE.H_twins,hrep]
    obtain ⟨hpq,hqp⟩ := coordinates_nonpartners σ hσE.involution e he u.val v.val hune i j
    have hlo := residual_pair_floor g hrows hcover σ hσE hτF _ _ hpq hqp hH
    apply color_eq_of_pair_floor (G g)
    · exact hlow _ (HighPointDeletion.survivingMap_mem_low e a b (u,i))
    · exact hlow _ (HighPointDeletion.survivingMap_mem_low e a b (v,j))
    · exact hlo
  · intro c
    exact color_fiber_capacity (G g) (G_length g hlen) (G_rows g hrows)
      (HighPointDeletion.lowSupport a b) hlow c

#print axioms gadget_impossible
end
end CoveringGadgetTrace
