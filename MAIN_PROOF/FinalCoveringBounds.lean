/- Concrete end-to-end composition from the actual exceptional and gadget branches.
All numerical endpoints take only original physical row-validity and covering premises. -/
module

public import PhysicalExceptionExclusion
public import GadgetExclusion
public import FinalLowerBoundWrappers

@[expose] public section

namespace Covering.FinalCoveringBounds
open NormalizedBridge20261003.A19Physical
open NormalizedBridge20261003.ExceptionBranch
open FinalLowerBoundWrappers

theorem exact_nineteen_excluded : ExactNineteenExcluded := by
  intro T hrows hcover hlen
  obtain ⟨g⟩ := physical_has_gadget T hrows hcover hlen
  exact CoveringGadgetTrace.gadget_impossible T hrows hcover hlen g

theorem c24_14_4_lower_twenty (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T) : 20 ≤ T.length :=
  c24_lower_twenty exact_nineteen_excluded T hrows hcover

theorem c25_15_5_lower_thirty_four (F : Family 25)
    (hrows : ∀ R, R ∈ F → ValidBlock 15 R) (hcover : IsCovering 5 F) : 34 ≤ F.length :=
  c25_lower_thirty_four exact_nineteen_excluded F hrows hcover

theorem no_design24_at_most_nineteen : ¬ ∃ T : Family 24, Design 14 4 19 T :=
  no_design24_budget19 exact_nineteen_excluded

theorem no_design25_at_most_thirty_three : ¬ ∃ F : Family 25, Design 15 5 33 F :=
  no_design25_budget33 exact_nineteen_excluded

end Covering.FinalCoveringBounds
#print axioms Covering.FinalCoveringBounds.exact_nineteen_excluded
#print axioms Covering.FinalCoveringBounds.c24_14_4_lower_twenty
#print axioms Covering.FinalCoveringBounds.c25_15_5_lower_thirty_four
#print axioms Covering.FinalCoveringBounds.no_design24_at_most_nineteen
#print axioms Covering.FinalCoveringBounds.no_design25_at_most_thirty_three
