import Statements.Model

namespace Covering

/-- The exact open construction target: at most 41 distinct 15-subsets of 25
points, with every 5-subset contained in at least one block. -/
def Target : Prop :=
  ∃ F : Family 25, Design 15 5 41 F

end Covering
