module

public import Statements.Model

@[expose] public section

namespace Covering

/-- Ordered triples, allowing equal coordinates, witnessed in a residual row. -/
def Shadow3 {n : Nat} (H : Family n) (u v w : Fin n) : Prop :=
  ∃ R, R ∈ H ∧ u ∈ R ∧ v ∈ R ∧ w ∈ R

end Covering
