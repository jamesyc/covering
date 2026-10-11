module

public import Covering.Kernel.Balanced

@[expose] public section

/-!
# Regular components

Components on which every vertex has the full weighted degree.
-/

open Matrix Finset
open scoped BigOperators
namespace WeightedKernelComponents.System
open WeightedSignlessKernel
variable {V : Type*} [Fintype V] [DecidableEq V] (S : System V)

def RegularComponent (c : S.graph.ConnectedComponent) : Prop :=
  ∀ i, S.graph.connectedComponentMk i = c → rowSum S.W i = S.d

end WeightedKernelComponents.System
