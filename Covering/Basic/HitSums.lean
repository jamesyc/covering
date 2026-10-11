module

public import Covering.PairCover.TwoSets

@[expose] public section

/-!
# Counting hits

Summing the number of selected points met by each block.
-/

namespace Covering.HitSums

open CrossGrid

theorem sum_constant_hits {n : Nat} (X R : Block n) (w : Nat) :
    (X.map (fun x => if x ∈ R then w else 0)).sum = w * (hits X R).length := by
  induction X with
  | nil => simp [hits]
  | cons x X ih =>
    by_cases hx : x ∈ R <;> simp [hits,hx,ih,Nat.mul_add,Nat.add_comm]

end Covering.HitSums
