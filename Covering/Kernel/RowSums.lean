module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Constant row sums

The all-ones vector is an eigenvector of a matrix with constant row sums.
-/

open Matrix Finset
open scoped BigOperators
namespace RowSumFactorization
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
def ones (n m : Type*) : Matrix n m ℝ := fun _ _ => 1

end RowSumFactorization
