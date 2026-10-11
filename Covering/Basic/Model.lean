module

public import Std

@[expose] public section

/-!
# The covering model

Points are `Fin n`; a block is a list of points and a family is a list of
blocks, so repeated blocks are allowed and every count below is a count of
list positions. `IsCovering t F` says that every `t`-set of points lies in
some block of `F`. Set comparisons are extensional.
-/

namespace Covering

abbrev Block (n : Nat) := List (Fin n)
abbrev Family (n : Nat) := List (Block n)

def ValidBlock {n : Nat} (k : Nat) (B : Block n) : Prop :=
  B.Nodup ∧ B.length = k

def Subset {n : Nat} (A B : Block n) : Prop :=
  ∀ x, x ∈ A → x ∈ B

def Covers {n : Nat} (F : Family n) (T : Block n) : Prop :=
  ∃ B, B ∈ F ∧ Subset T B

def IsCovering {n : Nat} (t : Nat) (F : Family n) : Prop :=
  ∀ T, ValidBlock t T → Covers F T

def complement {n : Nat} (B : Block n) : Block n :=
  (List.finRange n).filter (fun p => p ∉ B)

def Disjoint {n : Nat} (A B : Block n) : Prop :=
  ∀ x, x ∈ A → x ∈ B → False

def relabelBlock {n : Nat} (f : Fin n → Fin n) (B : Block n) : Block n :=
  B.map f

def relabelFamily {n : Nat} (f : Fin n → Fin n) (F : Family n) : Family n :=
  F.map (relabelBlock f)

end Covering
