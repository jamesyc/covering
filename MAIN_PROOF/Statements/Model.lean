import Std

/-!
The independently readable target model. Points of `Fin n` have public labels
`p.val + 1`. A block is a list, but all set comparisons below are extensional.
In particular, permuting a row does not produce a distinct block.

This module states definitions only. It imports no experimental proof files.
-/

namespace Covering

abbrev Block (n : Nat) := List (Fin n)
abbrev Family (n : Nat) := List (Block n)

def publicLabel {n : Nat} (p : Fin n) : Nat := p.val + 1

def ValidBlock {n : Nat} (k : Nat) (B : Block n) : Prop :=
  B.Nodup ∧ B.length = k

def Subset {n : Nat} (A B : Block n) : Prop :=
  ∀ x, x ∈ A → x ∈ B

def SameSet {n : Nat} (A B : Block n) : Prop :=
  Subset A B ∧ Subset B A

def Distinct {n : Nat} (F : Family n) : Prop :=
  F.Pairwise (fun A B => ¬ SameSet A B)

def Covers {n : Nat} (F : Family n) (T : Block n) : Prop :=
  ∃ B, B ∈ F ∧ Subset T B

def IsCovering {n : Nat} (t : Nat) (F : Family n) : Prop :=
  ∀ T, ValidBlock t T → Covers F T

def Admissible {n : Nat} (k budget : Nat) (F : Family n) : Prop :=
  F.length ≤ budget ∧ (∀ B, B ∈ F → ValidBlock k B) ∧ Distinct F

def Design {n : Nat} (k t budget : Nat) (F : Family n) : Prop :=
  Admissible k budget F ∧ IsCovering t F

def complement {n : Nat} (B : Block n) : Block n :=
  (List.finRange n).filter (fun p => p ∉ B)

def Disjoint {n : Nat} (A B : Block n) : Prop :=
  ∀ x, x ∈ A → x ∈ B → False

def ResidualCovered {n : Nat} (t : Nat) (kept added : Family n) : Prop :=
  ∀ T, ValidBlock t T → ¬ Covers kept T → Covers added T

def relabelBlock {n : Nat} (f : Fin n → Fin n) (B : Block n) : Block n :=
  B.map f

def relabelFamily {n : Nat} (f : Fin n → Fin n) (F : Family n) : Family n :=
  F.map (relabelBlock f)

end Covering
