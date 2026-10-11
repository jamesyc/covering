module

public import Covering.Quadruple.OutsideTrace

@[expose] public section

/-!
# Four block classes

The classes `H, E, F, G` of Section 4.1 and the sizes of their traces.
-/

namespace Covering.BlockClasses
open Covering Covering.PointDegree Covering.SideLift

def common {n : Nat} (T : Family n) (u v : Fin n) : Family n :=
  T.filter (fun R => u ∈ R ∧ v ∈ R)
def leftOnly {n : Nat} (T : Family n) (u v : Fin n) : Family n :=
  T.filter (fun R => u ∈ R ∧ v ∉ R)
def rightOnly {n : Nat} (T : Family n) (u v : Fin n) : Family n :=
  T.filter (fun R => u ∉ R ∧ v ∈ R)
def neither {n : Nat} (T : Family n) (u v : Fin n) : Family n :=
  T.filter (fun R => u ∉ R ∧ v ∉ R)

lemma common_length {n : Nat} (T : Family n) (u v : Fin n) :
    (common T u v).length=pairDegree T u v := rfl

lemma left_length {n : Nat} (T : Family n) (u v : Fin n) :
    (leftOnly T u v).length+(common T u v).length=degree T u := by
  induction T with
  | nil => simp [leftOnly,common,degree]
  | cons R T ih =>
    by_cases hu : u ∈ R <;> by_cases hv : v ∈ R <;>
      simp [leftOnly,common,degree,hu,hv] at ih ⊢ <;> omega

lemma right_length {n : Nat} (T : Family n) (u v : Fin n) :
    (rightOnly T u v).length+(common T u v).length=degree T v := by
  simpa only [leftOnly,rightOnly,common,and_comm] using left_length T v u

lemma neither_length {n : Nat} (T : Family n) (u v : Fin n) :
    (neither T u v).length+degree T u+degree T v=T.length+(common T u v).length :=
  Covering.PairData.pair_slot_partition T u v

lemma degree_four {n : Nat} (T : Family n) (u v x : Fin n) :
    degree (common T u v) x+degree (leftOnly T u v) x+
      degree (rightOnly T u v) x+degree (neither T u v) x=degree T x := by
  induction T with
  | nil => simp [leftOnly,rightOnly,common,neither,degree]
  | cons R T ih =>
    by_cases hu : u ∈ R <;> by_cases hv : v ∈ R <;> by_cases hx : x ∈ R <;>
      simp [leftOnly,rightOnly,common,neither,degree,hu,hv,hx] at ih ⊢ <;> omega

lemma pair_four {n : Nat} (T : Family n) (u v x y : Fin n) :
    pairDegree (common T u v) x y+pairDegree (leftOnly T u v) x y+
      pairDegree (rightOnly T u v) x y+pairDegree (neither T u v) x y=pairDegree T x y := by
  induction T with
  | nil => simp [leftOnly,rightOnly,common,neither,pairDegree]
  | cons R T ih =>
    by_cases hu : u ∈ R <;> by_cases hv : v ∈ R <;> by_cases hx : x ∈ R <;> by_cases hy : y ∈ R <;>
      simp [leftOnly,rightOnly,common,neither,pairDegree,hu,hv,hx,hy] at ih ⊢ <;> omega

end Covering.BlockClasses
