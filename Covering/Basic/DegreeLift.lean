module

public import Covering.Basic.TwoPointDerivative

@[expose] public section

/-!
# Degrees under derivatives

How point degrees change when a family is split at one point.
-/

namespace Covering.Floors

open PointSplit PointDegree

@[simp] theorem filter_true {α : Type} (L : List α) : L.filter (fun _ => true)=L :=
  List.filter_eq_self.mpr (fun _ _ => rfl)

@[simp] theorem filter_false {α : Type} (L : List α) : L.filter (fun _ => false)=[] :=
  List.filter_eq_nil_iff.mpr (fun _ _ => by simp)

theorem degree_split_old {n : Nat} (F : Family (n+1)) (p : Fin n) :
    degree (through F) p+degree (away F) p=degree F p.castSucc := by
  induction F with
  | nil => simp [degree,through,away]
  | cons R F ih =>
    by_cases hl : Fin.last n ∈ R <;> by_cases hp : p.castSucc ∈ R <;>
      simp [degree,through,away,hl,hp,mem_trace,Nat.add_assoc,
        Nat.add_comm,Nat.add_left_comm] at ih ⊢ <;> omega

theorem degree_lift_last {n : Nat} (A B : Family n) :
    degree (lift A B) (Fin.last n)=A.length := by
  simp [degree,lift,List.filter_append,List.filter_map,Function.comp_def]

theorem degree_lift_old {n : Nat} (A B : Family n) (p : Fin n) :
    degree (lift A B) p.castSucc=degree A p+degree B p := by
  simp [degree,lift,List.filter_append,List.filter_map,Function.comp_def]

end Covering.Floors
