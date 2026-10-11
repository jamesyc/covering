module
public import Covering.Components.Excess
@[expose] public section

/-!
# Balanced quadruples

Definition of a balanced quadruple and the codegree `λ(u, v) = 6` (Section 4.1).
-/
open Finset
open scoped BigOperators
namespace Covering.Quadruple
open PointDegree SideLift
open Floors Nineteen

structure BalancedQuadruple (T : Family 24) where
  u : LowPoint T
  v : LowPoint T
  s : LowPoint T
  t : LowPoint T
  distinct : u ≠ v ∧ u ≠ s ∧ u ≠ t ∧ v ≠ s ∧ v ≠ t ∧ s ≠ t
  row_balance : ∀ R, R ∈ T →
    (if u.val ∈ R then (1:ℕ) else 0) + (if v.val ∈ R then 1 else 0) =
    (if s.val ∈ R then 1 else 0) + (if t.val ∈ R then 1 else 0)

lemma balance_pair_count {n : Nat} (T : Family n) (u v s t : Fin n)
    (hb : ∀ R, R ∈ T →
      (if u ∈ R then (1:ℕ) else 0) + (if v ∈ R then 1 else 0) =
      (if s ∈ R then 1 else 0) + (if t ∈ R then 1 else 0)) :
    degree T u + pairDegree T u v = pairDegree T u s + pairDegree T u t := by
  induction T with
  | nil => simp [degree, pairDegree]
  | cons R T ih =>
    have hR := hb R (by simp)
    have hT := ih (fun Q hQ => hb Q (by simp [hQ]))
    by_cases hu : u ∈ R <;> by_cases hv : v ∈ R <;>
      by_cases hs : s ∈ R <;> by_cases ht : t ∈ R <;>
      simp [degree, pairDegree, hu, hv, hs, ht] at hR hT ⊢ <;> omega

lemma selected_excess_le_five (T : Family 24)
    (hr : ∀ R, R ∈ T → ValidBlock 14 R) (hc : IsCovering 4 T)
    (u : LowPoint T) (S : Finset (Fin 24)) :
    (∑ x ∈ S, fullExcess T u.val x) ≤ 5 := by
  calc
    _ ≤ ∑ x, fullExcess T u.val x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ => fullExcess_nonnegative T hr hc u.val x)
    _ = 5 := fullExcess_low_row_sum T hr u

lemma BalancedQuadruple.left_codegrees {T : Family 24} (g : BalancedQuadruple T)
    (hr : ∀ R, R ∈ T → ValidBlock 14 R) (hc : IsCovering 4 T) :
    pairDegree T g.u.val g.v.val = 6 ∧
      ∀ x, x ≠ g.u.val → x ≠ g.v.val → x ≠ g.s.val → x ≠ g.t.val →
        pairDegree T g.u.val x = 6 := by
  rcases g.distinct with ⟨huv,hus,hut,hvs,hvt,hst⟩
  have neval (p q : LowPoint T) (h : p ≠ q) : p.val ≠ q.val :=
    fun he => h (Subtype.ext he)
  have huv' := neval _ _ huv
  have hus' := neval _ _ hus
  have hut' := neval _ _ hut
  have hvs' := neval _ _ hvs
  have hvt' := neval _ _ hvt
  have hst' := neval _ _ hst
  have hbal := balance_pair_count T g.u.val g.v.val g.s.val g.t.val g.row_balance
  rw [g.u.property] at hbal
  have hbR : (11:ℝ) + (pairDegree T g.u.val g.v.val : ℝ) =
      (pairDegree T g.u.val g.s.val : ℝ) + (pairDegree T g.u.val g.t.val : ℝ) := by
    exact_mod_cast hbal
  have hu : fullExcess T g.u.val g.v.val = (pairDegree T g.u.val g.v.val : ℝ)-6 := by
    simp [fullExcess,huv']
  have hs : fullExcess T g.u.val g.s.val = (pairDegree T g.u.val g.s.val : ℝ)-6 := by
    simp [fullExcess,hus']
  have ht : fullExcess T g.u.val g.t.val = (pairDegree T g.u.val g.t.val : ℝ)-6 := by
    simp [fullExcess,hut']
  have hb : fullExcess T g.u.val g.v.val + fullExcess T g.u.val g.s.val +
      fullExcess T g.u.val g.t.val ≤ 5 := by
    simpa [hvs',hvt',hst',add_assoc] using
      selected_excess_le_five T hr hc g.u {g.v.val,g.s.val,g.t.val}
  have hlo : (6:ℝ) ≤ (pairDegree T g.u.val g.v.val : ℝ) := by
    exact_mod_cast pair_floor_six T hr hc _ _ huv'
  have h6 : pairDegree T g.u.val g.v.val=6 := by
    rw [hu,hs,ht] at hb
    have he : (pairDegree T g.u.val g.v.val : ℝ)=6 := by linarith
    exact_mod_cast he
  have hsat : fullExcess T g.u.val g.v.val + fullExcess T g.u.val g.s.val +
      fullExcess T g.u.val g.t.val = 5 := by
    rw [hu,hs,ht,h6]
    rw [h6] at hbR
    norm_num only [Nat.cast_ofNat] at hbR ⊢
    linarith
  refine ⟨h6,?_⟩
  intro x hxu hxv hxs hxt
  have hb4 : fullExcess T g.u.val x + (fullExcess T g.u.val g.v.val +
      fullExcess T g.u.val g.s.val + fullExcess T g.u.val g.t.val) ≤ 5 := by
    simpa [hxv,hxs,hxt,hvs',hvt',hst',add_assoc] using
      selected_excess_le_five T hr hc g.u {x,g.v.val,g.s.val,g.t.val}
  rw [hsat] at hb4
  have hn := fullExcess_nonnegative T hr hc g.u.val x
  have hz : fullExcess T g.u.val x=0 := by linarith
  simp only [fullExcess,Ne.symm hxu,ite_false] at hz
  have he : (pairDegree T g.u.val x : ℝ)=6 := by linarith
  exact_mod_cast he

/-- The codegree `λ(u, v) = 6` and the outside codegrees follow from the balance
equation (13). -/
lemma BalancedQuadruple.codegrees {T : Family 24} (g : BalancedQuadruple T)
    (hr : ∀ R, R ∈ T → ValidBlock 14 R) (hc : IsCovering 4 T) :
    pairDegree T g.u.val g.v.val = 6 ∧
      ∀ x, x ≠ g.u.val → x ≠ g.v.val → x ≠ g.s.val → x ≠ g.t.val →
        pairDegree T g.u.val x = 6 ∧ pairDegree T g.v.val x = 6 := by
  rcases g.distinct with ⟨huv,hus,hut,hvs,hvt,hst⟩
  let g' : BalancedQuadruple T :=
    ⟨g.v,g.u,g.s,g.t,⟨Ne.symm huv,hvs,hvt,hus,hut,hst⟩,by
      intro R hR
      have h := g.row_balance R hR
      omega⟩
  obtain ⟨h6,hu⟩ := g.left_codegrees hr hc
  have hv := (g'.left_codegrees hr hc).2
  exact ⟨h6,fun x hxu hxv hxs hxt => ⟨hu x hxu hxv hxs hxt,hv x hxv hxu hxs hxt⟩⟩

end Covering.Quadruple