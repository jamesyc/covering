module

public import Covering.Quadruple.OutsideTrace
public import Covering.Basic.ExcessPatterns
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Omission colours

Section 4.3: colouring ordinary points by the `G`-block that omits them.
-/

open Finset
open scoped BigOperators
namespace Covering.Colors
open Covering Covering.PointDegree Covering.SideLift Covering.CrossGrid
open Covering.Floors Covering.PointCover
open Covering.PairData
noncomputable section

lemma degree_bound {n : Nat} (F : Family n) (p : Fin n) : degree F p ≤ F.length :=
  List.length_filter_le _ _

lemma total_degree {n k : Nat} (F : Family n) (hr : ∀ R, R ∈ F → ValidBlock k R) :
    ∑ p, degree F p = k*F.length := by
  rw [Fin.sum_univ_def,incidence_on_eq]
  have hh : ∀ R, R∈F → (hits (List.finRange n) R).length=k := by
    intro R hR
    have hv := hr R hR
    rw [LinearTriples.supported_hits_length (List.finRange n) R
      (List.nodup_finRange n) hv.1 (fun p _ => by simp)]
    exact hv.2
  rw [List.map_congr_left hh,sum_map_const]
  exact Nat.mul_comm _ _

/-- Three 14-point blocks on 20 points, each point of degree at least two: exactly
two points have degree three. -/
theorem two_high_points (F : Family 20) (hlen : F.length=3)
    (hr : ∀ R, R ∈ F → ValidBlock 14 R) (hfloor : ∀ p, 2 ≤ degree F p) :
    ∃ a b, a≠b ∧ degree F a=3 ∧ degree F b=3 ∧
      ∀ p, p≠a → p≠b → degree F p=2 := by
  let e := fun p => degree F p-2
  have hp : ∀ p, e p+2=degree F p := fun p => Nat.sub_add_cancel (hfloor p)
  have ht := total_degree F hr
  rw [hlen] at ht
  have hs : (∑ p, e p)+40=42 := by
    have h := Finset.sum_congr rfl (fun p (_ : p ∈ (univ : Finset (Fin 20))) => hp p)
    simpa [Finset.sum_add_distrib,ht] using h
  have he : ∑ p,e p=2 := by omega
  rcases Covering.FiniteExcess.sum_two_pattern e he with ⟨p,hp2,_⟩ | ⟨a,b,hab,ha,hb,hrest⟩
  · have h := hp p
    have hu := degree_bound F p
    omega
  · refine ⟨a,b,hab,?_,?_,?_⟩
    · have h := hp a; omega
    · have h := hp b; omega
    · intro p hpa hpb
      have hz := hrest p hpa hpb
      have h := hp p
      omega

/-- The colour of a point: the set of blocks omitting it (used with `F = G`). -/
def color {n : Nat} (F : Family n) (p : Fin n) : Finset (Fin F.length) :=
  univ.filter (fun j => p ∉ F.get j)

lemma color_eq_of_twins {n : Nat} (F : Family n) (p q : Fin n)
    (ht : ∀ R, R ∈ F → (p∈R ↔ q∈R)) : color F p=color F q := by
  ext j
  simp only [color,mem_filter,mem_univ,true_and]
  exact not_congr (ht (F.get j) (List.get_mem F j))

lemma color_eq_of_pair_floor {n : Nat} (F : Family n) (p q : Fin n)
    (hp : degree F p=2) (hq : degree F q=2) (hpq : 2≤pairDegree F p q) :
    color F p=color F q := by
  have hle := pair_le_point F p q
  have he : pairDegree F p q=2 := by omega
  apply color_eq_of_twins F p q
  exact pair_equal_degrees_twins F p q (by omega) (by omega)

lemma missing_slot {n : Nat} (F : Family n) (p : Fin n)
    (hp : degree F p<F.length) : ∃ j : Fin F.length, p∉F.get j := by
  by_contra hh
  have hall : ∀ R, R ∈ F → p∈R := by
    intro R hR
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hR
    exact by_contra (fun hn => hh ⟨j,hn⟩)
  have he : degree F p=F.length := by
    unfold degree
    congr 1
    apply List.filter_eq_self.mpr
    intro R hR
    simpa using hall R hR
  omega

lemma omitted_points_card (R : Block 20) (hR : ValidBlock 14 R) :
    (univ.filter (fun p : Fin 20 => p∉R)).card=6 := by
  have he : (univ.filter (fun p : Fin 20 => p∉R))=R.toFinsetᶜ := by ext p; simp
  rw [he,Finset.card_compl]
  rw [List.toFinset_card_of_nodup hR.1,hR.2]
  rfl

/-- Each colour class of ordinary points lies in the six-point complement of one
`G`-block. -/
theorem color_fiber_capacity (F : Family 20) (hlen : F.length=3)
    (hr : ∀ R, R ∈ F → ValidBlock 14 R) (L : Finset (Fin 20))
    (hL : ∀ p, p∈L → degree F p=2) (c : Finset (Fin F.length)) :
    (L.filter (fun p => color F p=c)).card≤6 := by
  classical
  by_cases hh : (L.filter (fun p => color F p=c)).Nonempty
  · obtain ⟨p,hp⟩ := hh
    obtain ⟨hpL,hpc⟩ := mem_filter.mp hp
    obtain ⟨j,hj⟩ := missing_slot F p (by rw [hL p hpL,hlen]; decide)
    have hjc : j∈c := by
      rw [← hpc]
      exact mem_filter.mpr ⟨mem_univ j,hj⟩
    have hsub : L.filter (fun p => color F p=c) ⊆ univ.filter (fun p => p∉F.get j) := by
      intro q hq
      have hqc := (mem_filter.mp hq).2
      have hqj : j∈color F q := by rw [hqc]; exact hjc
      simpa only [color,mem_filter,mem_univ,true_and] using hqj
    calc
      _ ≤ (univ.filter (fun p : Fin 20 => p∉F.get j)).card := card_le_card hsub
      _ = 6 := omitted_points_card _ (hr _ (List.get_mem F j))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hh]
    simp

end
end Covering.Colors
