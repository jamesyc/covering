module

public import A19PhysicalBalance
public import WeightedComponentSupports

@[expose] public section

open Matrix Finset
open scoped BigOperators
namespace Covering.NormalizedBridge20261003.A19Physical
open PointDegree SideLift WeightedSignlessKernel WeightedKernelComponents

lemma sum_capacity_outside {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (f : V → ℝ) (hzero : ∀ i ∈ s, f i = 0) (hcap : ∀ i, f i ≤ 5) :
    (∑ i, f i) ≤ 5 * (sᶜ.card : ℝ) := by
  have hz : (∑ i ∈ s, f i) = 0 := Finset.sum_eq_zero hzero
  have hs := s.sum_add_sum_compl f
  rw [hz, zero_add] at hs
  rw [← hs]
  calc
    (∑ i ∈ sᶜ, f i) ≤ ∑ i ∈ sᶜ, (5 : ℝ) := Finset.sum_le_sum (fun i _ => hcap i)
    _ = 5 * (sᶜ.card : ℝ) := by simp; ring

lemma good_to_high_zero (T : Family 24) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (hcover : IsCovering 4 T) (p : LowPoint T)
    (hp : p ∈ (lowSystem T hrows hcover).goodVertices)
    (q : Fin 24) (hq : degree T q ≠ 11) : fullExcess T p.val q = 0 := by
  apply high_excess_zero_of_regular_low_row T hrows hcover p _ q hq
  exact (lowSystem T hrows hcover).good_vertex_regular p hp

lemma low_pair_capacity (T : Family 24) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (hcover : IsCovering 4 T) (r : LowPoint T) (p q : Fin 24) (hpq : p ≠ q) :
    fullExcess T p r.val + fullExcess T q r.val ≤ 5 := by
  rw [fullExcess_symmetric T p r.val, fullExcess_symmetric T q r.val]
  have h := Finset.sum_le_sum_of_subset_of_nonneg (s := ({p, q} : Finset (Fin 24)))
    (t := univ) (fun i _ => mem_univ i)
    (fun i _ _ => fullExcess_nonnegative T hrows hcover r.val i)
  rw [Finset.sum_pair hpq, fullExcess_low_row_sum T hrows r] at h
  exact h

lemma good_vertices_le_sixteen_one_high (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (p : Fin 24) (hp : degree T p = 13) (hrest : ∀ q, q ≠ p → degree T q = 11) :
    (lowSystem T hrows hcover).goodVertices.card ≤ 16 := by
  classical
  let S := lowSystem T hrows hcover
  change S.goodVertices.card ≤ 16
  have hpnot : degree T p ≠ 11 := by omega
  have hs := Fintype.sum_subtype_add_sum_subtype (fun q => degree T q = 11)
    (fun q => fullExcess T p q)
  have hz : (∑ q : {q : Fin 24 // ¬ degree T q = 11}, fullExcess T p q.val) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    have hqp : q.val = p := by
      by_contra h
      exact q.property (hrest q.val h)
    rw [hqp, fullExcess_diagonal]
  have hfull : (∑ q, fullExcess T p q) = 31 := by
    rw [fullExcess_row_sum T hrows, hp]; norm_num
  have hlow : (∑ q : LowPoint T, fullExcess T p q.val) = 31 := by
    rw [hz, add_zero, hfull] at hs
    exact hs
  have hcap := sum_capacity_outside S.goodVertices (fun q => fullExcess T p q.val)
    (fun q hq => by rw [fullExcess_symmetric]; exact good_to_high_zero T hrows hcover q hq p hpnot)
    (fun q => by rw [fullExcess_symmetric]; exact fullExcess_low_entry_le_five T hrows hcover q p)
  rw [hlow] at hcap
  have hnat : 31 ≤ 5 * S.goodVerticesᶜ.card := by exact_mod_cast hcap
  have hc := Finset.card_add_card_compl S.goodVertices
  rw [low_card_one_high T p hp hrest] at hc
  omega

lemma good_vertices_le_sixteen_two_high (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (p q : Fin 24) (hpq : p ≠ q) (hp : degree T p = 12) (hq : degree T q = 12)
    (hrest : ∀ r, r ≠ p → r ≠ q → degree T r = 11) :
    (lowSystem T hrows hcover).goodVertices.card ≤ 16 := by
  classical
  let S := lowSystem T hrows hcover
  change S.goodVertices.card ≤ 16
  let H := {r : Fin 24 // ¬ degree T r = 11}
  let P : H := ⟨p, by omega⟩
  let Q : H := ⟨q, by omega⟩
  have hPQ : P ≠ Q := fun h => hpq (congrArg Subtype.val h)
  have huniv : (univ : Finset H) = {P, Q} := by
    ext r
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    by_cases hrp : r.val = p
    · exact Or.inl (Subtype.ext hrp)
    · right
      apply Subtype.ext
      by_contra hrq
      exact r.property (hrest r.val hrp hrq)
  have hs := Fintype.sum_subtype_add_sum_subtype (fun r => degree T r = 11)
    (fun r => fullExcess T p r + fullExcess T q r)
  have hhigh : (∑ r : H, (fullExcess T p r.val + fullExcess T q r.val)) =
      2 * fullExcess T p q := by
    rw [huniv, Finset.sum_pair hPQ]
    simp only [P, Q, fullExcess_diagonal, zero_add, add_zero]
    rw [fullExcess_symmetric T q p]
    ring
  have hfull : (∑ r, (fullExcess T p r + fullExcess T q r)) = 36 := by
    rw [Finset.sum_add_distrib, fullExcess_row_sum T hrows, fullExcess_row_sum T hrows, hp, hq]
    norm_num
  have ht : fullExcess T p q ≤ 6 := by
    have h := Regular22Incidence.pair_le_point T p q
    rw [hp] at h
    have h' : (pairDegree T p q : ℝ) ≤ 12 := by exact_mod_cast h
    simp only [fullExcess, if_neg hpq]
    linarith
  have hlow : 24 ≤ ∑ r : LowPoint T, (fullExcess T p r.val + fullExcess T q r.val) := by
    rw [hhigh, hfull] at hs
    linarith
  have hcap := sum_capacity_outside S.goodVertices
    (fun r => fullExcess T p r.val + fullExcess T q r.val)
    (fun r hr => by
      rw [fullExcess_symmetric T p r.val, fullExcess_symmetric T q r.val,
        good_to_high_zero T hrows hcover r hr p (by omega),
        good_to_high_zero T hrows hcover r hr q (by omega)]
      simp)
    (fun r => low_pair_capacity T hrows hcover r p q hpq)
  have hnat : 24 ≤ 5 * S.goodVerticesᶜ.card := by exact_mod_cast hlow.trans hcap
  have hc := Finset.card_add_card_compl S.goodVertices
  rw [low_card_two_high T p q hpq hp hq hrest] at hc
  obtain ⟨k, hk⟩ := S.good_vertices_even
  omega

lemma good_vertices_le_sixteen (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T) (hlen : T.length = 19) :
    (lowSystem T hrows hcover).goodVertices.card ≤ 16 := by
  rcases degree_patterns T hrows hcover hlen with ⟨p, hp, hrest⟩ | ⟨p, q, hpq, hp, hq, hrest⟩
  · exact good_vertices_le_sixteen_one_high T hrows hcover p hp hrest
  · exact good_vertices_le_sixteen_two_high T hrows hcover p q hpq hp hq hrest

end Covering.NormalizedBridge20261003.A19Physical
#print axioms Covering.NormalizedBridge20261003.A19Physical.good_vertices_le_sixteen_one_high
#print axioms Covering.NormalizedBridge20261003.A19Physical.good_vertices_le_sixteen_two_high
#print axioms Covering.NormalizedBridge20261003.A19Physical.good_vertices_le_sixteen
