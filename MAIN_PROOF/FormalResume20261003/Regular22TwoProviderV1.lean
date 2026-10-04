module

public import FormalResume20261003.Regular22IncidenceV1

@[expose] public section

namespace Covering.NormalizedBridge20261003.Regular22Incidence

open PointDegree SideLift

def commonRows {n : Nat} (F : Family n) (p q : Fin n) : Family n :=
  F.filter (fun R => p ∈ R ∧ q ∈ R)

def neitherRows {n : Nat} (F : Family n) (p q : Fin n) : Family n :=
  F.filter (fun R => p ∉ R ∧ q ∉ R)

theorem common_degree_left {n : Nat} (F : Family n) (p q : Fin n) :
    degree (commonRows F p q) p=pairDegree F p q := by
  induction F with
  | nil => simp [commonRows,degree,pairDegree]
  | cons R F ih =>
    by_cases hp : p ∈ R <;> by_cases hq : q ∈ R <;>
      simp [commonRows,degree,pairDegree,hp,hq] at ih ⊢ <;> omega

theorem common_degree_right {n : Nat} (F : Family n) (p q : Fin n) :
    degree (commonRows F p q) q=pairDegree F p q := by
  have he : commonRows F p q=commonRows F q p := by simp only [commonRows,and_comm]
  rw [he,common_degree_left,pair_symmetric]

theorem degree_positive_of_mem {n : Nat} (F : Family n) (p : Fin n)
    (R : Block n) (hR : R ∈ F) (hp : p ∈ R) : 1≤degree F p := by
  have hh := Weighted.term_le_sum_map F (fun S => if p ∈ S then 1 else 0) R hR
  rw [sum_indicator_eq_filter_length] at hh
  simpa only [if_pos hp,degree] using hh

/-- Two providers of a pair cover every third point exactly once. -/
theorem common_third_exactly_one (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (p q : Fin 22) (hpq : p≠q) (hpair : pairDegree F p q=2)
    (z : Fin 22) (hzp : z≠p) (hzq : z≠q) : degree (commonRows F p q) z=1 := by
  let T := commonRows F p q
  let f := fun r : Fin 22 => 1+(if r ∈ [p,q] then 1 else 0)
  have hTlen : T.length=2 := hpair
  have hTrows : ∀ R, R ∈ T → ValidBlock 12 R :=
    fun R hR => hrows R (List.mem_filter.mp hR).1
  have hlo : ∀ r, f r≤degree T r := by
    intro r
    by_cases hrp : r=p
    · subst r
      rw [common_degree_left,hpair]
      simp [f]
    · by_cases hrq : r=q
      · subst r
        rw [common_degree_right,hpair]
        simp [f]
      · have hvalid : ValidBlock 3 [p,q,r] := by
          simp [ValidBlock,hpq,Ne.symm hrp,Ne.symm hrq]
        obtain ⟨R,hR,hs⟩ := hcover [p,q,r] hvalid
        have hRT : R ∈ T := List.mem_filter.mpr ⟨hR,by
          simp only [decide_eq_true_eq]
          exact ⟨hs p (by simp),hs q (by simp)⟩⟩
        have hh := degree_positive_of_mem T r R hRT (hs r (by simp))
        simpa [f,hrp,hrq] using hh
  have hsum : ((List.finRange 22).map f).sum=24 := by
    unfold f
    rw [Weighted.sum_map_add,sum_map_const,List.length_finRange]
    rw [LinearTriples.presence_sum (List.finRange 22) [p,q]
      (List.nodup_finRange 22) (by simp [hpq]) (fun r _ => by simp)]
    rfl
  have hi := incidence_le T
  have hu := Weighted.sum_map_le_length_mul T List.length 12
    (fun R hR => Nat.le_of_eq (hTrows R hR).2)
  rw [hTlen] at hu
  have he := pointwise_eq_of_sum_le (List.finRange 22) f (degree T)
    (fun r _ => hlo r) (by rw [hsum]; omega)
  have hz := he z (by simp)
  simpa [f,hzp,hzq] using hz.symm

theorem pair_slot_partition {n : Nat} (F : Family n) (p q : Fin n) :
    (neitherRows F p q).length+degree F p+degree F q=F.length+pairDegree F p q := by
  induction F with
  | nil => simp [neitherRows,degree,pairDegree]
  | cons R F ih =>
    by_cases hp : p ∈ R <;> by_cases hq : q ∈ R <;>
      simp [neitherRows,degree,pairDegree,hp,hq] at ih ⊢ <;> omega

theorem pair_third_partition {n : Nat} (F : Family n) (p q z : Fin n) :
    pairDegree F p z+pairDegree F q z+degree (neitherRows F p q) z=
      degree F z+degree (commonRows F p q) z := by
  induction F with
  | nil => simp [neitherRows,commonRows,degree,pairDegree]
  | cons R F ih =>
    by_cases hp : p ∈ R <;> by_cases hq : q ∈ R <;> by_cases hz : z ∈ R <;>
      simp [neitherRows,commonRows,degree,pairDegree,hp,hq,hz] at ih ⊢ <;> omega

theorem two_provider_pair_sum (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (hlen : F.length=11) (hregular : ∀ p, degree F p=6)
    (p q : Fin 22) (hpq : p≠q) (hpair : pairDegree F p q=2)
    (z : Fin 22) (hzp : z≠p) (hzq : z≠q) :
    6≤pairDegree F p z+pairDegree F q z ∧ pairDegree F p z+pairDegree F q z≤7 := by
  have hn := pair_slot_partition F p q
  rw [hregular p,hregular q,hlen,hpair] at hn
  have hnl : (neitherRows F p q).length=1 := by omega
  have hd : degree (neitherRows F p q) z≤1 := by
    have hh := List.length_filter_le (fun R : Block 22 => decide (z ∈ R)) (neitherRows F p q)
    simpa only [degree,hnl] using hh
  have he := pair_third_partition F p q z
  rw [hregular z,common_third_exactly_one F hrows hcover p q hpq hpair z hzp hzq] at he
  omega

/-- Every other codegree from an endpoint of a codegree-two pair is three or four. -/
theorem two_provider_endpoint_bounds (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (hlen : F.length=11) (hregular : ∀ p, degree F p=6)
    (p q : Fin 22) (hpq : p≠q) (hpair : pairDegree F p q=2)
    (z : Fin 22) (hzp : z≠p) (hzq : z≠q) :
    3≤pairDegree F p z ∧ pairDegree F p z≤4 := by
  have hs := two_provider_pair_sum F hrows hcover hlen hregular p q hpq hpair z hzp hzq
  have hpz := triple_pair_floor_two F hrows hcover p z (Ne.symm hzp)
  have hqz := triple_pair_floor_two F hrows hcover q z (Ne.symm hzq)
  have hpnot : pairDegree F p z≠2 := by
    intro hh
    exact hzq (Regular22Matching.codegree_two_matching F hrows hcover p z q
      (Ne.symm hzp) hpq (hregular p) hh hpair)
  have hqnot : pairDegree F q z≠2 := by
    intro hh
    have hqp : pairDegree F q p=2 := by rw [pair_symmetric]; exact hpair
    exact hzp (Regular22Matching.codegree_two_matching F hrows hcover q z p
      (Ne.symm hzq) (Ne.symm hpq) (hregular q) hh hqp)
  omega

end Covering.NormalizedBridge20261003.Regular22Incidence
