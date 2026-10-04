import Regular20Extension

namespace CoveringMatrixRegular20
open Covering Covering.PointSplit Covering.PointDegree Covering.TwoPointSplit Covering.SideLift
open Covering.NormalizedBridge20261003 Covering.NormalizedBridge20261003.Regular22Incidence

lemma exists_old (x : Fin 22) (hfirst : x≠anchorFirst) (hsecond : x≠anchorSecond) :
    ∃ p : Fin 20, old p=x := by
  obtain ⟨y,hy⟩ := Regular22Matching.cast_of_ne_last x hfirst
  have hyn : y≠Fin.last 20 := by
    intro hh
    apply hsecond
    rw [← hy,hh]
    rfl
  obtain ⟨p,hp⟩ := Regular22Matching.cast_of_ne_last y hyn
  refine ⟨p,?_⟩
  unfold old
  rw [hp,hy]

structure TwinData (H E : Family 20) (σ : Fin 20 → Fin 20) : Prop where
  no_fixed : ∀ p, σ p≠p
  involution : ∀ p, σ (σ p)=p
  pair_array : ∀ p q, pairDegree H p q+pairDegree E p q=
    if p=q ∨ q=σ p then 6 else 3
  H_twins : ∀ p R, R ∈ H → (p ∈ R ↔ σ p ∈ R)
  E_twins : ∀ p R, R ∈ E → (p ∈ R ↔ σ p ∈ R)

/-- The old physical points inherit the regular22 twin involution. -/
theorem old_twin_geometry (H E : Family 20) (h : Completion H E) :
    ∃ σ : Fin 20 → Fin 20, TwinData H E σ := by
  classical
  obtain ⟨τ,hne,hinv,hpair,htwin⟩ := CoveringMatrixRegular22.regular22_physical_twins
    (extended H E) (extended_rows H E h) (extended_cover H E h)
    (extended_length H E h) (extended_degree H E h)
  have hmapex : ∀ p : Fin 20, ∃ q : Fin 20, old q=τ (old p) := by
    intro p
    apply exists_old
    · intro hh
      have h6 : pairDegree (extended H E) (old p) anchorFirst=6 := by
        rw [← hh,hpair]
        simp
      have h3 : pairDegree (extended H E) (old p) anchorFirst=3 := by
        rw [pair_symmetric]
        exact first_old_pair H E h p
      omega
    · intro hh
      have h6 : pairDegree (extended H E) (old p) anchorSecond=6 := by
        rw [← hh,hpair]
        simp
      have h3 : pairDegree (extended H E) (old p) anchorSecond=3 := by
        rw [pair_symmetric]
        exact second_old_pair H E h p
      omega
  choose σ hmap using hmapex
  refine ⟨σ,?_⟩
  constructor
  · intro p hp
    have hh := hmap p
    rw [hp] at hh
    exact hne (old p) hh.symm
  · intro p
    apply old_injective
    rw [hmap,hmap,hinv]
  · intro p q
    have he : old p=old q ↔ p=q := ⟨fun he => old_injective he,fun he => congrArg old he⟩
    have hm : old q=τ (old p) ↔ q=σ p := by
      rw [← hmap p]
      exact ⟨fun he => old_injective he,fun he => congrArg old he⟩
    have hh := hpair (old p) (old q)
    simpa only [old_pair,he,hm] using hh
  · intro p R hR
    have hh := htwin (old p) (cone (cone R)) (H_row_lift_mem H E R hR)
    rw [← hmap p] at hh
    simpa only [old,mem_cone] using hh
  · intro p R hR
    have hh := htwin (old p) (embed (embed R)) (E_row_lift_mem H E R hR)
    rw [← hmap p] at hh
    simpa only [old,mem_embed] using hh

lemma pair_of_membership_imp {n : Nat} (F : Family n) (p q : Fin n)
    (hsub : ∀ R, R ∈ F → p ∈ R → q ∈ R) : pairDegree F p q=degree F p := by
  unfold pairDegree degree
  apply congrArg List.length
  apply List.filter_congr
  intro R hR
  by_cases hp : p ∈ R
  · have hq := hsub R hR hp
    simp [hp,hq]
  · simp [hp]

/-- The pairing is determined by H itself, so different completions share it. -/
theorem H_signature_characterizes (H E : Family 20) (h : Completion H E)
    (σ : Fin 20 → Fin 20) (ht : TwinData H E σ) (p q : Fin 20) (hpq : p≠q) :
    (∀ R, R ∈ H → (p ∈ R ↔ q ∈ R)) ↔ q=σ p := by
  constructor
  · intro hsig
    have hH : pairDegree H p q=3 := by
      rw [pair_of_membership_imp H p q (fun R hR => (hsig R hR).mp),h.H_degree]
    have hE := pair_slots_lower E p q
    rw [h.E_degree,h.E_degree,h.E_length] at hE
    have ha := ht.pair_array p q
    by_contra hq
    simp only [hpq,hq,or_self,if_false,hH] at ha
    omega
  · intro hh
    subst q
    exact ht.H_twins p

theorem completions_share_pairing (H E F : Family 20)
    (hE : Completion H E) (hF : Completion H F)
    (σ τ : Fin 20 → Fin 20) (hσ : TwinData H E σ) (hτ : TwinData H F τ) : σ=τ := by
  funext p
  exact (H_signature_characterizes H F hF τ hτ p (σ p) (Ne.symm (hσ.no_fixed p))).mp
    (hσ.H_twins p)

theorem nonpartner_H_codegree (H E : Family 20) (h : Completion H E)
    (σ : Fin 20 → Fin 20) (ht : TwinData H E σ)
    (p q : Fin 20) (hpq : p≠q) (hqp : q≠σ p) :
    pairDegree H p q=1 ∨ pairDegree H p q=2 := by
  obtain ⟨R,hR,hs⟩ := h.H_cover [p,q] (by simp [ValidBlock,hpq])
  have hm : R ∈ H.filter (fun S => p ∈ S ∧ q ∈ S) :=
    List.mem_filter.mpr ⟨hR,by simp only [decide_eq_true_eq]; exact ⟨hs p (by simp),hs q (by simp)⟩⟩
  have hlo : 0<pairDegree H p q := List.length_pos_of_mem hm
  have hE := pair_slots_lower E p q
  rw [h.E_degree,h.E_degree,h.E_length] at hE
  have ha := ht.pair_array p q
  simp only [hpq,hqp,or_self,if_false] at ha
  omega

#print axioms old_twin_geometry
#print axioms completions_share_pairing
#print axioms nonpartner_H_codegree
end CoveringMatrixRegular20
