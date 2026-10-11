module
public import Covering.Rigidity.Energy
public import Covering.Rigidity.Regularity
@[expose] public section

/-!
# Eleven-block rigidity

Theorem 2.1: the points of an eleven-block `(22,12,3)` cover split into twin pairs.
-/
open Matrix Finset
open scoped BigOperators
namespace Covering.Rigidity
open Covering.RowEnergy Covering.IncidenceMatrix
open PointDegree SideLift
open PairData
lemma six_partner_unique (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (hlen : F.length=11) (hregular : ∀ p, degree F p=6) (p : Fin 22) :
    ∃! q, q≠p ∧ pairDegree F p q=6 := by
  have hs := signed_row_data F hrows hcover hlen hregular
  have hr := incidence_energy_ge F hrows hregular hlen
  obtain ⟨q,hq,hu⟩ := twin_partner_exists_unique_of_total (coverWeights F) hs hr p
  have hq6 : pairDegree F p q=6 := by
    have hh : (pairDegree F p q : ℝ)=6 := by
      have hh := hq.2
      simp only [coverWeights,Ne.symm hq.1,ite_false] at hh
      linarith
    exact_mod_cast hh
  refine ⟨q,⟨hq.1,hq6⟩,?_⟩
  intro r hr
  apply hu r
  exact ⟨hr.1,by norm_num [coverWeights,Ne.symm hr.1,hr.2]⟩

/-- Theorem 2.1: an eleven-block `(22,12,3)` cover has a fixed-point-free twin
involution `σ` with `λ(p, σ p) = 6` and `λ(p, q) = 3` otherwise; twins lie in the
same blocks. -/
theorem eleven_block_rigidity (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (hlen : F.length=11) :
    ∃ σ : Fin 22 → Fin 22,
      (∀ p, σ p≠p) ∧ (∀ p, σ (σ p)=p) ∧
      (∀ p q, pairDegree F p q=if p=q ∨ q=σ p then 6 else 3) ∧
      (∀ p R, R ∈ F → (p ∈ R ↔ σ p ∈ R)) := by
  classical
  have hregular := eleven_block_regular F hrows hcover hlen
  have hex := six_partner_unique F hrows hcover hlen hregular
  choose σ hσ huniq using hex
  have hinv : ∀ p, σ (σ p)=p := by
    intro p
    symm
    apply huniq (σ p) p
    refine ⟨Ne.symm (hσ p).1,?_⟩
    rw [pair_symmetric]
    exact (hσ p).2
  refine ⟨σ,fun p => (hσ p).1,hinv,?_,?_⟩
  · intro p q
    by_cases hpq : p=q
    · subst q; simp [pair_diagonal,hregular]
    · by_cases hqp : q=σ p
      · subst q; simp [hpq,(hσ p).2]
      · simp only [hpq,hqp,or_self,ite_false]
        have hs := signed_row_data F hrows hcover hlen hregular
        have hr := incidence_energy_ge F hrows hregular hlen
        rcases entry_zero_or_three_of_total (coverWeights F) hs hr p q with hz | hthree
        · have hh : (pairDegree F p q : ℝ)=3 := by
            simp only [coverWeights,hpq,ite_false] at hz
            linarith
          exact_mod_cast hh
        · have hq6 : pairDegree F p q=6 := by
            have hh : (pairDegree F p q : ℝ)=6 := by
              simp only [coverWeights,hpq,ite_false] at hthree
              linarith
            exact_mod_cast hh
          exact False.elim (hqp (huniq p q ⟨Ne.symm hpq,hq6⟩))
  · intro p R hR
    apply pair_equal_degrees_twins F p (σ p) _ _ R hR
    · rw [hregular]; exact (hσ p).2
    · rw [hregular]; exact (hσ p).2

/-- Distinct indexed blocks meet in six points. The Gram entry counts the intersection. -/
theorem eleven_block_intersections (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (hlen : F.length = 11) (i j : Fin F.length) (hij : i ≠ j) :
    ((incidence F).transpose * incidence F) i j = 6 := by
  have hregular := eleven_block_regular F hrows hcover hlen
  have hs := signed_row_data F hrows hcover hlen hregular
  have he := every_energy_nine_of_total (coverWeights F) hs
    (incidence_energy_ge F hrows hregular hlen)
  have hid := incidence_deficit_identity F hrows hregular hlen
  have hd : (∑ p, (9 - energy (coverWeights F) p)) = 0 := by simp [he]
  rw [hd, zero_add] at hid
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (univ : Finset (Fin F.length))) =>
      Finset.sum_nonneg (fun j _ => sq_nonneg
        (if i = j then 0 else ((incidence F).transpose * incidence F) i j - 6)))).mp hid
      i (mem_univ i)
  have heq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (univ : Finset (Fin F.length))) =>
      sq_nonneg (if i = j then 0 else ((incidence F).transpose * incidence F) i j - 6))).mp hi
        j (mem_univ j)
  simp only [ite_eq_right hij] at heq
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp heq)

end Covering.Rigidity