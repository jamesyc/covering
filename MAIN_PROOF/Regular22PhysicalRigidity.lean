module

public import Regular22MatrixRows
public import PhysicalIncidenceMatrix
public import RowSumFactorization

@[expose] public section

open Matrix Finset
open scoped BigOperators

namespace CoveringMatrixRegular22

open Covering Covering.PointDegree Covering.SideLift
open Covering.NormalizedBridge20261003.Regular22Incidence
open CoveringMatrixIncidence

/-- Signed excess of the actual physical pair-codegree array. -/
def physicalWeights (F : Family 22) : Matrix (Fin 22) (Fin 22) ℝ :=
  fun p q => if p=q then 0 else (pairDegree F p q : ℝ)-3

lemma physical_signed_data (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (hlen : F.length=11) (hregular : ∀ p, degree F p=6) :
    SignedData (physicalWeights F) := by
  have hd := physical_pair_data F hrows hcover hregular
  constructor
  · intro p q
    by_cases hpq : p=q
    · subst q; rfl
    · simp only [physicalWeights,hpq,Ne.symm hpq,if_false,hd.symmetric p q]
  · intro p; simp [physicalWeights]
  · intro p
    have hs : (∑ q, (pairDegree F p q : ℝ))=72 := by
      rw [fin_nat_sum,hd.row_sum p]
      norm_num
    have he (q : Fin 22) : (pairDegree F p q : ℝ)=
        physicalWeights F p q+3+(if q=p then 3 else 0) := by
      by_cases hpq : p=q
      · subst q; norm_num [physicalWeights,hd.diagonal]
      · simp only [physicalWeights,hpq,Ne.symm hpq,if_false]
        ring
    simp_rw [he,Finset.sum_add_distrib] at hs
    norm_num at hs
    linarith
  · intro i j hij
    have hne : i≠j := by intro hh; subst j; simpa [physicalWeights] using hij
    have hl := (hd.off_diagonal_bounds i j hne).1
    have hlt : pairDegree F i j<3 := by
      have hh : (pairDegree F i j : ℝ)<3 := by
        simpa only [physicalWeights,hne,if_false,sub_lt_zero] using hij
      exact_mod_cast hh
    have htwo : pairDegree F i j=2 := by omega
    refine ⟨by norm_num [physicalWeights,hne,htwo],?_⟩
    intro k hkj
    by_cases hki : k=i
    · subst k; left; simp [physicalWeights]
    · have hb := two_provider_endpoint_bounds F hrows hcover hlen hregular
        i j hne htwo k hki hkj
      have hv : pairDegree F i k=3 ∨ pairDegree F i k=4 := by omega
      rcases hv with hv | hv
      · left; norm_num [physicalWeights,Ne.symm hki,hv]
      · right; norm_num [physicalWeights,Ne.symm hki,hv]

lemma physical_shift_eq (F : Family 22) (hregular : ∀ p, degree F p=6) :
    shift (physicalWeights F)=incidence F*(incidence F).transpose-
      (3:ℝ) • RowSumFactorization.ones (Fin 22) (Fin 22) := by
  ext p q
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    RowSumFactorization.ones,mul_one,gram_entry]
  by_cases hpq : p=q
  · subst q; norm_num [shift,physicalWeights,pair_diagonal,hregular]
  · simp [shift,physicalWeights,hpq]

lemma physical_shift_rank (F : Family 22) (hlen : F.length=11)
    (hregular : ∀ p, degree F p=6) : (shift (physicalWeights F)).rank≤11 := by
  let M := incidence F
  have hM : ∀ p, ∑ j, M p j=6 := by
    intro p
    rw [row_sum,hregular]
    norm_num
  have hf : M*M.transpose-(3:ℝ) • RowSumFactorization.ones (Fin 22) (Fin 22)=
      M*(1-(1/12:ℝ) • RowSumFactorization.ones (Fin F.length) (Fin F.length))*M.transpose := by
    convert RowSumFactorization.row_sum_factorization M 6 (1/12) hM using 1 <;> norm_num
  rw [physical_shift_eq F hregular,hf]
  have hh := ((Matrix.rank_mul_le_left M
    (1-(1/12:ℝ) • RowSumFactorization.ones (Fin F.length) (Fin F.length))).trans M.rank_le_card_width)
  have hr := (Matrix.rank_mul_le_left
    (M*(1-(1/12:ℝ) • RowSumFactorization.ones (Fin F.length) (Fin F.length))) M.transpose).trans hh
  simpa [hlen] using hr

lemma physical_six_partner_unique (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (hlen : F.length=11) (hregular : ∀ p, degree F p=6) (p : Fin 22) :
    ∃! q, q≠p ∧ pairDegree F p q=6 := by
  have hs := physical_signed_data F hrows hcover hlen hregular
  have hr := physical_shift_rank F hlen hregular
  obtain ⟨q,hq,hu⟩ := twin_partner_exists_unique (physicalWeights F) hs hr p
  have hq6 : pairDegree F p q=6 := by
    have hh : (pairDegree F p q : ℝ)=6 := by
      have hh := hq.2
      simp only [physicalWeights,Ne.symm hq.1,if_false] at hh
      linarith
    exact_mod_cast hh
  refine ⟨q,⟨hq.1,hq6⟩,?_⟩
  intro r hr
  apply hu r
  exact ⟨hr.1,by norm_num [physicalWeights,Ne.symm hr.1,hr.2]⟩

/-- A physical twin involution and the entire pair-codegree array, derived from
actual uniform rows, triple coverage, eleven row slots and degree six. -/
theorem regular22_physical_twins (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (hlen : F.length=11) (hregular : ∀ p, degree F p=6) :
    ∃ σ : Fin 22 → Fin 22,
      (∀ p, σ p≠p) ∧ (∀ p, σ (σ p)=p) ∧
      (∀ p q, pairDegree F p q=if p=q ∨ q=σ p then 6 else 3) ∧
      (∀ p R, R ∈ F → (p ∈ R ↔ σ p ∈ R)) := by
  classical
  have hex := physical_six_partner_unique F hrows hcover hlen hregular
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
      · simp only [hpq,hqp,or_self,if_false]
        have hs := physical_signed_data F hrows hcover hlen hregular
        have hr := physical_shift_rank F hlen hregular
        rcases entry_zero_or_three (physicalWeights F) hs hr p q with hz | hthree
        · have hh : (pairDegree F p q : ℝ)=3 := by
            simp only [physicalWeights,hpq,if_false] at hz
            linarith
          exact_mod_cast hh
        · have hq6 : pairDegree F p q=6 := by
            have hh : (pairDegree F p q : ℝ)=6 := by
              simp only [physicalWeights,hpq,if_false] at hthree
              linarith
            exact_mod_cast hh
          exact False.elim (hqp (huniq p q ⟨Ne.symm hpq,hq6⟩))
  · intro p R hR
    apply pair_equal_degrees_twins F p (σ p) _ _ R hR
    · rw [hregular]; exact (hσ p).2
    · rw [hregular]; exact (hσ p).2

#print axioms regular22_physical_twins

end CoveringMatrixRegular22
