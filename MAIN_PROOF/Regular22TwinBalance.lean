module

public import Regular22PhysicalRigidity

@[expose] public section

open Matrix Finset
open scoped BigOperators
namespace CoveringMatrixRegular22
open Covering Covering.PointDegree Covering.SideLift CoveringMatrixIncidence

lemma transpose_kernel_sum_zero (F : Family 22) (hregular : ∀ p, degree F p=6)
    (z : Fin 22 → ℝ) (hz : (incidence F).transpose *ᵥ z=0) : ∑ p, z p=0 := by
  have hs : (∑ j, ((incidence F).transpose *ᵥ z) j)=0 := by rw [hz]; simp
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply] at hs
  rw [Finset.sum_comm] at hs
  simp_rw [← Finset.sum_mul,row_sum,hregular] at hs
  norm_num at hs
  rw [← Finset.mul_sum] at hs
  linarith

lemma twin_gram_action (F : Family 22) (σ : Fin 22 → Fin 22)
    (hne : ∀ p, σ p≠p)
    (hpair : ∀ p q, pairDegree F p q=if p=q ∨ q=σ p then 6 else 3)
    (z : Fin 22 → ℝ) (p : Fin 22) :
    ((incidence F*(incidence F).transpose) *ᵥ z) p=
      3*z p+3*z (σ p)+3*∑ q, z q := by
  have he (q : Fin 22) : (incidence F*(incidence F).transpose) p q=
      3*(if q=p then 1 else 0)+3*(if q=σ p then 1 else 0)+3 := by
    rw [gram_entry,hpair]
    by_cases hqp : q=p
    · subst q; norm_num [Ne.symm (hne p)]
    · by_cases hqσ : q=σ p
      · norm_num [hqp,Ne.symm hqp,hqσ,hne p]
      · norm_num [hqp,Ne.symm hqp,hqσ,hne p]
  simp [Matrix.mulVec,dotProduct,he,add_mul,mul_ite,ite_mul,
    Finset.sum_add_distrib,Finset.mul_sum]

/-- A direct physical balance consequence with no quotient or inverse matrix. -/
theorem twin_balance_from_pair_data (F : Family 22)
    (hregular : ∀ p, degree F p=6) (σ : Fin 22 → Fin 22)
    (hne : ∀ p, σ p≠p)
    (hpair : ∀ p q, pairDegree F p q=if p=q ∨ q=σ p then 6 else 3)
    (z : Fin 22 → ℝ) (hz : (incidence F).transpose *ᵥ z=0) :
    ∀ p, z (σ p) = -z p := by
  have hs := transpose_kernel_sum_zero F hregular z hz
  have hG : (incidence F*(incidence F).transpose) *ᵥ z=0 := by
    rw [← Matrix.mulVec_mulVec,hz,Matrix.mulVec_zero]
  intro p
  have hp := congrFun hG p
  rw [twin_gram_action F σ hne hpair z p,hs] at hp
  simp only [Pi.zero_apply,mul_zero,add_zero] at hp
  linarith

theorem regular22_twins_with_balance (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (hlen : F.length=11) (hregular : ∀ p, degree F p=6) :
    ∃ σ : Fin 22 → Fin 22,
      (∀ p, σ p≠p) ∧ (∀ p, σ (σ p)=p) ∧
      (∀ p q, pairDegree F p q=if p=q ∨ q=σ p then 6 else 3) ∧
      (∀ p R, R ∈ F → (p ∈ R ↔ σ p ∈ R)) ∧
      (∀ z : Fin 22 → ℝ, (incidence F).transpose *ᵥ z=0 → ∀ p, z (σ p) = -z p) := by
  obtain ⟨σ,hne,hinv,hpair,htwin⟩ := regular22_physical_twins F hrows hcover hlen hregular
  exact ⟨σ,hne,hinv,hpair,htwin,twin_balance_from_pair_data F hregular σ hne hpair⟩

#print axioms regular22_twins_with_balance
end CoveringMatrixRegular22
