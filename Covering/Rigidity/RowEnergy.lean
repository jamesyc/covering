module

public import Covering.Rigidity.SignedEnergy
public import Covering.Rigidity.IncidenceMatrix

@[expose] public section

/-!
# Row energy of a cover

The deviations `e_pq = λ(p, q) - 3` of an eleven-block cover satisfy the hypotheses of Lemma 2.2.
-/
open Matrix Finset
open scoped BigOperators
namespace Covering.RowEnergy
open Covering Covering.PointDegree Covering.SideLift
open Covering.PairData
open Covering.IncidenceMatrix
/-- The deviations `e_pq = λ(p, q) - 3`. -/
def coverWeights (F : Family 22) : Matrix (Fin 22) (Fin 22) ℝ :=
  fun p q => if p=q then 0 else (pairDegree F p q : ℝ)-3

lemma signed_row_data (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (hlen : F.length=11) (hregular : ∀ p, degree F p=6) :
    SignedData (coverWeights F) := by
  have hd := cover_pair_data F hrows hcover hregular
  constructor
  · intro p q
    by_cases hpq : p=q
    · subst q; rfl
    · simp only [coverWeights,hpq,Ne.symm hpq,ite_false,hd.symmetric p q]
  · intro p; simp [coverWeights]
  · intro p
    have hs : (∑ q, (pairDegree F p q : ℝ))=72 := by
      rw [fin_nat_sum,hd.row_sum p]
      norm_num
    have he (q : Fin 22) : (pairDegree F p q : ℝ)=
        coverWeights F p q+3+(if q=p then 3 else 0) := by
      by_cases hpq : p=q
      · subst q; norm_num [coverWeights,hd.diagonal]
      · simp only [coverWeights,hpq,Ne.symm hpq,ite_false]
        ring
    simp_rw [he,Finset.sum_add_distrib] at hs
    norm_num at hs
    linarith
  · intro i j hij
    have hne : i≠j := by intro hh; subst j; simp [coverWeights] at hij
    have hl := (hd.off_diagonal_bounds i j hne).1
    have hlt : pairDegree F i j<3 := by
      have hh : (pairDegree F i j : ℝ)<3 := by
        simpa only [coverWeights,hne,ite_false,sub_lt_zero] using hij
      exact_mod_cast hh
    have htwo : pairDegree F i j=2 := by omega
    refine ⟨by norm_num [coverWeights,hne,htwo],?_⟩
    intro k hkj
    by_cases hki : k=i
    · subst k; left; simp [coverWeights]
    · have hb := two_provider_endpoint_bounds F hrows hcover hlen hregular
        i j hne htwo k hki hkj
      have hv : pairDegree F i k=3 ∨ pairDegree F i k=4 := by omega
      rcases hv with hv | hv
      · left; norm_num [coverWeights,Ne.symm hki,hv]
      · right; norm_num [coverWeights,Ne.symm hki,hv]

end Covering.RowEnergy
