module

public import Regular22PhysicalRigidity

@[expose] public section

open Matrix Finset
open scoped BigOperators
namespace CoveringMatrixRegular22
open Covering Covering.PointDegree CoveringMatrixIncidence

lemma physical_shift_rank_le (F : Family 22) (hregular : ∀ p, degree F p=6) :
    (shift (physicalWeights F)).rank≤(incidence F).rank := by
  let M := incidence F
  have hM : ∀ p, ∑ j, M p j=6 := by
    intro p; rw [row_sum,hregular]; norm_num
  have hf : M*M.transpose-(3:ℝ) • RowSumFactorization.ones (Fin 22) (Fin 22)=
      M*(1-(1/12:ℝ) • RowSumFactorization.ones (Fin F.length) (Fin F.length))*M.transpose := by
    convert RowSumFactorization.row_sum_factorization M 6 (1/12) hM using 1 <;> norm_num
  rw [physical_shift_eq F hregular,hf]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)

theorem physical_full_column_rank (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (hlen : F.length=11) (hregular : ∀ p, degree F p=6) : (incidence F).rank=11 := by
  let W := physicalWeights F
  have hs := physical_signed_data F hrows hcover hlen hregular
  have hr := physical_shift_rank F hlen hregular
  have hsq : (shift W*shift W).trace=396 := by
    rw [shift_trace_square W hs]
    simp_rw [every_energy_nine W hs hr]
    norm_num
  have hc := MatrixFoundation.trace_sq_le_rank_mul_trace_square (shift W) (shift_symmetric W hs)
  rw [shift_trace,hsq] at hc
  have hlo : (11:ℝ)≤((shift W).rank : ℝ) := by nlinarith
  have hloN : 11≤(shift W).rank := by exact_mod_cast hlo
  apply Nat.le_antisymm
  · simpa [hlen] using (incidence F).rank_le_card_width
  · exact hloN.trans (physical_shift_rank_le F hregular)

theorem physical_column_map_injective (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 3 F)
    (hlen : F.length=11) (hregular : ∀ p, degree F p=6) :
    Function.Injective (incidence F).mulVecLin := by
  have hr := physical_full_column_rank F hrows hcover hlen hregular
  have hn := LinearMap.finrank_range_add_finrank_ker (incidence F).mulVecLin
  change (incidence F).rank+Module.finrank ℝ (incidence F).mulVecLin.ker=
    Module.finrank ℝ (Fin F.length → ℝ) at hn
  have hd : Module.finrank ℝ (Fin F.length → ℝ)=11 := by simp [hlen]
  rw [hr,hd] at hn
  have hk : Module.finrank ℝ (incidence F).mulVecLin.ker=0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

#print axioms physical_full_column_rank
#print axioms physical_column_map_injective
end CoveringMatrixRegular22
