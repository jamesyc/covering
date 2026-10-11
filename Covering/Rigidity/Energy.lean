module
public import Covering.Rigidity.RowEnergy
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
@[expose] public section

/-!
# The double count

Equations (4)–(6): the energy identity forcing every row energy to be nine and every block intersection to be six.
-/
open Matrix Finset
open scoped BigOperators
namespace Covering.Rigidity
open Covering.IncidenceMatrix Covering.RowEnergy
open PointDegree SideLift
open PairData

lemma gram_symmetric {V I : Type*} [Fintype V] [Fintype I]
    (M : Matrix V I ℝ) (p q : V) :
    (M * M.transpose) p q = (M * M.transpose) q p := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma trace_square_eq {V : Type*} [Fintype V] (A : Matrix V V ℝ)
    (hs : ∀ i j, A i j = A j i) :
    (A * A).trace = ∑ i, ∑ j, (A i j)^2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs j i]
  ring

/-- Equation (4): double counting two points in two blocks. -/
lemma gram_frobenius {V I : Type*} [Fintype V] [Fintype I]
    (M : Matrix V I ℝ) :
    (∑ p, ∑ q, ((M * M.transpose) p q)^2) =
      ∑ i, ∑ j, ((M.transpose * M) i j)^2 := by
  calc
    _ = ((M * M.transpose) * (M * M.transpose)).trace :=
      (trace_square_eq _ (gram_symmetric M)).symm
    _ = (((M * M.transpose) * M) * M.transpose).trace := by simp only [Matrix.mul_assoc]
    _ = ((M.transpose * (M * M.transpose)) * M).trace := Matrix.trace_mul_cycle _ _ _
    _ = ((M.transpose * M) * (M.transpose * M)).trace := by simp only [Matrix.mul_assoc]
    _ = _ := trace_square_eq _ (by
      intro i j
      simpa only [Matrix.transpose_transpose] using gram_symmetric M.transpose i j)

lemma centered_row {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℝ) (i : V) (d r c : ℝ) (hd : f i = d) (hr : ∑ j, f j = r) :
    (∑ j, (if i = j then 0 else f j - c)^2) =
      (∑ j, (f j)^2) - 2*c*r + (Fintype.card V : ℝ)*c^2 - (d-c)^2 := by
  have ht (j : V) : (if i = j then 0 else f j-c)^2 =
      (f j)^2 - 2*c*f j + c^2 - (if j=i then (d-c)^2 else 0) := by
    by_cases hij : i=j
    · subst j
      simp only [ite_true, hd, zero_pow (by decide : 2 ≠ 0)]
      ring
    · simp only [hij, Ne.symm hij, ite_false, sub_zero]
      ring
  simp only [ht, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hr]
  simp

/-- Equation (5): the energy identity. -/
theorem incidence_excess_variance (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R)
    (hregular : ∀ p, degree F p=6) (hlen : F.length=11) :
    (∑ p, energy (coverWeights F) p) = 198 +
      ∑ i : Fin F.length, ∑ j : Fin F.length,
        (if i=j then 0 else ((incidence F).transpose * incidence F) i j - 6)^2 := by
  let M := incidence F
  let A : Matrix (Fin 22) (Fin 22) ℝ := M * M.transpose
  let B : Matrix (Fin F.length) (Fin F.length) ℝ := M.transpose * M
  have hMr (p : Fin 22) : ∑ i, M p i = 6 := by
    change (∑ i, incidence F p i) = 6
    rw [row_sum, hregular]
    norm_num
  have hMc (i : Fin F.length) : ∑ p, M p i = 12 := by
    change (∑ p, incidence F p i) = 12
    rw [column_sum F hrows]
    norm_num
  have hAd (p : Fin 22) : A p p = 6 := by
    change (incidence F * (incidence F).transpose) p p = 6
    rw [gram_entry, pair_diagonal, hregular]
    norm_num
  have hAr (p : Fin 22) : ∑ q, A p q = 72 := by
    simp only [A, Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hMc]
    rw [← Finset.sum_mul, hMr]
    norm_num
  have hBd (i : Fin F.length) : B i i = 12 := by
    change (∑ p, M p i * M p i) = 12
    have ht (p : Fin 22) : M p i * M p i = M p i := by
      dsimp [M, incidence]
      split_ifs <;> norm_num
    simp_rw [ht]
    exact hMc i
  have hBr (i : Fin F.length) : ∑ j, B i j = 72 := by
    simp only [B, Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hMr]
    rw [← Finset.sum_mul, hMc]
    norm_num
  have hAp (p : Fin 22) :
      (∑ q, (if p=q then 0 else A p q-3)^2) = (∑ q, (A p q)^2)-243 := by
    have h := centered_row (A p) p 6 72 3 (hAd p) (hAr p)
    norm_num only [Fintype.card_fin, Nat.cast_ofNat] at h
    (convert h using 1; ring)
  have hBp (i : Fin F.length) :
      (∑ j, (if i=j then 0 else B i j-6)^2) = (∑ j, (B i j)^2)-504 := by
    have h := centered_row (B i) i 12 72 6 (hBd i) (hBr i)
    norm_num only [Fintype.card_fin, hlen, Nat.cast_ofNat] at h
    (convert h using 1; ring)
  have hAs : (∑ p, ∑ q, (if p=q then 0 else A p q-3)^2) =
      (∑ p, ∑ q, (A p q)^2) - 5346 := by
    simp_rw [hAp]
    rw [Finset.sum_sub_distrib]
    simp
    ring
  have hBs : (∑ i, ∑ j, (if i=j then 0 else B i j-6)^2) =
      (∑ i, ∑ j, (B i j)^2) - 5544 := by
    simp_rw [hBp]
    rw [Finset.sum_sub_distrib]
    simp [hlen]
    ring
  have hg : (∑ p, ∑ q, (A p q)^2) = ∑ i, ∑ j, (B i j)^2 := gram_frobenius M
  have hv : (∑ p, ∑ q, (if p=q then 0 else A p q-3)^2) =
      198 + ∑ i, ∑ j, (if i=j then 0 else B i j-6)^2 := by
    rw [hAs, hBs, hg]
    ring
  simpa only [A, B, M, gram_entry, energy, coverWeights] using hv

/-- Equation (6): a sum of nonnegative defects vanishes. -/
theorem incidence_deficit_identity (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R)
    (hregular : ∀ p, degree F p = 6) (hlen : F.length = 11) :
    (∑ p, (9 - energy (coverWeights F) p)) +
      (∑ i : Fin F.length, ∑ j : Fin F.length,
        (if i = j then 0 else ((incidence F).transpose * incidence F) i j - 6)^2) = 0 := by
  have hv := incidence_excess_variance F hrows hregular hlen
  have hconst : (∑ _ : Fin 22, (9 : ℝ)) = 198 := by norm_num
  rw [Finset.sum_sub_distrib, hconst]
  linarith

lemma incidence_energy_ge (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R)
    (hregular : ∀ p, degree F p=6) (hlen : F.length=11) :
    198 ≤ ∑ p, energy (coverWeights F) p := by
  have hid := incidence_deficit_identity F hrows hregular hlen
  have hconst : (∑ _ : Fin 22, (9 : ℝ)) = 198 := by norm_num
  rw [Finset.sum_sub_distrib, hconst] at hid
  have hn : 0 ≤ ∑ i : Fin F.length, ∑ j : Fin F.length,
      (if i=j then 0 else ((incidence F).transpose * incidence F) i j - 6)^2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  linarith

lemma every_energy_nine_of_total (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W)
    (htotal : 198 ≤ ∑ i, energy W i) : ∀ i, energy W i=9 := by
  have hl := htotal
  have hu : (∑ i, energy W i)≤198 := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 22)))
      (f := energy W) (g := fun _ => (9:ℝ)) (fun i _ => energy_le_nine W h i)
    calc
      _ ≤ ∑ _ : Fin 22, (9:ℝ) := hh
      _ = 198 := by norm_num
  have hs : (∑ i, energy W i)=198 := by linarith
  have hz : (∑ i, (9-energy W i))=0 := by rw [Finset.sum_sub_distrib,hs]; norm_num
  have hh := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 22))) => sub_nonneg.mpr (energy_le_nine W h i))).mp hz
  intro i
  have hi := hh i (Finset.mem_univ i)
  linarith

lemma nonnegative_of_total (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W)
    (htotal : 198 ≤ ∑ i, energy W i) : ∀ i j, 0≤W i j := by
  intro i j
  by_contra hn
  have hn' : W i j<0 := lt_of_not_ge hn
  have h5 := negative_energy W h i j hn'
  have h9 := every_energy_nine_of_total W h htotal i
  linarith

lemma entry_zero_or_three_of_total (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W)
    (htotal : 198 ≤ ∑ i, energy W i) (i j : Fin 22) : W i j=0 ∨ W i j=3 := by
  have hn := nonnegative_of_total W h htotal i
  have hu (k : Fin 22) : W i k≤3 := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 22)))
      (f := W i) (fun j _ => hn j) (Finset.mem_univ k)
    simpa only [h.row_sum i] using hh
  have hterm (k : Fin 22) : 0≤3*W i k-(W i k)^2 := by
    have hk := hn k
    have hk' := hu k
    nlinarith
  have hz : (∑ k, (3*W i k-(W i k)^2))=0 := by
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,h.row_sum i]
    change 3*3-energy W i=0
    rw [every_energy_nine_of_total W h htotal i]
    norm_num
  have he := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin 22))) => hterm k)).mp hz j (Finset.mem_univ j)
  have hp : W i j*(W i j-3)=0 := by nlinarith
  rcases mul_eq_zero.mp hp with hh | hh
  · exact Or.inl hh
  · exact Or.inr (sub_eq_zero.mp hh)

lemma unique_three_of_total (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W)
    (htotal : 198 ≤ ∑ i, energy W i) (i : Fin 22) : ∃! j, W i j=3 := by
  have hn := nonnegative_of_total W h htotal i
  have hex : ∃ j, W i j=3 := by
    by_contra hh
    have hz : ∀ j, W i j=0 := by
      intro j
      exact (entry_zero_or_three_of_total W h htotal i j).resolve_right (fun hj => hh ⟨j,hj⟩)
    have hs := h.row_sum i
    simp only [hz,Finset.sum_const_zero] at hs
    norm_num at hs
  obtain ⟨j,hj⟩ := hex
  refine ⟨j,hj,?_⟩
  intro k hk
  by_contra hkj
  have hle : (∑ x ∈ ({j,k} : Finset (Fin 22)), W i x)≤∑ x, W i x := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ => hn x)
  simp only [Finset.sum_pair (Ne.symm hkj),hj,hk,h.row_sum i] at hle
  norm_num at hle

/-- Signed-data rigidity from the counting lower bound, with no rank premise. -/
theorem twin_partner_exists_unique_of_total (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W)
    (htotal : 198 ≤ ∑ i, energy W i) : ∀ i, ∃! j, j≠i ∧ W i j=3 := by
  intro i
  obtain ⟨j,hj,hu⟩ := unique_three_of_total W h htotal i
  have hji : j≠i := by intro hh; subst j; rw [h.diagonal] at hj; norm_num at hj
  exact ⟨j,⟨hji,hj⟩,fun k hk => hu k hk.2⟩

end Covering.Rigidity