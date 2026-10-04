import MatrixFoundation
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
open Matrix Finset
open scoped BigOperators
namespace WeightedSignlessKernel
variable {V : Type*} [Fintype V] [DecidableEq V]

def rowSum (W : Matrix V V ℝ) (i : V) : ℝ := ∑ j, W i j
def signless (W : Matrix V V ℝ) (d : ℝ) : Matrix V V ℝ := d • (1 : Matrix V V ℝ) + W

lemma signless_mulVec_apply (W : Matrix V V ℝ) (d : ℝ) (x : V → ℝ) (i : V) :
    (signless W d *ᵥ x) i = d * x i + ∑ j, W i j * x j := by
  rw [signless, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

lemma symmetric_square_sum (W : Matrix V V ℝ) (hW : ∀ i j, W i j = W j i) (x : V → ℝ) :
    (∑ i, ∑ j, W i j * x j ^ 2) = ∑ i, ∑ j, W i j * x i ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hW j i]

lemma energy_identity (W : Matrix V V ℝ) (hW : ∀ i j, W i j = W j i)
    (d : ℝ) (x : V → ℝ) :
    (∑ i, x i * (signless W d *ᵥ x) i) =
      (∑ i, (d - rowSum W i) * x i ^ 2) +
      (∑ i, ∑ j, W i j * (x i + x j) ^ 2) / 2 := by
  have hs := symmetric_square_sum W hW x
  simp_rw [signless_mulVec_apply, rowSum, add_sq, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul]
  simp_rw [show ∀ i j, W i j * (2 * x i * x j) = 2 * (x i * (W i j * x j)) by
    intro i j; ring, ← Finset.mul_sum]
  have h1 : (∑ i, x i * (d * x i)) = ∑ i, d * x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h1, hs, ← Finset.mul_sum]
  ring

lemma kernel_local_iff (W : Matrix V V ℝ) (d : ℝ)
    (hW : ∀ i j, W i j = W j i) (hn : ∀ i j, 0 ≤ W i j)
    (hd : ∀ i, rowSum W i ≤ d) (x : V → ℝ) :
    signless W d *ᵥ x = 0 ↔
      (∀ i, rowSum W i < d → x i = 0) ∧
      (∀ i j, 0 < W i j → x i = - x j) := by
  constructor
  · intro hx
    have he := energy_identity W hW d x
    rw [hx] at he
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at he
    have ha : ∀ i, 0 ≤ (d - rowSum W i) * x i ^ 2 :=
      fun i => mul_nonneg (sub_nonneg.mpr (hd i)) (sq_nonneg _)
    have hb : ∀ i j, 0 ≤ W i j * (x i + x j) ^ 2 :=
      fun i j => mul_nonneg (hn i j) (sq_nonneg _)
    have hsa := Finset.sum_nonneg (fun i (_ : i ∈ (univ : Finset V)) => ha i)
    have hsb := Finset.sum_nonneg (fun i (_ : i ∈ (univ : Finset V)) =>
      Finset.sum_nonneg (fun j (_ : j ∈ (univ : Finset V)) => hb i j))
    have za : (∑ i, (d - rowSum W i) * x i ^ 2) = 0 := by linarith
    have zb : (∑ i, ∑ j, W i j * (x i + x j) ^ 2) = 0 := by linarith
    have za' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).mp za
    have zb' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => hb i j))).mp zb
    constructor
    · intro i hi
      have hz := za' i (mem_univ i)
      have : x i ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (sub_pos.mpr hi))
      exact sq_eq_zero_iff.mp this
    · intro i j hij
      have zi := zb' i (mem_univ i)
      have zij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hb i j)).mp zi j (mem_univ j)
      have hz : (x i + x j) ^ 2 = 0 := (mul_eq_zero.mp zij).resolve_left (ne_of_gt hij)
      have hz' : x i + x j = 0 := sq_eq_zero_iff.mp hz
      linarith
  · rintro ⟨hdef, hedge⟩
    ext i
    rw [signless_mulVec_apply]
    have hs : (∑ j, W i j * x j) = - rowSum W i * x i := by
      calc
        (∑ j, W i j * x j) = ∑ j, W i j * (- x i) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases h : W i j = 0
          · simp [h]
          · have hp := lt_of_le_of_ne (hn i j) (Ne.symm h)
            have he := hedge i j hp
            rw [show x j = - x i by linarith]
        _ = - rowSum W i * x i := by rw [← Finset.sum_mul]; simp [rowSum]
    rw [hs]
    by_cases h : rowSum W i = d
    · simp [h]
    · rw [hdef i (lt_of_le_of_ne (hd i) h)]
      simp
end WeightedSignlessKernel
#print axioms WeightedSignlessKernel.energy_identity
#print axioms WeightedSignlessKernel.kernel_local_iff
