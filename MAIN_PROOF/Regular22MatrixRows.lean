import MatrixFoundation

open Matrix Finset
open scoped BigOperators

namespace CoveringMatrixRegular22

/-- Exact signed row data supplied by physical regular22 incidence. -/
structure SignedData (W : Matrix (Fin 22) (Fin 22) ℝ) : Prop where
  symmetric : ∀ i j, W i j=W j i
  diagonal : ∀ i, W i i=0
  row_sum : ∀ i, ∑ j, W i j=3
  negative_row : ∀ i j, W i j<0 → W i j = -1 ∧
    ∀ k, k≠j → W i k=0 ∨ W i k=1

def energy (W : Matrix (Fin 22) (Fin 22) ℝ) (i : Fin 22) : ℝ :=
  ∑ j, (W i j)^2

def shift (W : Matrix (Fin 22) (Fin 22) ℝ) : Matrix (Fin 22) (Fin 22) ℝ :=
  fun i j => if i=j then 3 else W i j

lemma negative_energy (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W)
    (i j : Fin 22) (hj : W i j<0) : energy W i=5 := by
  obtain ⟨hj,hh⟩ := h.negative_row i j hj
  have he (k : Fin 22) : (W i k)^2=W i k+(if k=j then 2 else 0) := by
    by_cases hk : k=j
    · subst k; norm_num [hj]
    · rcases hh k hk with hk' | hk' <;> norm_num [hk,hk']
  unfold energy
  simp_rw [he]
  rw [Finset.sum_add_distrib,h.row_sum i]
  norm_num

lemma energy_le_nine (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W)
    (i : Fin 22) : energy W i≤9 := by
  by_cases hn : ∃ j, W i j<0
  · obtain ⟨j,hj⟩ := hn
    rw [negative_energy W h i j hj]
    norm_num
  · have hp : ∀ j, 0≤W i j := fun j => le_of_not_gt (fun hj => hn ⟨j,hj⟩)
    have hh := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := W i)
      (fun j _ => hp j)
    change (∑ j, (W i j)^2)≤9
    calc
      _ ≤ (∑ j, W i j)^2 := hh
      _ = 9 := by rw [h.row_sum i]; norm_num

lemma shift_symmetric (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W) :
    (shift W).IsHermitian := by
  show (shift W).conjTranspose=shift W
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial,shift]
  by_cases hij : i=j
  · subst j; rfl
  · simp only [hij,Ne.symm hij,if_false,h.symmetric j i]

lemma shift_trace (W : Matrix (Fin 22) (Fin 22) ℝ) : (shift W).trace=66 := by
  norm_num [Matrix.trace,Matrix.diag,shift]

lemma shift_trace_square (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W) :
    (shift W*shift W).trace=198+∑ i, energy W i := by
  have he (i j : Fin 22) : shift W i j*shift W j i=
      (if j=i then 9 else 0)+(W i j)^2 := by
    by_cases hij : i=j
    · subst j; norm_num [shift,h.diagonal]
    · simp only [shift,hij,Ne.symm hij,if_false,zero_add,h.symmetric j i,pow_two]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,he,Finset.sum_add_distrib]
  norm_num [energy]

lemma every_energy_nine (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W)
    (hrank : (shift W).rank≤11) : ∀ i, energy W i=9 := by
  have hl := MatrixFoundation.trace_square_ge_396 (shift W) (shift_symmetric W h)
    (shift_trace W) hrank
  rw [shift_trace_square W h] at hl
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

lemma nonnegative_of_rank (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W)
    (hrank : (shift W).rank≤11) : ∀ i j, 0≤W i j := by
  intro i j
  by_contra hn
  have hn' : W i j<0 := lt_of_not_ge hn
  have h5 := negative_energy W h i j hn'
  have h9 := every_energy_nine W h hrank i
  linarith

lemma entry_zero_or_three (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W)
    (hrank : (shift W).rank≤11) (i j : Fin 22) : W i j=0 ∨ W i j=3 := by
  have hn := nonnegative_of_rank W h hrank i
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
    rw [every_energy_nine W h hrank i]
    norm_num
  have he := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin 22))) => hterm k)).mp hz j (Finset.mem_univ j)
  have hp : W i j*(W i j-3)=0 := by nlinarith
  rcases mul_eq_zero.mp hp with hh | hh
  · exact Or.inl hh
  · exact Or.inr (sub_eq_zero.mp hh)

lemma unique_three (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W)
    (hrank : (shift W).rank≤11) (i : Fin 22) : ∃! j, W i j=3 := by
  have hn := nonnegative_of_rank W h hrank i
  have hex : ∃ j, W i j=3 := by
    by_contra hh
    have hz : ∀ j, W i j=0 := by
      intro j
      exact (entry_zero_or_three W h hrank i j).resolve_right (fun hj => hh ⟨j,hj⟩)
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

/-- Matrix-only rigidity, still requiring its physical signed-data and rank bridges. -/
theorem twin_partner_exists_unique (W : Matrix (Fin 22) (Fin 22) ℝ) (h : SignedData W)
    (hrank : (shift W).rank≤11) : ∀ i, ∃! j, j≠i ∧ W i j=3 := by
  intro i
  obtain ⟨j,hj,hu⟩ := unique_three W h hrank i
  have hji : j≠i := by intro hh; subst j; rw [h.diagonal] at hj; norm_num at hj
  exact ⟨j,⟨hji,hj⟩,fun k hk => hu k hk.2⟩

#print axioms twin_partner_exists_unique
#print axioms every_energy_nine

end CoveringMatrixRegular22
