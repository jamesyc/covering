import WeightedSignlessKernel
open Matrix Finset
open scoped BigOperators
namespace WeightedKernelComponents
open WeightedSignlessKernel
variable {V : Type*} [Fintype V] [DecidableEq V]

structure System (V : Type*) [Fintype V] where
  W : Matrix V V ℝ
  d : ℝ
  symmetric : ∀ i j, W i j = W j i
  nonnegative : ∀ i j, 0 ≤ W i j
  zero_diagonal : ∀ i, W i i = 0
  degree_le : ∀ i, rowSum W i ≤ d

namespace System
variable (S : System V)

def Q : Matrix V V ℝ := signless S.W S.d

def graph : SimpleGraph V where
  Adj i j := 0 < S.W i j
  symm := ⟨fun i j h => by simpa [S.symmetric j i] using h⟩
  loopless := ⟨fun i h => by simpa [S.zero_diagonal i] using h⟩

abbrev kernel : Submodule ℝ (V → ℝ) := S.Q.mulVecLin.ker

lemma kernel_iff (x : V → ℝ) : x ∈ S.kernel ↔
    (∀ i, rowSum S.W i < S.d → x i = 0) ∧
    (∀ i j, S.graph.Adj i j → x i = - x j) :=
  kernel_local_iff S.W S.d S.symmetric S.nonnegative S.degree_le x

lemma reachable_eq_or_neg {x : V → ℝ} (hx : x ∈ S.kernel) {i j : V}
    (hij : S.graph.Reachable i j) : x i = x j ∨ x i = - x j := by
  obtain ⟨w⟩ := hij
  have he := (S.kernel_iff x).mp hx |>.2
  induction w with
  | nil => exact Or.inl rfl
  | @cons a b c hab w ih =>
    have hab' := he a b hab
    rcases ih with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)

lemma reachable_zero_iff {x : V → ℝ} (hx : x ∈ S.kernel) {i j : V}
    (hij : S.graph.Reachable i j) : x i = 0 ↔ x j = 0 := by
  rcases S.reachable_eq_or_neg hx hij with h | h <;> constructor <;> intro hz <;> linarith

lemma regular_of_nonzero {x : V → ℝ} (hx : x ∈ S.kernel) {i : V}
    (hi : x i ≠ 0) : rowSum S.W i = S.d := by
  by_contra h
  exact hi ((S.kernel_iff x).mp hx |>.1 i (lt_of_le_of_ne (S.degree_le i) h))

lemma sum_kernel_eq_zero {x : V → ℝ} (hd : S.d ≠ 0) (hx : x ∈ S.kernel) :
    ∑ i, x i = 0 := by
  have he : ∀ i, rowSum S.W i * x i = S.d * x i := by
    intro i
    by_cases hi : x i = 0
    · simp [hi]
    · rw [S.regular_of_nonzero hx hi]
  have hz : (∑ i, (S.Q *ᵥ x) i) = 0 := by
    have hx' : S.Q *ᵥ x = 0 := hx
    rw [hx']; simp
  simp_rw [Q, signless_mulVec_apply, Finset.sum_add_distrib] at hz
  have hsum : (∑ i, ∑ j, S.W i j * x j) = S.d * ∑ j, x j := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    have hc : ∀ j, (∑ i, S.W i j) = rowSum S.W j := by
      intro j; simp_rw [S.symmetric _ j]; rfl
    simp_rw [hc, he]
    rw [Finset.mul_sum]
  rw [hsum, ← Finset.mul_sum] at hz
  have hh : S.d * (∑ i, x i) = 0 := by linarith
  exact (mul_eq_zero.mp hh).resolve_left hd

noncomputable def representative (c : S.graph.ConnectedComponent) : V :=
  Classical.choose (Quot.exists_rep c)

lemma representative_mem (c : S.graph.ConnectedComponent) :
    S.graph.connectedComponentMk (S.representative c) = c :=
  Classical.choose_spec (Quot.exists_rep c)

lemma representative_reachable (i : V) :
    S.graph.Reachable (S.representative (S.graph.connectedComponentMk i)) i := by
  apply SimpleGraph.ConnectedComponent.exact
  exact S.representative_mem _

def Active (c : S.graph.ConnectedComponent) : Prop :=
  ∃ x : S.kernel, x.val (S.representative c) ≠ 0

noncomputable def evaluateActive : S.kernel →ₗ[ℝ] ({c // S.Active c} → ℝ) where
  toFun x c := x.val (S.representative c.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma evaluateActive_injective : Function.Injective S.evaluateActive := by
  intro x y hxy
  apply Subtype.ext
  funext i
  let c := S.graph.connectedComponentMk i
  have hrep : x.val (S.representative c) = y.val (S.representative c) := by
    by_cases hc : S.Active c
    · exact congrFun hxy ⟨c, hc⟩
    · have hx : x.val (S.representative c) = 0 := by
        by_contra h; exact hc ⟨x, h⟩
      have hy : y.val (S.representative c) = 0 := by
        by_contra h; exact hc ⟨y, h⟩
      rw [hx, hy]
  have hz : ((x - y : S.kernel) : V → ℝ) (S.representative c) = 0 := by
    change x.val (S.representative c) - y.val (S.representative c) = 0
    exact sub_eq_zero.mpr hrep
  have hh := (S.reachable_zero_iff (x - y).property (S.representative_reachable i)).mp hz
  exact sub_eq_zero.mp hh

lemma nullity_le_active_components :
    Module.finrank ℝ S.kernel ≤ Nat.card {c // S.Active c} := by
  classical
  letI : Fintype {c // S.Active c} := Fintype.ofFinite _
  have h := LinearMap.finrank_le_finrank_of_injective S.evaluateActive_injective
  simpa [Module.finrank_pi, Nat.card_eq_fintype_card] using h

open scoped Classical in
lemma component_restrict_mem {x : V → ℝ} (hx : x ∈ S.kernel)
    (c : S.graph.ConnectedComponent) :
    (fun i => if S.graph.connectedComponentMk i = c then x i else 0) ∈ S.kernel := by
  classical
  rw [S.kernel_iff]
  constructor
  · intro i hi
    by_cases hc : S.graph.connectedComponentMk i = c
    · simp [hc, (S.kernel_iff x).mp hx |>.1 i hi]
    · simp [hc]
  · intro i j hij
    have hc : S.graph.connectedComponentMk i = S.graph.connectedComponentMk j :=
      SimpleGraph.ConnectedComponent.sound hij.reachable
    have he := (S.kernel_iff x).mp hx |>.2 i j hij
    by_cases hi : S.graph.connectedComponentMk i = c
    · have hj : S.graph.connectedComponentMk j = c := hc.symm.trans hi
      simpa [hi, hj] using he
    · have hj : S.graph.connectedComponentMk j ≠ c := fun h => hi (hc.trans h)
      simp [hi, hj]

end System
end WeightedKernelComponents
#print axioms WeightedKernelComponents.System.reachable_eq_or_neg
#print axioms WeightedKernelComponents.System.sum_kernel_eq_zero
#print axioms WeightedKernelComponents.System.nullity_le_active_components
#print axioms WeightedKernelComponents.System.component_restrict_mem
