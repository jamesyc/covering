module

public import WeightedKernelBalanced

@[expose] public section

open Matrix Finset
open scoped BigOperators
namespace WeightedKernelComponents.System
open WeightedSignlessKernel
variable {V : Type*} [Fintype V] [DecidableEq V] (S : System V)

lemma zero_on_deficient_component {x : V → ℝ} (hx : x ∈ S.kernel) {i j : V}
    (hi : rowSum S.W i < S.d) (hij : S.graph.Reachable i j) : x j = 0 :=
  (S.reachable_zero_iff hx hij).mp ((S.kernel_iff x).mp hx |>.1 i hi)

lemma zero_on_inactive_component (c : S.graph.ConnectedComponent) (hc : ¬ S.Active c)
    {x : V → ℝ} (hx : x ∈ S.kernel) {i : V}
    (hi : S.graph.connectedComponentMk i = c) : x i = 0 := by
  have hr : x (S.representative c) = 0 := by
    by_contra h; exact hc ⟨⟨x, hx⟩, h⟩
  have hreach : S.graph.Reachable (S.representative c) i :=
    SimpleGraph.ConnectedComponent.exact ((S.representative_mem c).trans hi.symm)
  exact (S.reachable_zero_iff hx hreach).mp hr

lemma alternating_constant_on_component (c : S.graph.ConnectedComponent)
    {z x : V → ℝ} (hz : z ∈ S.kernel) (hx : x ∈ S.kernel)
    (hrep : z (S.representative c) = 1) {i : V}
    (hi : S.graph.connectedComponentMk i = c) :
    x i = x (S.representative c) * z i := by
  let y : V → ℝ := x - x (S.representative c) • z
  have hy : y ∈ S.kernel := S.kernel.sub_mem hx (S.kernel.smul_mem _ hz)
  have hzero : y (S.representative c) = 0 := by simp [y, hrep]
  have hreach : S.graph.Reachable (S.representative c) i :=
    SimpleGraph.ConnectedComponent.exact ((S.representative_mem c).trans hi.symm)
  have hyi := (S.reachable_zero_iff hy hreach).mp hzero
  exact sub_eq_zero.mp hyi

lemma evaluateActive_surjective : Function.Surjective S.evaluateActive := by
  classical
  letI : Fintype {c // S.Active c} := Fintype.ofFinite _
  choose z hz hin hout hrep using
    (fun c : {c // S.Active c} => S.active_normalized_vector c.val c.property)
  let Z : {c // S.Active c} → S.kernel := fun c => ⟨z c, hz c⟩
  have heval : ∀ a b : {c // S.Active c}, S.evaluateActive (Z a) b = if a = b then 1 else 0 := by
    intro a b
    by_cases h : a = b
    · subst b
      exact (hrep a).trans (by simp)
    · have hv : b.val ≠ a.val := by
        intro hh; exact h (Subtype.ext hh.symm)
      have hn : S.graph.connectedComponentMk (S.representative b.val) ≠ a.val := by
        rw [S.representative_mem]; exact hv
      change z a (S.representative b.val) = _
      rw [hout a _ hn]
      simp [h]
  intro f
  refine ⟨∑ a, f a • Z a, ?_⟩
  rw [map_sum]
  ext b
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, heval]
  simp

lemma nullity_eq_active_components :
    Module.finrank ℝ S.kernel = Nat.card {c // S.Active c} := by
  classical
  letI : Fintype {c // S.Active c} := Fintype.ofFinite _
  apply Nat.le_antisymm S.nullity_le_active_components
  have h := LinearMap.finrank_le_finrank_of_surjective S.evaluateActive_surjective
  simpa [Module.finrank_pi, Nat.card_eq_fintype_card] using h

end WeightedKernelComponents.System
#print axioms WeightedKernelComponents.System.zero_on_deficient_component
#print axioms WeightedKernelComponents.System.alternating_constant_on_component
#print axioms WeightedKernelComponents.System.evaluateActive_surjective
#print axioms WeightedKernelComponents.System.nullity_eq_active_components
