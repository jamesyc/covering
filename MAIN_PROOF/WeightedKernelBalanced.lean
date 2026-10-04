import WeightedKernelComponents
open Matrix Finset
open scoped BigOperators
namespace WeightedKernelComponents.System
open WeightedSignlessKernel
variable {V : Type*} [Fintype V] [DecidableEq V] (S : System V)

lemma component_closed (c : S.graph.ConnectedComponent) {i j : V}
    (hi : S.graph.connectedComponentMk i = c) (hj : S.graph.connectedComponentMk j ≠ c) :
    S.W i j = 0 := by
  by_contra h
  have hp : S.graph.Adj i j := lt_of_le_of_ne (S.nonnegative i j) (Ne.symm h)
  exact hj ((SimpleGraph.ConnectedComponent.sound hp.reachable).symm.trans hi)

lemma active_normalized_vector (c : S.graph.ConnectedComponent) (hc : S.Active c) :
    ∃ z : V → ℝ, z ∈ S.kernel ∧
      (∀ i, S.graph.connectedComponentMk i = c → z i = 1 ∨ z i = -1) ∧
      (∀ i, S.graph.connectedComponentMk i ≠ c → z i = 0) ∧
      z (S.representative c) = 1 := by
  classical
  obtain ⟨x, hx⟩ := hc
  let a : ℝ := x.val (S.representative c)
  let y : V → ℝ := fun i => if S.graph.connectedComponentMk i = c then x.val i else 0
  have hy : y ∈ S.kernel := S.component_restrict_mem x.property c
  let z : V → ℝ := a⁻¹ • y
  have hz : z ∈ S.kernel := S.kernel.smul_mem _ hy
  refine ⟨z, hz, ?_, ?_, ?_⟩
  · intro i hi
    have hr : S.graph.Reachable i (S.representative c) :=
      SimpleGraph.ConnectedComponent.exact (hi.trans (S.representative_mem c).symm)
    rcases S.reachable_eq_or_neg x.property hr with hp | hm
    · left; simp [z, y, hi, hp, a, hx]
    · right; simp [z, y, hi, hm, a, hx]
  · intro i hi
    simp [z, y, hi]
  · simp [z, y, S.representative_mem c, a, hx]

def BalancedBipartite (c : S.graph.ConnectedComponent) : Prop :=
  ∃ s t : Finset V,
    s.Nonempty ∧ t.Nonempty ∧ Disjoint s t ∧ s.card = t.card ∧
    (∀ i, S.graph.connectedComponentMk i = c ↔ i ∈ s ∨ i ∈ t) ∧
    (∀ i, S.graph.connectedComponentMk i = c → rowSum S.W i = S.d) ∧
    (∀ i j, S.graph.connectedComponentMk i = c → S.graph.Adj i j →
      (i ∈ s ∧ j ∈ t) ∨ (i ∈ t ∧ j ∈ s)) ∧
    (∀ i j, S.graph.connectedComponentMk i = c → S.graph.connectedComponentMk j ≠ c →
      S.W i j = 0)

lemma active_balanced_bipartite (hd : S.d ≠ 0) (c : S.graph.ConnectedComponent)
    (hc : S.Active c) : S.BalancedBipartite c := by
  classical
  obtain ⟨z, hz, hin, hout, hrep⟩ := S.active_normalized_vector c hc
  let s := univ.filter (fun i => z i = 1)
  let t := univ.filter (fun i => z i = -1)
  have hs : ∀ i, i ∈ s ↔ z i = 1 := by intro i; simp [s]
  have ht : ∀ i, i ∈ t ↔ z i = -1 := by intro i; simp [t]
  have hcomp : ∀ i, S.graph.connectedComponentMk i = c ↔ i ∈ s ∨ i ∈ t := by
    intro i
    constructor
    · intro hi; simpa [hs, ht] using hin i hi
    · intro hi
      by_contra hn
      have hzero := hout i hn
      rcases hi with hi | hi
      · have hh := (hs i).mp hi; linarith
      · have hh := (ht i).mp hi; linarith
  have hvalues : ∀ i, z i = 0 ∨ z i = 1 ∨ z i = -1 := by
    intro i
    by_cases hi : S.graph.connectedComponentMk i = c
    · exact Or.inr (hin i hi)
    · exact Or.inl (hout i hi)
  have hsum : (∑ i, z i) = (s.card : ℝ) - (t.card : ℝ) := by
    have hv : ∀ i, z i = (if z i = 1 then (1 : ℝ) else 0) -
        (if z i = -1 then (1 : ℝ) else 0) := by
      intro i
      rcases hvalues i with h | h | h <;> norm_num [h]
    calc
      (∑ i, z i) = ∑ i, ((if z i = 1 then (1 : ℝ) else 0) -
          (if z i = -1 then (1 : ℝ) else 0)) := Finset.sum_congr rfl (fun i _ => hv i)
      _ = (s.card : ℝ) - (t.card : ℝ) := by rw [Finset.sum_sub_distrib]; simp [s, t]
  have hcard : s.card = t.card := by
    have hh := S.sum_kernel_eq_zero hd hz
    rw [hsum] at hh
    exact_mod_cast sub_eq_zero.mp hh
  have hsnonempty : s.Nonempty := ⟨S.representative c, (hs _).mpr hrep⟩
  refine ⟨s, t, hsnonempty, ?_, ?_, hcard, hcomp, ?_, ?_, ?_⟩
  · apply Finset.card_pos.mp
    rw [← hcard]
    exact Finset.card_pos.mpr hsnonempty
  · apply Finset.disjoint_left.mpr
    intro i hi hi'
    have h1 := (hs i).mp hi
    have h2 := (ht i).mp hi'
    linarith
  · intro i hi
    apply S.regular_of_nonzero hz
    rcases hin i hi with h | h <;> rw [h] <;> norm_num
  · intro i j hi hij
    have hj : S.graph.connectedComponentMk j = c :=
      (SimpleGraph.ConnectedComponent.sound hij.reachable).symm.trans hi
    have he := (S.kernel_iff z).mp hz |>.2 i j hij
    rcases hin i hi with h1 | h1
    · left
      exact ⟨(hs i).mpr h1, (ht j).mpr (by linarith)⟩
    · right
      exact ⟨(ht i).mpr h1, (hs j).mpr (by linarith)⟩
  · exact fun i j hi hj => S.component_closed c hi hj

lemma nullity_le_balanced_bipartite_components (hd : S.d ≠ 0) :
    Module.finrank ℝ S.kernel ≤ Nat.card {c // S.BalancedBipartite c} := by
  classical
  let f : {c // S.Active c} → {c // S.BalancedBipartite c} :=
    fun c => ⟨c.val, S.active_balanced_bipartite hd c.val c.property⟩
  have hf : Function.Injective f := by
    intro c c' h
    apply Subtype.ext
    exact congrArg (fun z : {c // S.BalancedBipartite c} => z.val) h
  exact S.nullity_le_active_components.trans (Nat.card_le_card_of_injective f hf)

end WeightedKernelComponents.System
#print axioms WeightedKernelComponents.System.active_normalized_vector
#print axioms WeightedKernelComponents.System.active_balanced_bipartite
#print axioms WeightedKernelComponents.System.nullity_le_balanced_bipartite_components
