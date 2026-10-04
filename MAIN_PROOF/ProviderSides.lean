module

public import SignedTraceBalance

@[expose] public section

open Matrix Finset
open scoped BigOperators
namespace Covering.NormalizedBridge20261003.ExceptionBranch
open TwinFrame PointDegree SideLift CrossGrid A19Physical CoveringOutsideTrace WeightedKernelComponents

structure ProviderSide (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (f : TwinFrame T) (e : Fin 22 ≃ Outside f.removed)
    (c : (lowSystem T hrows hcover).graph.ConnectedComponent) where
  A : Block 22
  B : Block 22
  nodup_A : A.Nodup
  nodup_B : B.Nodup
  disjoint : Covering.Disjoint A B
  twice_length : 2 * A.length = (lowSystem T hrows hcover).componentSize c
  kernel : (CoveringMatrixIncidence.incidence (traces e f.providers)).transpose *ᵥ signedVector A B = 0
  member_component : ∀ p, p ∈ A ++ B → ∃ r : LowPoint T,
    r.val = point e p ∧ (lowSystem T hrows hcover).graph.connectedComponentMk r = c
  pair_left : ∀ p, p ∈ A → ∀ q, q ∈ A → p ≠ q → pairDegree T (point e p) (point e q) = 6

lemma provider_side_of_component (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (E : ExceptionalComponents T hrows hcover) (f : TwinFrame T)
    (hf : ∀ r : LowPoint T, (lowSystem T hrows hcover).graph.connectedComponentMk r = E.c2 ↔
      r = f.q ∨ r = f.mate)
    (e : Fin 22 ≃ Outside f.removed)
    (c : (lowSystem T hrows hcover).graph.ConnectedComponent) (hc2 : c ≠ E.c2)
    (hc : (lowSystem T hrows hcover).BalancedBipartite c) :
    Nonempty (ProviderSide T hrows hcover f e c) := by
  classical
  let S := lowSystem T hrows hcover
  obtain ⟨A, B, _, _, hdis, hcard, hcomp, hbal, hedge⟩ :=
    component_slot_balance_with_edges T hrows hcover c hc
  have hAc : ∀ r ∈ A, S.graph.connectedComponentMk r = c :=
    fun r hr => (hcomp r).mpr (Or.inl hr)
  have hBc : ∀ r ∈ B, S.graph.connectedComponentMk r = c :=
    fun r hr => (hcomp r).mpr (Or.inr hr)
  have hUA := part_disjoint_removed hrows hcover E f hf c hc2 A hAc
  have hUB := part_disjoint_removed hrows hcover E f hf c hc2 B hBc
  have hsupp : S.componentVertices c = A ∪ B := by
    ext r
    simpa [System.componentVertices, S] using hcomp r
  refine ⟨⟨trace e (partBlock A), trace e (partBlock B), trace_nodup _ _, trace_nodup _ _,
    ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro p hpA hpB
    obtain ⟨r, hr, hrx⟩ := (mem_partBlock A _).mp ((mem_trace e _ p).mp hpA)
    obtain ⟨s, hs, hsx⟩ := (mem_partBlock B _).mp ((mem_trace e _ p).mp hpB)
    have he : r = s := Subtype.ext (hrx.trans hsx.symm)
    exact Finset.disjoint_left.mp hdis hr (he.symm ▸ hs)
  · change 2 * (trace e (partBlock A)).length = (S.componentVertices c).card
    rw [trace_length_disjoint e f.removed_valid.1 _ (partBlock_nodup A) hUA,
      partBlock_length, hsupp, Finset.card_union_of_disjoint hdis, ← hcard]
    omega
  · apply trace_signed_kernel e f.removed_valid.1 f.providers (partBlock A) (partBlock B)
      (partBlock_nodup A) (partBlock_nodup B) hUA hUB
    intro R hR
    exact parts_balance_rows A B hbal R (List.mem_filter.mp hR).1
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨r, hr, hrx⟩ := (mem_partBlock A _).mp ((mem_trace e _ p).mp hp)
      exact ⟨r, hrx, hAc r hr⟩
    · obtain ⟨r, hr, hrx⟩ := (mem_partBlock B _).mp ((mem_trace e _ p).mp hp)
      exact ⟨r, hrx, hBc r hr⟩
  · intro p hp q hq hpq
    obtain ⟨r, hr, hrx⟩ := (mem_partBlock A _).mp ((mem_trace e _ p).mp hp)
    obtain ⟨s, hs, hsy⟩ := (mem_partBlock A _).mp ((mem_trace e _ q).mp hq)
    have hrs : r ≠ s := by
      intro he
      exact hpq ((point_injective e) (hrx.symm.trans ((congrArg Subtype.val he).trans hsy)))
    have hz : fullExcess T r.val s.val = 0 := by
      by_contra hn
      have hadj : S.graph.Adj r s :=
        lt_of_le_of_ne (fullExcess_nonnegative T hrows hcover r.val s.val) (Ne.symm hn)
      rcases hedge r s (hAc r hr) hadj with h | h
      · exact Finset.disjoint_left.mp hdis hs h.2
      · exact Finset.disjoint_left.mp hdis hr h.1
    rw [← hrx, ← hsy]
    exact zero_excess_codegree_six T r.val s.val (fun h => hrs (Subtype.ext h)) hz

lemma provider_sides_disjoint {T : Family 24}
    {hrows : ∀ R, R ∈ T → ValidBlock 14 R} {hcover : IsCovering 4 T}
    {f : TwinFrame T} {e : Fin 22 ≃ Outside f.removed}
    {c d : (lowSystem T hrows hcover).graph.ConnectedComponent} (hcd : c ≠ d)
    (C : ProviderSide T hrows hcover f e c) (D : ProviderSide T hrows hcover f e d) :
    Covering.Disjoint (C.A ++ C.B) (D.A ++ D.B) := by
  intro p hp hq
  obtain ⟨r, hr, hrc⟩ := C.member_component p hp
  obtain ⟨s, hs, hsd⟩ := D.member_component p hq
  have h : r = s := Subtype.ext (hr.trans hs.symm)
  subst s
  exact hcd (hrc.symm.trans hsd)

lemma provider_side_degree {T : Family 24}
    {hrows : ∀ R, R ∈ T → ValidBlock 14 R} {hcover : IsCovering 4 T}
    {f : TwinFrame T} {e : Fin 22 ≃ Outside f.removed}
    {c : (lowSystem T hrows hcover).graph.ConnectedComponent}
    (C : ProviderSide T hrows hcover f e c) (p : Fin 22) (hp : p ∈ C.A ++ C.B) :
    degree T (point e p) = 11 := by
  obtain ⟨r, hr, _⟩ := C.member_component p hp
  rw [← hr]
  exact r.property

lemma provider_sides_cross_pair {T : Family 24}
    {hrows : ∀ R, R ∈ T → ValidBlock 14 R} {hcover : IsCovering 4 T}
    {f : TwinFrame T} {e : Fin 22 ≃ Outside f.removed}
    {c d : (lowSystem T hrows hcover).graph.ConnectedComponent} (hcd : c ≠ d)
    (C : ProviderSide T hrows hcover f e c) (D : ProviderSide T hrows hcover f e d)
    (p : Fin 22) (hp : p ∈ C.A ++ C.B) (q : Fin 22) (hq : q ∈ D.A ++ D.B) :
    pairDegree T (point e p) (point e q) = 6 := by
  obtain ⟨r, hr, hrc⟩ := C.member_component p hp
  obtain ⟨s, hs, hsd⟩ := D.member_component q hq
  have hrs : r ≠ s := by intro h; subst s; exact hcd (hrc.symm.trans hsd)
  have hnot : (lowSystem T hrows hcover).graph.connectedComponentMk s ≠ c := by
    rw [hsd]; exact Ne.symm hcd
  have hz := (lowSystem T hrows hcover).component_closed c hrc hnot
  rw [← hr, ← hs]
  exact zero_excess_codegree_six T r.val s.val (fun h => hrs (Subtype.ext h)) hz

end Covering.NormalizedBridge20261003.ExceptionBranch
#print axioms Covering.NormalizedBridge20261003.ExceptionBranch.provider_side_of_component
#print axioms Covering.NormalizedBridge20261003.ExceptionBranch.provider_sides_cross_pair
