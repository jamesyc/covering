module

public import BalancedSidesObstruction

@[expose] public section

open Matrix Finset
open scoped BigOperators
namespace Covering.NormalizedBridge20261003.ExceptionBranch
open TwinFrame PointDegree SideLift CrossGrid A19Physical CoveringOutsideTrace WeightedKernelComponents

lemma traced_degree_partition {T : Family 24} (f : TwinFrame T)
    (e : Fin 22 ≃ Outside f.removed) (p : Fin 22) :
    degree (traces e f.providers) p + degree (traces e f.remainder) p = degree T (point e p) := by
  rw [degree_traces, degree_traces]
  exact filter_degree_partition T f.q.val (point e p)

lemma traced_pair_partition {T : Family 24} (f : TwinFrame T)
    (e : Fin 22 ≃ Outside f.removed) (p q : Fin 22) :
    pairDegree (traces e f.providers) p q + pairDegree (traces e f.remainder) p q =
      pairDegree T (point e p) (point e q) := by
  rw [pair_degree_traces, pair_degree_traces]
  exact filter_pair_partition T f.q.val (point e p) (point e q)

lemma exception_impossible (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T) (hlen : T.length = 19)
    (E : ExceptionalComponents T hrows hcover) : False := by
  classical
  let S := lowSystem T hrows hcover
  obtain ⟨f, hf⟩ := twin_frame_of_exception T hrows hcover E
  let e : Fin 22 ≃ Outside f.removed := coordinates f.removed f.removed_valid (by decide)
  let F := traces e f.providers
  let R := traces e f.remainder
  have hc : S.BalancedBipartite E.c6 := by
    apply (S.mem_goodComponents _).mp
    rw [E.all_components]
    simp
  have hd : S.BalancedBipartite E.cLarge := by
    apply (S.mem_goodComponents _).mp
    rw [E.all_components]
    simp
  obtain ⟨C⟩ := provider_side_of_component T hrows hcover E f hf e E.c6
    (Ne.symm E.distinct.1) hc
  obtain ⟨D⟩ := provider_side_of_component T hrows hcover E f hf e E.cLarge
    (Ne.symm E.distinct.2.1) hd
  have hC3 : C.A.length = 3 := by
    have h := C.twice_length
    rw [E.size_six] at h
    omega
  have hD3 : 3 ≤ D.A.length := by
    have h := D.twice_length
    rcases E.size_large with hsz | hsz <;> rw [hsz] at h <;> omega
  have hcross := provider_sides_disjoint E.distinct.2.2 C D
  have hlow : ∀ p, p ∈ C.A ++ D.A → degree T (point e p) = 11 := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact provider_side_degree C p (List.mem_append.mpr (Or.inl hp))
    · exact provider_side_degree D p (List.mem_append.mpr (Or.inl hp))
  have hfullPair : ∀ p, p ∈ C.A ++ D.A → ∀ q, q ∈ C.A ++ D.A → p ≠ q →
      pairDegree T (point e p) (point e q) = 6 := by
    intro p hp q hq hpq
    rcases List.mem_append.mp hp with hp | hp <;> rcases List.mem_append.mp hq with hq | hq
    · exact C.pair_left p hp q hq hpq
    · exact provider_sides_cross_pair E.distinct.2.2 C D p
        (List.mem_append.mpr (Or.inl hp)) q (List.mem_append.mpr (Or.inl hq))
    · exact provider_sides_cross_pair (Ne.symm E.distinct.2.2) D C p
        (List.mem_append.mpr (Or.inl hp)) q (List.mem_append.mpr (Or.inl hq))
    · exact D.pair_left p hp q hq hpq
  obtain ⟨high, high', hhh', hhigh, hhigh', hrest⟩ := E.high_points
  have high_out : high ∉ f.removed := by
    have hq := f.q.property
    have hm := f.mate.property
    simp only [removed, List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · intro h
      rw [← h] at hq
      omega
    · intro h
      rw [← h] at hm
      omega
  let oldHigh : Fin 22 := e.symm ⟨high, by simpa using high_out⟩
  have hpoint : point e oldHigh = high := by simp [oldHigh, point]
  have hnot : oldHigh ∉ (C.A ++ C.B) ++ (D.A ++ D.B) := by
    intro hp
    rcases List.mem_append.mp hp with hp | hp
    · have h := provider_side_degree C oldHigh hp
      rw [hpoint] at h
      omega
    · have h := provider_side_degree D oldHigh hp
      rw [hpoint] at h
      omega
  have high_pair (c : S.graph.ConnectedComponent) (hc : S.BalancedBipartite c)
      (L : ProviderSide T hrows hcover f e c) (p : Fin 22) (hp : p ∈ L.A ++ L.B) :
      pairDegree T (point e p) high = 6 := by
    obtain ⟨r, hr, hrc⟩ := L.member_component p hp
    have hgood : r ∈ S.goodVertices := by
      apply (S.mem_goodVertices r).mpr
      rw [hrc]
      exact hc
    have hne : r.val ≠ high := by
      intro he
      have hd := r.property
      rw [he] at hd
      omega
    have hz := good_to_high_zero T hrows hcover r hgood high (by omega)
    rw [← hr]
    exact zero_excess_codegree_six T r.val high hne hz
  have hfullHigh : ∀ p, p ∈ C.A ++ D.A → pairDegree T (point e p) (point e oldHigh) = 6 := by
    intro p hp
    rw [hpoint]
    rcases List.mem_append.mp hp with hp | hp
    · exact high_pair E.c6 hc C p (List.mem_append.mpr (Or.inl hp))
    · exact high_pair E.cLarge hd D p (List.mem_append.mpr (Or.inl hp))
  have hRlen : R.length = 8 := by
    rw [show R = traces e f.remainder from rfl, traces_length]
    exact f.remainder_length hlen
  have hRdegree : ∀ p, p ∈ C.A ++ D.A → degree R p = 5 := by
    intro p hp
    have h := traced_degree_partition f e p
    have hF := f.provider_trace_regular e p
    have hT := hlow p hp
    change degree F p + degree R p = degree T (point e p) at h
    change degree F p = 6 at hF
    omega
  have hRhigh : degree R oldHigh = 6 := by
    have h := traced_degree_partition f e oldHigh
    have hF := f.provider_trace_regular e oldHigh
    rw [hpoint] at h
    change degree F oldHigh + degree R oldHigh = degree T high at h
    change degree F oldHigh = 6 at hF
    omega
  obtain ⟨σ, hne, hinv, hpair, htwin, hanti⟩ := f.provider_twins hrows hcover e
  apply balanced_sides_obstruction F R hRlen σ hpair hanti C.A C.B D.A D.B C.nodup_A D.nodup_A
    (by omega) hD3 C.disjoint D.disjoint hcross C.kernel D.kernel oldHigh hRhigh hnot hRdegree
  · intro p hp q hq hpq
    exact (traced_pair_partition f e p q).trans (hfullPair p hp q hq hpq)
  · intro p hp
    exact (traced_pair_partition f e p oldHigh).trans (hfullHigh p hp)

lemma physical_has_gadget (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T) (hlen : T.length = 19) :
    HasGadget T := by
  rcases gadget_or_exceptional_components T hrows hcover hlen with h | h
  · exact h
  · obtain ⟨E⟩ := h
    exact (exception_impossible T hrows hcover hlen E).elim

end Covering.NormalizedBridge20261003.ExceptionBranch
#print axioms Covering.NormalizedBridge20261003.ExceptionBranch.exception_impossible

#print axioms Covering.NormalizedBridge20261003.ExceptionBranch.physical_has_gadget
