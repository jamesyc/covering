module

public import A19ComponentDichotomy
public import PhysicalOutsideTrace
public import Regular22TwinBalance

@[expose] public section

open Matrix Finset
open scoped BigOperators
namespace Covering.NormalizedBridge20261003.ExceptionBranch
open PointDegree SideLift CrossGrid A19Physical CoveringOutsideTrace

structure TwinFrame (T : Family 24) where
  q : LowPoint T
  mate : LowPoint T
  distinct : q ≠ mate
  rows : ∀ R, R ∈ T → (q.val ∈ R ↔ mate.val ∈ R)
  outside : ∀ x : Fin 24, x ≠ q.val → x ≠ mate.val → pairDegree T q.val x = 6

namespace TwinFrame

def removed {T : Family 24} (f : TwinFrame T) : Block 24 := [f.q.val, f.mate.val]
def providers {T : Family 24} (f : TwinFrame T) : Family 24 := T.filter (fun R => f.q.val ∈ R)
def remainder {T : Family 24} (f : TwinFrame T) : Family 24 := T.filter (fun R => f.q.val ∉ R)

lemma removed_valid {T : Family 24} (f : TwinFrame T) : ValidBlock 2 f.removed := by
  have h : f.q.val ≠ f.mate.val := fun he => f.distinct (Subtype.ext he)
  simp [removed, ValidBlock, h]

lemma providers_length {T : Family 24} (f : TwinFrame T) : f.providers.length = 11 :=
  f.q.property

lemma filter_degree_partition {n : ℕ} (T : Family n) (p x : Fin n) :
    degree (T.filter (fun R => p ∈ R)) x + degree (T.filter (fun R => p ∉ R)) x = degree T x := by
  induction T with
  | nil => simp [degree]
  | cons R T ih =>
    by_cases hp : p ∈ R <;> by_cases hx : x ∈ R <;> simp_all [degree] <;> omega

lemma filter_pair_partition {n : ℕ} (T : Family n) (p x y : Fin n) :
    pairDegree (T.filter (fun R => p ∈ R)) x y +
      pairDegree (T.filter (fun R => p ∉ R)) x y = pairDegree T x y := by
  induction T with
  | nil => simp [pairDegree]
  | cons R T ih =>
    by_cases hp : p ∈ R <;> by_cases hx : x ∈ R <;> by_cases hy : y ∈ R <;>
      simp_all [pairDegree] <;> omega

lemma filter_length_partition {n : ℕ} (T : Family n) (p : Fin n) :
    (T.filter (fun R => p ∈ R)).length + (T.filter (fun R => p ∉ R)).length = T.length := by
  induction T with
  | nil => simp
  | cons R T ih => by_cases hp : p ∈ R <;> simp_all <;> omega

lemma remainder_length {T : Family 24} (f : TwinFrame T) (hlen : T.length = 19) :
    f.remainder.length = 8 := by
  have h := filter_length_partition T f.q.val
  have hp := f.providers_length
  change f.providers.length + f.remainder.length = T.length at h
  omega

lemma provider_contains_removed {T : Family 24} (f : TwinFrame T)
    (R : Block 24) (hR : R ∈ f.providers) : Covering.Subset f.removed R := by
  have hm := List.mem_filter.mp hR
  have hq : f.q.val ∈ R := by simpa using hm.2
  have hmate := (f.rows R hm.1).mp hq
  intro x hx
  simp only [removed, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> assumption

lemma remainder_avoids_removed {T : Family 24} (f : TwinFrame T)
    (R : Block 24) (hR : R ∈ f.remainder) : Covering.Disjoint f.removed R := by
  have hm := List.mem_filter.mp hR
  have hq : f.q.val ∉ R := by simpa using hm.2
  have hmate : f.mate.val ∉ R := fun h => hq ((f.rows R hm.1).mpr h)
  intro x hx hxR
  simp only [removed, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact hq hxR
  · exact hmate hxR

lemma removed_hits_providers {T : Family 24} (f : TwinFrame T) (R : Block 24)
    (hR : R ∈ f.providers) : (hits f.removed R).length = 2 := by
  have h := f.provider_contains_removed R hR
  have hq := h f.q.val (by simp [removed])
  have hm := h f.mate.val (by simp [removed])
  simp [hits, removed, hq, hm]

lemma removed_hits_remainder {T : Family 24} (f : TwinFrame T) (R : Block 24)
    (hR : R ∈ f.remainder) : (hits f.removed R).length = 0 := by
  have h := f.remainder_avoids_removed R hR
  have hq : f.q.val ∉ R := h f.q.val (by simp [removed])
  have hm : f.mate.val ∉ R := h f.mate.val (by simp [removed])
  simp [hits, removed, hq, hm]

lemma provider_trace_valid {T : Family 24} (f : TwinFrame T)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (e : Fin 22 ≃ Outside f.removed) :
    ∀ R, R ∈ traces e f.providers → ValidBlock 12 R := by
  intro R hR
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hR
  exact valid_trace e (k := 12) (c := 2) f.removed_valid.1 A (hrows A (List.mem_filter.mp hA).1)
    (f.removed_hits_providers A hA)

lemma remainder_trace_valid {T : Family 24} (f : TwinFrame T)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (e : Fin 22 ≃ Outside f.removed) :
    ∀ R, R ∈ traces e f.remainder → ValidBlock 14 R := by
  intro R hR
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hR
  exact valid_trace e (k := 14) (c := 0) f.removed_valid.1 A (hrows A (List.mem_filter.mp hA).1)
    (f.removed_hits_remainder A hA)

lemma provider_trace_cover {T : Family 24} (f : TwinFrame T) (hcover : IsCovering 4 T)
    (e : Fin 22 ≃ Outside f.removed) : IsCovering 3 (traces e f.providers) := by
  have h := covering_from_core e T [f.q.val] (s := 1) (t := 3)
    (by simp [ValidBlock]) (by
      intro x hx
      have hxq : x = f.q.val := by simpa using hx
      subst x
      simp [removed]) hcover
  have he : T.filter (fun R => Covering.Subset [f.q.val] R) = f.providers := by
    apply List.filter_congr
    intro R _
    simp [providers, Covering.Subset]
  rwa [he] at h

lemma point_outside_pair {T : Family 24} (f : TwinFrame T)
    (e : Fin 22 ≃ Outside f.removed) (p : Fin 22) :
    point e p ≠ f.q.val ∧ point e p ≠ f.mate.val := by
  have h := point_not_mem e p
  simpa [removed] using h

lemma provider_trace_regular {T : Family 24} (f : TwinFrame T)
    (e : Fin 22 ≃ Outside f.removed) : ∀ p, degree (traces e f.providers) p = 6 := by
  intro p
  rw [degree_traces, providers, degree_filtered_eq_pair]
  exact f.outside (point e p) (f.point_outside_pair e p).1 (f.point_outside_pair e p).2

lemma provider_twins {T : Family 24} (f : TwinFrame T)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (e : Fin 22 ≃ Outside f.removed) :
    ∃ σ : Fin 22 → Fin 22,
      (∀ p, σ p ≠ p) ∧ (∀ p, σ (σ p) = p) ∧
      (∀ p q, pairDegree (traces e f.providers) p q = if p = q ∨ q = σ p then 6 else 3) ∧
      (∀ p R, R ∈ traces e f.providers → (p ∈ R ↔ σ p ∈ R)) ∧
      (∀ z : Fin 22 → ℝ, (CoveringMatrixIncidence.incidence (traces e f.providers)).transpose *ᵥ z = 0 →
        ∀ p, z (σ p) = -z p) :=
  CoveringMatrixRegular22.regular22_twins_with_balance (traces e f.providers)
    (f.provider_trace_valid hrows e) (f.provider_trace_cover hcover e)
    (by rw [traces_length, f.providers_length]) (f.provider_trace_regular e)

end TwinFrame
open TwinFrame

lemma twin_frame_of_exception (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (E : ExceptionalComponents T hrows hcover) :
    ∃ f : TwinFrame T, ∀ r : LowPoint T,
      (lowSystem T hrows hcover).graph.connectedComponentMk r = E.c2 ↔ r = f.q ∨ r = f.mate := by
  classical
  let S := lowSystem T hrows hcover
  have hc : S.BalancedBipartite E.c2 := by
    apply (S.mem_goodComponents E.c2).mp
    rw [E.all_components]
    simp
  obtain ⟨q, mate, hne, hcomp, hbal⟩ := pair_from_two_component T hrows hcover E.c2 hc E.size_two
  have hqcomp : S.graph.connectedComponentMk q = E.c2 := (hcomp q).mpr (Or.inl rfl)
  refine ⟨⟨q, mate, hne, ?_, ?_⟩, hcomp⟩
  · intro R hR
    have h := hbal R hR
    by_cases hq : q.val ∈ R <;> by_cases hm : mate.val ∈ R <;> simp_all
  · intro x hxq hxm
    apply outside_component_codegree_six T hrows hcover E.c2 hc q hqcomp x
    intro r hr hxr
    rcases (hcomp r).mp hr with rfl | rfl
    · exact hxq hxr
    · exact hxm hxr

end Covering.NormalizedBridge20261003.ExceptionBranch
#print axioms Covering.NormalizedBridge20261003.ExceptionBranch.TwinFrame.provider_trace_cover
#print axioms Covering.NormalizedBridge20261003.ExceptionBranch.TwinFrame.provider_trace_regular
#print axioms Covering.NormalizedBridge20261003.ExceptionBranch.TwinFrame.provider_twins
#print axioms Covering.NormalizedBridge20261003.ExceptionBranch.twin_frame_of_exception
