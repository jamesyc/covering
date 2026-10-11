module

public import Covering.Components.LowPoints
public import Covering.Rigidity.IncidenceMatrix
public import Covering.Kernel.Incidence

@[expose] public section

/-!
# The relation space

Lemma 3.1 for a nineteen-block cover: at least three balanced components.
-/

open Matrix Finset
open scoped BigOperators
namespace Covering.Nineteen
open Covering.Floors
open PointDegree SideLift WeightedSignlessKernel WeightedKernelComponents

noncomputable def lowSystem (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T) : System (LowPoint T) where
  W := lowExcess T
  d := 5
  symmetric := fun p q => fullExcess_symmetric T p.val q.val
  nonnegative := fun p q => fullExcess_nonnegative T hrows hcover p.val q.val
  zero_diagonal := fun p => fullExcess_diagonal T p.val
  degree_le := fun p => lowExcess_row_le_five T hrows hcover p

def lowIncidence (T : Family 24) : Matrix (LowPoint T) (Fin T.length) ℝ :=
  Covering.IncidenceMatrix.incidenceOn T Subtype.val

lemma low_gram_identity (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T) :
    (lowSystem T hrows hcover).gram 6 = lowIncidence T * (lowIncidence T).transpose := by
  ext p q
  rw [show lowIncidence T = Covering.IncidenceMatrix.incidenceOn T Subtype.val from rfl,
    Covering.IncidenceMatrix.restricted_gram]
  simp only [System.gram, System.Q, signless, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, RowSumFactorization.ones]
  simp only [Matrix.one_apply]
  change 5 * (if p = q then (1 : ℝ) else 0) + lowExcess T p q + 6 * 1 = _
  by_cases h : p = q
  · subst q
    norm_num [lowExcess, fullExcess, PairData.pair_diagonal, p.property]
  · have hv : p.val ≠ q.val := fun he => h (Subtype.ext he)
    simp [lowExcess, fullExcess, h, hv]

lemma component_count_from_cover (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T) (hlen : T.length = 19) :
    Fintype.card (LowPoint T) - 19 ≤
      Nat.card {c // (lowSystem T hrows hcover).BalancedBipartite c} := by
  have h := (lowSystem T hrows hcover).components_from_incidence (by norm_num [lowSystem])
    6 (by norm_num) (lowIncidence T) (low_gram_identity T hrows hcover)
  simpa [hlen] using h

lemma at_least_three_components (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T) (hlen : T.length = 19) :
    3 ≤ Nat.card {c // (lowSystem T hrows hcover).BalancedBipartite c} := by
  have hc := low_card_cases T hrows hcover hlen
  have h := component_count_from_cover T hrows hcover hlen
  omega

lemma high_excess_zero_of_regular_low_row (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (p : LowPoint T) (hp : rowSum (lowExcess T) p = 5)
    (q : Fin 24) (hq : degree T q ≠ 11) : fullExcess T p.val q = 0 := by
  classical
  have hs := Fintype.sum_subtype_add_sum_subtype (fun r => degree T r = 11)
    (fun r => fullExcess T p.val r)
  have hf := fullExcess_low_row_sum T hrows p
  change (∑ r : LowPoint T, fullExcess T p.val r.val) = 5 at hp
  have hz : (∑ r : {r : Fin 24 // ¬ degree T r = 11}, fullExcess T p.val r.val) = 0 := by
    linarith
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun r _ =>
    fullExcess_nonnegative T hrows hcover p.val r.val)).mp hz ⟨q, hq⟩ (mem_univ _)

lemma component_closed_in_all_points (T : Family 24)
    (hrows : ∀ R, R ∈ T → ValidBlock 14 R) (hcover : IsCovering 4 T)
    (c : (lowSystem T hrows hcover).graph.ConnectedComponent)
    (hc : (lowSystem T hrows hcover).RegularComponent c)
    (p : LowPoint T) (hp : (lowSystem T hrows hcover).graph.connectedComponentMk p = c)
    (q : Fin 24) (hw : fullExcess T p.val q ≠ 0) :
    ∃ hq : degree T q = 11,
      (lowSystem T hrows hcover).graph.connectedComponentMk ⟨q, hq⟩ = c := by
  classical
  have hregular : rowSum (lowExcess T) p = 5 := hc p hp
  have hq : degree T q = 11 := by
    by_contra h
    exact hw (high_excess_zero_of_regular_low_row T hrows hcover p hregular q h)
  refine ⟨hq, ?_⟩
  by_contra hn
  have hz := (lowSystem T hrows hcover).component_closed c hp hn
  exact hw hz

end Covering.Nineteen
