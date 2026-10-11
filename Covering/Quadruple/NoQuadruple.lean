module
public import Covering.Quadruple.Traces
public import Covering.Quadruple.Colors
public import Covering.Quadruple.SevenVsSix
public import Covering.Quadruple.CompletionDegrees
@[expose] public section

/-!
# No balanced quadruple

Proposition 4.1: a nineteen-block `(24,14,4)` cover has no balanced quadruple.
-/
open Finset
open scoped BigOperators
namespace Covering.Quadruple
open Covering.Rigidity Covering.Quadruple
open PointDegree SideLift CrossGrid
open Floors Nineteen
open PairData
open Covering.Completions Covering.OutsideTrace Covering.BlockClasses Covering.Colors
noncomputable section

/-- Proposition 4.1: a nineteen-block `(24,14,4)` cover has no balanced quadruple. -/
theorem no_balanced_quadruple (T : Family 24)
    (hr : ∀ R, R ∈ T → ValidBlock 14 R) (hc : IsCovering 4 T)
    (hlen : T.length=19) (balanced : BalancedQuadruple T) : False := by
  classical
  let g : QuadrupleData T := quadruple_of_balance T hr hc balanced
  have he : Completion (H g) (E g) := completion_from_rigidity (H g) (E g)
    (H_length g) (E_length g) (H_rows g hr) (E_rows g hr)
    (H_cover g hc) (HE_cover g hc)
  have hf : Completion (H g) (F g) := completion_from_rigidity (H g) (F g)
    (H_length g) (F_length g) (H_rows g hr) (F_rows g hr)
    (H_cover g hc) (HF_cover g hc)
  obtain ⟨σ,hσ⟩ := old_twin_geometry (H g) (E g) he
  obtain ⟨τ,hτ⟩ := old_twin_geometry (H g) (F g) hf
  have hστ := completions_share_pairing (H g) (E g) (F g) he hf σ τ hσ hτ
  subst τ
  let N : Fin 20 → Finset (Fin 20) := fun p => univ.filter (fun q => pairDegree (H g) p q=2)
  have hp (p : Fin 20) : pairDegree (H g) p (σ p)=3 := by
    rw [pair_of_membership_imp (H g) p (σ p) (fun R hR => (hσ.H_twins p R hR).mp),he.H_degree]
  have hn (p : Fin 20) : p ∉ N p := by
    simp [N,pair_diagonal,he.H_degree]
  have hsym (p q : Fin 20) : q ∈ N p ↔ p ∈ N q := by
    simp only [N,mem_filter,mem_univ,true_and,pair_symmetric (H g) p q]
  have hcard (p : Fin 20) : (N p).card=6 := by
    have hs : (∑ q, pairDegree (H g) p q)=30 := by
      rw [Fin.sum_univ_def,pair_row_sum (H g) he.H_rows p,he.H_degree]
    have ht (q : Fin 20) : pairDegree (H g) p q =
        1 + (if q=p then 2 else 0) + (if q=σ p then 2 else 0) +
          (if q ∈ N p then 1 else 0) := by
      by_cases hqp : q=p
      · subst q
        simp [N,pair_diagonal,he.H_degree,Ne.symm (hσ.no_fixed p)]
      · by_cases hqσ : q=σ p
        · subst q
          simp [N,hp,hσ.no_fixed]
        · rcases nonpartner_H_codegree (H g) (E g) he σ hσ p q (Ne.symm hqp) hqσ with h | h
          · simp [N,h,hqp,hqσ]
          · simp [N,h,hqp,hqσ]
    have hcount : (∑ q, pairDegree (H g) p q)=24+(N p).card := by
      simp_rw [ht,Finset.sum_add_distrib]
      simp [N]
    omega
  have hGfloor (p : Fin 20) : 2 ≤ degree (G g) p := by
    have hh := degree_four T g.u.val g.v.val (outsidePoint g p)
    have hd : degree (H g) p + degree (E g) p + degree (F g) p + degree (G g) p =
        degree T (outsidePoint g p) := by
      simpa only [H, E, F, G, degree_traces, outsidePoint] using hh
    rw [he.H_degree, he.E_degree, hf.E_degree] at hd
    have hlo := point_floor_eleven T hr hc (outsidePoint g p)
    omega
  obtain ⟨a,b,hab,ha,hb,hrest⟩ := two_high_points (G g) (G_length g hlen) (G_rows g hr) hGfloor
  apply local_seven_vs_six N hn hsym hcard a b (color (G g))
  · intro p q hpa hpb hqa hqb hqN
    have hH : pairDegree (H g) p q=2 := (mem_filter.mp hqN).2
    have hpq : p ≠ q := by intro h; subst q; exact hn p hqN
    have hqp : q ≠ σ p := by intro h; subst q; have hh := hp p; omega
    have heq := hσ.pair_array p q
    have hfq := hτ.pair_array p q
    simp only [hpq,hqp,or_self,ite_false,hH] at heq hfq
    have hpq' : outsidePoint g p ≠ outsidePoint g q := by
      intro h
      exact hpq (point_injective (outsideCoordinates g) h)
    have hlo := pair_floor_six T hr hc _ _ hpq'
    have hsum := actual_pair_partition g p q
    have hG : 2 ≤ pairDegree (G g) p q := by omega
    exact color_eq_of_pair_floor (G g) p q (hrest p hpa hpb) (hrest q hqa hqb) hG
  · intro c
    let L : Finset (Fin 20) := univ.filter (fun p => p ≠ a ∧ p ≠ b)
    have hL : ∀ p, p ∈ L → degree (G g) p=2 := by
      intro p hpL
      have h := (mem_filter.mp hpL).2
      exact hrest p h.1 h.2
    have heq : univ.filter (fun p => p ≠ a ∧ p ≠ b ∧ color (G g) p=c) =
        L.filter (fun p => color (G g) p=c) := by
      ext p
      simp [L,and_assoc]
    rw [heq]
    exact color_fiber_capacity (G g) (G_length g hlen) (G_rows g hr) L hL c

end
end Covering.Quadruple