module

public import GadgetPhysicalTraces
public import GadgetResidualColors
public import Regular20RowIntersections

@[expose] public section

open Finset
open scoped BigOperators
namespace CoveringGadgetTrace
open Covering Covering.PointDegree Covering.SideLift Covering.CrossGrid
open Covering.NormalizedBridge20261003 Covering.NormalizedBridge20261003.A19Physical
open CoveringMatrixRegular20 CoveringOutsideTrace
noncomputable section
variable {T : Family 24}

lemma G_floor (g : GadgetData T) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (hcover : IsCovering 4 T) (p : Fin 20) : 2≤degree (G g) p := by
  have hh := G_degree_identity g hrows hcover p
  have hlo := point_floor_eleven T hrows hcover (outsidePoint g p)
  omega

lemma residual_pair_floor (g : GadgetData T) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (hcover : IsCovering 4 T) (σ : Fin 20 → Fin 20)
    (hσE : TwinData (H g) (E g) σ) (hσF : TwinData (H g) (F g) σ)
    (p q : Fin 20) (hpq : p≠q) (hqp : q≠σ p) (hH : pairDegree (H g) p q=2) :
    2≤pairDegree (G g) p q := by
  have he := hσE.pair_array p q
  have hf := hσF.pair_array p q
  simp only [hpq,hqp,or_self,if_false,hH] at he hf
  have hpq' : outsidePoint g p≠outsidePoint g q := by
    intro hh
    exact hpq (point_injective (outsideCoordinates g) hh)
  have hlo := pair_floor_six T hrows hcover _ _ hpq'
  have ht := actual_pair_partition g p q
  omega

lemma pair_membership_congr {n : Nat} (F : Family n) (p p' q q' : Fin n)
    (hp : ∀ R, R∈F → (p∈R ↔ p'∈R))
    (hq : ∀ R, R∈F → (q∈R ↔ q'∈R)) : pairDegree F p q=pairDegree F p' q' := by
  unfold pairDegree
  congr 1
  apply List.filter_congr
  intro R hR
  simp only [hp R hR,hq R hR]

lemma paired_membership (H : Family 20) (σ : Fin 20 → Fin 20)
    (e : (Fin 10×Fin 2)≃Fin 20) (he : ∀ i,e (i,1)=σ (e (i,0)))
    (ht : ∀ p R,R∈H → (p∈R ↔ σ p∈R)) (i : Fin 10) (b : Fin 2)
    (R : Block 20) (hR : R∈H) : e (i,b)∈R ↔ e (i,0)∈R := by
  have hb : b=0 ∨ b=1 := by omega
  rcases hb with rfl | rfl
  · rfl
  · rw [he]
    exact (ht (e (i,0)) R hR).symm

lemma paired_codegree (H : Family 20) (σ : Fin 20 → Fin 20)
    (e : (Fin 10×Fin 2)≃Fin 20) (he : ∀ i,e (i,1)=σ (e (i,0)))
    (ht : ∀ p R,R∈H → (p∈R ↔ σ p∈R)) (i j : Fin 10) (a b : Fin 2) :
    pairDegree H (e (i,a)) (e (j,b))=pairDegree H (e (i,0)) (e (j,0)) :=
  pair_membership_congr H _ _ _ _ (paired_membership H σ e he ht i a)
    (paired_membership H σ e he ht j b)

lemma coordinates_nonpartners (σ : Fin 20 → Fin 20) (hinv : ∀ p,σ (σ p)=p)
    (e : (Fin 10×Fin 2)≃Fin 20) (he : ∀ i,e (i,1)=σ (e (i,0)))
    (i j : Fin 10) (hij : i≠j) (a b : Fin 2) :
    e (i,a)≠e (j,b) ∧ e (j,b)≠σ (e (i,a)) := by
  constructor
  · intro hh
    exact hij (congrArg Prod.fst (e.injective hh))
  · intro hh
    have ha : a=0 ∨ a=1 := by omega
    rcases ha with rfl | rfl
    · rw [← he i] at hh
      exact hij (congrArg Prod.fst (e.injective hh)).symm
    · rw [he i,hinv] at hh
      exact hij (congrArg Prod.fst (e.injective hh)).symm

#print axioms residual_pair_floor
#print axioms paired_codegree
end
end CoveringGadgetTrace
