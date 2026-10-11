module

public import Covering.Quadruple.BlockClasses
public import Covering.Quadruple.SharedTwins
public import Covering.Quadruple.Completion
public import Covering.PairCover.NineteenGrid
public import Covering.Quadruple.Data

@[expose] public section

/-!
# Traces of the block classes

Coverage properties of the traces of `H`, `E`, `F` and `G` on the twenty old points.
-/

open Finset
open scoped BigOperators
namespace Covering.BlockClasses
open Covering Covering.PointDegree Covering.SideLift Covering.CrossGrid
open Covering.Nineteen
open Covering.OutsideTrace
noncomputable section

variable {T : Family 24}

def support (g : QuadrupleData T) : Block 24 := [g.u.val,g.v.val,g.s.val,g.t.val]
def outsideCoordinates (g : QuadrupleData T) : Fin 20 ≃ Outside (support g) :=
  coordinates (support g) ⟨g.distinct_points,by rfl⟩ (by decide : 24=4+20)
def outsidePoint (g : QuadrupleData T) (p : Fin 20) : Fin 24 := point (outsideCoordinates g) p

def H (g : QuadrupleData T) : Family 20 := traces (outsideCoordinates g) (common T g.u.val g.v.val)
def E (g : QuadrupleData T) : Family 20 := traces (outsideCoordinates g) (leftOnly T g.u.val g.v.val)
def F (g : QuadrupleData T) : Family 20 := traces (outsideCoordinates g) (rightOnly T g.u.val g.v.val)
def G (g : QuadrupleData T) : Family 20 := traces (outsideCoordinates g) (neither T g.u.val g.v.val)

lemma support_hits (g : QuadrupleData T) (R : Block 24) : (hits (support g) R).length=
    (if g.u.val ∈ R then 1 else 0)+(if g.v.val ∈ R then 1 else 0)+
    (if g.s.val ∈ R then 1 else 0)+(if g.t.val ∈ R then 1 else 0) := by
  by_cases hu : g.u.val ∈ R <;> by_cases hv : g.v.val ∈ R <;>
    by_cases hs : g.s.val ∈ R <;> by_cases ht : g.t.val ∈ R <;>
    simp [support,hits,hu,hv,hs,ht]

lemma H_length (g : QuadrupleData T) : (H g).length=6 := by
  simpa only [H,traces_length,common_length] using g.pivot_codegree
lemma E_length (g : QuadrupleData T) : (E g).length=5 := by
  have hh := left_length T g.u.val g.v.val
  rw [common_length,g.pivot_codegree,g.u.property] at hh
  change (traces (outsideCoordinates g) (leftOnly T g.u.val g.v.val)).length=5
  rw [traces_length]
  omega
lemma F_length (g : QuadrupleData T) : (F g).length=5 := by
  have hh := right_length T g.u.val g.v.val
  rw [common_length,g.pivot_codegree,g.v.property] at hh
  change (traces (outsideCoordinates g) (rightOnly T g.u.val g.v.val)).length=5
  rw [traces_length]
  omega
lemma G_length (g : QuadrupleData T) (hlen : T.length=19) : (G g).length=3 := by
  have hh := neither_length T g.u.val g.v.val
  rw [common_length,g.pivot_codegree,g.u.property,g.v.property,hlen] at hh
  change (traces (outsideCoordinates g) (neither T g.u.val g.v.val)).length=3
  rw [traces_length]
  omega

lemma H_rows (g : QuadrupleData T) (hrows : ∀ R, R ∈ T → ValidBlock 14 R) :
    ∀ R, R ∈ H g → ValidBlock 10 R := by
  intro R hR
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
  obtain ⟨hST,hb⟩ := List.mem_filter.mp hS
  have hb : g.u.val ∈ S ∧ g.v.val ∈ S := of_decide_eq_true hb
  refine valid_trace (k:=10) (c:=4) (outsideCoordinates g) g.distinct_points S (hrows S hST) ?_
  have hh := g.row_balance S hST
  rw [support_hits]
  simp only [ite_eq_left hb.1,ite_eq_left hb.2] at hh ⊢
  omega

lemma E_rows (g : QuadrupleData T) (hrows : ∀ R, R ∈ T → ValidBlock 14 R) :
    ∀ R, R ∈ E g → ValidBlock 12 R := by
  intro R hR
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
  obtain ⟨hST,hb⟩ := List.mem_filter.mp hS
  have hb : g.u.val ∈ S ∧ g.v.val ∉ S := of_decide_eq_true hb
  refine valid_trace (k:=12) (c:=2) (outsideCoordinates g) g.distinct_points S (hrows S hST) ?_
  have hh := g.row_balance S hST
  rw [support_hits]
  simp only [ite_eq_left hb.1,ite_eq_right hb.2] at hh ⊢
  omega

lemma F_rows (g : QuadrupleData T) (hrows : ∀ R, R ∈ T → ValidBlock 14 R) :
    ∀ R, R ∈ F g → ValidBlock 12 R := by
  intro R hR
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
  obtain ⟨hST,hb⟩ := List.mem_filter.mp hS
  have hb : g.u.val ∉ S ∧ g.v.val ∈ S := of_decide_eq_true hb
  refine valid_trace (k:=12) (c:=2) (outsideCoordinates g) g.distinct_points S (hrows S hST) ?_
  have hh := g.row_balance S hST
  rw [support_hits]
  simp only [ite_eq_right hb.1,ite_eq_left hb.2] at hh ⊢
  omega

lemma G_rows (g : QuadrupleData T) (hrows : ∀ R, R ∈ T → ValidBlock 14 R) :
    ∀ R, R ∈ G g → ValidBlock 14 R := by
  intro R hR
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
  obtain ⟨hST,hb⟩ := List.mem_filter.mp hS
  have hb : g.u.val ∉ S ∧ g.v.val ∉ S := of_decide_eq_true hb
  refine valid_trace (k:=14) (c:=0) (outsideCoordinates g) g.distinct_points S (hrows S hST) ?_
  have hh := g.row_balance S hST
  rw [support_hits]
  simp only [ite_eq_right hb.1,ite_eq_right hb.2] at hh ⊢
  omega

lemma H_cover (g : QuadrupleData T) (hcover : IsCovering 4 T) : IsCovering 2 (H g) := by
  have huv : g.u.val≠g.v.val := fun he => g.distinct.1 (Subtype.ext he)
  have hh := covering_from_core (s:=2) (t:=2) (outsideCoordinates g) T [g.u.val,g.v.val]
    (by simp [ValidBlock,huv]) (by simp [Covering.Subset,support]) hcover
  simpa [H,common,Covering.Subset] using hh

lemma HE_cover (g : QuadrupleData T) (hcover : IsCovering 4 T) : IsCovering 3 (H g++E g) := by
  have hc : IsCovering 3 (traces (outsideCoordinates g) (T.filter (fun R => g.u.val ∈ R))) := by
    have hh := covering_from_core (s:=1) (t:=3) (outsideCoordinates g) T [g.u.val]
      (by simp [ValidBlock]) (by simp [Covering.Subset,support]) hcover
    simpa [Covering.Subset] using hh
  intro Q hQ
  obtain ⟨R,hR,hs⟩ := hc Q hQ
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
  obtain ⟨hST,hu⟩ := List.mem_filter.mp hS
  have hu : g.u.val ∈ S := of_decide_eq_true hu
  refine ⟨trace (outsideCoordinates g) S,?_,hs⟩
  by_cases hv : g.v.val ∈ S
  · exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨S,List.mem_filter.mpr ⟨hST,by simp [hu,hv]⟩,rfl⟩))
  · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨S,List.mem_filter.mpr ⟨hST,by simp [hu,hv]⟩,rfl⟩))

lemma HF_cover (g : QuadrupleData T) (hcover : IsCovering 4 T) : IsCovering 3 (H g++F g) := by
  have hc : IsCovering 3 (traces (outsideCoordinates g) (T.filter (fun R => g.v.val ∈ R))) := by
    have hh := covering_from_core (s:=1) (t:=3) (outsideCoordinates g) T [g.v.val]
      (by simp [ValidBlock]) (by simp [Covering.Subset,support]) hcover
    simpa [Covering.Subset] using hh
  intro Q hQ
  obtain ⟨R,hR,hs⟩ := hc Q hQ
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
  obtain ⟨hST,hv⟩ := List.mem_filter.mp hS
  have hv : g.v.val ∈ S := of_decide_eq_true hv
  refine ⟨trace (outsideCoordinates g) S,?_,hs⟩
  by_cases hu : g.u.val ∈ S
  · exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨S,List.mem_filter.mpr ⟨hST,by simp [hu,hv]⟩,rfl⟩))
  · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨S,List.mem_filter.mpr ⟨hST,by simp [hu,hv]⟩,rfl⟩))

lemma actual_pair_partition (g : QuadrupleData T) (p q : Fin 20) :
    pairDegree (H g) p q+pairDegree (E g) p q+pairDegree (F g) p q+pairDegree (G g) p q=
      pairDegree T (outsidePoint g p) (outsidePoint g q) := by
  simpa only [H,E,F,G,pair_degree_traces,outsidePoint] using
    pair_four T g.u.val g.v.val (outsidePoint g p) (outsidePoint g q)

end
end Covering.BlockClasses
