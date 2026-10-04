module

public import GadgetSlotPartition
public import Regular20Twins
public import A19GadgetInterface

@[expose] public section

open Finset
open scoped BigOperators
namespace CoveringGadgetTrace
open Covering Covering.PointDegree Covering.SideLift Covering.CrossGrid
open Covering.NormalizedBridge20261003.A19Physical
open CoveringOutsideTrace
noncomputable section

variable {T : Family 24}

def support (g : GadgetData T) : Block 24 := [g.u.val,g.v.val,g.s.val,g.t.val]
def outsideCoordinates (g : GadgetData T) : Fin 20 ≃ Outside (support g) :=
  coordinates (support g) ⟨g.distinct_physical,by rfl⟩ (by decide : 24=4+20)
def outsidePoint (g : GadgetData T) (p : Fin 20) : Fin 24 := point (outsideCoordinates g) p

def H (g : GadgetData T) : Family 20 := traces (outsideCoordinates g) (common T g.u.val g.v.val)
def E (g : GadgetData T) : Family 20 := traces (outsideCoordinates g) (leftOnly T g.u.val g.v.val)
def F (g : GadgetData T) : Family 20 := traces (outsideCoordinates g) (rightOnly T g.u.val g.v.val)
def G (g : GadgetData T) : Family 20 := traces (outsideCoordinates g) (neither T g.u.val g.v.val)

lemma support_hits (g : GadgetData T) (R : Block 24) : (hits (support g) R).length=
    (if g.u.val ∈ R then 1 else 0)+(if g.v.val ∈ R then 1 else 0)+
    (if g.s.val ∈ R then 1 else 0)+(if g.t.val ∈ R then 1 else 0) := by
  by_cases hu : g.u.val ∈ R <;> by_cases hv : g.v.val ∈ R <;>
    by_cases hs : g.s.val ∈ R <;> by_cases ht : g.t.val ∈ R <;>
    simp [support,hits,hu,hv,hs,ht]

lemma outside_pairs (g : GadgetData T) (p : Fin 20) :
    pairDegree T g.u.val (outsidePoint g p)=6 ∧ pairDegree T g.v.val (outsidePoint g p)=6 := by
  have hn : outsidePoint g p ∉ support g := point_not_mem (outsideCoordinates g) p
  apply g.outside_codegree (outsidePoint g p)
  all_goals intro hh; apply hn; simp [support,hh]

lemma H_length (g : GadgetData T) : (H g).length=6 := by
  simpa only [H,traces_length,common_length] using g.pivot_codegree
lemma E_length (g : GadgetData T) : (E g).length=5 := by
  have hh := left_length T g.u.val g.v.val
  rw [common_length,g.pivot_codegree,g.u.property] at hh
  change (traces (outsideCoordinates g) (leftOnly T g.u.val g.v.val)).length=5
  rw [traces_length]
  omega
lemma F_length (g : GadgetData T) : (F g).length=5 := by
  have hh := right_length T g.u.val g.v.val
  rw [common_length,g.pivot_codegree,g.v.property] at hh
  change (traces (outsideCoordinates g) (rightOnly T g.u.val g.v.val)).length=5
  rw [traces_length]
  omega
lemma G_length (g : GadgetData T) (hlen : T.length=19) : (G g).length=3 := by
  have hh := neither_length T g.u.val g.v.val
  rw [common_length,g.pivot_codegree,g.u.property,g.v.property,hlen] at hh
  change (traces (outsideCoordinates g) (neither T g.u.val g.v.val)).length=3
  rw [traces_length]
  omega

lemma H_rows (g : GadgetData T) (hrows : ∀ R, R ∈ T → ValidBlock 14 R) :
    ∀ R, R ∈ H g → ValidBlock 10 R := by
  intro R hR
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
  obtain ⟨hST,hb⟩ := List.mem_filter.mp hS
  have hb : g.u.val ∈ S ∧ g.v.val ∈ S := of_decide_eq_true hb
  refine valid_trace (k:=10) (c:=4) (outsideCoordinates g) g.distinct_physical S (hrows S hST) ?_
  have hh := g.row_balance S hST
  rw [support_hits]
  simp only [if_pos hb.1,if_pos hb.2] at hh ⊢
  omega

lemma E_rows (g : GadgetData T) (hrows : ∀ R, R ∈ T → ValidBlock 14 R) :
    ∀ R, R ∈ E g → ValidBlock 12 R := by
  intro R hR
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
  obtain ⟨hST,hb⟩ := List.mem_filter.mp hS
  have hb : g.u.val ∈ S ∧ g.v.val ∉ S := of_decide_eq_true hb
  refine valid_trace (k:=12) (c:=2) (outsideCoordinates g) g.distinct_physical S (hrows S hST) ?_
  have hh := g.row_balance S hST
  rw [support_hits]
  simp only [if_pos hb.1,if_neg hb.2] at hh ⊢
  omega

lemma F_rows (g : GadgetData T) (hrows : ∀ R, R ∈ T → ValidBlock 14 R) :
    ∀ R, R ∈ F g → ValidBlock 12 R := by
  intro R hR
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
  obtain ⟨hST,hb⟩ := List.mem_filter.mp hS
  have hb : g.u.val ∉ S ∧ g.v.val ∈ S := of_decide_eq_true hb
  refine valid_trace (k:=12) (c:=2) (outsideCoordinates g) g.distinct_physical S (hrows S hST) ?_
  have hh := g.row_balance S hST
  rw [support_hits]
  simp only [if_neg hb.1,if_pos hb.2] at hh ⊢
  omega

lemma G_rows (g : GadgetData T) (hrows : ∀ R, R ∈ T → ValidBlock 14 R) :
    ∀ R, R ∈ G g → ValidBlock 14 R := by
  intro R hR
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hR
  obtain ⟨hST,hb⟩ := List.mem_filter.mp hS
  have hb : g.u.val ∉ S ∧ g.v.val ∉ S := of_decide_eq_true hb
  refine valid_trace (k:=14) (c:=0) (outsideCoordinates g) g.distinct_physical S (hrows S hST) ?_
  have hh := g.row_balance S hST
  rw [support_hits]
  simp only [if_neg hb.1,if_neg hb.2] at hh ⊢
  omega

lemma H_cover (g : GadgetData T) (hcover : IsCovering 4 T) : IsCovering 2 (H g) := by
  have huv : g.u.val≠g.v.val := fun he => g.distinct.1 (Subtype.ext he)
  have hh := covering_from_core (s:=2) (t:=2) (outsideCoordinates g) T [g.u.val,g.v.val]
    (by simp [ValidBlock,huv]) (by simp [Covering.Subset,support]) hcover
  simpa [H,common,Covering.Subset] using hh

lemma HE_cover (g : GadgetData T) (hcover : IsCovering 4 T) : IsCovering 3 (H g++E g) := by
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

lemma HF_cover (g : GadgetData T) (hcover : IsCovering 4 T) : IsCovering 3 (H g++F g) := by
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

lemma H_degree (g : GadgetData T) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (hcover : IsCovering 4 T) : ∀ p, degree (H g) p=3 :=
  CoveringMatrixRegular20.H_regular_from_pairs (H g) (H_length g) (H_rows g hrows) (H_cover g hcover)

lemma E_degree (g : GadgetData T) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (hcover : IsCovering 4 T) (p : Fin 20) : degree (E g) p=3 := by
  have hh : degree (H g) p+degree (E g) p=6 := by
    change degree (traces (outsideCoordinates g) (common T g.u.val g.v.val)) p+
      degree (traces (outsideCoordinates g) (leftOnly T g.u.val g.v.val)) p=6
    rw [degree_traces,degree_traces,degree_common_left]
    exact (outside_pairs g p).1
  rw [H_degree g hrows hcover p] at hh
  omega

lemma F_degree (g : GadgetData T) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (hcover : IsCovering 4 T) (p : Fin 20) : degree (F g) p=3 := by
  have hh : degree (H g) p+degree (F g) p=6 := by
    change degree (traces (outsideCoordinates g) (common T g.u.val g.v.val)) p+
      degree (traces (outsideCoordinates g) (rightOnly T g.u.val g.v.val)) p=6
    rw [degree_traces,degree_traces,degree_common_right]
    exact (outside_pairs g p).2
  rw [H_degree g hrows hcover p] at hh
  omega

/-- Two actual regular20 completions on one common physical outside-point map. -/
theorem actual_completions (g : GadgetData T) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (hcover : IsCovering 4 T) :
    CoveringMatrixRegular20.Completion (H g) (E g) ∧
      CoveringMatrixRegular20.Completion (H g) (F g) := by
  constructor
  · exact ⟨H_length g,E_length g,H_rows g hrows,E_rows g hrows,H_degree g hrows hcover,
      E_degree g hrows hcover,H_cover g hcover,HE_cover g hcover⟩
  · exact ⟨H_length g,F_length g,H_rows g hrows,F_rows g hrows,H_degree g hrows hcover,
      F_degree g hrows hcover,H_cover g hcover,HF_cover g hcover⟩

lemma G_degree_identity (g : GadgetData T) (hrows : ∀ R, R ∈ T → ValidBlock 14 R)
    (hcover : IsCovering 4 T) (p : Fin 20) : degree (G g) p+9=degree T (outsidePoint g p) := by
  have hh := degree_four T g.u.val g.v.val (outsidePoint g p)
  have ht : degree (H g) p+degree (E g) p+degree (F g) p+degree (G g) p=
      degree T (outsidePoint g p) := by
    simpa only [H,E,F,G,degree_traces,outsidePoint] using hh
  rw [H_degree g hrows hcover p,E_degree g hrows hcover p,F_degree g hrows hcover p] at ht
  omega

lemma actual_pair_partition (g : GadgetData T) (p q : Fin 20) :
    pairDegree (H g) p q+pairDegree (E g) p q+pairDegree (F g) p q+pairDegree (G g) p q=
      pairDegree T (outsidePoint g p) (outsidePoint g q) := by
  simpa only [H,E,F,G,pair_degree_traces,outsidePoint] using
    pair_four T g.u.val g.v.val (outsidePoint g p) (outsidePoint g q)

#print axioms actual_completions
#print axioms G_degree_identity
#print axioms actual_pair_partition
end
end CoveringGadgetTrace
