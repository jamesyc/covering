module

public import campaigns.async_goal.lean.recovered.CrossGridThreeRecoveredV3

@[expose] public section

/-! New reconstruction after workspace loss. Original PairLowerBoundV4 is not
recovered. This source needs a new bounded build and independent review. -/
namespace Covering.PairLowerBound

open CrossGrid

theorem list_of_length_two {α : Type} (L : List α) (h : L.length=2) :
    ∃ x y, L=[x,y] := by
  cases L with
  | nil => simp at h
  | cons x L =>
    cases L with
    | nil => simp at h
    | cons y L =>
      have hz : L.length=0 := by simp only [List.length_cons] at h; omega
      have he := List.length_eq_zero_iff.mp hz
      subst L
      exact ⟨x,y,rfl⟩

theorem list_of_length_three {α : Type} (L : List α) (h : L.length=3) :
    ∃ x y z, L=[x,y,z] := by
  cases L with
  | nil => simp at h
  | cons x L =>
    have hh : L.length=2 := by simp only [List.length_cons] at h; omega
    obtain ⟨y,z,rfl⟩ := list_of_length_two L hh
    exact ⟨x,y,z,rfl⟩

theorem joint_provider (F : Family 22) (h : IsCovering 2 F) (p q : Fin 22) :
    ∃ R, R ∈ F ∧ p ∈ R ∧ q ∈ R := by
  have hlen : (support [p,q]).length≤2 := by
    have hh := PointDegree.support_length_le [p,q]
    simpa [support] using hh
  obtain ⟨T,hT,hsub⟩ := exists_valid_extension [p,q] hlen (by decide : 2≤22)
  obtain ⟨R,hR,hTR⟩ := h T hT
  exact ⟨R,hR,hTR p (hsub p (by simp)),hTR q (hsub q (by simp))⟩

theorem no_five_pair_cover (F : Family 22) (hlen : F.length=5)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 2 F) : False := by
  obtain ⟨p,hpdeg⟩ := PointDegree.exists_degree_le (k:=12) (budget:=5) (cap:=2) F
    (by omega) (fun R hR => Nat.le_of_eq (hrows R hR).2) (by decide)
  let L := F.filter (fun R => p ∈ R)
  let M := F.filter (fun R => p ∉ R)
  have hdeg : L.length≤2 := hpdeg
  have hsplit : L.length+M.length=5 := by
    have hh := (List.filter_append_perm (fun R : Block 22 => decide (p ∈ R)) F).length_eq
    simpa [L,M,hlen] using hh
  have hLvalid (R : Block 22) (hR : R ∈ L) : ValidBlock 12 R :=
    hrows R (List.mem_filter.mp hR).1
  have hLcover (q : Fin 22) : ∃ R, R ∈ L ∧ q ∈ R := by
    obtain ⟨R,hR,hpR,hqR⟩ := joint_provider F hcover p q
    exact ⟨R,List.mem_filter.mpr ⟨hR,by simpa using hpR⟩,hqR⟩
  have hnzero : L.length≠0 := by
    intro hz
    have he := List.length_eq_zero_iff.mp hz
    obtain ⟨R,hR,_⟩ := hLcover p
    rw [he] at hR
    simp at hR
  have hnone : L.length≠1 := by
    intro ho
    cases hL : L with
    | nil => simp [hL] at ho
    | cons A tail =>
      have ht : tail.length=0 := by simp only [hL,List.length_cons] at ho; omega
      have ht' := List.length_eq_zero_iff.mp ht
      subst tail
      have hA : ValidBlock 12 A := hLvalid A (by rw [hL]; simp)
      have hall : Subset (List.finRange 22) A := by
        intro q _
        obtain ⟨R,hR,hqR⟩ := hLcover q
        rw [hL] at hR
        have he : R=A := by simpa using hR
        exact he ▸ hqR
      have hh := (List.nodup_finRange 22).length_le_of_subset hall
      rw [List.length_finRange,hA.2] at hh
      omega
  have htwo : L.length=2 := by omega
  obtain ⟨A,D,hAD⟩ := list_of_length_two L htwo
  have hA : ValidBlock 12 A := hLvalid A (by rw [hAD]; simp)
  have hD : ValidBlock 12 D := hLvalid D (by rw [hAD]; simp)
  have hUnion (q : Fin 22) : q ∈ A ∨ q ∈ D := by
    obtain ⟨R,hR,hqR⟩ := hLcover q
    rw [hAD] at hR
    simp at hR
    rcases hR with rfl | rfl
    · exact Or.inl hqR
    · exact Or.inr hqR
  let X := complement D
  let Y := complement A
  have hXn : X.Nodup := complement_nodup D
  have hYn : Y.Nodup := complement_nodup A
  have hXlen : X.length=10 := complement_length D hD
  have hYlen : Y.length=10 := complement_length A hA
  have hXY : Disjoint X Y := by
    intro q hqX hqY
    have hnD := (mem_complement D q).mp hqX
    have hnA := (mem_complement A q).mp hqY
    exact (hUnion q).elim hnA hnD
  have hMlen : M.length=3 := by omega
  obtain ⟨R,S,T,hRST⟩ := list_of_length_three M hMlen
  have hMv (U : Block 22) (hU : U ∈ M) : U.length≤12 :=
    Nat.le_of_eq (hrows U (List.mem_filter.mp hU).1).2
  have hgrid : CrossThree X Y R S T := by
    intro x hx y hy
    obtain ⟨U,hUF,hxU,hyU⟩ := joint_provider F hcover x y
    have hUp : p ∉ U := by
      intro hpU
      have hUL : U ∈ L := List.mem_filter.mpr ⟨hUF,by simpa using hpU⟩
      rw [hAD] at hUL
      simp at hUL
      rcases hUL with rfl | rfl
      · exact (mem_complement _ y).mp hy hyU
      · exact (mem_complement _ x).mp hx hxU
    have hUM : U ∈ M := List.mem_filter.mpr ⟨hUF,by simpa using hUp⟩
    rw [hRST] at hUM
    simp at hUM
    rcases hUM with rfl | rfl | rfl
    · exact Or.inl ⟨hxU,hyU⟩
    · exact Or.inr (Or.inl ⟨hxU,hyU⟩)
    · exact Or.inr (Or.inr ⟨hxU,hyU⟩)
  exact crossThree_impossible X Y R S T hXn hYn hXY (by omega) (by omega)
    (hMv R (by rw [hRST]; simp)) (hMv S (by rw [hRST]; simp))
    (hMv T (by rw [hRST]; simp)) hgrid

theorem pair_cover_22_12_ge_six (F : Family 22)
    (hrows : ∀ R, R ∈ F → ValidBlock 12 R) (hcover : IsCovering 2 F) :
    6≤F.length := by
  apply Classical.byContradiction
  intro hn
  have hle : F.length≤5 := by omega
  let A : Block 22 := [0,1,2,3,4,5,6,7,8,9,10,11]
  have hA : ValidBlock 12 A := by unfold ValidBlock A; decide
  let G := F++List.replicate (5-F.length) A
  have hGlen : G.length=5 := by
    simp only [G,List.length_append,List.length_replicate]
    omega
  have hGrow : ∀ R, R ∈ G → ValidBlock 12 R := by
    intro R hR
    rcases List.mem_append.mp hR with hf | ha
    · exact hrows R hf
    · have he : R=A := (List.mem_replicate.mp ha).2
      simpa only [he] using hA
  have hGcover : IsCovering 2 G := by
    intro T hT
    obtain ⟨R,hR,hTR⟩ := hcover T hT
    exact ⟨R,List.mem_append.mpr (Or.inl hR),hTR⟩
  exact no_five_pair_cover G hGlen hGrow hGcover

end Covering.PairLowerBound
