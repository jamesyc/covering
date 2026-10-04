module

public import FormalResume20261003.MatchingGridV1
public import FormalResume20261003.SlotDegreesV1

@[expose] public section

namespace Covering.NormalizedBridge20261003.Regular22Matching

open PointSplit PointDegree TwoPointSplit CrossGrid TwinCap.CliqueIncidence

theorem list_of_length_one {α : Type} (L : List α) (h : L.length=1) : ∃ a, L=[a] := by
  cases L with
  | nil => simp at h
  | cons a L =>
    have he : L=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at h; omega)
    subst L
    exact ⟨a,rfl⟩

theorem point_cover_count {n k : Nat} (F : Family n)
    (hrows : ∀ R, R ∈ F → R.length≤k) (hcover : IsCovering 1 F) : n≤F.length*k := by
  have hc : PointCover (List.finRange n) F := by
    intro p _
    obtain ⟨R,hR,hs⟩ := hcover [p] (by simp [ValidBlock])
    exact ⟨R,hR,hs p (by simp)⟩
  have hlo := point_cover_incidence (List.finRange n) F hc
  rw [List.length_finRange] at hlo
  have hhi := Weighted.sum_map_le_length_mul F
    (fun R => (hits (List.finRange n) R).length) k
    (fun R hR => Nat.le_trans (hits_le_row (List.finRange n) R (List.nodup_finRange n)) (hrows R hR))
  omega

theorem subset_equal_length {n : Nat} (X Y : Block n)
    (hX : X.Nodup) (hY : Y.Nodup) (hlen : X.length=Y.length) (hsub : Subset X Y) : Subset Y X := by
  intro p hp
  apply Classical.byContradiction
  intro hn
  have hn' : (p::X).Nodup := by simp [hn,hX]
  have hs : (p::X).Subset Y := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact hsub q hq
  have hh := hn'.length_le_of_subset hs
  simp only [List.length_cons] at hh
  omega

/-- Exact two-low-point split of a six-row(21,11,2) pair cover. The rows
remain arbitrary physical traces; no signature catalogue is assumed. -/
structure LowProfile (A B C D : Family 19) : Prop where
  total : A.length+B.length+C.length+D.length=6
  first : A.length+B.length=2
  second : A.length+C.length=2
  rowA : ∀ R, R ∈ A → ValidBlock 9 R
  rowB : ∀ R, R ∈ B → ValidBlock 10 R
  rowC : ∀ R, R ∈ C → ValidBlock 10 R
  rowD : ∀ R, R ∈ D → ValidBlock 11 R
  zero : IsCovering 0 A
  ab : IsCovering 1 (A++B)
  ac : IsCovering 1 (A++C)
  all : IsCovering 2 ((A++C)++(B++D))

theorem low_profile_impossible (A B C D : Family 19) (h : LowProfile A B C D) : False := by
  have hAlower : 1≤A.length := by
    obtain ⟨R,hR,_⟩ := h.zero [] (by unfold ValidBlock; decide)
    apply Classical.byContradiction
    intro hn
    have he : A=[] := List.length_eq_zero_iff.mp (by omega)
    simpa only [he,List.not_mem_nil] using hR
  have hAupper : A.length≤2 := by have hh := h.first; omega
  have hAnot2 : A.length≠2 := by
    intro hA
    have hB : B=[] := List.length_eq_zero_iff.mp (by have hh := h.first; omega)
    have hc : IsCovering 1 A := by simpa only [hB,List.append_nil] using h.ab
    have hh := point_cover_count A (fun R hR => Nat.le_of_eq (h.rowA R hR).2) hc
    omega
  have hA : A.length=1 := by omega
  have hB : B.length=1 := by have hh := h.first; omega
  have hC : C.length=1 := by have hh := h.second; omega
  have hD : D.length=3 := by have hh := h.total; omega
  obtain ⟨R,hAR⟩ := list_of_length_one A hA
  obtain ⟨S,hBS⟩ := list_of_length_one B hB
  obtain ⟨T,hCT⟩ := list_of_length_one C hC
  have hR : ValidBlock 9 R := h.rowA R (by rw [hAR]; simp)
  have hS : ValidBlock 10 S := h.rowB S (by rw [hBS]; simp)
  have hT : ValidBlock 10 T := h.rowC T (by rw [hCT]; simp)
  let Y := complement R
  have hY : ValidBlock 10 Y := ⟨complement_nodup R,by simpa using complement_length R hR⟩
  have hSY : Subset S Y := by
    have hYS : Subset Y S := by
      intro y hy
      obtain ⟨Q,hQ,hs⟩ := h.ab [y] (by simp [ValidBlock])
      rw [hAR,hBS] at hQ
      have hm : Q=R ∨ Q=S := by simpa only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] using hQ
      rcases hm with he | he
      · subst Q
        exact False.elim ((mem_complement R y).mp hy (hs y (by simp)))
      · subst Q
        exact hs y (by simp)
    exact subset_equal_length Y S hY.1 hS.1 (hY.2.trans hS.2.symm) hYS
  have hTY : Subset T Y := by
    have hYT : Subset Y T := by
      intro y hy
      obtain ⟨Q,hQ,hs⟩ := h.ac [y] (by simp [ValidBlock])
      rw [hAR,hCT] at hQ
      have hm : Q=R ∨ Q=T := by simpa only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] using hQ
      rcases hm with he | he
      · subst Q
        exact False.elim ((mem_complement R y).mp hy (hs y (by simp)))
      · subst Q
        exact hs y (by simp)
    exact subset_equal_length Y T hY.1 hT.1 (hY.2.trans hT.2.symm) hYT
  have hRY : Disjoint R Y := fun p hp hy => (mem_complement R p).mp hy hp
  have hcross : CrossCover R Y D := by
    intro x hx y hy
    have hxy : x≠y := fun he => hRY x hx (he.symm ▸ hy)
    obtain ⟨Q,hQ,hs⟩ := h.all [x,y] (by simp [ValidBlock,hxy])
    have hxQ := hs x (by simp)
    have hyQ := hs y (by simp)
    rw [hAR,hBS,hCT] at hQ
    have hm : Q=R ∨ Q=T ∨ Q=S ∨ Q ∈ D := by
      simpa only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] using hQ
    rcases hm with rfl | rfl | rfl | hd
    · exact False.elim (hRY y hyQ hy)
    · exact False.elim (hRY x hx (hTY x hxQ))
    · exact False.elim (hRY x hx (hSY x hxQ))
    · exact ⟨Q,hd,hxQ,hyQ⟩
  exact MatchingGrid.no_three_rows R Y D hR.1 hY.1 hRY
    (by rw [hR.2]; decide) (by rw [hY.2]; decide) (by rw [hR.2,hY.2]; decide)
    hD (fun Q hQ => Nat.le_of_eq (h.rowD Q hQ).2) hcross

end Covering.NormalizedBridge20261003.Regular22Matching
