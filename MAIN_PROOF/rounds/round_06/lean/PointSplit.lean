import Foundations.Capacity

namespace Covering.PointSplit

/-- Embed the old points; the new distinguished point is `Fin.last n`. -/
def embed {n : Nat} (T : Block n) : Block (n+1) := T.map Fin.castSucc

def cone {n : Nat} (T : Block n) : Block (n+1) := Fin.last n :: embed T

def trace {n : Nat} (T : Block (n+1)) : Block n :=
  T.filterMap (Fin.lastCases none (fun p => some p))

def lift {n : Nat} (A B : Family n) : Family (n+1) :=
  A.map cone ++ B.map embed

@[simp] theorem mem_embed {n : Nat} (T : Block n) (p : Fin n) :
    p.castSucc ∈ embed T ↔ p ∈ T := by simp [embed, Fin.castSucc_inj]

@[simp] theorem last_not_mem_embed {n : Nat} (T : Block n) :
    Fin.last n ∉ embed T := by
  intro h
  obtain ⟨p, _, hp⟩ := List.mem_map.mp h
  have hv := congrArg Fin.val hp
  have := p.isLt
  simp at hv
  omega

@[simp] theorem mem_cone {n : Nat} (T : Block n) (p : Fin n) :
    p.castSucc ∈ cone T ↔ p ∈ T := by
  simp only [cone, List.mem_cons, mem_embed]
  have hn : p.castSucc ≠ Fin.last n := by
    intro h; have hv := congrArg Fin.val h; have := p.isLt; simp at hv; omega
  simp [hn]

@[simp] theorem last_mem_cone {n : Nat} (T : Block n) :
    Fin.last n ∈ cone T := by simp [cone]

@[simp] theorem trace_nil {n : Nat} : trace ([] : Block (n+1)) = [] := rfl

@[simp] theorem trace_cons_last {n : Nat} (T : Block (n+1)) :
    trace (Fin.last n :: T) = trace T := by simp [trace]

@[simp] theorem trace_cons_embed {n : Nat} (T : Block (n+1)) (p : Fin n) :
    trace (p.castSucc :: T) = p :: trace T := by simp [trace]

@[simp] theorem mem_trace {n : Nat} (T : Block (n+1)) (p : Fin n) :
    p ∈ trace T ↔ p.castSucc ∈ T := by
  induction T with
  | nil => simp
  | cons q T ih =>
    refine Fin.lastCases ?_ (fun q => ?_) q
    · have hn : p.castSucc ≠ Fin.last n := by
        intro he; have hv := congrArg Fin.val he; have := p.isLt; simp at hv; omega
      simp [ih, hn]
    · simp [ih, Fin.castSucc_inj]

theorem trace_nodup {n : Nat} (T : Block (n+1)) (h : T.Nodup) :
    (trace T).Nodup := by
  induction T with
  | nil => simp
  | cons p T ih =>
    revert h
    refine Fin.lastCases ?_ (fun p => ?_) p <;> intro h
    · simpa using ih (List.nodup_cons.mp h).2
    · obtain ⟨hp, ht⟩ := List.nodup_cons.mp h
      simp only [trace_cons_embed, List.nodup_cons]
      exact ⟨fun hm => hp ((mem_trace T _).mp hm), ih ht⟩

theorem trace_length_absent {n : Nat} (T : Block (n+1))
    (h : Fin.last n ∉ T) : (trace T).length = T.length := by
  induction T with
  | nil => rfl
  | cons p T ih =>
    revert h
    refine Fin.lastCases ?_ (fun p => ?_) p <;> intro h
    · exact False.elim (h (by simp))
    · have ht : Fin.last n ∉ T := fun hm => h (by simp [hm])
      simpa using congrArg Nat.succ (ih ht)

theorem trace_length_present {n : Nat} (T : Block (n+1))
    (hd : T.Nodup) (h : Fin.last n ∈ T) : (trace T).length + 1 = T.length := by
  induction T with
  | nil => simp at h
  | cons p T ih =>
    revert hd h
    refine Fin.lastCases ?_ (fun p => ?_) p <;> intro hd h
    · obtain ⟨hp, _⟩ := List.nodup_cons.mp hd
      simpa using congrArg Nat.succ (trace_length_absent T hp)
    · obtain ⟨_, ht⟩ := List.nodup_cons.mp hd
      have hn : p.castSucc ≠ Fin.last n := by
        intro he; have hv := congrArg Fin.val he; have := p.isLt; simp at hv; omega
      have hm : Fin.last n ∈ T := (List.mem_cons.mp h).resolve_left (Ne.symm hn)
      simpa [Nat.add_assoc] using congrArg Nat.succ (ih ht hm)

theorem valid_embed {n k : Nat} (T : Block n) (h : ValidBlock k T) :
    ValidBlock k (embed T) := by
  constructor
  · exact List.Pairwise.map Fin.castSucc
      (fun _ _ hn he => hn (Fin.castSucc_inj.mp he)) h.1
  · simpa [embed] using h.2

theorem valid_cone {n k : Nat} (T : Block n) (h : ValidBlock k T) :
    ValidBlock (k+1) (cone T) := by
  exact ⟨List.nodup_cons.mpr ⟨last_not_mem_embed T, (valid_embed T h).1⟩,
    by simpa [cone, embed] using congrArg Nat.succ h.2⟩

theorem subset_embed_iff {n : Nat} (T U : Block n) :
    Subset (embed T) (embed U) ↔ Subset T U := by
  constructor
  · intro h p hp; exact (mem_embed U p).mp (h p.castSucc ((mem_embed T p).mpr hp))
  · intro h p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (mem_embed U q).mpr (h q hq)

theorem subset_embed_cone_iff {n : Nat} (T U : Block n) :
    Subset (embed T) (cone U) ↔ Subset T U := by
  constructor
  · intro h p hp; exact (mem_cone U p).mp (h p.castSucc ((mem_embed T p).mpr hp))
  · intro h p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (mem_cone U q).mpr (h q hq)

theorem subset_cone_iff {n : Nat} (T U : Block n) :
    Subset (cone T) (cone U) ↔ Subset T U := by
  constructor
  · intro h p hp; exact (mem_cone U p).mp (h p.castSucc ((mem_cone T p).mpr hp))
  · intro h p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact last_mem_cone U
    · exact (subset_embed_cone_iff T U).mpr h p hp

theorem covers_embed_iff {n : Nat} (A B : Family n) (T : Block n) :
    Covers (lift A B) (embed T) ↔ Covers (A ++ B) T := by
  constructor
  · rintro ⟨U, hU, hsub⟩
    rcases List.mem_append.mp hU with hA | hB
    · obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hA
      exact ⟨V, List.mem_append.mpr (Or.inl hV), (subset_embed_cone_iff T V).mp hsub⟩
    · obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hB
      exact ⟨V, List.mem_append.mpr (Or.inr hV), (subset_embed_iff T V).mp hsub⟩
  · rintro ⟨U, hU, hsub⟩
    rcases List.mem_append.mp hU with hA | hB
    · exact ⟨cone U, List.mem_append.mpr (Or.inl (List.mem_map_of_mem hA)),
        (subset_embed_cone_iff T U).mpr hsub⟩
    · exact ⟨embed U, List.mem_append.mpr (Or.inr (List.mem_map_of_mem hB)),
        (subset_embed_iff T U).mpr hsub⟩

theorem covers_cone_iff {n : Nat} (A B : Family n) (T : Block n) :
    Covers (lift A B) (cone T) ↔ Covers A T := by
  constructor
  · rintro ⟨U, hU, hsub⟩
    rcases List.mem_append.mp hU with hA | hB
    · obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hA
      exact ⟨V, hV, (subset_cone_iff T V).mp hsub⟩
    · obtain ⟨V, _, rfl⟩ := List.mem_map.mp hB
      exact False.elim (last_not_mem_embed V (hsub (Fin.last n) (last_mem_cone T)))
  · rintro ⟨U, hU, hsub⟩
    exact ⟨cone U, List.mem_append.mpr (Or.inl (List.mem_map_of_mem hU)),
      (subset_cone_iff T U).mpr hsub⟩

theorem subset_trace_embed {n : Nat} (T : Block (n+1))
    (h : Fin.last n ∉ T) : Subset T (embed (trace T)) := by
  intro p hp
  revert hp
  refine Fin.lastCases ?_ (fun p => ?_) p <;> intro hp
  · exact False.elim (h hp)
  · exact (mem_embed (trace T) p).mpr ((mem_trace T p).mpr hp)

theorem subset_trace_cone {n : Nat} (T : Block (n+1)) :
    Subset T (cone (trace T)) := by
  intro p hp
  revert hp
  refine Fin.lastCases ?_ (fun p => ?_) p <;> intro hp
  · exact last_mem_cone _
  · exact (mem_cone (trace T) p).mpr ((mem_trace T p).mpr hp)

theorem subset_embed_trace {n : Nat} (T : Block (n+1)) :
    Subset (embed (trace T)) T := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact (mem_trace T q).mp hq

theorem subset_cone_trace {n : Nat} (T : Block (n+1))
    (h : Fin.last n ∈ T) : Subset (cone (trace T)) T := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact h
  · exact subset_embed_trace T p hp

/-- Exact point split: tests containing the new point become t-tests on A;
all other tests become (t+1)-tests on the mixed family A++B. -/
theorem covering_lift_iff {n t : Nat} (A B : Family n) :
    IsCovering (t+1) (lift A B) ↔
      IsCovering t A ∧ IsCovering (t+1) (A ++ B) := by
  constructor
  · intro h
    exact ⟨fun T hT => (covers_cone_iff A B T).mp (h _ (valid_cone T hT)),
      fun T hT => (covers_embed_iff A B T).mp (h _ (valid_embed T hT))⟩
  · rintro ⟨hA, hAB⟩ T hT
    by_cases hp : Fin.last n ∈ T
    · have hv : ValidBlock t (trace T) := by
        refine ⟨trace_nodup T hT.1, ?_⟩
        have := trace_length_present T hT.1 hp
        have := hT.2
        omega
      obtain ⟨U, hU, hsub⟩ := (covers_cone_iff A B (trace T)).mpr (hA _ hv)
      exact ⟨U, hU, subset_trans (subset_trace_cone T) hsub⟩
    · have hv : ValidBlock (t+1) (trace T) :=
        ⟨trace_nodup T hT.1, (trace_length_absent T hp).trans hT.2⟩
      obtain ⟨U, hU, hsub⟩ := (covers_embed_iff A B (trace T)).mpr (hAB _ hv)
      exact ⟨U, hU, subset_trans (subset_trace_embed T hp) hsub⟩

/-- Through-point traces and away-from-point traces, retaining occurrence order. -/
def through {n : Nat} (F : Family (n+1)) : Family n :=
  (F.filter (fun T => Fin.last n ∈ T)).map trace

def away {n : Nat} (F : Family (n+1)) : Family n :=
  (F.filter (fun T => Fin.last n ∉ T)).map trace

@[simp] theorem through_length {n : Nat} (F : Family (n+1)) :
    (through F).length = (F.filter (fun T => Fin.last n ∈ T)).length := by
  simp [through]

theorem split_length {n : Nat} (F : Family (n+1)) :
    (through F).length + (away F).length = F.length := by
  have h := (List.filter_append_perm
    (fun T : Block (n+1) => decide (Fin.last n ∈ T)) F).length_eq
  simpa [through, away] using h

theorem through_valid {n k : Nat} (F : Family (n+1))
    (hF : ∀ T, T ∈ F → ValidBlock (k+1) T) :
    ∀ T, T ∈ through F → ValidBlock k T := by
  intro T hT
  obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hT
  obtain ⟨hUF, hp⟩ := List.mem_filter.mp hU
  have hp : Fin.last n ∈ U := of_decide_eq_true hp
  have hv := hF U hUF
  refine ⟨trace_nodup U hv.1, ?_⟩
  have := trace_length_present U hv.1 hp
  have := hv.2
  omega

theorem away_valid {n k : Nat} (F : Family (n+1))
    (hF : ∀ T, T ∈ F → ValidBlock k T) :
    ∀ T, T ∈ away F → ValidBlock k T := by
  intro T hT
  obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hT
  obtain ⟨hUF, hp⟩ := List.mem_filter.mp hU
  have hp : Fin.last n ∉ U := of_decide_eq_true hp
  exact ⟨trace_nodup U (hF U hUF).1, (trace_length_absent U hp).trans (hF U hUF).2⟩

/-- Reconstructing the split is extensionally coverage-equivalent to F.
No row-size, sorting or distinctness premise is needed. -/
theorem covers_split_iff {n : Nat} (F : Family (n+1)) (T : Block (n+1)) :
    Covers (lift (through F) (away F)) T ↔ Covers F T := by
  constructor
  · rintro ⟨U, hU, hsub⟩
    rcases List.mem_append.mp hU with hA | hB
    · obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hA
      obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hV
      obtain ⟨hWF, hp⟩ := List.mem_filter.mp hW
      exact ⟨W, hWF, subset_trans hsub (subset_cone_trace W (of_decide_eq_true hp))⟩
    · obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hB
      obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hV
      exact ⟨W, (List.mem_filter.mp hW).1, subset_trans hsub (subset_embed_trace W)⟩
  · rintro ⟨U, hU, hsub⟩
    by_cases hp : Fin.last n ∈ U
    · refine ⟨cone (trace U), ?_, subset_trans hsub (subset_trace_cone U)⟩
      exact List.mem_append.mpr (Or.inl (List.mem_map_of_mem
        (List.mem_map_of_mem (List.mem_filter.mpr ⟨hU, by simpa using hp⟩))))
    · refine ⟨embed (trace U), ?_, subset_trans hsub (subset_trace_embed U hp)⟩
      exact List.mem_append.mpr (Or.inr (List.mem_map_of_mem
        (List.mem_map_of_mem (List.mem_filter.mpr ⟨hU, by simpa using hp⟩))))

theorem covering_split {n t : Nat} (F : Family (n+1))
    (hF : IsCovering (t+1) F) :
    IsCovering t (through F) ∧ IsCovering (t+1) (through F ++ away F) := by
  apply (covering_lift_iff (through F) (away F)).mp
  intro T hT
  exact (covers_split_iff F T).mpr (hF T hT)

/-- Global mixed-size route. Duplicate raw rows are allowed in this search
interface and are removed extensionally when producing a canonical Design. -/
def Mixed {n : Nat} (k t budget : Nat) (A B : Family n) : Prop :=
  A.length + B.length ≤ budget ∧
  (∀ T, T ∈ A → ValidBlock k T) ∧
  (∀ T, T ∈ B → ValidBlock (k+1) T) ∧
  IsCovering t A ∧ IsCovering (t+1) (A ++ B)

theorem design_to_mixed {n k t budget : Nat} (F : Family (n+1))
    (h : Design (k+1) (t+1) budget F) :
    Mixed k t budget (through F) (away F) := by
  refine ⟨?_, through_valid F h.1.2.1, away_valid F h.1.2.1, covering_split F h.2⟩
  rw [split_length]
  exact h.1.1

theorem mixed_to_design {n k t budget : Nat} (A B : Family n)
    (h : Mixed k t budget A B) : ∃ F : Family (n+1), Design (k+1) (t+1) budget F := by
  obtain ⟨F, hlen, hmem, hdist, hcov⟩ := exists_distinct_subcover (lift A B)
  refine ⟨F, ⟨?_, ?_, hdist⟩, ?_⟩
  · have hl : (lift A B).length = A.length + B.length := by simp [lift]
    rw [hl] at hlen
    exact Nat.le_trans hlen h.1
  · intro U hU
    rcases List.mem_append.mp (hmem U hU) with hA | hB
    · obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hA
      exact valid_cone V (h.2.1 V hV)
    · obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hB
      exact valid_embed V (h.2.2.1 V hV)
  · intro T hT
    exact (hcov T).mpr ((covering_lift_iff A B).mpr h.2.2.2 T hT)

/-- Unrestricted equivalence, with no fixed incumbent, row pool, or symmetry
hypothesis. Taking n=24,k=14,t=4,budget=41 is the original target. -/
theorem exists_design_iff_mixed {n k t budget : Nat} :
    (∃ F : Family (n+1), Design (k+1) (t+1) budget F) ↔
      ∃ A B : Family n, Mixed k t budget A B := by
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨through F, away F, design_to_mixed F hF⟩
  · rintro ⟨A, B, h⟩
    exact mixed_to_design A B h

end Covering.PointSplit
