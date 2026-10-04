module

public import rounds.round_16.lean.TwoPointSplit

@[expose] public section

/-! New 2026-10-03 source. Generic physical slot-degree identities needed to
retain actual common minimum pivots through the three exact point splits. -/
namespace Covering.NormalizedBridge20261003

open PointSplit PointDegree

def MinimumAt {n : Nat} (F : Family n) (p : Fin n) : Prop :=
  ∀ q, degree F p ≤ degree F q

theorem fin_minimum_exists (n : Nat) (f : Fin (n+1) → Nat) :
    ∃ p, ∀ q, f p ≤ f q := by
  induction n with
  | zero =>
    refine ⟨0,?_⟩
    intro q
    have hq : q=0 := Fin.ext (by omega)
    rw [hq]
    exact Nat.le_refl _
  | succ n ih =>
    obtain ⟨p,hp⟩ := ih (fun q => f q.castSucc)
    by_cases h : f (Fin.last (n+1)) ≤ f p.castSucc
    · refine ⟨Fin.last (n+1),?_⟩
      intro q
      exact Fin.lastCases (Nat.le_refl _) (fun q => Nat.le_trans h (hp q)) q
    · refine ⟨p.castSucc,?_⟩
      intro q
      exact Fin.lastCases (by omega) hp q

theorem minimum_exists {n : Nat} (F : Family (n+1)) :
    ∃ p, MinimumAt F p := fin_minimum_exists n (degree F)

@[simp] theorem filter_true {α : Type} (L : List α) : L.filter (fun _ => true)=L :=
  List.filter_eq_self.mpr (fun _ _ => rfl)

@[simp] theorem filter_false {α : Type} (L : List α) : L.filter (fun _ => false)=[] :=
  List.filter_eq_nil_iff.mpr (fun _ _ => by simp)

theorem degree_append {n : Nat} (A B : Family n) (p : Fin n) :
    degree (A++B) p=degree A p+degree B p := by
  simp [degree,List.filter_append]

theorem degree_split_old {n : Nat} (F : Family (n+1)) (p : Fin n) :
    degree (through F) p+degree (away F) p=degree F p.castSucc := by
  induction F with
  | nil => simp [degree,through,away]
  | cons R F ih =>
    by_cases hl : Fin.last n ∈ R <;> by_cases hp : p.castSucc ∈ R <;>
      simp [degree,through,away,List.filter_cons,hl,hp,mem_trace,Nat.add_assoc,
        Nat.add_comm,Nat.add_left_comm] at ih ⊢ <;> omega

theorem degree_lift_last {n : Nat} (A B : Family n) :
    degree (lift A B) (Fin.last n)=A.length := by
  simp [degree,lift,List.filter_append,List.filter_map,Function.comp_def]

theorem degree_lift_old {n : Nat} (A B : Family n) (p : Fin n) :
    degree (lift A B) p.castSucc=degree A p+degree B p := by
  simp [degree,lift,List.filter_append,List.filter_map,Function.comp_def]

theorem minimum_incidence_bound {n k : Nat} (F : Family n) (p : Fin n)
    (hp : MinimumAt F p) (hrows : ∀ R, R ∈ F → R.length≤k) :
    n*degree F p≤k*F.length := by
  have hlo := Weighted.sum_map_le (List.finRange n) (fun _ => degree F p)
    (degree F) (fun q _ => hp q)
  have hi := incidence_le F
  have hu := Weighted.sum_map_le_length_mul F List.length k hrows
  simp only [sum_map_const,List.length_finRange] at hlo
  rw [Nat.mul_comm k F.length]
  omega

theorem minimum_relabel {n : Nat} (F : Family n) (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p)=p) (hed : ∀ p, e (d p)=p) (p : Fin n)
    (hp : MinimumAt F p) : MinimumAt (relabelFamily e F) (e p) := by
  intro q
  rw [degree_relabel e d hde hed,degree_relabel e d hde hed,hde]
  exact hp (d q)

theorem min_normalize_last {n : Nat} (F : Family (n+1)) :
    ∃ e : Fin (n+1) → Fin (n+1), (∀ p, e (e p)=p) ∧
      MinimumAt (relabelFamily e F) (Fin.last n) := by
  obtain ⟨p,hp⟩ := minimum_exists F
  let e := swapPoint p (Fin.last n)
  have he : ∀ q, e (e q)=q := swapPoint_involutive p (Fin.last n)
  refine ⟨e,he,?_⟩
  intro q
  rw [degree_relabel e e he he,degree_relabel e e he he]
  have hp' : e (Fin.last n)=p := swapPoint_right p (Fin.last n)
  rw [hp']
  exact hp (e q)

end Covering.NormalizedBridge20261003
