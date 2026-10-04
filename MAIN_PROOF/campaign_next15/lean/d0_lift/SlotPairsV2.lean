import campaigns.async_goal.lean.d0.DerivativeV1

namespace Covering.SideLift

def pairDegree {n : Nat} (F : Family n) (p q : Fin n) : Nat :=
  (F.filter (fun R => p ∈ R ∧ q ∈ R)).length

/-- Inclusion-exclusion on actual row slots, without any distinct-row premise. -/
theorem pair_slots_lower {n : Nat} (F : Family n) (p q : Fin n) :
    PointDegree.degree F p+PointDegree.degree F q ≤ F.length+pairDegree F p q := by
  induction F with
  | nil => simp [PointDegree.degree,pairDegree]
  | cons R F ih =>
    by_cases hp : p ∈ R <;> by_cases hq : q ∈ R <;>
      simp [PointDegree.degree,pairDegree,hp,hq] at * <;> omega

theorem degree_filtered_eq_pair {n : Nat} (F : Family n) (p q : Fin n) :
    PointDegree.degree (F.filter (fun R => p ∈ R)) q=pairDegree F p q := by
  induction F with
  | nil => simp [PointDegree.degree,pairDegree]
  | cons R F ih =>
    by_cases hp : p ∈ R <;> by_cases hq : q ∈ R <;>
      simp_all [PointDegree.degree,pairDegree]

theorem pair_degree_relabel {n : Nat} (e d : Fin n → Fin n)
    (hde : ∀ p, d (e p)=p) (hed : ∀ p, e (d p)=p)
    (F : Family n) (p q : Fin n) :
    pairDegree (relabelFamily e F) p q=pairDegree F (d p) (d q) := by
  simp only [pairDegree,relabelFamily,List.filter_map,List.length_map]
  congr 1
  apply congrArg (fun f => F.filter f)
  funext R
  simp only [Function.comp_apply,mem_relabelBlock_iff e d hde hed R p,
    mem_relabelBlock_iff e d hde hed R q]

theorem degree_through {n : Nat} (F : Family (n+1)) (p : Fin n) :
    PointDegree.degree (PointSplit.through F) p=pairDegree F (Fin.last n) p.castSucc := by
  unfold PointDegree.degree PointSplit.through
  rw [List.filter_map,List.length_map]
  simp only [Function.comp_def,PointSplit.mem_trace]
  exact degree_filtered_eq_pair F (Fin.last n) p.castSucc

theorem through_append {n : Nat} (F G : Family (n+1)) :
    PointSplit.through (F++G)=PointSplit.through F++PointSplit.through G := by
  simp [PointSplit.through,List.filter_append,List.map_append]

theorem pointwise_eq_of_sum_le {α : Type} (L : List α) (f g : α → Nat)
    (hle : ∀ x, x ∈ L → f x ≤ g x) (hs : (L.map g).sum ≤ (L.map f).sum) :
    ∀ x, x ∈ L → f x=g x := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha : f a ≤ g a := hle a (by simp)
    have htail : ∀ x, x ∈ L → f x ≤ g x := fun x hx => hle x (by simp [hx])
    have ht := Weighted.sum_map_le L f g htail
    simp only [List.map_cons,List.sum_cons] at hs
    have hae : f a=g a := by omega
    have hrest : (L.map g).sum ≤ (L.map f).sum := by omega
    intro x hx
    rcases List.mem_cons.mp hx with he | hx
    · subst x
      exact hae
    · exact ih htail hrest x hx

end Covering.SideLift
