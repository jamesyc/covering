module
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
@[expose] public section

/-!
# Seven points in a class of six

The final counting step of Section 4.3.
-/
open Finset
namespace Covering.Quadruple
lemma exists_clean_neighborhood (N : Fin 20 → Finset (Fin 20))
    (hc : ∀ x, (N x).card = 6)
    (hs : ∀ x y, y ∈ N x ↔ x ∈ N y) (a b : Fin 20) :
    ∃ x, x ≠ a ∧ x ≠ b ∧ a ∉ N x ∧ b ∉ N x := by
  classical
  let bad : Finset (Fin 20) := ({a,b} ∪ N a) ∪ N b
  have hp : ({a,b} : Finset (Fin 20)).card ≤ 2 := by
    by_cases hab : a=b <;> simp [hab]
  have hbad : bad.card ≤ 14 := by
    have h1 := card_union_le ({a,b} ∪ N a) (N b)
    have h2 := card_union_le ({a,b} : Finset (Fin 20)) (N a)
    rw [hc] at h1 h2
    dsimp [bad]
    omega
  have hex : ∃ x : Fin 20, x ∉ bad := by
    by_contra hn
    have hall : (univ : Finset (Fin 20)) ⊆ bad := by
      intro x _
      by_contra hx
      exact hn ⟨x,hx⟩
    have h := card_le_card hall
    simp only [card_univ, Fintype.card_fin] at h
    omega
  obtain ⟨x,hx⟩ := hex
  have hxa : x ≠ a := by intro h; apply hx; simp [bad,h]
  have hxb : x ≠ b := by intro h; apply hx; simp [bad,h]
  have hna : x ∉ N a := by intro h; apply hx; simp [bad,h]
  have hnb : x ∉ N b := by intro h; apply hx; simp [bad,h]
  exact ⟨x,hxa,hxb,fun h => hna ((hs x a).mp h),fun h => hnb ((hs x b).mp h)⟩

/-- A six-regular graph on twenty points whose edges stay inside colour classes of
    size at most six, with two exceptional points, is impossible. -/
theorem local_seven_vs_six {C : Type*} [DecidableEq C]
    (N : Fin 20 → Finset (Fin 20))
    (hn : ∀ x, x ∉ N x) (hs : ∀ x y, y ∈ N x ↔ x ∈ N y)
    (hc : ∀ x, (N x).card=6) (a b : Fin 20) (color : Fin 20 → C)
    (hedge : ∀ x y, x ≠ a → x ≠ b → y ≠ a → y ≠ b →
      y ∈ N x → color x = color y)
    (hcap : ∀ c, (univ.filter (fun x => x ≠ a ∧ x ≠ b ∧ color x=c)).card ≤ 6) :
    False := by
  classical
  obtain ⟨x,hxa,hxb,hna,hnb⟩ := exists_clean_neighborhood N hc hs a b
  let S := insert x (N x)
  have hSc : S.card=7 := by simp [S, hn x, hc x]
  have hsub : S ⊆ univ.filter (fun y => y ≠ a ∧ y ≠ b ∧ color y=color x) := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact mem_filter.mpr ⟨mem_univ _,hxa,hxb,rfl⟩
    · have hya : y ≠ a := by intro h; subst y; exact hna hy
      have hyb : y ≠ b := by intro h; subst y; exact hnb hy
      exact mem_filter.mpr ⟨mem_univ _,hya,hyb,(hedge x y hxa hxb hya hyb hy).symm⟩
  have hle := (card_le_card hsub).trans (hcap (color x))
  omega

end Covering.Quadruple