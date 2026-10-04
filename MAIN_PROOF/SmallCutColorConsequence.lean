import SmallCutConnectivity
import Mathlib.Data.Fintype.Prod

/-!
Color propagation for the physical two-point fibers over surviving graph
vertices. The low-point support is explicit: no color-capacity hypothesis is
imposed on physical points outside it.
-/
namespace SmallCutColorConsequence
open SimpleGraph SmallCutConnectivity

/-- The exact count of surviving quotient classes. -/
theorem survivor_card (R : Finset (Fin 10)) :
    Fintype.card {x : Fin 10 // x ∉ R} = 10 - R.card := by
  simpa only [Fintype.card_fin, Fintype.card_coe] using
    (Fintype.card_subtype_compl (fun x : Fin 10 => x ∈ R))

theorem eight_survive (R : Finset (Fin 10)) (hR : R.card ≤ 2) :
    8 ≤ Fintype.card {x : Fin 10 // x ∉ R} := by
  rw [survivor_card]
  omega

theorem survivor_nontrivial (R : Finset (Fin 10)) (hR : R.card ≤ 2) :
    Nontrivial {x : Fin 10 // x ∉ R} := by
  apply Fintype.one_lt_card_iff_nontrivial.mp
  have := eight_survive R hR
  omega

/-- Every surviving class has a surviving neighbor, including after no deletions. -/
theorem survivor_has_neighbor (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (hdegree : ∀ x, G.degree x = 3)
    (hadj : ∀ x y, G.Adj x y → G.commonNeighbors x y = ∅)
    (hnonadj : ∀ x y, x ≠ y → ¬G.Adj x y → ∃! z, z ∈ G.commonNeighbors x y)
    (R : Finset (Fin 10)) (hR : R.card ≤ 2)
    (u : {x : Fin 10 // x ∉ R}) :
    ∃ v : {x : Fin 10 // x ∉ R}, G.Adj u v := by
  let : Nontrivial ({x : Fin 10 | x ∉ R} : Set (Fin 10)) := survivor_nontrivial R hR
  exact (cubic_ten_connected_delete_le_two G hdegree hadj hnonadj R hR).preconnected.exists_adj_of_nontrivial u

/-- Edgewise equality propagates along an actual graph walk. -/
theorem color_eq_of_reachable {V C : Type*} {G : SimpleGraph V} (c : V → C)
    (hedge : ∀ u v, G.Adj u v → c u = c v) {u v : V}
    (h : G.Reachable u v) : c u = c v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | @cons a b d hab w ih => exact (hedge a b hab).trans ih

/-- All cross-endpoint fiber colors agreeing on every edge makes every fiber
monochromatic and all fibers agree, provided the connected graph is nontrivial.
The index type I may be arbitrary. -/
theorem edge_forces_fiber_monochromatic {V I C : Type*} [Nontrivial V]
    (G : SimpleGraph V) (hG : G.Connected) (c : V × I → C)
    (hedge : ∀ u v, G.Adj u v → ∀ i j, c (u, i) = c (v, j)) :
    ∀ p q, c p = c q := by
  intro p q
  have hsame (u : V) (i j : I) : c (u, i) = c (u, j) := by
    obtain ⟨v, huv⟩ := hG.preconnected.exists_adj_of_nontrivial u
    exact (hedge u v huv i j).trans (hedge u v huv j j).symm
  have hpath : c (p.1, p.2) = c (q.1, p.2) :=
    color_eq_of_reachable (fun u => c (u, p.2))
      (fun u v huv => hedge u v huv p.2 p.2) (hG p.1 q.1)
  exact hpath.trans (hsame q.1 p.2 q.2)

/-- Explicitly injective two-point fibers in a low-point support occupy one
color fiber, whose cardinality is at least twice the number of classes. -/
theorem physical_fiber_monochromatic {V P C : Type*} [Fintype V] [Nontrivial V]
    [DecidableEq C] (G : SimpleGraph V) (hG : G.Connected)
    (L : Finset P) (f : V × Fin 2 → P) (hf : Function.Injective f)
    (hL : ∀ x, f x ∈ L) (c : P → C)
    (hedge : ∀ u v, G.Adj u v → ∀ i j, c (f (u, i)) = c (f (v, j))) :
    ∃ k, (∀ x, c (f x) = k) ∧
      Fintype.card V * 2 ≤ (L.filter fun p => c p = k).card := by
  classical
  let : Nonempty V := hG.nonempty
  let x0 : V × Fin 2 := (Classical.arbitrary V, 0)
  have hc : ∀ x, c (f x) = c (f x0) :=
    fun x => edge_forces_fiber_monochromatic G hG (fun x => c (f x)) hedge x x0
  refine ⟨c (f x0), hc, ?_⟩
  have hcount : (Finset.univ : Finset (V × Fin 2)).card ≤
      (L.filter fun p => c p = c (f x0)).card :=
    Finset.card_le_card_of_injOn f
      (fun x _ => Finset.mem_filter.mpr ⟨hL x, hc x⟩)
      (fun _ _ _ _ he => hf he)
  simpa using hcount

/-- The surviving physical points are all one color, and at least sixteen
points of the explicitly supplied low-point support have that color. -/
theorem cubic_ten_fiber_monochromatic {P C : Type*} [DecidableEq C]
    (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (hdegree : ∀ x, G.degree x = 3)
    (hadj : ∀ x y, G.Adj x y → G.commonNeighbors x y = ∅)
    (hnonadj : ∀ x y, x ≠ y → ¬G.Adj x y → ∃! z, z ∈ G.commonNeighbors x y)
    (R : Finset (Fin 10)) (hR : R.card ≤ 2)
    (L : Finset P) (f : {x : Fin 10 // x ∉ R} × Fin 2 → P)
    (hf : Function.Injective f) (hL : ∀ x, f x ∈ L) (c : P → C)
    (hedge : ∀ u v : {x : Fin 10 // x ∉ R}, G.Adj u v →
      ∀ i j, c (f (u, i)) = c (f (v, j))) :
    ∃ k, (∀ x, c (f x) = k) ∧ 16 ≤ (L.filter fun p => c p = k).card := by
  let : Nontrivial ({x : Fin 10 | x ∉ R} : Set (Fin 10)) := survivor_nontrivial R hR
  obtain ⟨k, hmono, hk⟩ := physical_fiber_monochromatic
    (G.induce {x | x ∉ R})
    (cubic_ten_connected_delete_le_two G hdegree hadj hnonadj R hR)
    L f hf hL c hedge
  have hn := eight_survive R hR
  have hc : Fintype.card ({x : Fin 10 | x ∉ R} : Set (Fin 10)) =
      Fintype.card {x : Fin 10 // x ∉ R} := Fintype.card_congr (Equiv.refl _)
  rw [hc] at hk
  exact ⟨k, hmono, by omega⟩

/-- The omission-color contradiction in the gadget branch. Only low points
belonging to L are counted; no bound is assumed for the two high points. -/
theorem cubic_ten_color_capacity_impossible {P C : Type*} [DecidableEq C]
    (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (hdegree : ∀ x, G.degree x = 3)
    (hadj : ∀ x y, G.Adj x y → G.commonNeighbors x y = ∅)
    (hnonadj : ∀ x y, x ≠ y → ¬G.Adj x y → ∃! z, z ∈ G.commonNeighbors x y)
    (R : Finset (Fin 10)) (hR : R.card ≤ 2)
    (L : Finset P) (f : {x : Fin 10 // x ∉ R} × Fin 2 → P)
    (hf : Function.Injective f) (hL : ∀ x, f x ∈ L) (c : P → C)
    (hedge : ∀ u v : {x : Fin 10 // x ∉ R}, G.Adj u v →
      ∀ i j, c (f (u, i)) = c (f (v, j)))
    (hcap : ∀ k, (L.filter fun p => c p = k).card ≤ 6) : False := by
  obtain ⟨k, _, hk⟩ := cubic_ten_fiber_monochromatic
    G hdegree hadj hnonadj R hR L f hf hL c hedge
  have := hcap k
  omega

#print axioms SmallCutColorConsequence.survivor_card
#print axioms SmallCutColorConsequence.eight_survive
#print axioms SmallCutColorConsequence.survivor_nontrivial
#print axioms SmallCutColorConsequence.survivor_has_neighbor
#print axioms SmallCutColorConsequence.color_eq_of_reachable
#print axioms SmallCutColorConsequence.edge_forces_fiber_monochromatic
#print axioms SmallCutColorConsequence.physical_fiber_monochromatic
#print axioms SmallCutColorConsequence.cubic_ten_fiber_monochromatic
#print axioms SmallCutColorConsequence.cubic_ten_color_capacity_impossible
end SmallCutColorConsequence
