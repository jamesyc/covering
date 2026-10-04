import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
A local, census-free connectivity theorem. The proof explicitly reroutes a walk
around a deleted set of size at most two. It does not use the Petersen graph's
uniqueness, a classification of small graphs, or spectral graph theory.
-/
namespace SmallCutConnectivity
open SimpleGraph
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Minimum degree three leaves a neighbor outside any two forbidden vertices. -/
lemma neighbor_outside (hd : ∀ x, 3 ≤ G.degree x) (R : Finset V)
    (hR : R.card ≤ 2) (x : V) : ∃ a, G.Adj x a ∧ a ∉ R := by
  classical
  have hc : R.card < (G.neighborFinset x).card := by
    rw [G.card_neighborFinset_eq_degree]
    exact lt_of_le_of_lt hR (lt_of_lt_of_le (by decide : 2 < 3) (hd x))
  obtain ⟨a, ha, har⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨a, (G.mem_neighborFinset x a).mp ha, har⟩

omit [Fintype V] in
/-- In a set of size at most two, deleting one member leaves at most one. -/
lemma same_other_deleted (R : Finset V) (hR : R.card ≤ 2)
    {w z t : V} (hw : w ∈ R) (hz : z ∈ R) (ht : t ∈ R)
    (hzw : z ≠ w) (htw : t ≠ w) : t = z := by
  classical
  have hc : (R.erase w).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hw]
    omega
  exact (Finset.card_le_one.mp hc) t (Finset.mem_erase.mpr ⟨htw, ht⟩)
    z (Finset.mem_erase.mpr ⟨hzw, hz⟩)

/-- Triangle-free graphs of minimum degree three in which distinct nonadjacent
vertices have exactly one common neighbor remain preconnected after deleting
at most two vertices. No bound on the number of vertices is needed. -/
theorem preconnected_delete_le_two
    (hd : ∀ x, 3 ≤ G.degree x)
    (htri : ∀ {x y z}, G.Adj x y → G.Adj x z → G.Adj y z → False)
    (hcommon : ∀ x y, x ≠ y → ¬G.Adj x y → ∃! z, G.Adj x z ∧ G.Adj y z)
    (R : Finset V) (hR : R.card ≤ 2) :
    (G.induce {x | x ∉ R}).Preconnected := by
  classical
  let H := G.induce {x | x ∉ R}
  have edge {a b : V} (ha : a ∉ R) (hb : b ∉ R) (hab : G.Adj a b) :
      H.Reachable ⟨a, ha⟩ ⟨b, hb⟩ := SimpleGraph.Adj.reachable hab
  intro u v
  by_contra hnr
  have huv : (u : V) ≠ v := by
    intro he
    have : u = v := Subtype.ext he
    subst v
    exact hnr SimpleGraph.Reachable.rfl
  have hnuv : ¬G.Adj u v := fun h => hnr (edge u.property v.property h)
  obtain ⟨w, ⟨huw, hvw⟩, hwunique⟩ := hcommon u v huv hnuv
  have hwR : w ∈ R := by
    by_contra hw
    exact hnr ((edge u.property hw huw).trans (edge hw v.property hvw.symm))
  obtain ⟨a, hua, haR⟩ := neighbor_outside G hd R hR u
  have haw : a ≠ w := fun he => haR (he.symm ▸ hwR)
  have hav : a ≠ v := by
    intro he
    exact hnuv (he ▸ hua)
  have hnav : ¬G.Adj a v := by
    intro hav'
    exact haw (hwunique a ⟨hua, hav'.symm⟩)
  obtain ⟨z, ⟨haz, hvz⟩, _⟩ := hcommon a v hav hnav
  have hzR : z ∈ R := by
    by_contra hz
    exact hnr ((edge u.property haR hua).trans
      ((edge haR hz haz).trans (edge hz v.property hvz.symm)))
  have hzw : z ≠ w := by
    intro he
    exact htri hua huw (he ▸ haz)
  have other : ∀ t ∈ R, t ≠ w → t = z :=
    fun t ht htw => same_other_deleted R hR hwR hzR ht hzw htw
  obtain ⟨b, hub, hb⟩ := neighbor_outside G hd {w, a} Finset.card_le_two u
  have hb' : b ≠ w ∧ b ≠ a := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hb
  have hbw : b ≠ w := hb'.1
  have hba : b ≠ a := hb'.2
  have hbz : b ≠ z := by
    intro he
    exact htri hua (he ▸ hub) haz
  have hbR : b ∉ R := fun hb' => hbz (other b hb' hbw)
  have hbv : b ≠ v := by
    intro he
    exact hnuv (he ▸ hub)
  have hnbv : ¬G.Adj b v := by
    intro hbv'
    exact hbw (hwunique b ⟨hub, hbv'.symm⟩)
  obtain ⟨t, ⟨hbt, hvt⟩, _⟩ := hcommon b v hbv hnbv
  have htR : t ∈ R := by
    by_contra ht
    exact hnr ((edge u.property hbR hub).trans
      ((edge hbR ht hbt).trans (edge ht v.property hvt.symm)))
  have htw : t ≠ w := by
    intro he
    exact htri hub huw (he ▸ hbt)
  have htz : t = z := other t htR htw
  have hnab : ¬G.Adj a b := fun hab => htri hua hub hab
  obtain ⟨c, _, hcunique⟩ := hcommon a b hba.symm hnab
  have huc : (u : V) = c := hcunique u ⟨hua.symm, hub.symm⟩
  have hzc : z = c := hcunique z ⟨haz, htz ▸ hbt⟩
  exact u.property ((huc.trans hzc.symm).symm ▸ hzR)

/-- The actual connectivity conclusion, including nonemptiness of the remainder. -/
theorem connected_delete_le_two [Nonempty V]
    (hd : ∀ x, 3 ≤ G.degree x)
    (htri : ∀ {x y z}, G.Adj x y → G.Adj x z → G.Adj y z → False)
    (hcommon : ∀ x y, x ≠ y → ¬G.Adj x y → ∃! z, G.Adj x z ∧ G.Adj y z)
    (R : Finset V) (hR : R.card ≤ 2) :
    (G.induce {x | x ∉ R}).Connected := by
  obtain ⟨x⟩ := ‹Nonempty V›
  obtain ⟨a, _, ha⟩ := neighbor_outside G hd R hR x
  let : Nonempty {x : V | x ∉ R} := ⟨⟨a, ha⟩⟩
  exact ⟨preconnected_delete_le_two G hd htri hcommon R hR⟩

/-- Exact interface for the ten-class quotient graph in the covering argument.
`∃!` is the statement that the common-neighbor set has exactly one element. -/
theorem cubic_ten_connected_delete_le_two
    (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (hdegree : ∀ x, G.degree x = 3)
    (hadj : ∀ x y, G.Adj x y → G.commonNeighbors x y = ∅)
    (hnonadj : ∀ x y, x ≠ y → ¬G.Adj x y → ∃! z, z ∈ G.commonNeighbors x y)
    (R : Finset (Fin 10)) (hR : R.card ≤ 2) :
    (G.induce {x | x ∉ R}).Connected := by
  apply connected_delete_le_two G (fun x => (hdegree x).ge) ?_ ?_ R hR
  · intro x y z hxy hxz hyz
    have hm : z ∈ G.commonNeighbors x y := ⟨hxz, hyz⟩
    rw [hadj x y hxy] at hm
    exact hm
  · exact hnonadj

#print axioms SmallCutConnectivity.neighbor_outside
#print axioms SmallCutConnectivity.same_other_deleted
#print axioms SmallCutConnectivity.preconnected_delete_le_two
#print axioms SmallCutConnectivity.connected_delete_le_two
#print axioms SmallCutConnectivity.cubic_ten_connected_delete_le_two
end SmallCutConnectivity
