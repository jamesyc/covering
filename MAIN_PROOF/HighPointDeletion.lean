module

public import SmallCutColorConsequence

@[expose] public section

/-! Canonical deletion of all quotient classes meeting either high physical
point, using the same physical pairing equivalence throughout. -/
namespace HighPointDeletion
open SimpleGraph SmallCutColorConsequence

/-- Only physical points other than the two named high points are counted. -/
def lowSupport (a b : Fin 20) : Finset (Fin 20) :=
  Finset.univ.filter (fun p => p ≠ a ∧ p ≠ b)

/-- The two high points may occupy one class or two different classes. -/
def removedClasses (e : (Fin 10 × Fin 2) ≃ Fin 20) (a b : Fin 20) : Finset (Fin 10) :=
  {(e.symm a).1, (e.symm b).1}

abbrev SurvivingClasses (e : (Fin 10 × Fin 2) ≃ Fin 20) (a b : Fin 20) :=
  {i : Fin 10 // i ∉ removedClasses e a b}

lemma removed_card_le_two (e : (Fin 10 × Fin 2) ≃ Fin 20) (a b : Fin 20) :
    (removedClasses e a b).card ≤ 2 := Finset.card_le_two

lemma surviving_classes_ge_eight (e : (Fin 10 × Fin 2) ≃ Fin 20) (a b : Fin 20) :
    8 ≤ Fintype.card (SurvivingClasses e a b) :=
  eight_survive (removedClasses e a b) (removed_card_le_two e a b)

/-- The one canonical physical map on surviving class/index pairs. -/
def survivingMap (e : (Fin 10 × Fin 2) ≃ Fin 20) (a b : Fin 20)
    (x : SurvivingClasses e a b × Fin 2) : Fin 20 := e (x.1.val, x.2)

lemma survivingMap_injective (e : (Fin 10 × Fin 2) ≃ Fin 20) (a b : Fin 20) :
    Function.Injective (survivingMap e a b) := by
  intro x y h
  have hp : (x.1.val, x.2) = (y.1.val, y.2) := e.injective h
  exact Prod.ext (Subtype.ext (congrArg (fun p : Fin 10 × Fin 2 => p.1) hp))
    (congrArg (fun p : Fin 10 × Fin 2 => p.2) hp)

/-- Both physical points of every surviving class are genuinely low. -/
lemma survivingMap_mem_low (e : (Fin 10 × Fin 2) ≃ Fin 20) (a b : Fin 20)
    (x : SurvivingClasses e a b × Fin 2) : survivingMap e a b x ∈ lowSupport a b := by
  have hclass (p : Fin 20) (h : survivingMap e a b x = p) :
      x.1.val = (e.symm p).1 := by
    simpa [survivingMap] using congrArg (fun p : Fin 20 => (e.symm p).1) h
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro h
    apply x.1.property
    exact Finset.mem_insert.mpr (Or.inl (hclass a h))
  · intro h
    apply x.1.property
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (hclass b h)))

/-- The canonical image contains at least sixteen distinct low points. -/
lemma surviving_image_ge_sixteen (e : (Fin 10 × Fin 2) ≃ Fin 20) (a b : Fin 20) :
    16 ≤ ((Finset.univ : Finset (SurvivingClasses e a b × Fin 2)).image
      (survivingMap e a b)).card := by
  rw [Finset.card_image_of_injective _ (survivingMap_injective e a b), Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin]
  have h := surviving_classes_ge_eight e a b
  omega

/-- With the matrix-derived graph premises, every surviving class has a
surviving neighbor. This supplies within-class color equality later. -/
lemma every_survivor_has_neighbor (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (hdegree : ∀ x, G.degree x = 3)
    (hadj : ∀ x y, G.Adj x y → G.commonNeighbors x y = ∅)
    (hnonadj : ∀ x y, x ≠ y → ¬G.Adj x y → ∃! z, z ∈ G.commonNeighbors x y)
    (e : (Fin 10 × Fin 2) ≃ Fin 20) (a b : Fin 20)
    (u : SurvivingClasses e a b) : ∃ v : SurvivingClasses e a b, G.Adj u v :=
  survivor_has_neighbor G hdegree hadj hnonadj (removedClasses e a b)
    (removed_card_le_two e a b) u

/-- A total physical color may be arbitrary on the high points. Edge equality
is required for all cross-endpoint physical pairs; no pre-existing class color
or within-class equality is assumed. -/
theorem physical_colors_monochromatic {C : Type*} [DecidableEq C]
    (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (hdegree : ∀ x, G.degree x = 3)
    (hadj : ∀ x y, G.Adj x y → G.commonNeighbors x y = ∅)
    (hnonadj : ∀ x y, x ≠ y → ¬G.Adj x y → ∃! z, z ∈ G.commonNeighbors x y)
    (e : (Fin 10 × Fin 2) ≃ Fin 20) (a b : Fin 20) (c : Fin 20 → C)
    (hedge : ∀ u v : SurvivingClasses e a b, G.Adj u v → ∀ i j,
      c (survivingMap e a b (u, i)) = c (survivingMap e a b (v, j))) :
    ∃ k, (∀ x, c (survivingMap e a b x) = k) ∧
      16 ≤ ((lowSupport a b).filter fun p => c p = k).card :=
  cubic_ten_fiber_monochromatic G hdegree hadj hnonadj
    (removedClasses e a b) (removed_card_le_two e a b) (lowSupport a b)
    (survivingMap e a b) (survivingMap_injective e a b) (survivingMap_mem_low e a b) c hedge

/-- The exact high-deletion/physical-color capacity consumer. -/
theorem physical_color_capacity_impossible {C : Type*} [DecidableEq C]
    (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (hdegree : ∀ x, G.degree x = 3)
    (hadj : ∀ x y, G.Adj x y → G.commonNeighbors x y = ∅)
    (hnonadj : ∀ x y, x ≠ y → ¬G.Adj x y → ∃! z, z ∈ G.commonNeighbors x y)
    (e : (Fin 10 × Fin 2) ≃ Fin 20) (a b : Fin 20) (c : Fin 20 → C)
    (hedge : ∀ u v : SurvivingClasses e a b, G.Adj u v → ∀ i j,
      c (survivingMap e a b (u, i)) = c (survivingMap e a b (v, j)))
    (hcap : ∀ k, ((lowSupport a b).filter fun p => c p = k).card ≤ 6) : False :=
  cubic_ten_color_capacity_impossible G hdegree hadj hnonadj
    (removedClasses e a b) (removed_card_le_two e a b) (lowSupport a b)
    (survivingMap e a b) (survivingMap_injective e a b) (survivingMap_mem_low e a b) c hedge hcap

#print axioms HighPointDeletion.removed_card_le_two
#print axioms HighPointDeletion.surviving_classes_ge_eight
#print axioms HighPointDeletion.survivingMap_injective
#print axioms HighPointDeletion.survivingMap_mem_low
#print axioms HighPointDeletion.surviving_image_ge_sixteen
#print axioms HighPointDeletion.every_survivor_has_neighbor
#print axioms HighPointDeletion.physical_colors_monochromatic
#print axioms HighPointDeletion.physical_color_capacity_impossible
end HighPointDeletion
