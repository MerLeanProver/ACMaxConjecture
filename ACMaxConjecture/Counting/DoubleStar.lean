import ACMaxConjecture.Base

/-!
# Degree-class vocabulary

The final ACMAX proof uses only three vertex classes from the former double-star
development: degree-3 vertices, hubs of degree at least four, and degree-3
vertices having no degree-3 neighbour.
-/

namespace ACMax

open scoped Classical

variable {V : Type*} [Fintype V]

/-- Vertices of degree exactly three. -/
noncomputable def deg3Set (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter fun v => G.degree v = 3

theorem mem_deg3Set {G : SimpleGraph V} {v : V} :
    v ∈ deg3Set G ↔ G.degree v = 3 := by
  unfold deg3Set
  simp

/-- Vertices of degree at least four. -/
noncomputable def hubSet (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter fun v => 4 ≤ G.degree v

theorem mem_hubSet {G : SimpleGraph V} {v : V} :
    v ∈ hubSet G ↔ 4 ≤ G.degree v := by
  unfold hubSet
  simp

/-- Degree-3 vertices having no degree-3 neighbour. -/
noncomputable def isoTwins (G : SimpleGraph V) : Finset V :=
  (deg3Set G).filter fun t => ∀ w : V, G.Adj t w → G.degree w ≠ 3

theorem mem_isoTwins {G : SimpleGraph V} {t : V} :
    t ∈ isoTwins G ↔
      G.degree t = 3 ∧ ∀ w : V, G.Adj t w → G.degree w ≠ 3 := by
  unfold isoTwins deg3Set
  simp

end ACMax
