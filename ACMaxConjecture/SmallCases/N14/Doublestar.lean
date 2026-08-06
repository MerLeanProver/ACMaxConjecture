import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N14.Core
import ACMaxConjecture.SmallCases.N14.Align

/-!
# Double-star leaves for the single-twin alignment (`n = 14`)

This file supplies the dominating-double-star helpers feeding `single_twin_config` (in
`TwinCert14Align`).  One lemma:

* `dom_doublestar_leaves` — from a dominating edge whose two centres both have in-`M`-degree `3`,
  extracts the four degree-`3` leaves with their single-centre `D`-neighbourhood.
-/

namespace ACMax

open scoped Classical

namespace N14

/-- **Double-star leaf extraction.**  When the dominating edge `{c₁, c₂}` has both centres of
in-`M`-degree exactly `3`, the degree-`3` subgraph `M` is a double star: `c₁` carries two leaves
`ℓ₁, ℓ₂` (its `D`-neighbours besides `c₂`) and `c₂` two leaves `ℓ₃, ℓ₄`.  Each leaf's only
`D`-neighbour is its own centre (`hdom` plus the triangle bound `hT` forbidding the leaf reaching
the opposite centre), the six vertices are pairwise distinct, and each leaf misses the opposite
centre. -/
theorem dom_doublestar_leaves (G : SimpleGraph (Fin 14)) (D : Finset (Fin 14))
    (hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (c₁ c₂ : Fin 14) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 3) (hin2 : (G.neighborFinset c₂ ∩ D).card = 3)
    (hdom : ∀ p q : Fin 14, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂) :
    ∃ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Fin 14,
      G.degree ℓ₁ = 3 ∧ G.degree ℓ₂ = 3 ∧ G.degree ℓ₃ = 3 ∧ G.degree ℓ₄ = 3 ∧
      ({c₁, c₂, ℓ₁, ℓ₂, ℓ₃, ℓ₄} : Finset (Fin 14)).card = 6 ∧
      G.Adj c₁ ℓ₁ ∧ G.Adj c₁ ℓ₂ ∧ G.Adj c₂ ℓ₃ ∧ G.Adj c₂ ℓ₄ ∧
      G.neighborFinset ℓ₁ ∩ D = {c₁} ∧ G.neighborFinset ℓ₂ ∩ D = {c₁} ∧
      G.neighborFinset ℓ₃ ∩ D = {c₂} ∧ G.neighborFinset ℓ₄ ∩ D = {c₂} ∧
      ¬G.Adj ℓ₁ c₂ ∧ ¬G.Adj ℓ₂ c₂ ∧ ¬G.Adj ℓ₃ c₁ ∧ ¬G.Adj ℓ₄ c₁ ∧
      ℓ₁ ≠ ℓ₂ ∧ ℓ₃ ≠ ℓ₄ := by
  classical
  have hc1deg : G.degree c₁ = 3 := (hmemD c₁).mp hc1D
  have hc2deg : G.degree c₂ = 3 := (hmemD c₂).mp hc2D
  have hc2mem1 : c₂ ∈ G.neighborFinset c₁ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
  have hc1mem2 : c₁ ∈ G.neighborFinset c₂ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
  have herase1 : ((G.neighborFinset c₁ ∩ D).erase c₂).card = 2 := by
    rw [Finset.card_erase_of_mem hc2mem1, hin1]
  have herase2 : ((G.neighborFinset c₂ ∩ D).erase c₁).card = 2 := by
    rw [Finset.card_erase_of_mem hc1mem2, hin2]
  obtain ⟨ℓ₁, ℓ₂, hℓ12, hℓset1⟩ := Finset.card_eq_two.mp herase1
  obtain ⟨ℓ₃, ℓ₄, hℓ34, hℓset2⟩ := Finset.card_eq_two.mp herase2
  have hmem1 : ∀ w : Fin 14, w = ℓ₁ ∨ w = ℓ₂ →
      w ≠ c₂ ∧ G.Adj c₁ w ∧ G.degree w = 3 := by
    intro w hw
    have hwe : w ∈ (G.neighborFinset c₁ ∩ D).erase c₂ := by
      rw [hℓset1]; rcases hw with rfl | rfl <;> simp
    rw [Finset.mem_erase] at hwe
    obtain ⟨hwc2, hwND⟩ := hwe
    obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hwND
    exact ⟨hwc2, (G.mem_neighborFinset _ _).mp hwN, (hmemD w).mp hwD⟩
  have hmem2 : ∀ w : Fin 14, w = ℓ₃ ∨ w = ℓ₄ →
      w ≠ c₁ ∧ G.Adj c₂ w ∧ G.degree w = 3 := by
    intro w hw
    have hwe : w ∈ (G.neighborFinset c₂ ∩ D).erase c₁ := by
      rw [hℓset2]; rcases hw with rfl | rfl <;> simp
    rw [Finset.mem_erase] at hwe
    obtain ⟨hwc1, hwND⟩ := hwe
    obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hwND
    exact ⟨hwc1, (G.mem_neighborFinset _ _).mp hwN, (hmemD w).mp hwD⟩
  obtain ⟨h1c2, ha1, hd1⟩ := hmem1 ℓ₁ (Or.inl rfl)
  obtain ⟨h2c2, ha2, hd2⟩ := hmem1 ℓ₂ (Or.inr rfl)
  obtain ⟨h3c1, ha3, hd3⟩ := hmem2 ℓ₃ (Or.inl rfl)
  obtain ⟨h4c1, ha4, hd4⟩ := hmem2 ℓ₄ (Or.inr rfl)
  have hℓ1D : ℓ₁ ∈ D := (hmemD ℓ₁).mpr hd1
  have hℓ2D : ℓ₂ ∈ D := (hmemD ℓ₂).mpr hd2
  have hℓ3D : ℓ₃ ∈ D := (hmemD ℓ₃).mpr hd3
  have hℓ4D : ℓ₄ ∈ D := (hmemD ℓ₄).mpr hd4
  have hℓ1c1 : ℓ₁ ≠ c₁ := (G.ne_of_adj ha1).symm
  have hℓ2c1 : ℓ₂ ≠ c₁ := (G.ne_of_adj ha2).symm
  have hℓ3c2 : ℓ₃ ≠ c₂ := (G.ne_of_adj ha3).symm
  have hℓ4c2 : ℓ₄ ≠ c₂ := (G.ne_of_adj ha4).symm
  have hn1 : ¬G.Adj ℓ₁ c₂ := fun hadj =>
    hT ⟨c₁, ℓ₁, c₂, ha1.ne, (G.ne_of_adj hadj), hc12.ne, ha1, hadj, hc12, by omega⟩
  have hn2 : ¬G.Adj ℓ₂ c₂ := fun hadj =>
    hT ⟨c₁, ℓ₂, c₂, ha2.ne, (G.ne_of_adj hadj), hc12.ne, ha2, hadj, hc12, by omega⟩
  have hn3 : ¬G.Adj ℓ₃ c₁ := fun hadj =>
    hT ⟨c₂, ℓ₃, c₁, ha3.ne, (G.ne_of_adj hadj), hc12.ne.symm, ha3, hadj, hc12.symm, by omega⟩
  have hn4 : ¬G.Adj ℓ₄ c₁ := fun hadj =>
    hT ⟨c₂, ℓ₄, c₁, ha4.ne, (G.ne_of_adj hadj), hc12.ne.symm, ha4, hadj, hc12.symm, by omega⟩
  have hND1 : G.neighborFinset ℓ₁ ∩ D = {c₁} := by
    apply Finset.Subset.antisymm
    · intro w hw
      obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
      have hadj : G.Adj ℓ₁ w := (G.mem_neighborFinset _ _).mp hwN
      rcases hdom ℓ₁ w hℓ1D hwD hadj with e | e | e | e
      · exact absurd e hℓ1c1
      · exact absurd e h1c2
      · rw [e]; simp
      · exact absurd (e ▸ hadj) hn1
    · intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha1.symm, hc1D⟩
  have hND2 : G.neighborFinset ℓ₂ ∩ D = {c₁} := by
    apply Finset.Subset.antisymm
    · intro w hw
      obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
      have hadj : G.Adj ℓ₂ w := (G.mem_neighborFinset _ _).mp hwN
      rcases hdom ℓ₂ w hℓ2D hwD hadj with e | e | e | e
      · exact absurd e hℓ2c1
      · exact absurd e h2c2
      · rw [e]; simp
      · exact absurd (e ▸ hadj) hn2
    · intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha2.symm, hc1D⟩
  have hND3 : G.neighborFinset ℓ₃ ∩ D = {c₂} := by
    apply Finset.Subset.antisymm
    · intro w hw
      obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
      have hadj : G.Adj ℓ₃ w := (G.mem_neighborFinset _ _).mp hwN
      rcases hdom ℓ₃ w hℓ3D hwD hadj with e | e | e | e
      · exact absurd e h3c1
      · exact absurd e hℓ3c2
      · exact absurd (e ▸ hadj) hn3
      · rw [e]; simp
    · intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha3.symm, hc2D⟩
  have hND4 : G.neighborFinset ℓ₄ ∩ D = {c₂} := by
    apply Finset.Subset.antisymm
    · intro w hw
      obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
      have hadj : G.Adj ℓ₄ w := (G.mem_neighborFinset _ _).mp hwN
      rcases hdom ℓ₄ w hℓ4D hwD hadj with e | e | e | e
      · exact absurd e h4c1
      · exact absurd e hℓ4c2
      · exact absurd (e ▸ hadj) hn4
      · rw [e]; simp
    · intro w hw
      rw [Finset.mem_singleton] at hw; subst hw
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha4.symm, hc2D⟩
  have hcross : ∀ u v : Fin 14, G.neighborFinset u ∩ D = {c₁} →
      G.Adj c₂ v → u ≠ v := by
    intro u v hu hcv e
    subst e
    have hmem : c₂ ∈ G.neighborFinset u ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hcv.symm, hc2D⟩
    rw [hu, Finset.mem_singleton] at hmem
    exact hc12.ne hmem.symm
  have h13 : ℓ₁ ≠ ℓ₃ := hcross ℓ₁ ℓ₃ hND1 ha3
  have h14 : ℓ₁ ≠ ℓ₄ := hcross ℓ₁ ℓ₄ hND1 ha4
  have h23 : ℓ₂ ≠ ℓ₃ := hcross ℓ₂ ℓ₃ hND2 ha3
  have h24 : ℓ₂ ≠ ℓ₄ := hcross ℓ₂ ℓ₄ hND2 ha4
  have hcard6 : ({c₁, c₂, ℓ₁, ℓ₂, ℓ₃, ℓ₄} : Finset (Fin 14)).card = 6 := by
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hc12.ne, ha1.ne, ha2.ne, h3c1.symm, h4c1.symm⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨h1c2.symm, h2c2.symm, ha3.ne, ha4.ne⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hℓ12, h13, h14⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨h23, h24⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]; exact hℓ34),
        Finset.card_singleton]
  exact ⟨ℓ₁, ℓ₂, ℓ₃, ℓ₄, hd1, hd2, hd3, hd4, hcard6,
    ha1, ha2, ha3, ha4, hND1, hND2, hND3, hND4, hn1, hn2, hn3, hn4, hℓ12, hℓ34⟩

/-- **Both dominating-edge centres have in-`M`-degree `3`.**  In the dominating-edge branch with
`∑_{v∈D}|N v ∩ D| = 10` (i.e. `e(M) = 5`), the two centres `c₁, c₂` each have exactly `3`
`D`-neighbours.  Every non-centre `D`-vertex has its `D`-neighbours inside `{c₁, c₂}`, so a cross
count gives `∑ = 2(m₁ + m₂) − 2` with `mᵢ = |N cᵢ ∩ D| ≤ 3`; `2(m₁ + m₂) − 2 = 10` forces
`m₁ = m₂ = 3`. -/
theorem dom_centres_indeg3 (G : SimpleGraph (Fin 14)) (D : Finset (Fin 14))
    (c₁ c₂ : Fin 14) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hindle : ∀ x : Fin 14, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3)
    (hcov : ∀ p q : Fin 14, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hsum : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 10) :
    (G.neighborFinset c₁ ∩ D).card = 3 ∧ (G.neighborFinset c₂ ∩ D).card = 3 := by
  classical
  have hsub : ({c₁, c₂} : Finset (Fin 14)) ⊆ D := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl; exacts [hc1D, hc2D]
  have hsplit :
      ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 14)), (G.neighborFinset v ∩ D).card
        + ∑ v ∈ ({c₁, c₂} : Finset (Fin 14)), (G.neighborFinset v ∩ D).card
      = ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
    Finset.sum_sdiff hsub
  have hpair : ∑ v ∈ ({c₁, c₂} : Finset (Fin 14)), (G.neighborFinset v ∩ D).card
      = (G.neighborFinset c₁ ∩ D).card + (G.neighborFinset c₂ ∩ D).card := by
    rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
  have hScong :
      ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 14)), (G.neighborFinset v ∩ D).card
        = ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 14)),
          (G.neighborFinset v ∩ ({c₁, c₂} : Finset (Fin 14))).card := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.mem_sdiff] at hv
    obtain ⟨hvD, hvnot⟩ := hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvnot
    congr 1
    apply Finset.Subset.antisymm
    · intro w hw
      obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
      have hvw : G.Adj v w := (G.mem_neighborFinset _ _).mp hwN
      rcases hcov v w hvD hwD hvw with e | e | e | e
      · exact absurd e hvnot.1
      · exact absurd e hvnot.2
      · exact Finset.mem_inter.mpr ⟨hwN, by rw [e]; simp⟩
      · exact Finset.mem_inter.mpr ⟨hwN, by rw [e]; simp⟩
    · intro w hw
      obtain ⟨hwN, hwm⟩ := Finset.mem_inter.mp hw
      exact Finset.mem_inter.mpr ⟨hwN, hsub hwm⟩
  rw [hScong,
    cross_count_fourteen G (D \ ({c₁, c₂} : Finset (Fin 14)))
      ({c₁, c₂} : Finset (Fin 14))] at hsplit
  have hpair2 : ∑ w ∈ ({c₁, c₂} : Finset (Fin 14)),
        (G.neighborFinset w ∩ (D \ ({c₁, c₂} : Finset (Fin 14)))).card
      = (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 14)))).card
        + (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 14)))).card := by
    rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
  have hc2mem : c₂ ∈ G.neighborFinset c₁ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
  have hc1mem : c₁ ∈ G.neighborFinset c₂ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
  have hb1eq : (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 14)))).card
      = (G.neighborFinset c₁ ∩ D).card - 1 := by
    have heq : G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 14)))
        = (G.neighborFinset c₁ ∩ D).erase c₂ := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_erase, G.mem_neighborFinset,
        Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · rintro ⟨hadj, hwD, _, hwc2⟩; exact ⟨hwc2, hadj, hwD⟩
      · rintro ⟨hwc2, hadj, hwD⟩
        exact ⟨hadj, hwD, fun e => G.irrefl (e ▸ hadj), hwc2⟩
    rw [heq, Finset.card_erase_of_mem hc2mem]
  have hb2eq : (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 14)))).card
      = (G.neighborFinset c₂ ∩ D).card - 1 := by
    have heq : G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 14)))
        = (G.neighborFinset c₂ ∩ D).erase c₁ := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_erase, G.mem_neighborFinset,
        Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · rintro ⟨hadj, hwD, hwc1, _⟩; exact ⟨hwc1, hadj, hwD⟩
      · rintro ⟨hwc1, hadj, hwD⟩
        exact ⟨hadj, hwD, hwc1, fun e => G.irrefl (e ▸ hadj)⟩
    rw [heq, Finset.card_erase_of_mem hc1mem]
  rw [hpair2, hpair, hb1eq, hb2eq] at hsplit
  have hi1 := hindle c₁ hc1D
  have hi2 := hindle c₂ hc2D
  have hm1pos : 1 ≤ (G.neighborFinset c₁ ∩ D).card :=
    Finset.card_pos.mpr ⟨c₂, hc2mem⟩
  have hm2pos : 1 ≤ (G.neighborFinset c₂ ∩ D).card :=
    Finset.card_pos.mpr ⟨c₁, hc1mem⟩
  rw [hsum] at hsplit
  omega

end N14

end ACMax
