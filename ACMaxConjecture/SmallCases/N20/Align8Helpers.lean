import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.Dense
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.NonisoBound

/-!
# Assembly cluster for the `n = 18` `e(M) = 3` / `e(M) ≥ 4` alignment corners

Ported `Fin 17 → Fin 20` analogues of the single-vertex / two-hub assembly lemmas used to close the
residual alignment corners.  The single-vertex selectors route the proved degree-`4` double-star /
`C₅` hub-avoidance lemmas (`hub_meets_path_le_one_twenty`, `hub_cycle_cases_twenty`) through
`assemble_single_vertex_config`; the dense assembly lemmas package the `|D| = 8` regime into
`SingleVertexConfig` / `TwoHubConfig`.

`n = 20` count (`∑ deg = 72`): in the `nodeg5` regime `|D| = 8`, `|Hub₄| = 12`, and under
`e(M) ≤ 3` (`hs6`) the twin pigeonhole **ties** (`|Iso| ≥ 4`, `3·4 = 12 = |Hub₄|`); in the
degree-`5` regime the refined count needs `|Iso| + |D| + |Hub₄| ≥ 25` and ties by `1` exactly
when `|S| = 4` and `|H₅| = |D| − 8`.  Unlike at `n ≤ 19`, the shared degree-`4` hub is therefore
**not** forced: both `shared_deg4_hub_*` lemmas conclude a disjunction — the shared hub, or one
of the signed-cut configurations — with the tie routed through the 3-way dichotomy
`nonisolated_le_three_or_star_or_path` (`|S| ≤ 3`, star `K₁,₃`, or path `P₄` with profile
`(1, 2, 2, 1)`).
-/

namespace ACMax

open scoped Classical

namespace N20

theorem assemble_single_vertex_config (G : SimpleGraph (Fin 20))
    (t h₁ h₂ x y z : Fin 20)
    (ht3 : G.degree t = 3) (htiso : ∀ w : Fin 20, G.Adj t w → G.degree w ≠ 3)
    (hh₁4 : G.degree h₁ = 4) (hh₂4 : G.degree h₂ = 4) (hne12 : h₁ ≠ h₂)
    (hth₁ : G.Adj t h₁) (hth₂ : G.Adj t h₂)
    (hx3 : G.degree x = 3) (hy3 : G.degree y = 3) (hz3 : G.degree z = 3)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz_ne : x ≠ z) (hxz : ¬G.Adj x z)
    (hh₁x : ¬G.Adj h₁ x) (hh₁y : ¬G.Adj h₁ y) (hh₁z : ¬G.Adj h₁ z)
    (hh₂x : ¬G.Adj h₂ x) (hh₂y : ¬G.Adj h₂ y) (hh₂z : ¬G.Adj h₂ z) :
    SingleVertexConfig G := by
  classical
  have htx : ¬G.Adj t x := fun h => htiso x h hx3
  have hty : ¬G.Adj t y := fun h => htiso y h hy3
  have htz : ¬G.Adj t z := fun h => htiso z h hz3
  have hsum0 : ∑ p ∈ ({t, h₁, h₂} : Finset (Fin 20)),
      (G.neighborFinset p ∩ ({x, y, z} : Finset (Fin 20))).card = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨hadj, hwxyz⟩ := hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hwxyz
    rcases hp with rfl | rfl | rfl <;> rcases hwxyz with rfl | rfl | rfl
    · exact htx hadj
    · exact hty hadj
    · exact htz hadj
    · exact hh₁x hadj
    · exact hh₁y hadj
    · exact hh₁z hadj
    · exact hh₂x hadj
    · exact hh₂y hadj
    · exact hh₂z hadj
  have hside : 2 * (∑ p ∈ ({t, h₁, h₂} : Finset (Fin 20)),
      (G.neighborFinset p ∩ ({x, y, z} : Finset (Fin 20))).card)
      + G.degree h₁ + G.degree h₂ ≤ 8 + 2 * (if G.Adj h₁ h₂ then 1 else 0) := by
    rw [hsum0, hh₁4, hh₂4]
    have hnn : (0 : ℕ) ≤ 2 * (if G.Adj h₁ h₂ then 1 else 0) := Nat.zero_le _
    omega
  have htv_x : t ≠ x := by rintro rfl; exact htiso y hxy hy3
  have htv_y : t ≠ y := by rintro rfl; exact htiso x hxy.symm hx3
  have htv_z : t ≠ z := by rintro rfl; exact htiso y hyz.symm hy3
  have hh1_x : h₁ ≠ x := by rintro rfl; omega
  have hh1_y : h₁ ≠ y := by rintro rfl; omega
  have hh1_z : h₁ ≠ z := by rintro rfl; omega
  have hh2_x : h₂ ≠ x := by rintro rfl; omega
  have hh2_y : h₂ ≠ y := by rintro rfl; omega
  have hh2_z : h₂ ≠ z := by rintro rfl; omega
  exact ⟨t, h₁, h₂, x, y, z, ht3, hx3, hy3, hz3, hth₁, hth₂, hxy, hyz, hxz, hside,
    hne12, htv_x, htv_y, htv_z, hh1_x, hh1_y, hh1_z, hh2_x, hh2_y, hh2_z,
    hxy.ne, hyz.ne, hxz_ne⟩

theorem dom_doublestar_leaves (G : SimpleGraph (Fin 20)) (D : Finset (Fin 20))
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (c₁ c₂ : Fin 20) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 3) (hin2 : (G.neighborFinset c₂ ∩ D).card = 3)
    (hdom : ∀ p q : Fin 20, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂) :
    ∃ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Fin 20,
      G.degree ℓ₁ = 3 ∧ G.degree ℓ₂ = 3 ∧ G.degree ℓ₃ = 3 ∧ G.degree ℓ₄ = 3 ∧
      ({c₁, c₂, ℓ₁, ℓ₂, ℓ₃, ℓ₄} : Finset (Fin 20)).card = 6 ∧
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
  obtain ⟨ℓ₃, ℓ₄, hℓ36, hℓset2⟩ := Finset.card_eq_two.mp herase2
  have hmem1 : ∀ w : Fin 20, w = ℓ₁ ∨ w = ℓ₂ →
      w ≠ c₂ ∧ G.Adj c₁ w ∧ G.degree w = 3 := by
    intro w hw
    have hwe : w ∈ (G.neighborFinset c₁ ∩ D).erase c₂ := by
      rw [hℓset1]; rcases hw with rfl | rfl <;> simp
    rw [Finset.mem_erase] at hwe
    obtain ⟨hwc2, hwND⟩ := hwe
    obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hwND
    exact ⟨hwc2, (G.mem_neighborFinset _ _).mp hwN, (hmemD w).mp hwD⟩
  have hmem2 : ∀ w : Fin 20, w = ℓ₃ ∨ w = ℓ₄ →
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
  have hcross : ∀ u v : Fin 20, G.neighborFinset u ∩ D = {c₁} →
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
  have hcard6 : ({c₁, c₂, ℓ₁, ℓ₂, ℓ₃, ℓ₄} : Finset (Fin 20)).card = 6 := by
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
          simp only [Finset.mem_singleton]; exact hℓ36),
        Finset.card_singleton]
  exact ⟨ℓ₁, ℓ₂, ℓ₃, ℓ₄, hd1, hd2, hd3, hd4, hcard6,
    ha1, ha2, ha3, ha4, hND1, hND2, hND3, hND4, hn1, hn2, hn3, hn4, hℓ12, hℓ36⟩

theorem dom_centres_indeg3 (G : SimpleGraph (Fin 20)) (D : Finset (Fin 20))
    (c₁ c₂ : Fin 20) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hindle : ∀ x : Fin 20, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3)
    (hcov : ∀ p q : Fin 20, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hsum : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 10) :
    (G.neighborFinset c₁ ∩ D).card = 3 ∧ (G.neighborFinset c₂ ∩ D).card = 3 := by
  classical
  have hsub : ({c₁, c₂} : Finset (Fin 20)) ⊆ D := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl; exacts [hc1D, hc2D]
  have hsplit :
      ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 20)), (G.neighborFinset v ∩ D).card
        + ∑ v ∈ ({c₁, c₂} : Finset (Fin 20)), (G.neighborFinset v ∩ D).card
      = ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
    Finset.sum_sdiff hsub
  have hpair : ∑ v ∈ ({c₁, c₂} : Finset (Fin 20)), (G.neighborFinset v ∩ D).card
      = (G.neighborFinset c₁ ∩ D).card + (G.neighborFinset c₂ ∩ D).card := by
    rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
  have hScong :
      ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 20)), (G.neighborFinset v ∩ D).card
        = ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 20)),
          (G.neighborFinset v ∩ ({c₁, c₂} : Finset (Fin 20))).card := by
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
    cross_count_twenty G (D \ ({c₁, c₂} : Finset (Fin 20)))
      ({c₁, c₂} : Finset (Fin 20))] at hsplit
  have hpair2 : ∑ w ∈ ({c₁, c₂} : Finset (Fin 20)),
        (G.neighborFinset w ∩ (D \ ({c₁, c₂} : Finset (Fin 20)))).card
      = (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 20)))).card
        + (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 20)))).card := by
    rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
  have hc2mem : c₂ ∈ G.neighborFinset c₁ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
  have hc1mem : c₁ ∈ G.neighborFinset c₂ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
  have hb1eq : (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 20)))).card
      = (G.neighborFinset c₁ ∩ D).card - 1 := by
    have heq : G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 20)))
        = (G.neighborFinset c₁ ∩ D).erase c₂ := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_erase, G.mem_neighborFinset,
        Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · rintro ⟨hadj, hwD, _, hwc2⟩; exact ⟨hwc2, hadj, hwD⟩
      · rintro ⟨hwc2, hadj, hwD⟩
        exact ⟨hadj, hwD, fun e => G.irrefl (e ▸ hadj), hwc2⟩
    rw [heq, Finset.card_erase_of_mem hc2mem]
  have hb2eq : (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 20)))).card
      = (G.neighborFinset c₂ ∩ D).card - 1 := by
    have heq : G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 20)))
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

/-- **Single-vertex double-star alignment by leaf counting.**  The `SingleVertexConfig` analogue of
`single_twin_doublestar_count`: the same all-degree-`4`-hub double-star selection, but routed through
`assemble_single_vertex_config` (recording the cherry non-adjacency `¬leaf∼c'`). -/
theorem single_vertex_doublestar_count (G : SimpleGraph (Fin 20)) (D : Finset (Fin 20))
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (t a b c : Fin 20) (ht3 : G.degree t = 3)
    (htiso : ∀ w : Fin 20, G.Adj t w → G.degree w ≠ 3)
    (hda : G.degree a = 4) (hdb : G.degree b = 4) (hdc : G.degree c = 4)
    (habne : a ≠ b) (hacne : a ≠ c) (hbcne : b ≠ c)
    (hta : G.Adj t a) (htb : G.Adj t b) (htc : G.Adj t c)
    (c₁ c₂ : Fin 20) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 3) (hin2 : (G.neighborFinset c₂ ∩ D).card = 3)
    (hdom : ∀ p q : Fin 20, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂) :
    SingleVertexConfig G := by
  classical
  have hc1deg : G.degree c₁ = 3 := (hmemD c₁).mp hc1D
  have hc2deg : G.degree c₂ = 3 := (hmemD c₂).mp hc2D
  obtain ⟨ℓ₁, ℓ₂, ℓ₃, ℓ₄, hd1, hd2, hd3, hd4, hcard6,
      hac1, hac2, hac3, hac4, hND1, hND2, hND3, hND4, hn1, hn2, hn3, hn4, hℓ12, hℓ36⟩ :=
    dom_doublestar_leaves G D hmemD hT c₁ c₂ hc1D hc2D hc12 hin1 hin2 hdom
  have leafdeg : ∀ w : Fin 20, (w = ℓ₁ ∨ w = ℓ₂ ∨ w = ℓ₃ ∨ w = ℓ₄) → G.degree w = 3 := by
    rintro w (rfl | rfl | rfl | rfl) <;> assumption
  have leafD : ∀ w : Fin 20, (w = ℓ₁ ∨ w = ℓ₂ ∨ w = ℓ₃ ∨ w = ℓ₄) → w ∈ D :=
    fun w hw => (hmemD w).mpr (leafdeg w hw)
  have hlne : ∀ w cen oth : Fin 20, G.neighborFinset w ∩ D = {cen} →
      (G.neighborFinset oth ∩ D).card = 3 → w ≠ oth := by
    intro w cen oth hw hoth e
    subst e
    rw [hw, Finset.card_singleton] at hoth
    omega
  have hleafnec : ∀ w : Fin 20, (w = ℓ₁ ∨ w = ℓ₂ ∨ w = ℓ₃ ∨ w = ℓ₄) → w ≠ c₁ ∧ w ≠ c₂ := by
    rintro w (rfl | rfl | rfl | rfl)
    · exact ⟨(G.ne_of_adj hac1).symm, hlne w c₁ c₂ hND1 hin2⟩
    · exact ⟨(G.ne_of_adj hac2).symm, hlne w c₁ c₂ hND2 hin2⟩
    · exact ⟨hlne w c₂ c₁ hND3 hin1, (G.ne_of_adj hac3).symm⟩
    · exact ⟨hlne w c₂ c₁ hND4 hin1, (G.ne_of_adj hac4).symm⟩
  have hleafnonadj : ∀ u v : Fin 20, (u = ℓ₁ ∨ u = ℓ₂ ∨ u = ℓ₃ ∨ u = ℓ₄) →
      (v = ℓ₁ ∨ v = ℓ₂ ∨ v = ℓ₃ ∨ v = ℓ₄) → u ≠ v → ¬G.Adj u v := by
    intro u v hu hv huv hadj
    rcases hdom u v (leafD u hu) (leafD v hv) hadj with e | e | e | e
    · exact (hleafnec u hu).1 e
    · exact (hleafnec u hu).2 e
    · exact (hleafnec v hv).1 e
    · exact (hleafnec v hv).2 e
  have hNc1 : G.neighborFinset c₁ ∩ D = G.neighborFinset c₁ :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [G.card_neighborFinset_eq_degree, hc1deg, hin1])
  have hNc2 : G.neighborFinset c₂ ∩ D = G.neighborFinset c₂ :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [G.card_neighborFinset_eq_degree, hc2deg, hin2])
  have hubcen : ∀ hh : Fin 20, (hh = a ∨ hh = b ∨ hh = c) →
      ¬G.Adj hh c₁ ∧ ¬G.Adj hh c₂ := by
    intro hh hhmem
    have hh4 : G.degree hh = 4 := by rcases hhmem with rfl | rfl | rfl <;> assumption
    constructor
    · intro hadj
      have hmem : hh ∈ G.neighborFinset c₁ := (G.mem_neighborFinset _ _).mpr hadj.symm
      rw [← hNc1] at hmem
      have := (hmemD hh).mp (Finset.mem_inter.mp hmem).2
      omega
    · intro hadj
      have hmem : hh ∈ G.neighborFinset c₂ := (G.mem_neighborFinset _ _).mpr hadj.symm
      rw [← hNc2] at hmem
      have := (hmemD hh).mp (Finset.mem_inter.mp hmem).2
      omega
  -- Each degree-`4` hub meets at most one leaf of each centre (induced `P₃`).
  have ind2 : ∀ p q : Prop, ¬(p ∧ q) →
      (if p then 1 else 0) + (if q then 1 else 0) ≤ 1 := by
    intro p q hpq
    rcases Classical.em p with hp | hp
    · rcases Classical.em q with hq | hq
      · exact absurd ⟨hp, hq⟩ hpq
      · rw [if_pos hp, if_neg hq]
    · rw [if_neg hp]
      split_ifs <;> omega
  have hpair : ∀ hh : Fin 20, G.degree hh = 4 →
      ¬(G.Adj hh ℓ₁ ∧ G.Adj hh ℓ₂) ∧ ¬(G.Adj hh ℓ₃ ∧ G.Adj hh ℓ₄) := by
    intro hh hh4
    refine ⟨?_, ?_⟩
    · exact (hub_meets_path_le_one_twenty G hT hC4 hh4 hd1 hc1deg hd2
        hac1.symm hac2
        (hleafnonadj ℓ₁ ℓ₂ (Or.inl rfl) (Or.inr (Or.inl rfl)) hℓ12)
        (G.ne_of_adj hac1).symm (G.ne_of_adj hac2) hℓ12).2.2
    · exact (hub_meets_path_le_one_twenty G hT hC4 hh4 hd3 hc2deg hd4
        hac3.symm hac4
        (hleafnonadj ℓ₃ ℓ₄ (Or.inr (Or.inr (Or.inl rfl)))
          (Or.inr (Or.inr (Or.inr rfl))) hℓ36)
        (G.ne_of_adj hac3).symm (G.ne_of_adj hac4) hℓ36).2.2
  obtain ⟨hpa12, hpa36⟩ := hpair a hda
  obtain ⟨hpb12, hpb36⟩ := hpair b hdb
  obtain ⟨hpc12, hpc36⟩ := hpair c hdc
  -- Counting: some leaf is met by at most one of the three hubs.
  have keyleaf : ∃ w : Fin 20, (w = ℓ₁ ∨ w = ℓ₂ ∨ w = ℓ₃ ∨ w = ℓ₄) ∧
      (if G.Adj a w then 1 else 0) + (if G.Adj b w then 1 else 0)
        + (if G.Adj c w then 1 else 0) ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have hc1 := hcon ℓ₁ (Or.inl rfl)
    have hc2 := hcon ℓ₂ (Or.inr (Or.inl rfl))
    have hc3 := hcon ℓ₃ (Or.inr (Or.inr (Or.inl rfl)))
    have hc4 := hcon ℓ₄ (Or.inr (Or.inr (Or.inr rfl)))
    have ca12 := ind2 _ _ hpa12
    have ca36 := ind2 _ _ hpa36
    have cb12 := ind2 _ _ hpb12
    have cb36 := ind2 _ _ hpb36
    have cc12 := ind2 _ _ hpc12
    have cc36 := ind2 _ _ hpc36
    omega
  obtain ⟨w, hwleaf, hwcnt⟩ := keyleaf
  have amem : (a = a ∨ a = b ∨ a = c) := Or.inl rfl
  have bmem : (b = a ∨ b = b ∨ b = c) := Or.inr (Or.inl rfl)
  have cmem : (c = a ∨ c = b ∨ c = c) := Or.inr (Or.inr rfl)
  have key : ∃ w' h₁ h₂ : Fin 20, (w' = ℓ₁ ∨ w' = ℓ₂ ∨ w' = ℓ₃ ∨ w' = ℓ₄) ∧
      (h₁ = a ∨ h₁ = b ∨ h₁ = c) ∧ (h₂ = a ∨ h₂ = b ∨ h₂ = c) ∧ h₁ ≠ h₂ ∧
      ¬G.Adj w' h₁ ∧ ¬G.Adj w' h₂ := by
    refine ⟨w, ?_⟩
    rcases Classical.em (G.Adj a w) with ha' | ha'
    · rcases Classical.em (G.Adj b w) with hb' | hb'
      · rw [if_pos ha', if_pos hb'] at hwcnt; omega
      · rcases Classical.em (G.Adj c w) with hc' | hc'
        · rw [if_pos ha', if_pos hc'] at hwcnt; omega
        · exact ⟨b, c, hwleaf, bmem, cmem, hbcne,
            fun h => hb' h.symm, fun h => hc' h.symm⟩
    · rcases Classical.em (G.Adj b w) with hb' | hb'
      · rcases Classical.em (G.Adj c w) with hc' | hc'
        · rw [if_pos hb', if_pos hc'] at hwcnt; omega
        · exact ⟨a, c, hwleaf, amem, cmem, hacne,
            fun h => ha' h.symm, fun h => hc' h.symm⟩
      · exact ⟨a, b, hwleaf, amem, bmem, habne,
          fun h => ha' h.symm, fun h => hb' h.symm⟩
  obtain ⟨w', h₁, h₂, hwleaf', hh₁mem, hh₂mem, hh12, hwh₁, hwh₂⟩ := key
  have hdh₁ : G.degree h₁ = 4 := by rcases hh₁mem with rfl | rfl | rfl <;> assumption
  have hdh₂ : G.degree h₂ = 4 := by rcases hh₂mem with rfl | rfl | rfl <;> assumption
  have hth₁ : G.Adj t h₁ := by rcases hh₁mem with rfl | rfl | rfl <;> assumption
  have hth₂ : G.Adj t h₂ := by rcases hh₂mem with rfl | rfl | rfl <;> assumption
  obtain ⟨hh₁c1, hh₁c2⟩ := hubcen h₁ hh₁mem
  obtain ⟨hh₂c1, hh₂c2⟩ := hubcen h₂ hh₂mem
  rcases hwleaf' with rfl | rfl | rfl | rfl
  · exact assemble_single_vertex_config G t h₁ h₂ w' c₁ c₂ ht3 htiso hdh₁ hdh₂ hh12
      hth₁ hth₂ hd1 hc1deg hc2deg hac1.symm hc12 (hlne w' c₁ c₂ hND1 hin2) hn1
      (fun h => hwh₁ h.symm) hh₁c1 hh₁c2 (fun h => hwh₂ h.symm) hh₂c1 hh₂c2
  · exact assemble_single_vertex_config G t h₁ h₂ w' c₁ c₂ ht3 htiso hdh₁ hdh₂ hh12
      hth₁ hth₂ hd2 hc1deg hc2deg hac2.symm hc12 (hlne w' c₁ c₂ hND2 hin2) hn2
      (fun h => hwh₁ h.symm) hh₁c1 hh₁c2 (fun h => hwh₂ h.symm) hh₂c1 hh₂c2
  · exact assemble_single_vertex_config G t h₁ h₂ w' c₂ c₁ ht3 htiso hdh₁ hdh₂ hh12
      hth₁ hth₂ hd3 hc2deg hc1deg hac3.symm hc12.symm (hlne w' c₂ c₁ hND3 hin1) hn3
      (fun h => hwh₁ h.symm) hh₁c2 hh₁c1 (fun h => hwh₂ h.symm) hh₂c2 hh₂c1
  · exact assemble_single_vertex_config G t h₁ h₂ w' c₂ c₁ ht3 htiso hdh₁ hdh₂ hh12
      hth₁ hth₂ hd4 hc2deg hc1deg hac4.symm hc12.symm (hlne w' c₂ c₁ hND4 hin1) hn4
      (fun h => hwh₁ h.symm) hh₁c2 hh₁c1 (fun h => hwh₂ h.symm) hh₂c2 hh₂c1

/-- **Single-vertex `C₅` alignment.**  The `SingleVertexConfig` analogue of
`single_twin_config_from_C5_three_hubs`: identical induced-`C₅` hub-avoidance case analysis, routed
through `assemble_single_vertex_config` (recording the cherry non-adjacency from the `C₅` chords). -/
theorem single_vertex_config_from_C5_three_hubs (G : SimpleGraph (Fin 20))
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (t h₁ h₂ h₃ : Fin 20) (ht3 : G.degree t = 3)
    (htiso : ∀ w : Fin 20, G.Adj t w → G.degree w ≠ 3)
    (hh₁4 : G.degree h₁ = 4) (hh₂4 : G.degree h₂ = 4) (hh₃4 : G.degree h₃ = 4)
    (hne12 : h₁ ≠ h₂) (hne13 : h₁ ≠ h₃) (hne23 : h₂ ≠ h₃)
    (htg₁ : G.Adj t h₁) (htg₂ : G.Adj t h₂) (htg₃ : G.Adj t h₃)
    (v₁ v₂ v₃ v₄ v₅ : Fin 20)
    (hd1 : G.degree v₁ = 3) (hd2 : G.degree v₂ = 3) (hd3 : G.degree v₃ = 3)
    (hd4 : G.degree v₄ = 3) (hd5 : G.degree v₅ = 3)
    (hcard5 : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 20)).card = 5)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e36 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁)
    (n13 : ¬G.Adj v₁ v₃) (n14 : ¬G.Adj v₁ v₄) (n24 : ¬G.Adj v₂ v₄)
    (n25 : ¬G.Adj v₂ v₅) (n35 : ¬G.Adj v₃ v₅) :
    SingleVertexConfig G := by
  obtain ⟨d12, d13, d14, d15, d23, d24, d25, d36, d35, d45⟩ :=
    distinct_five_twenty v₁ v₂ v₃ v₄ v₅ hcard5
  -- Generic cherry closers, one per consecutive triple, for an arbitrary hub pair.
  have mg1 : ∀ ha hb : Fin 20, G.degree ha = 4 → G.degree hb = 4 → ha ≠ hb →
      G.Adj t ha → G.Adj t hb →
      ¬G.Adj ha v₁ → ¬G.Adj ha v₂ → ¬G.Adj ha v₃ →
      ¬G.Adj hb v₁ → ¬G.Adj hb v₂ → ¬G.Adj hb v₃ → SingleVertexConfig G :=
    fun ha hb hca hcb hcne hta htb a1 a2 a3 b1 b2 b3 =>
      assemble_single_vertex_config G t ha hb v₁ v₂ v₃ ht3 htiso hca hcb hcne hta htb
        hd1 hd2 hd3 e12 e23 d13 n13 a1 a2 a3 b1 b2 b3
  have mg2 : ∀ ha hb : Fin 20, G.degree ha = 4 → G.degree hb = 4 → ha ≠ hb →
      G.Adj t ha → G.Adj t hb →
      ¬G.Adj ha v₂ → ¬G.Adj ha v₃ → ¬G.Adj ha v₄ →
      ¬G.Adj hb v₂ → ¬G.Adj hb v₃ → ¬G.Adj hb v₄ → SingleVertexConfig G :=
    fun ha hb hca hcb hcne hta htb a1 a2 a3 b1 b2 b3 =>
      assemble_single_vertex_config G t ha hb v₂ v₃ v₄ ht3 htiso hca hcb hcne hta htb
        hd2 hd3 hd4 e23 e36 d24 n24 a1 a2 a3 b1 b2 b3
  have mg3 : ∀ ha hb : Fin 20, G.degree ha = 4 → G.degree hb = 4 → ha ≠ hb →
      G.Adj t ha → G.Adj t hb →
      ¬G.Adj ha v₃ → ¬G.Adj ha v₄ → ¬G.Adj ha v₅ →
      ¬G.Adj hb v₃ → ¬G.Adj hb v₄ → ¬G.Adj hb v₅ → SingleVertexConfig G :=
    fun ha hb hca hcb hcne hta htb a1 a2 a3 b1 b2 b3 =>
      assemble_single_vertex_config G t ha hb v₃ v₄ v₅ ht3 htiso hca hcb hcne hta htb
        hd3 hd4 hd5 e36 e45 d35 n35 a1 a2 a3 b1 b2 b3
  have mg4 : ∀ ha hb : Fin 20, G.degree ha = 4 → G.degree hb = 4 → ha ≠ hb →
      G.Adj t ha → G.Adj t hb →
      ¬G.Adj ha v₄ → ¬G.Adj ha v₅ → ¬G.Adj ha v₁ →
      ¬G.Adj hb v₄ → ¬G.Adj hb v₅ → ¬G.Adj hb v₁ → SingleVertexConfig G :=
    fun ha hb hca hcb hcne hta htb a1 a2 a3 b1 b2 b3 =>
      assemble_single_vertex_config G t ha hb v₄ v₅ v₁ ht3 htiso hca hcb hcne hta htb
        hd4 hd5 hd1 e45 e51 d14.symm (fun h => n14 h.symm) a1 a2 a3 b1 b2 b3
  have mg5 : ∀ ha hb : Fin 20, G.degree ha = 4 → G.degree hb = 4 → ha ≠ hb →
      G.Adj t ha → G.Adj t hb →
      ¬G.Adj ha v₅ → ¬G.Adj ha v₁ → ¬G.Adj ha v₂ →
      ¬G.Adj hb v₅ → ¬G.Adj hb v₁ → ¬G.Adj hb v₂ → SingleVertexConfig G :=
    fun ha hb hca hcb hcne hta htb a1 a2 a3 b1 b2 b3 =>
      assemble_single_vertex_config G t ha hb v₅ v₁ v₂ ht3 htiso hca hcb hcne hta htb
        hd5 hd1 hd2 e51 e12 d25.symm (fun h => n25 h.symm) a1 a2 a3 b1 b2 b3
  have hB := hub_cycle_cases_twenty G hT hC4 h₁ v₁ v₂ v₃ v₄ v₅ hh₁4 hd1 hd2 hd3 hd4 hd5
    e12 e23 e36 e45 e51 n13 n14 n24 n25 n35 d12 d13 d14 d15 d23 d24 d25 d36 d35 d45
  have hC := hub_cycle_cases_twenty G hT hC4 h₂ v₁ v₂ v₃ v₄ v₅ hh₂4 hd1 hd2 hd3 hd4 hd5
    e12 e23 e36 e45 e51 n13 n14 n24 n25 n35 d12 d13 d14 d15 d23 d24 d25 d36 d35 d45
  have hD := hub_cycle_cases_twenty G hT hC4 h₃ v₁ v₂ v₃ v₄ v₅ hh₃4 hd1 hd2 hd3 hd4 hd5
    e12 e23 e36 e45 e51 n13 n14 n24 n25 n35 d12 d13 d14 d15 d23 d24 d25 d36 d35 d45
  rcases hB with ⟨p1, p2, p3, p4, p5⟩ | ⟨p2, p3, p4, p5⟩ | ⟨p1, p3, p4, p5⟩ |
    ⟨p1, p2, p4, p5⟩ | ⟨p1, p2, p3, p5⟩ | ⟨p1, p2, p3, p4⟩
  · rcases hC with ⟨r1, r2, r3, r4, r5⟩ | ⟨r2, r3, r4, r5⟩ | ⟨r1, r3, r4, r5⟩ |
      ⟨r1, r2, r4, r5⟩ | ⟨r1, r2, r3, r5⟩ | ⟨r1, r2, r3, r4⟩
    · exact mg1 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p1 p2 p3 r1 r2 r3
    · exact mg2 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p2 p3 p4 r2 r3 r4
    · exact mg3 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p3 p4 p5 r3 r4 r5
    · exact mg4 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p4 p5 p1 r4 r5 r1
    · exact mg1 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p1 p2 p3 r1 r2 r3
    · exact mg1 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p1 p2 p3 r1 r2 r3
  · rcases hC with ⟨r1, r2, r3, r4, r5⟩ | ⟨r2, r3, r4, r5⟩ | ⟨r1, r3, r4, r5⟩ |
      ⟨r1, r2, r4, r5⟩ | ⟨r1, r2, r3, r5⟩ | ⟨r1, r2, r3, r4⟩
    · exact mg2 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p2 p3 p4 r2 r3 r4
    · exact mg2 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p2 p3 p4 r2 r3 r4
    · exact mg3 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p3 p4 p5 r3 r4 r5
    · rcases hD with ⟨q1, q2, q3, q4, q5⟩ | ⟨q2, q3, q4, q5⟩ | ⟨q1, q3, q4, q5⟩ |
        ⟨q1, q2, q4, q5⟩ | ⟨q1, q2, q3, q5⟩ | ⟨q1, q2, q3, q4⟩
      · exact mg2 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p2 p3 p4 q2 q3 q4
      · exact mg2 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p2 p3 p4 q2 q3 q4
      · exact mg3 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p3 p4 p5 q3 q4 q5
      · exact mg4 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r4 r5 r1 q4 q5 q1
      · exact mg5 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r5 r1 r2 q5 q1 q2
      · exact mg2 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p2 p3 p4 q2 q3 q4
    · rcases hD with ⟨q1, q2, q3, q4, q5⟩ | ⟨q2, q3, q4, q5⟩ | ⟨q1, q3, q4, q5⟩ |
        ⟨q1, q2, q4, q5⟩ | ⟨q1, q2, q3, q5⟩ | ⟨q1, q2, q3, q4⟩
      · exact mg2 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p2 p3 p4 q2 q3 q4
      · exact mg2 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p2 p3 p4 q2 q3 q4
      · exact mg3 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p3 p4 p5 q3 q4 q5
      · exact mg5 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r5 r1 r2 q5 q1 q2
      · exact mg5 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r5 r1 r2 q5 q1 q2
      · exact mg2 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p2 p3 p4 q2 q3 q4
    · exact mg2 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p2 p3 p4 r2 r3 r4
  · rcases hC with ⟨r1, r2, r3, r4, r5⟩ | ⟨r2, r3, r4, r5⟩ | ⟨r1, r3, r4, r5⟩ |
      ⟨r1, r2, r4, r5⟩ | ⟨r1, r2, r3, r5⟩ | ⟨r1, r2, r3, r4⟩
    · exact mg3 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p3 p4 p5 r3 r4 r5
    · exact mg3 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p3 p4 p5 r3 r4 r5
    · exact mg3 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p3 p4 p5 r3 r4 r5
    · exact mg4 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p4 p5 p1 r4 r5 r1
    · rcases hD with ⟨q1, q2, q3, q4, q5⟩ | ⟨q2, q3, q4, q5⟩ | ⟨q1, q3, q4, q5⟩ |
        ⟨q1, q2, q4, q5⟩ | ⟨q1, q2, q3, q5⟩ | ⟨q1, q2, q3, q4⟩
      · exact mg3 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p3 p4 p5 q3 q4 q5
      · exact mg3 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p3 p4 p5 q3 q4 q5
      · exact mg3 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p3 p4 p5 q3 q4 q5
      · exact mg4 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p4 p5 p1 q4 q5 q1
      · exact mg5 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r5 r1 r2 q5 q1 q2
      · exact mg1 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r1 r2 r3 q1 q2 q3
    · rcases hD with ⟨q1, q2, q3, q4, q5⟩ | ⟨q2, q3, q4, q5⟩ | ⟨q1, q3, q4, q5⟩ |
        ⟨q1, q2, q4, q5⟩ | ⟨q1, q2, q3, q5⟩ | ⟨q1, q2, q3, q4⟩
      · exact mg3 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p3 p4 p5 q3 q4 q5
      · exact mg3 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p3 p4 p5 q3 q4 q5
      · exact mg3 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p3 p4 p5 q3 q4 q5
      · exact mg4 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p4 p5 p1 q4 q5 q1
      · exact mg1 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r1 r2 r3 q1 q2 q3
      · exact mg1 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r1 r2 r3 q1 q2 q3
  · rcases hC with ⟨r1, r2, r3, r4, r5⟩ | ⟨r2, r3, r4, r5⟩ | ⟨r1, r3, r4, r5⟩ |
      ⟨r1, r2, r4, r5⟩ | ⟨r1, r2, r3, r5⟩ | ⟨r1, r2, r3, r4⟩
    · exact mg4 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p4 p5 p1 r4 r5 r1
    · rcases hD with ⟨q1, q2, q3, q4, q5⟩ | ⟨q2, q3, q4, q5⟩ | ⟨q1, q3, q4, q5⟩ |
        ⟨q1, q2, q4, q5⟩ | ⟨q1, q2, q3, q5⟩ | ⟨q1, q2, q3, q4⟩
      · exact mg4 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p4 p5 p1 q4 q5 q1
      · exact mg2 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r2 r3 r4 q2 q3 q4
      · exact mg4 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p4 p5 p1 q4 q5 q1
      · exact mg4 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p4 p5 p1 q4 q5 q1
      · exact mg5 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p5 p1 p2 q5 q1 q2
      · exact mg2 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r2 r3 r4 q2 q3 q4
    · exact mg4 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p4 p5 p1 r4 r5 r1
    · exact mg4 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p4 p5 p1 r4 r5 r1
    · exact mg5 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p5 p1 p2 r5 r1 r2
    · rcases hD with ⟨q1, q2, q3, q4, q5⟩ | ⟨q2, q3, q4, q5⟩ | ⟨q1, q3, q4, q5⟩ |
        ⟨q1, q2, q4, q5⟩ | ⟨q1, q2, q3, q5⟩ | ⟨q1, q2, q3, q4⟩
      · exact mg4 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p4 p5 p1 q4 q5 q1
      · exact mg2 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r2 r3 r4 q2 q3 q4
      · exact mg4 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p4 p5 p1 q4 q5 q1
      · exact mg4 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p4 p5 p1 q4 q5 q1
      · exact mg5 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p5 p1 p2 q5 q1 q2
      · exact mg1 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r1 r2 r3 q1 q2 q3
  · rcases hC with ⟨r1, r2, r3, r4, r5⟩ | ⟨r2, r3, r4, r5⟩ | ⟨r1, r3, r4, r5⟩ |
      ⟨r1, r2, r4, r5⟩ | ⟨r1, r2, r3, r5⟩ | ⟨r1, r2, r3, r4⟩
    · exact mg1 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p1 p2 p3 r1 r2 r3
    · rcases hD with ⟨q1, q2, q3, q4, q5⟩ | ⟨q2, q3, q4, q5⟩ | ⟨q1, q3, q4, q5⟩ |
        ⟨q1, q2, q4, q5⟩ | ⟨q1, q2, q3, q5⟩ | ⟨q1, q2, q3, q4⟩
      · exact mg5 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p5 p1 p2 q5 q1 q2
      · exact mg2 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r2 r3 r4 q2 q3 q4
      · exact mg3 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r3 r4 r5 q3 q4 q5
      · exact mg5 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p5 p1 p2 q5 q1 q2
      · exact mg5 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p5 p1 p2 q5 q1 q2
      · exact mg1 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p1 p2 p3 q1 q2 q3
    · rcases hD with ⟨q1, q2, q3, q4, q5⟩ | ⟨q2, q3, q4, q5⟩ | ⟨q1, q3, q4, q5⟩ |
        ⟨q1, q2, q4, q5⟩ | ⟨q1, q2, q3, q5⟩ | ⟨q1, q2, q3, q4⟩
      · exact mg5 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p5 p1 p2 q5 q1 q2
      · exact mg3 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r3 r4 r5 q3 q4 q5
      · exact mg3 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r3 r4 r5 q3 q4 q5
      · exact mg5 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p5 p1 p2 q5 q1 q2
      · exact mg5 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p5 p1 p2 q5 q1 q2
      · exact mg1 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p1 p2 p3 q1 q2 q3
    · exact mg5 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p5 p1 p2 r5 r1 r2
    · exact mg1 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p1 p2 p3 r1 r2 r3
    · exact mg1 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p1 p2 p3 r1 r2 r3
  · rcases hC with ⟨r1, r2, r3, r4, r5⟩ | ⟨r2, r3, r4, r5⟩ | ⟨r1, r3, r4, r5⟩ |
      ⟨r1, r2, r4, r5⟩ | ⟨r1, r2, r3, r5⟩ | ⟨r1, r2, r3, r4⟩
    · exact mg1 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p1 p2 p3 r1 r2 r3
    · exact mg2 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p2 p3 p4 r2 r3 r4
    · rcases hD with ⟨q1, q2, q3, q4, q5⟩ | ⟨q2, q3, q4, q5⟩ | ⟨q1, q3, q4, q5⟩ |
        ⟨q1, q2, q4, q5⟩ | ⟨q1, q2, q3, q5⟩ | ⟨q1, q2, q3, q4⟩
      · exact mg1 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p1 p2 p3 q1 q2 q3
      · exact mg2 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p2 p3 p4 q2 q3 q4
      · exact mg3 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r3 r4 r5 q3 q4 q5
      · exact mg4 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r4 r5 r1 q4 q5 q1
      · exact mg1 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p1 p2 p3 q1 q2 q3
      · exact mg1 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p1 p2 p3 q1 q2 q3
    · rcases hD with ⟨q1, q2, q3, q4, q5⟩ | ⟨q2, q3, q4, q5⟩ | ⟨q1, q3, q4, q5⟩ |
        ⟨q1, q2, q4, q5⟩ | ⟨q1, q2, q3, q5⟩ | ⟨q1, q2, q3, q4⟩
      · exact mg1 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p1 p2 p3 q1 q2 q3
      · exact mg2 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p2 p3 p4 q2 q3 q4
      · exact mg4 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r4 r5 r1 q4 q5 q1
      · exact mg4 h₂ h₃ hh₂4 hh₃4 hne23 htg₂ htg₃ r4 r5 r1 q4 q5 q1
      · exact mg1 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p1 p2 p3 q1 q2 q3
      · exact mg1 h₁ h₃ hh₁4 hh₃4 hne13 htg₁ htg₃ p1 p2 p3 q1 q2 q3
    · exact mg1 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p1 p2 p3 r1 r2 r3
    · exact mg1 h₁ h₂ hh₁4 hh₂4 hne12 htg₁ htg₂ p1 p2 p3 r1 r2 r3

/-- **Single-vertex assembly (dense `|D| = 8` regime).**  A degree-`3` apex `v` adjacent to two
degree-`4` hubs `h₁, h₂`, all avoiding a cherry `x–y–z`, packages into a `SingleVertexConfig`.  The
cross sum vanishes, so the side budget is `8 ≤ 8 + 2·[h₁∼h₂]`. -/
theorem dense_single_vertex_assemble (G : SimpleGraph (Fin 20)) (v h₁ h₂ x y z : Fin 20)
    (hdegv : G.degree v = 3) (hdegh1 : G.degree h₁ = 4) (hdegh2 : G.degree h₂ = 4)
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hvh1 : G.Adj v h₁) (hvh2 : G.Adj v h₂)
    (hxyA : G.Adj x y) (hyzA : G.Adj y z) (hxzN : ¬G.Adj x z)
    (hvx : ¬G.Adj v x) (hvy : ¬G.Adj v y) (hvz : ¬G.Adj v z)
    (hh1x : ¬G.Adj h₁ x) (hh1y : ¬G.Adj h₁ y) (hh1z : ¬G.Adj h₁ z)
    (hh2x : ¬G.Adj h₂ x) (hh2y : ¬G.Adj h₂ y) (hh2z : ¬G.Adj h₂ z)
    (hne_h12 : h₁ ≠ h₂) (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z) :
    SingleVertexConfig G := by
  have hS : (∑ p ∈ ({v, h₁, h₂} : Finset (Fin 20)),
      (G.neighborFinset p ∩ ({x, y, z} : Finset (Fin 20))).card) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_inter, G.mem_neighborFinset] at ha
    obtain ⟨hpa, hamem⟩ := ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hamem
    rcases hp with rfl | rfl | rfl <;> rcases hamem with rfl | rfl | rfl <;>
      first
      | exact hvx hpa | exact hvy hpa | exact hvz hpa
      | exact hh1x hpa | exact hh1y hpa | exact hh1z hpa
      | exact hh2x hpa | exact hh2y hpa | exact hh2z hpa
  refine ⟨v, h₁, h₂, x, y, z, hdegv, hdegx, hdegy, hdegz, hvh1, hvh2, hxyA, hyzA, hxzN, ?_,
    hne_h12, (by rintro rfl; exact hvy hxyA),
    (by rintro rfl; exact hvx hxyA.symm),
    (by rintro rfl; exact hvy hyzA.symm),
    (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
    (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
    hxy_ne, hyz_ne, hxz_ne⟩
  rw [hS, hdegh1, hdegh2]
  by_cases hadj : G.Adj h₁ h₂ <;> simp [hadj]

/-- **Two-hub assembly (dense `|D| = 8` regime).**  Two non-adjacent degree-`4` hubs `h₁, h₂`, each
carrying two private `M`-isolated degree-`3` twins (`a, b` for `h₁`; `c, d` for `h₂`), package into a
`TwoHubConfig`.  Twin/twin and twin/degree-`3` non-adjacencies follow from `M`-isolation. -/
theorem dense_two_hub_assemble (G : SimpleGraph (Fin 20)) (h₁ h₂ a b c d : Fin 20)
    (hdegh1 : G.degree h₁ = 4) (hdegh2 : G.degree h₂ = 4)
    (hdega : G.degree a = 3) (hdegb : G.degree b = 3)
    (hdegc : G.degree c = 3) (hdegd : G.degree d = 3)
    (hah1 : G.Adj a h₁) (hbh1 : G.Adj b h₁) (hch2 : G.Adj c h₂) (hdh2 : G.Adj d h₂)
    (hnadj : ¬G.Adj h₁ h₂)
    (hn_h1c : ¬G.Adj h₁ c) (hn_h1d : ¬G.Adj h₁ d)
    (hn_ah2 : ¬G.Adj a h₂) (hn_bh2 : ¬G.Adj b h₂)
    (haiso : ∀ w : Fin 20, G.Adj a w → G.degree w ≠ 3)
    (hbiso : ∀ w : Fin 20, G.Adj b w → G.degree w ≠ 3)
    (hne_ab : a ≠ b) (hne_cd : c ≠ d) :
    TwoHubConfig G := by
  exact ⟨h₁, h₂, a, b, c, d, hdegh1, hdegh2, hdega, hdegb, hdegc, hdegd,
    hah1, hbh1, hch2, hdh2, hnadj, hn_h1c, hn_h1d, hn_ah2,
    (fun hadj => haiso c hadj hdegc), (fun hadj => haiso d hadj hdegd), hn_bh2,
    (fun hadj => hbiso c hadj hdegc), (fun hadj => hbiso d hadj hdegd),
    (by rintro rfl; exact hn_ah2 hah1),
    (by rintro rfl; exact G.irrefl hah1), (by rintro rfl; exact G.irrefl hbh1),
    (by rintro rfl; omega), (by rintro rfl; omega),
    (by rintro rfl; omega), (by rintro rfl; omega),
    (by rintro rfl; exact G.irrefl hch2), (by rintro rfl; exact G.irrefl hdh2),
    hne_ab, (by rintro rfl; exact hn_ah2 hch2), (by rintro rfl; exact hn_ah2 hdh2),
    (by rintro rfl; exact hn_bh2 hch2), (by rintro rfl; exact hn_bh2 hdh2), hne_cd⟩

/-- **Star-shape extraction (`e(M) ≤ 3`, in-`M`-degree-`3` centre).**  If some `c ∈ D` has
in-`M`-degree `3` under the edge budget `∑_{v∈D}|N v ∩ D| ≤ 6`, then `M` is exactly the star
`K₁,₃` centred at `c`: the three leaves have in-`M`-neighbourhood `{c}`, are pairwise
non-adjacent, and exhaust `N(c)`. -/
theorem star_centre_leaves_twenty (G : SimpleGraph (Fin 20)) (D : Finset (Fin 20))
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 6)
    (c : Fin 20) (hcD : c ∈ D) (hc3 : (G.neighborFinset c ∩ D).card = 3) :
    ∃ l₁ l₂ l₃ : Fin 20, l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧
      G.Adj c l₁ ∧ G.Adj c l₂ ∧ G.Adj c l₃ ∧
      G.degree l₁ = 3 ∧ G.degree l₂ = 3 ∧ G.degree l₃ = 3 ∧
      G.neighborFinset l₁ ∩ D = {c} ∧ G.neighborFinset l₂ ∩ D = {c} ∧
      G.neighborFinset l₃ ∩ D = {c} ∧
      ¬G.Adj l₁ l₂ ∧ ¬G.Adj l₁ l₃ ∧ ¬G.Adj l₂ l₃ ∧
      (∀ w : Fin 20, G.Adj c w → w = l₁ ∨ w = l₂ ∨ w = l₃) := by
  classical
  have hcdeg : G.degree c = 3 := (hmemD c).mp hcD
  have hNceq : G.neighborFinset c ∩ D = G.neighborFinset c :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [G.card_neighborFinset_eq_degree, hcdeg, hc3])
  obtain ⟨l₁, l₂, l₃, h12, h13, h23, hset⟩ := Finset.card_eq_three.mp hc3
  have hmem : ∀ w : Fin 20, w ∈ ({l₁, l₂, l₃} : Finset (Fin 20)) →
      G.Adj c w ∧ w ∈ D ∧ G.degree w = 3 := by
    intro w hw
    have hw2 : w ∈ G.neighborFinset c ∩ D := hset ▸ hw
    obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw2
    exact ⟨(G.mem_neighborFinset _ _).mp hwN, hwD, (hmemD w).mp hwD⟩
  obtain ⟨ha1, hD1, hd1⟩ := hmem l₁ (by simp)
  obtain ⟨ha2, hD2, hd2⟩ := hmem l₂ (by simp)
  obtain ⟨ha3, hD3, hd3⟩ := hmem l₃ (by simp)
  have hcnb : ∀ w : Fin 20, G.Adj c w → w = l₁ ∨ w = l₂ ∨ w = l₃ := by
    intro w hw
    have hw2 : w ∈ G.neighborFinset c ∩ D := by
      rw [hNceq]; exact (G.mem_neighborFinset _ _).mpr hw
    rw [hset] at hw2
    simpa using hw2
  have hsub4 : ({c, l₁, l₂, l₃} : Finset (Fin 20)) ⊆ D := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    exacts [hcD, hD1, hD2, hD3]
  have hsumle : ∑ v ∈ ({c, l₁, l₂, l₃} : Finset (Fin 20)),
      (G.neighborFinset v ∩ D).card ≤ 6 :=
    le_trans (Finset.sum_le_sum_of_subset hsub4) hs6
  have hexp : ∑ v ∈ ({c, l₁, l₂, l₃} : Finset (Fin 20)), (G.neighborFinset v ∩ D).card
      = (G.neighborFinset c ∩ D).card + ((G.neighborFinset l₁ ∩ D).card
        + ((G.neighborFinset l₂ ∩ D).card + (G.neighborFinset l₃ ∩ D).card)) := by
    rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨ha1.ne, ha2.ne, ha3.ne⟩),
      Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
      Finset.sum_singleton]
  have hm1 : c ∈ G.neighborFinset l₁ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha1.symm, hcD⟩
  have hm2 : c ∈ G.neighborFinset l₂ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha2.symm, hcD⟩
  have hm3 : c ∈ G.neighborFinset l₃ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha3.symm, hcD⟩
  have hpos1 : 1 ≤ (G.neighborFinset l₁ ∩ D).card := Finset.card_pos.mpr ⟨c, hm1⟩
  have hpos2 : 1 ≤ (G.neighborFinset l₂ ∩ D).card := Finset.card_pos.mpr ⟨c, hm2⟩
  have hpos3 : 1 ≤ (G.neighborFinset l₃ ∩ D).card := Finset.card_pos.mpr ⟨c, hm3⟩
  have hone1 : (G.neighborFinset l₁ ∩ D).card = 1 := by omega
  have hone2 : (G.neighborFinset l₂ ∩ D).card = 1 := by omega
  have hone3 : (G.neighborFinset l₃ ∩ D).card = 1 := by omega
  have hsingle : ∀ l : Fin 20, c ∈ G.neighborFinset l ∩ D →
      (G.neighborFinset l ∩ D).card = 1 → G.neighborFinset l ∩ D = {c} := by
    intro l hmemc hone
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hone
    rw [hw] at hmemc ⊢
    rw [Finset.mem_singleton] at hmemc
    rw [hmemc]
  have hN1 : G.neighborFinset l₁ ∩ D = {c} := hsingle l₁ hm1 hone1
  have hN2 : G.neighborFinset l₂ ∩ D = {c} := hsingle l₂ hm2 hone2
  have hN3 : G.neighborFinset l₃ ∩ D = {c} := hsingle l₃ hm3 hone3
  have hnadj : ∀ u w : Fin 20, G.neighborFinset u ∩ D = {c} → w ∈ D → G.Adj c w →
      ¬G.Adj u w := by
    intro u w hu hwD hcw hadj
    have hwm : w ∈ G.neighborFinset u ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hwD⟩
    rw [hu, Finset.mem_singleton] at hwm
    exact G.irrefl (hwm ▸ hcw)
  exact ⟨l₁, l₂, l₃, h12, h13, h23, ha1, ha2, ha3, hd1, hd2, hd3, hN1, hN2, hN3,
    hnadj l₁ l₂ hN1 hD2 ha2, hnadj l₁ l₃ hN1 hD3 ha3, hnadj l₂ l₃ hN2 hD3 ha3, hcnb⟩

/-- **Twin-capacity cap for a degree-`5` hub with a non-isolated neighbour.**  A degree-`5`
vertex adjacent to some vertex outside `Iso` has at most `4` neighbours in `Iso`. -/
theorem iso_cap_of_outside_neighbor_twenty (G : SimpleGraph (Fin 20)) (Iso : Finset (Fin 20))
    (h w : Fin 20) (hdeg5 : G.degree h = 5) (hadj : G.Adj h w) (hw : w ∉ Iso) :
    (G.neighborFinset h ∩ Iso).card ≤ 4 := by
  have hsub : G.neighborFinset h ∩ Iso ⊆ (G.neighborFinset h).erase w := by
    intro u hu
    obtain ⟨huN, huIso⟩ := Finset.mem_inter.mp hu
    exact Finset.mem_erase.mpr ⟨fun e => hw (e ▸ huIso), huN⟩
  have hcard : ((G.neighborFinset h).erase w).card = 4 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hadj),
      G.card_neighborFinset_eq_degree, hdeg5]
  exact le_trans (Finset.card_le_card hsub) (le_of_eq hcard)

/-- **Two-twin packaging for a degree-`5` shared hub.**  A degree-`5` hub adjacent to two
distinct `M`-isolated degree-`3` twins, avoiding all three vertices of a cherry `x–y–z` of
degree-`3` vertices, yields a `TwoTwinConfig` (the hub bound there is `G.degree h ≤ 5`). -/
theorem deg5_shared_hub_two_twin_twenty (G : SimpleGraph (Fin 20)) (Iso : Finset (Fin 20))
    (hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3)
    (h x y z : Fin 20) (hdeg5 : G.degree h = 5)
    (h2tw : 2 ≤ (G.neighborFinset h ∩ Iso).card)
    (hdx : G.degree x = 3) (hdy : G.degree y = 3) (hdz : G.degree z = 3)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz_ne : x ≠ z)
    (hhx : ¬G.Adj h x) (hhy : ¬G.Adj h y) (hhz : ¬G.Adj h z) :
    TwoTwinConfig G := by
  classical
  have h1lt : 1 < (G.neighborFinset h ∩ Iso).card := by omega
  obtain ⟨t₁, ht1, t₂, ht2, ht12⟩ := Finset.one_lt_card.mp h1lt
  obtain ⟨ht1N, ht1Iso⟩ := Finset.mem_inter.mp ht1
  obtain ⟨ht2N, ht2Iso⟩ := Finset.mem_inter.mp ht2
  obtain ⟨ht1deg, ht1iso⟩ := hIsoiso t₁ ht1Iso
  obtain ⟨ht2deg, ht2iso⟩ := hIsoiso t₂ ht2Iso
  exact ⟨t₁, t₂, h, x, y, z, ht1deg, ht2deg, le_of_eq hdeg5, hdx, hdy, hdz,
    ((G.mem_neighborFinset _ _).mp ht1N).symm, ((G.mem_neighborFinset _ _).mp ht2N).symm,
    hxy, hyz,
    (fun hadj => ht1iso x hadj hdx), (fun hadj => ht1iso y hadj hdy),
    (fun hadj => ht1iso z hadj hdz),
    (fun hadj => ht2iso x hadj hdx), (fun hadj => ht2iso y hadj hdy),
    (fun hadj => ht2iso z hadj hdz),
    hhx, hhy, hhz, ht12,
    (by rintro rfl; exact ht1iso y hxy hdy), (by rintro rfl; exact ht1iso x hxy.symm hdx),
    (by rintro rfl; exact ht1iso y hyz.symm hdy),
    (by rintro rfl; exact ht2iso y hxy hdy), (by rintro rfl; exact ht2iso x hxy.symm hdx),
    (by rintro rfl; exact ht2iso y hyz.symm hdy),
    (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
    hxy.ne, hyz.ne, hxz_ne⟩

/-- **Cherry-avoiding hub pigeonhole (no-degree-`5` regime).**  If every `M`-isolated twin sends
all `3` of its edges into `Hub₄` (`hsum3`), no degree-`4` hub carries two twins (`hcap`), and
the cherry `x–y–z` receives at most `4` incidences from `Hub₄` (`hbound`), then some twin
retains two cherry-avoiding degree-`4` hubs and the single-vertex assembly applies. -/
theorem cherry_two_free_hubs_twenty (G : SimpleGraph (Fin 20)) (Iso Hub4 : Finset (Fin 20))
    (hmemHub4 : ∀ v : Fin 20, v ∈ Hub4 ↔ G.degree v = 4)
    (hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3)
    (hsum3 : 3 * Iso.card ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card)
    (hIso3 : 3 ≤ Iso.card)
    (hcap : ∀ h : Fin 20, G.degree h = 4 → (G.neighborFinset h ∩ Iso).card ≤ 1)
    (x y z : Fin 20) (hdx : G.degree x = 3) (hdy : G.degree y = 3) (hdz : G.degree z = 3)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : ¬G.Adj x z) (hxz_ne : x ≠ z)
    (hbound : (G.neighborFinset x ∩ Hub4).card + (G.neighborFinset y ∩ Hub4).card
      + (G.neighborFinset z ∩ Hub4).card ≤ 4) :
    SingleVertexConfig G := by
  classical
  set Good : Finset (Fin 20) :=
    Hub4.filter (fun h => ¬G.Adj h x ∧ ¬G.Adj h y ∧ ¬G.Adj h z) with hGooddef
  set Bad : Finset (Fin 20) :=
    Hub4.filter (fun h => ¬(¬G.Adj h x ∧ ¬G.Adj h y ∧ ¬G.Adj h z)) with hBaddef
  have hdisjGB : Disjoint Good Bad := by
    rw [hGooddef, hBaddef]
    exact Finset.disjoint_left.mpr (fun h hG hB =>
      (Finset.mem_filter.mp hB).2 (Finset.mem_filter.mp hG).2)
  have hunGB : Good ∪ Bad = Hub4 := by
    rw [hGooddef, hBaddef]
    ext h
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have hsplitGB : ∀ v : Fin 20, (G.neighborFinset v ∩ Hub4).card
      = (G.neighborFinset v ∩ Good).card + (G.neighborFinset v ∩ Bad).card := by
    intro v
    have hdisj : Disjoint (G.neighborFinset v ∩ Good) (G.neighborFinset v ∩ Bad) :=
      hdisjGB.mono Finset.inter_subset_right Finset.inter_subset_right
    rw [← Finset.card_union_of_disjoint hdisj, ← Finset.inter_union_distrib_left, hunGB]
  have hBadsub : Bad ⊆ (G.neighborFinset x ∩ Hub4) ∪ (G.neighborFinset y ∩ Hub4)
      ∪ (G.neighborFinset z ∩ Hub4) := by
    intro h hh
    rw [hBaddef, Finset.mem_filter] at hh
    obtain ⟨hhHub, hhbad⟩ := hh
    simp only [Finset.mem_union, Finset.mem_inter, G.mem_neighborFinset]
    by_cases e1 : G.Adj h x
    · exact Or.inl (Or.inl ⟨e1.symm, hhHub⟩)
    · by_cases e2 : G.Adj h y
      · exact Or.inl (Or.inr ⟨e2.symm, hhHub⟩)
      · by_cases e3 : G.Adj h z
        · exact Or.inr ⟨e3.symm, hhHub⟩
        · exact absurd ⟨e1, e2, e3⟩ hhbad
  have hBadcard : Bad.card ≤ 4 := by
    refine le_trans (Finset.card_le_card hBadsub) (le_trans (Finset.card_union_le _ _) ?_)
    exact le_trans (Nat.add_le_add_right (Finset.card_union_le _ _) _) hbound
  have hcrossBad : ∑ v ∈ Iso, (G.neighborFinset v ∩ Bad).card
      = ∑ h ∈ Bad, (G.neighborFinset h ∩ Iso).card := cross_count_twenty G Iso Bad
  have hBadsum : ∑ h ∈ Bad, (G.neighborFinset h ∩ Iso).card ≤ 4 := by
    have hBaddeg : ∀ h ∈ Bad, G.degree h = 4 := by
      intro h hh
      rw [hBaddef, Finset.mem_filter] at hh
      exact (hmemHub4 h).mp hh.1
    have hle : ∑ h ∈ Bad, (G.neighborFinset h ∩ Iso).card ≤ ∑ _h ∈ Bad, 1 :=
      Finset.sum_le_sum (fun h hh => hcap h (hBaddeg h hh))
    rw [Finset.sum_const, smul_eq_mul, mul_one] at hle
    omega
  have hsplitsum : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card
      = ∑ v ∈ Iso, (G.neighborFinset v ∩ Good).card
        + ∑ v ∈ Iso, (G.neighborFinset v ∩ Bad).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => hsplitGB v)
  have hkey : ∃ v ∈ Iso, 2 ≤ (G.neighborFinset v ∩ Good).card := by
    by_contra hcon
    push Not at hcon
    have hle : ∑ v ∈ Iso, (G.neighborFinset v ∩ Good).card ≤ ∑ _v ∈ Iso, 1 :=
      Finset.sum_le_sum (fun v hv => by have := hcon v hv; omega)
    rw [Finset.sum_const, smul_eq_mul, mul_one] at hle
    omega
  obtain ⟨v, hvIso, hv2⟩ := hkey
  obtain ⟨hvdeg, hviso⟩ := hIsoiso v hvIso
  have h1lt : 1 < (G.neighborFinset v ∩ Good).card := by omega
  obtain ⟨h₁, hh1, h₂, hh2, hne12⟩ := Finset.one_lt_card.mp h1lt
  obtain ⟨h1N, h1G⟩ := Finset.mem_inter.mp hh1
  obtain ⟨h2N, h2G⟩ := Finset.mem_inter.mp hh2
  rw [hGooddef, Finset.mem_filter] at h1G h2G
  obtain ⟨h1Hub, h1nx, h1ny, h1nz⟩ := h1G
  obtain ⟨h2Hub, h2nx, h2ny, h2nz⟩ := h2G
  exact dense_single_vertex_assemble G v h₁ h₂ x y z hvdeg
    ((hmemHub4 h₁).mp h1Hub) ((hmemHub4 h₂).mp h2Hub) hdx hdy hdz
    ((G.mem_neighborFinset _ _).mp h1N) ((G.mem_neighborFinset _ _).mp h2N) hxy hyz hxz
    (fun hadj => hviso x hadj hdx) (fun hadj => hviso y hadj hdy)
    (fun hadj => hviso z hadj hdz)
    h1nx h1ny h1nz h2nx h2ny h2nz hne12 hxy.ne hyz.ne hxz_ne

/-- **Shared degree-`4` hub or signed-cut configuration, no-degree-`5` regime (`n = 20`).**
All hubs have degree exactly `4`, so `|D| = 8` and `|Hub₄| = 12`; each `M`-isolated twin sends
all `3` of its edges into `Hub₄`.  At `n = 20` the twin pigeonhole **ties** (`3·4 = 12 =
|Hub₄|`), so the shared hub is not forced; the 3-way dichotomy
`nonisolated_le_three_or_star_or_path` routes the tie.  Either `|S| ≤ 3` (then `|Iso| ≥ 5` and
`15 > 12` closes the pigeonhole), or `M` is a star `K₁,₃` / path `P₄`, whose cherry receives at
most `4` hub-incidences, so some twin keeps two cherry-avoiding hubs and
`cherry_two_free_hubs_twenty` produces a `SingleVertexConfig`. -/
theorem shared_deg4_hub_nodeg5_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (h2k2 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hno5 : ∀ v : Fin 20, G.degree v ≤ 4)
    (hs6 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card ≤ 6) :
    (∃ h t₁ t₂ : Fin 20, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 20, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 20, G.Adj t₂ w → G.degree w ≠ 3)) ∨
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  set D : Finset (Fin 20) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub4 : Finset (Fin 20) := Finset.univ.filter (fun v => G.degree v = 4) with hHub4def
  have hmemHub4 : ∀ v : Fin 20, v ∈ Hub4 ↔ G.degree v = 4 := by intro v; rw [hHub4def]; simp
  have hHub4deg : ∀ h ∈ Hub4, G.degree h = 4 := fun h hh => (hmemHub4 h).mp hh
  have hHub4eqDc : Hub4 = Dᶜ := by
    ext w
    rw [hmemHub4, Finset.mem_compl, hmemD]
    constructor
    · intro h4 h3eq; omega
    · intro hne3; have := h3 w; have := hno5 w; omega
  have hDcdeg4 : ∀ v ∈ Dᶜ, G.degree v = 4 := by
    intro v hv; rw [Finset.mem_compl, hmemD] at hv; have := h3 v; have := hno5 v; omega
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsumDc : ∑ v ∈ Dᶜ, G.degree v = 4 * Dᶜ.card := by
    rw [Finset.sum_congr rfl hDcdeg4, Finset.sum_const, smul_eq_mul, mul_comm]
  have hsum48 : ∑ v : Fin 20, G.degree v = 72 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 72 := by
    rw [Finset.sum_add_sum_compl]; exact hsum48
  have hcc : D.card + Dᶜ.card = 20 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h
    exact h
  have hD8 : D.card = 8 := by rw [hsumD, hsumDc] at hsplit; omega
  have hHub4card : Hub4.card = 12 := by rw [hHub4eqDc]; omega
  set Iso : Finset (Fin 20) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3 := by
    intro v hv
    rw [hIsodef, Finset.mem_filter] at hv
    obtain ⟨hvD, hv0⟩ := hv
    refine ⟨(hmemD v).mp hvD, fun w hadj hw3 => ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
    exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
  have hpart := Finset.card_filter_add_card_filter_not (s := D)
    (fun v => (G.neighborFinset v ∩ D).card = 0)
  rw [← hIsodef] at hpart
  have hnb := nonisolated_component_bound G D hmemD h2k2
  have hIso4 : 4 ≤ Iso.card := by omega
  have hthree : ∀ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card = 3 := by
    intro v hv
    obtain ⟨hvdeg3, _⟩ := hIsoiso v hv
    have hv0 : (G.neighborFinset v ∩ D).card = 0 := by
      rw [hIsodef, Finset.mem_filter] at hv; exact hv.2
    have hsub : G.neighborFinset v ⊆ Hub4 := by
      rw [hHub4eqDc]
      intro w hw
      rw [Finset.mem_compl, hmemD]
      intro hw3
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
      exact hv0 w (Finset.mem_inter.mpr ⟨hw, (hmemD w).mpr hw3⟩)
    rw [Finset.inter_eq_left.mpr hsub, G.card_neighborFinset_eq_degree, hvdeg3]
  have hsum3 : 3 * Iso.card ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
    have hns := Finset.card_nsmul_le_sum Iso
      (fun v => (G.neighborFinset v ∩ Hub4).card) 3
      (fun v hv => le_of_eq (hthree v hv).symm)
    simpa [smul_eq_mul, mul_comm] using hns
  by_cases hshare : ∃ h t₁ t₂ : Fin 20, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 20, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 20, G.Adj t₂ w → G.degree w ≠ 3)
  · exact Or.inl hshare
  have hcap : ∀ h : Fin 20, G.degree h = 4 → (G.neighborFinset h ∩ Iso).card ≤ 1 := by
    intro h hh4
    by_contra hcon
    push Not at hcon
    obtain ⟨t₁, ht1, t₂, ht2, ht12⟩ := Finset.one_lt_card.mp hcon
    obtain ⟨ht1N, ht1Iso⟩ := Finset.mem_inter.mp ht1
    obtain ⟨ht2N, ht2Iso⟩ := Finset.mem_inter.mp ht2
    obtain ⟨ht1deg, ht1iso⟩ := hIsoiso t₁ ht1Iso
    obtain ⟨ht2deg, ht2iso⟩ := hIsoiso t₂ ht2Iso
    exact hshare ⟨h, t₁, t₂, hh4, ht12, ht1deg, ht2deg,
      ((G.mem_neighborFinset _ _).mp ht1N).symm, ((G.mem_neighborFinset _ _).mp ht2N).symm,
      ht1iso, ht2iso⟩
  have hdegsplit : ∀ v : Fin 20,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
    intro v
    have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dᶜ) :=
      Finset.disjoint_left.mpr (fun a ha ha2 => by
        rw [Finset.mem_inter] at ha ha2; exact (Finset.mem_compl.mp ha2.2) ha.2)
    have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dᶜ) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
  rcases nonisolated_le_three_or_star_or_path G D hmemD h2k2 hs6 with
    hS3 | ⟨c, hcD, hc3in⟩ | ⟨a, b, c, _d, _hcard4, haD, hbD, hcD, _hdD,
      hab, hbc, _hcd, nac, _nad, _nbd, ha1, hb2, hc2, _hd1⟩
  · -- `|S| ≤ 3`: at least five isolated twins, and `15 > 12` closes the pigeonhole.
    simp only [ne_eq] at hS3
    have hcount : Hub4.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by omega
    exact absurd (shared_deg4_hub_from_count_twenty G Iso Hub4 hIsoiso hHub4deg hcount) hshare
  · -- Star `K₁,₃`: the cherry `l₁ – c – l₂` receives at most `2 + 0 + 2 = 4` hub-incidences.
    obtain ⟨l₁, l₂, l₃, h12, _h13, _h23, hal1, hal2, _hal3, hld1, hld2, _hld3,
      hN1, hN2, _hN3, hn12, _hn13, _hn23, _hcnb⟩ :=
      star_centre_leaves_twenty G D hmemD hs6 c hcD hc3in
    have hcdeg : G.degree c = 3 := (hmemD c).mp hcD
    have hbx : (G.neighborFinset l₁ ∩ Hub4).card = 2 := by
      have hds := hdegsplit l₁
      rw [hN1, Finset.card_singleton] at hds
      rw [hHub4eqDc]
      omega
    have hby : (G.neighborFinset c ∩ Hub4).card = 0 := by
      have hds := hdegsplit c
      rw [hc3in] at hds
      rw [hHub4eqDc]
      omega
    have hbz : (G.neighborFinset l₂ ∩ Hub4).card = 2 := by
      have hds := hdegsplit l₂
      rw [hN2, Finset.card_singleton] at hds
      rw [hHub4eqDc]
      omega
    exact Or.inr (Or.inl (cherry_two_free_hubs_twenty G Iso Hub4 hmemHub4 hIsoiso hsum3
      (by omega) hcap l₁ c l₂ hld1 hcdeg hld2 hal1.symm hal2 hn12 h12 (by omega)))
  · -- Path `P₄`: the cherry `a – b – c` receives at most `2 + 1 + 1 = 4` hub-incidences.
    have hdega : G.degree a = 3 := (hmemD a).mp haD
    have hdegb : G.degree b = 3 := (hmemD b).mp hbD
    have hdegc : G.degree c = 3 := (hmemD c).mp hcD
    have hacne : a ≠ c := by
      intro e
      rw [e] at ha1
      omega
    have hbx : (G.neighborFinset a ∩ Hub4).card = 2 := by
      have hds := hdegsplit a
      rw [ha1] at hds
      rw [hHub4eqDc]
      omega
    have hby : (G.neighborFinset b ∩ Hub4).card = 1 := by
      have hds := hdegsplit b
      rw [hb2] at hds
      rw [hHub4eqDc]
      omega
    have hbz : (G.neighborFinset c ∩ Hub4).card = 1 := by
      have hds := hdegsplit c
      rw [hc2] at hds
      rw [hHub4eqDc]
      omega
    exact Or.inr (Or.inl (cherry_two_free_hubs_twenty G Iso Hub4 hmemHub4 hIsoiso hsum3
      (by omega) hcap a b c hdega hdegb hdegc hab hbc nac hacne (by omega)))

/-- **Shared degree-`4` hub or signed-cut configuration, degree-`5` regime (`n = 20`).**  With
`g` of degree `≥ 5` we get `|D| ≥ 9`, `|Iso| ≥ |D| − 4` and `|H₅| ≤ |D| − 8`; the refined cross
count `∑_{v∈Iso}|N v ∩ Hub₄| ≥ 3|Iso| − ∑_{H₅} deg` needs `|Iso| + |D| + |Hub₄| ≥ 25`, which at
`n = 20` ties by exactly `1` when `|S| = 4` and `|H₅| = |D| − 8`.  The 3-way dichotomy routes
the tie: `|S| ≤ 3` restores the count; a degree-`≥ 6` hub gives `|H₅| ≤ |D| − 9` and the plain
count closes; otherwise every `H₅`-hub has degree exactly `5` and in the star/path shapes it is
capped at `4` twins (avoiding the cherry with two twins is a `TwoTwinConfig`; a blocked hub
spends one of its `5` slots on the cherry), so `3(|D| − 4) ≤ |Hub₄| + 4|H₅| ≤ 2|D| − 4` forces
`|D| ≤ 8`, contradicting `|D| ≥ 9`. -/
theorem shared_deg4_hub_deg5_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (_hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (_hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (h2k2 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hs6 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card ≤ 6)
    (g : Fin 20) (hg5 : 5 ≤ G.degree g) :
    (∃ h t₁ t₂ : Fin 20, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 20, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 20, G.Adj t₂ w → G.degree w ≠ 3)) ∨
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  set D : Finset (Fin 20) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 20) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 20, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  set Hub4 : Finset (Fin 20) := Finset.univ.filter (fun v => G.degree v = 4) with hHub4def
  have hmemHub4 : ∀ v : Fin 20, v ∈ Hub4 ↔ G.degree v = 4 := by intro v; rw [hHub4def]; simp
  have hHub4deg : ∀ h ∈ Hub4, G.degree h = 4 := fun h hh => (hmemHub4 h).mp hh
  set H5 : Finset (Fin 20) := Finset.univ.filter (fun v => 5 ≤ G.degree v) with hH5def
  have hmemH5 : ∀ v : Fin 20, v ∈ H5 ↔ 5 ≤ G.degree v := by intro v; rw [hH5def]; simp
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  have hDcdeg : ∀ v ∈ Dᶜ, 4 ≤ G.degree v := by
    intro v hv; rw [Finset.mem_compl, hmemD] at hv; have := h3 v; omega
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsum52 : ∑ v : Fin 20, G.degree v = 72 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 72 := by
    rw [Finset.sum_add_sum_compl]; exact hsum52
  have hcc : D.card + Dᶜ.card = 20 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h; exact h
  have hgDc : g ∈ Dᶜ := by rw [Finset.mem_compl, hmemD]; omega
  have hD9 : 9 ≤ D.card := by
    have hsg := (Finset.add_sum_erase Dᶜ (fun v => G.degree v) hgDc).symm
    have hrest : 4 * (Dᶜ.erase g).card ≤ ∑ v ∈ Dᶜ.erase g, G.degree v := by
      have hb : ∀ x ∈ Dᶜ.erase g, 4 ≤ G.degree x :=
        fun x hx => hDcdeg x (Finset.mem_of_mem_erase hx)
      have hns := Finset.card_nsmul_le_sum (Dᶜ.erase g) (fun v => G.degree v) 4 hb
      simpa [smul_eq_mul, mul_comm] using hns
    have hcg : (Dᶜ.erase g).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hgDc
    have hpos : 1 ≤ Dᶜ.card := Finset.card_pos.mpr ⟨g, hgDc⟩
    omega
  have hH5le : H5.card ≤ D.card - 8 := by
    have hpt : ∀ v ∈ Dᶜ, 4 + (if v ∈ H5 then 1 else 0) ≤ G.degree v := by
      intro v hv
      by_cases hvH5 : v ∈ H5
      · rw [if_pos hvH5]; have := (hmemH5 v).mp hvH5; omega
      · rw [if_neg hvH5]; exact hDcdeg v hv
    have hsumpt : ∑ v ∈ Dᶜ, (4 + (if v ∈ H5 then 1 else 0)) ≤ ∑ v ∈ Dᶜ, G.degree v :=
      Finset.sum_le_sum hpt
    have hsumval : ∑ v ∈ Dᶜ, (4 + (if v ∈ H5 then 1 else 0))
        = 4 * Dᶜ.card + H5.card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm,
        ← Finset.card_filter]
      have hfilt : Dᶜ.filter (fun v => v ∈ H5) = H5 := by
        apply Finset.Subset.antisymm
        · intro v hv; exact (Finset.mem_filter.mp hv).2
        · intro v hv
          have hvge : 5 ≤ G.degree v := (hmemH5 v).mp hv
          exact Finset.mem_filter.mpr ⟨by rw [Finset.mem_compl, hmemD]; omega, hv⟩
      rw [hfilt]
    rw [hsumval] at hsumpt
    omega
  set Iso : Finset (Fin 20) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3 := by
    intro v hv
    rw [hIsodef, Finset.mem_filter] at hv
    obtain ⟨hvD, hv0⟩ := hv
    refine ⟨(hmemD v).mp hvD, fun w hadj hw3 => ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
    exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
  have hpart := Finset.card_filter_add_card_filter_not (s := D)
    (fun v => (G.neighborFinset v ∩ D).card = 0)
  rw [← hIsodef] at hpart
  have hnb := nonisolated_component_bound G D hmemD h2k2
  have hIso5 : D.card - 4 ≤ Iso.card := by omega
  have hdisjHub : Disjoint Hub4 H5 :=
    Finset.disjoint_left.mpr (fun a ha ha2 => by
      have := (hmemHub4 a).mp ha; have := (hmemH5 a).mp ha2; omega)
  have huHub : Hub4 ∪ H5 = Hub := by
    ext w; rw [Finset.mem_union, hmemHub4, hmemH5, hmemHub]; omega
  have hHubpart : Hub4.card + H5.card = Dᶜ.card := by
    rw [← hHubeqDc, ← huHub, Finset.card_union_of_disjoint hdisjHub]
  have hHub4degsum : ∑ v ∈ Hub4, G.degree v = 4 * Hub4.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemHub4 v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hDcdegsplit : ∑ v ∈ Hub4, G.degree v + ∑ v ∈ H5, G.degree v = ∑ v ∈ Dᶜ, G.degree v := by
    rw [← Finset.sum_union hdisjHub, huHub.trans hHubeqDc]
  have hsumHub3 : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card = 3 * Iso.card := by
    rw [Finset.sum_congr rfl (fun v hv => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hIsodef, Finset.mem_filter] at hv
    exact each_iso_three_hubs G D Hub hmemD hmemHub h3 v hv.1 hv.2
  have hvsplit : ∀ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card + (G.neighborFinset v ∩ H5).card
      = (G.neighborFinset v ∩ Hub).card := by
    intro v _
    have hdisj : Disjoint (G.neighborFinset v ∩ Hub4) (G.neighborFinset v ∩ H5) :=
      Finset.disjoint_left.mpr (fun a ha ha2 => by
        rw [Finset.mem_inter] at ha ha2
        have := (hmemHub4 a).mp ha.2; have := (hmemH5 a).mp ha2.2; omega)
    rw [← Finset.card_union_of_disjoint hdisj, ← Finset.inter_union_distrib_left, huHub]
  have hsumsplit : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card
      + ∑ v ∈ Iso, (G.neighborFinset v ∩ H5).card = 3 * Iso.card := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hvsplit, hsumHub3]
  have hcrossH5 : ∑ v ∈ Iso, (G.neighborFinset v ∩ H5).card
      = ∑ h ∈ H5, (G.neighborFinset h ∩ Iso).card := cross_count_twenty G Iso H5
  have hcross4 : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card
      = ∑ h ∈ Hub4, (G.neighborFinset h ∩ Iso).card := cross_count_twenty G Iso Hub4
  have hH5degbound : ∑ h ∈ H5, (G.neighborFinset h ∩ Iso).card ≤ ∑ h ∈ H5, G.degree h := by
    apply Finset.sum_le_sum
    intro h _
    calc (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree h := G.card_neighborFinset_eq_degree h
  by_cases hshare : ∃ h t₁ t₂ : Fin 20, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 20, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 20, G.Adj t₂ w → G.degree w ≠ 3)
  · exact Or.inl hshare
  have hcap4 : ∀ h : Fin 20, G.degree h = 4 → (G.neighborFinset h ∩ Iso).card ≤ 1 := by
    intro h hh4
    by_contra hcon
    push Not at hcon
    obtain ⟨t₁, ht1, t₂, ht2, ht12⟩ := Finset.one_lt_card.mp hcon
    obtain ⟨ht1N, ht1Iso⟩ := Finset.mem_inter.mp ht1
    obtain ⟨ht2N, ht2Iso⟩ := Finset.mem_inter.mp ht2
    obtain ⟨ht1deg, ht1iso⟩ := hIsoiso t₁ ht1Iso
    obtain ⟨ht2deg, ht2iso⟩ := hIsoiso t₂ ht2Iso
    exact hshare ⟨h, t₁, t₂, hh4, ht12, ht1deg, ht2deg,
      ((G.mem_neighborFinset _ _).mp ht1N).symm, ((G.mem_neighborFinset _ _).mp ht2N).symm,
      ht1iso, ht2iso⟩
  have hsum4cap : ∑ h ∈ Hub4, (G.neighborFinset h ∩ Iso).card ≤ Hub4.card := by
    have hle : ∑ h ∈ Hub4, (G.neighborFinset h ∩ Iso).card ≤ ∑ _h ∈ Hub4, 1 :=
      Finset.sum_le_sum (fun h hh => hcap4 h (hHub4deg h hh))
    rw [Finset.sum_const, smul_eq_mul, mul_one] at hle
    exact hle
  by_cases hbig : ∃ h ∈ H5, 6 ≤ G.degree h
  · -- A degree-`≥ 6` hub: `∑_{H₅} deg ≥ 5|H₅| + 1`, so `|H₅| ≤ |D| − 9` and the count closes.
    obtain ⟨h₀, hh0H5, hh06⟩ := hbig
    have hsg := (Finset.add_sum_erase H5 (fun v => G.degree v) hh0H5).symm
    have hrest : 5 * (H5.erase h₀).card ≤ ∑ v ∈ H5.erase h₀, G.degree v := by
      have hb : ∀ x ∈ H5.erase h₀, 5 ≤ G.degree x :=
        fun x hx => (hmemH5 x).mp (Finset.mem_of_mem_erase hx)
      have hns := Finset.card_nsmul_le_sum (H5.erase h₀) (fun v => G.degree v) 5 hb
      simpa [smul_eq_mul, mul_comm] using hns
    have hcg : (H5.erase h₀).card = H5.card - 1 := Finset.card_erase_of_mem hh0H5
    have hposH5 : 1 ≤ H5.card := Finset.card_pos.mpr ⟨h₀, hh0H5⟩
    have hcount : Hub4.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by omega
    exact absurd (shared_deg4_hub_from_count_twenty G Iso Hub4 hIsoiso hHub4deg hcount) hshare
  have hH5deg5 : ∀ h ∈ H5, G.degree h = 5 := by
    intro h hh
    have h5 := (hmemH5 h).mp hh
    have hlt : G.degree h < 6 := by
      by_contra hcon
      push Not at hcon
      exact hbig ⟨h, hh, hcon⟩
    omega
  by_cases hTT : TwoTwinConfig G
  · exact Or.inr (Or.inr (Or.inl hTT))
  rcases nonisolated_le_three_or_star_or_path G D hmemD h2k2 hs6 with
    hS3 | ⟨c, hcD, hc3in⟩ | ⟨a, b, c, _d, _hcard4, haD, hbD, hcD, _hdD,
      hab, hbc, _hcd, _nac, _nad, _nbd, ha1, hb2, hc2, _hd1⟩
  · -- `|S| ≤ 3`: `|Iso| ≥ |D| − 3` restores the refined count.
    simp only [ne_eq] at hS3
    have hIso3 : D.card - 3 ≤ Iso.card := by omega
    have hcount : Hub4.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by omega
    exact absurd (shared_deg4_hub_from_count_twenty G Iso Hub4 hIsoiso hHub4deg hcount) hshare
  · -- Star `K₁,₃`: every degree-`5` hub is capped at `4` twins via the cherry `l₁ – c – l₂`.
    obtain ⟨l₁, l₂, l₃, h12, _h13, _h23, hal1, hal2, _hal3, hld1, hld2, _hld3,
      hN1, hN2, _hN3, _hn12, _hn13, _hn23, hcnb⟩ :=
      star_centre_leaves_twenty G D hmemD hs6 c hcD hc3in
    have hcdeg : G.degree c = 3 := (hmemD c).mp hcD
    have hl1NotIso : l₁ ∉ Iso := by
      intro hmem
      rw [hIsodef, Finset.mem_filter] at hmem
      have h1 : (G.neighborFinset l₁ ∩ D).card = 0 := hmem.2
      rw [hN1, Finset.card_singleton] at h1
      exact one_ne_zero h1
    have hl2NotIso : l₂ ∉ Iso := by
      intro hmem
      rw [hIsodef, Finset.mem_filter] at hmem
      have h1 : (G.neighborFinset l₂ ∩ D).card = 0 := hmem.2
      rw [hN2, Finset.card_singleton] at h1
      exact one_ne_zero h1
    have hnc : ∀ hv : Fin 20, G.degree hv = 5 → ¬G.Adj hv c := by
      intro hv h5 hadj
      rcases hcnb hv hadj.symm with rfl | rfl | rfl <;> omega
    have hcap5 : ∀ h ∈ H5, (G.neighborFinset h ∩ Iso).card ≤ 4 := by
      intro h hh
      have hdeg5 := hH5deg5 h hh
      by_cases h2tw : 2 ≤ (G.neighborFinset h ∩ Iso).card
      · by_cases e1 : G.Adj h l₁
        · exact iso_cap_of_outside_neighbor_twenty G Iso h l₁ hdeg5 e1 hl1NotIso
        · by_cases e2 : G.Adj h l₂
          · exact iso_cap_of_outside_neighbor_twenty G Iso h l₂ hdeg5 e2 hl2NotIso
          · exact absurd (deg5_shared_hub_two_twin_twenty G Iso hIsoiso h l₁ c l₂ hdeg5 h2tw
              hld1 hcdeg hld2 hal1.symm hal2 h12 e1 (hnc h hdeg5) e2) hTT
      · omega
    have hsum45 : ∑ h ∈ H5, (G.neighborFinset h ∩ Iso).card ≤ 4 * H5.card := by
      have hle : ∑ h ∈ H5, (G.neighborFinset h ∩ Iso).card ≤ ∑ _h ∈ H5, 4 :=
        Finset.sum_le_sum hcap5
      rw [Finset.sum_const, smul_eq_mul, mul_comm] at hle
      exact hle
    exfalso
    omega
  · -- Path `P₄`: every degree-`5` hub is capped at `4` twins via the cherry `a – b – c`.
    have hdega : G.degree a = 3 := (hmemD a).mp haD
    have hdegb : G.degree b = 3 := (hmemD b).mp hbD
    have hdegc : G.degree c = 3 := (hmemD c).mp hcD
    have hacne : a ≠ c := by
      intro e
      rw [e] at ha1
      omega
    have haNotIso : a ∉ Iso := by
      intro hmem
      rw [hIsodef, Finset.mem_filter] at hmem
      have h1 : (G.neighborFinset a ∩ D).card = 0 := hmem.2
      omega
    have hbNotIso : b ∉ Iso := by
      intro hmem
      rw [hIsodef, Finset.mem_filter] at hmem
      have h1 : (G.neighborFinset b ∩ D).card = 0 := hmem.2
      omega
    have hcNotIso : c ∉ Iso := by
      intro hmem
      rw [hIsodef, Finset.mem_filter] at hmem
      have h1 : (G.neighborFinset c ∩ D).card = 0 := hmem.2
      omega
    have hcap5 : ∀ h ∈ H5, (G.neighborFinset h ∩ Iso).card ≤ 4 := by
      intro h hh
      have hdeg5 := hH5deg5 h hh
      by_cases h2tw : 2 ≤ (G.neighborFinset h ∩ Iso).card
      · by_cases ea : G.Adj h a
        · exact iso_cap_of_outside_neighbor_twenty G Iso h a hdeg5 ea haNotIso
        · by_cases eb : G.Adj h b
          · exact iso_cap_of_outside_neighbor_twenty G Iso h b hdeg5 eb hbNotIso
          · by_cases ec : G.Adj h c
            · exact iso_cap_of_outside_neighbor_twenty G Iso h c hdeg5 ec hcNotIso
            · exact absurd (deg5_shared_hub_two_twin_twenty G Iso hIsoiso h a b c hdeg5 h2tw
                hdega hdegb hdegc hab hbc hacne ea eb ec) hTT
      · omega
    have hsum45 : ∑ h ∈ H5, (G.neighborFinset h ∩ Iso).card ≤ 4 * H5.card := by
      have hle : ∑ h ∈ H5, (G.neighborFinset h ∩ Iso).card ≤ ∑ _h ∈ H5, 4 :=
        Finset.sum_le_sum hcap5
      rw [Finset.sum_const, smul_eq_mul, mul_comm] at hle
      exact hle
    exfalso
    omega

end N20

end ACMax
