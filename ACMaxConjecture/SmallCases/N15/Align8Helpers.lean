import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N15.Dense
import ACMaxConjecture.SmallCases.N15.Core

/-!
# Assembly cluster for the `n = 15` `e(M) = 3` / `e(M) ≥ 4` alignment corners

Ported `Fin 14 → Fin 15` analogues of the single-vertex / two-hub assembly lemmas used to close the
residual alignment corners (`exists_align_six_config_fifteen` `|D| = 8`, `halign8_fifteen`).  The
single-vertex selectors route the proved degree-`4` double-star / `C₅` hub-avoidance lemmas
(`hub_meets_path_le_one_fifteen`, `hub_cycle_cases_fifteen`) through `assemble_single_vertex_config`;
the dense assembly lemmas package the rigid `|D| = 8` regime into `SingleVertexConfig` / `TwoHubConfig`.
-/

namespace ACMax

open scoped Classical

namespace N15

theorem assemble_single_vertex_config (G : SimpleGraph (Fin 15))
    (t h₁ h₂ x y z : Fin 15)
    (ht3 : G.degree t = 3) (htiso : ∀ w : Fin 15, G.Adj t w → G.degree w ≠ 3)
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
  have hsum0 : ∑ p ∈ ({t, h₁, h₂} : Finset (Fin 15)),
      (G.neighborFinset p ∩ ({x, y, z} : Finset (Fin 15))).card = 0 := by
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
  have hside : 2 * (∑ p ∈ ({t, h₁, h₂} : Finset (Fin 15)),
      (G.neighborFinset p ∩ ({x, y, z} : Finset (Fin 15))).card)
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

theorem dom_doublestar_leaves (G : SimpleGraph (Fin 15)) (D : Finset (Fin 15))
    (hmemD : ∀ v : Fin 15, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 15, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (c₁ c₂ : Fin 15) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 3) (hin2 : (G.neighborFinset c₂ ∩ D).card = 3)
    (hdom : ∀ p q : Fin 15, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂) :
    ∃ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Fin 15,
      G.degree ℓ₁ = 3 ∧ G.degree ℓ₂ = 3 ∧ G.degree ℓ₃ = 3 ∧ G.degree ℓ₄ = 3 ∧
      ({c₁, c₂, ℓ₁, ℓ₂, ℓ₃, ℓ₄} : Finset (Fin 15)).card = 6 ∧
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
  have hmem1 : ∀ w : Fin 15, w = ℓ₁ ∨ w = ℓ₂ →
      w ≠ c₂ ∧ G.Adj c₁ w ∧ G.degree w = 3 := by
    intro w hw
    have hwe : w ∈ (G.neighborFinset c₁ ∩ D).erase c₂ := by
      rw [hℓset1]; rcases hw with rfl | rfl <;> simp
    rw [Finset.mem_erase] at hwe
    obtain ⟨hwc2, hwND⟩ := hwe
    obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hwND
    exact ⟨hwc2, (G.mem_neighborFinset _ _).mp hwN, (hmemD w).mp hwD⟩
  have hmem2 : ∀ w : Fin 15, w = ℓ₃ ∨ w = ℓ₄ →
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
  have hcross : ∀ u v : Fin 15, G.neighborFinset u ∩ D = {c₁} →
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
  have hcard6 : ({c₁, c₂, ℓ₁, ℓ₂, ℓ₃, ℓ₄} : Finset (Fin 15)).card = 6 := by
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

theorem dom_centres_indeg3 (G : SimpleGraph (Fin 15)) (D : Finset (Fin 15))
    (c₁ c₂ : Fin 15) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hindle : ∀ x : Fin 15, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3)
    (hcov : ∀ p q : Fin 15, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hsum : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 10) :
    (G.neighborFinset c₁ ∩ D).card = 3 ∧ (G.neighborFinset c₂ ∩ D).card = 3 := by
  classical
  have hsub : ({c₁, c₂} : Finset (Fin 15)) ⊆ D := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl; exacts [hc1D, hc2D]
  have hsplit :
      ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 15)), (G.neighborFinset v ∩ D).card
        + ∑ v ∈ ({c₁, c₂} : Finset (Fin 15)), (G.neighborFinset v ∩ D).card
      = ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
    Finset.sum_sdiff hsub
  have hpair : ∑ v ∈ ({c₁, c₂} : Finset (Fin 15)), (G.neighborFinset v ∩ D).card
      = (G.neighborFinset c₁ ∩ D).card + (G.neighborFinset c₂ ∩ D).card := by
    rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
  have hScong :
      ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 15)), (G.neighborFinset v ∩ D).card
        = ∑ v ∈ D \ ({c₁, c₂} : Finset (Fin 15)),
          (G.neighborFinset v ∩ ({c₁, c₂} : Finset (Fin 15))).card := by
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
    cross_count G (D \ ({c₁, c₂} : Finset (Fin 15)))
      ({c₁, c₂} : Finset (Fin 15))] at hsplit
  have hpair2 : ∑ w ∈ ({c₁, c₂} : Finset (Fin 15)),
        (G.neighborFinset w ∩ (D \ ({c₁, c₂} : Finset (Fin 15)))).card
      = (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 15)))).card
        + (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 15)))).card := by
    rw [Finset.sum_insert (by simp [hc12.ne]), Finset.sum_singleton]
  have hc2mem : c₂ ∈ G.neighborFinset c₁ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
  have hc1mem : c₁ ∈ G.neighborFinset c₂ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
  have hb1eq : (G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 15)))).card
      = (G.neighborFinset c₁ ∩ D).card - 1 := by
    have heq : G.neighborFinset c₁ ∩ (D \ ({c₁, c₂} : Finset (Fin 15)))
        = (G.neighborFinset c₁ ∩ D).erase c₂ := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_erase, G.mem_neighborFinset,
        Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · rintro ⟨hadj, hwD, _, hwc2⟩; exact ⟨hwc2, hadj, hwD⟩
      · rintro ⟨hwc2, hadj, hwD⟩
        exact ⟨hadj, hwD, fun e => G.irrefl (e ▸ hadj), hwc2⟩
    rw [heq, Finset.card_erase_of_mem hc2mem]
  have hb2eq : (G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 15)))).card
      = (G.neighborFinset c₂ ∩ D).card - 1 := by
    have heq : G.neighborFinset c₂ ∩ (D \ ({c₁, c₂} : Finset (Fin 15)))
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
theorem single_vertex_doublestar_count (G : SimpleGraph (Fin 15)) (D : Finset (Fin 15))
    (hmemD : ∀ v : Fin 15, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 15, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (t a b c : Fin 15) (ht3 : G.degree t = 3)
    (htiso : ∀ w : Fin 15, G.Adj t w → G.degree w ≠ 3)
    (hda : G.degree a = 4) (hdb : G.degree b = 4) (hdc : G.degree c = 4)
    (habne : a ≠ b) (hacne : a ≠ c) (hbcne : b ≠ c)
    (hta : G.Adj t a) (htb : G.Adj t b) (htc : G.Adj t c)
    (c₁ c₂ : Fin 15) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 3) (hin2 : (G.neighborFinset c₂ ∩ D).card = 3)
    (hdom : ∀ p q : Fin 15, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂) :
    SingleVertexConfig G := by
  classical
  have hc1deg : G.degree c₁ = 3 := (hmemD c₁).mp hc1D
  have hc2deg : G.degree c₂ = 3 := (hmemD c₂).mp hc2D
  obtain ⟨ℓ₁, ℓ₂, ℓ₃, ℓ₄, hd1, hd2, hd3, hd4, hcard6,
      hac1, hac2, hac3, hac4, hND1, hND2, hND3, hND4, hn1, hn2, hn3, hn4, hℓ12, hℓ34⟩ :=
    dom_doublestar_leaves G D hmemD hT c₁ c₂ hc1D hc2D hc12 hin1 hin2 hdom
  have leafdeg : ∀ w : Fin 15, (w = ℓ₁ ∨ w = ℓ₂ ∨ w = ℓ₃ ∨ w = ℓ₄) → G.degree w = 3 := by
    rintro w (rfl | rfl | rfl | rfl) <;> assumption
  have leafD : ∀ w : Fin 15, (w = ℓ₁ ∨ w = ℓ₂ ∨ w = ℓ₃ ∨ w = ℓ₄) → w ∈ D :=
    fun w hw => (hmemD w).mpr (leafdeg w hw)
  have hlne : ∀ w cen oth : Fin 15, G.neighborFinset w ∩ D = {cen} →
      (G.neighborFinset oth ∩ D).card = 3 → w ≠ oth := by
    intro w cen oth hw hoth e
    subst e
    rw [hw, Finset.card_singleton] at hoth
    omega
  have hleafnec : ∀ w : Fin 15, (w = ℓ₁ ∨ w = ℓ₂ ∨ w = ℓ₃ ∨ w = ℓ₄) → w ≠ c₁ ∧ w ≠ c₂ := by
    rintro w (rfl | rfl | rfl | rfl)
    · exact ⟨(G.ne_of_adj hac1).symm, hlne w c₁ c₂ hND1 hin2⟩
    · exact ⟨(G.ne_of_adj hac2).symm, hlne w c₁ c₂ hND2 hin2⟩
    · exact ⟨hlne w c₂ c₁ hND3 hin1, (G.ne_of_adj hac3).symm⟩
    · exact ⟨hlne w c₂ c₁ hND4 hin1, (G.ne_of_adj hac4).symm⟩
  have hleafnonadj : ∀ u v : Fin 15, (u = ℓ₁ ∨ u = ℓ₂ ∨ u = ℓ₃ ∨ u = ℓ₄) →
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
  have hubcen : ∀ hh : Fin 15, (hh = a ∨ hh = b ∨ hh = c) →
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
  have hpair : ∀ hh : Fin 15, G.degree hh = 4 →
      ¬(G.Adj hh ℓ₁ ∧ G.Adj hh ℓ₂) ∧ ¬(G.Adj hh ℓ₃ ∧ G.Adj hh ℓ₄) := by
    intro hh hh4
    refine ⟨?_, ?_⟩
    · exact (hub_meets_path_le_one_fifteen G hT hC4 hh4 hd1 hc1deg hd2
        hac1.symm hac2
        (hleafnonadj ℓ₁ ℓ₂ (Or.inl rfl) (Or.inr (Or.inl rfl)) hℓ12)
        (G.ne_of_adj hac1).symm (G.ne_of_adj hac2) hℓ12).2.2
    · exact (hub_meets_path_le_one_fifteen G hT hC4 hh4 hd3 hc2deg hd4
        hac3.symm hac4
        (hleafnonadj ℓ₃ ℓ₄ (Or.inr (Or.inr (Or.inl rfl)))
          (Or.inr (Or.inr (Or.inr rfl))) hℓ34)
        (G.ne_of_adj hac3).symm (G.ne_of_adj hac4) hℓ34).2.2
  obtain ⟨hpa12, hpa34⟩ := hpair a hda
  obtain ⟨hpb12, hpb34⟩ := hpair b hdb
  obtain ⟨hpc12, hpc34⟩ := hpair c hdc
  -- Counting: some leaf is met by at most one of the three hubs.
  have keyleaf : ∃ w : Fin 15, (w = ℓ₁ ∨ w = ℓ₂ ∨ w = ℓ₃ ∨ w = ℓ₄) ∧
      (if G.Adj a w then 1 else 0) + (if G.Adj b w then 1 else 0)
        + (if G.Adj c w then 1 else 0) ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have hc1 := hcon ℓ₁ (Or.inl rfl)
    have hc2 := hcon ℓ₂ (Or.inr (Or.inl rfl))
    have hc3 := hcon ℓ₃ (Or.inr (Or.inr (Or.inl rfl)))
    have hc4 := hcon ℓ₄ (Or.inr (Or.inr (Or.inr rfl)))
    have ca12 := ind2 _ _ hpa12
    have ca34 := ind2 _ _ hpa34
    have cb12 := ind2 _ _ hpb12
    have cb34 := ind2 _ _ hpb34
    have cc12 := ind2 _ _ hpc12
    have cc34 := ind2 _ _ hpc34
    omega
  obtain ⟨w, hwleaf, hwcnt⟩ := keyleaf
  have amem : (a = a ∨ a = b ∨ a = c) := Or.inl rfl
  have bmem : (b = a ∨ b = b ∨ b = c) := Or.inr (Or.inl rfl)
  have cmem : (c = a ∨ c = b ∨ c = c) := Or.inr (Or.inr rfl)
  have key : ∃ w' h₁ h₂ : Fin 15, (w' = ℓ₁ ∨ w' = ℓ₂ ∨ w' = ℓ₃ ∨ w' = ℓ₄) ∧
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
theorem single_vertex_config_from_C5_three_hubs (G : SimpleGraph (Fin 15))
    (hT : ¬∃ x y z : Fin 15, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (t h₁ h₂ h₃ : Fin 15) (ht3 : G.degree t = 3)
    (htiso : ∀ w : Fin 15, G.Adj t w → G.degree w ≠ 3)
    (hh₁4 : G.degree h₁ = 4) (hh₂4 : G.degree h₂ = 4) (hh₃4 : G.degree h₃ = 4)
    (hne12 : h₁ ≠ h₂) (hne13 : h₁ ≠ h₃) (hne23 : h₂ ≠ h₃)
    (htg₁ : G.Adj t h₁) (htg₂ : G.Adj t h₂) (htg₃ : G.Adj t h₃)
    (v₁ v₂ v₃ v₄ v₅ : Fin 15)
    (hd1 : G.degree v₁ = 3) (hd2 : G.degree v₂ = 3) (hd3 : G.degree v₃ = 3)
    (hd4 : G.degree v₄ = 3) (hd5 : G.degree v₅ = 3)
    (hcard5 : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 15)).card = 5)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e34 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁)
    (n13 : ¬G.Adj v₁ v₃) (n14 : ¬G.Adj v₁ v₄) (n24 : ¬G.Adj v₂ v₄)
    (n25 : ¬G.Adj v₂ v₅) (n35 : ¬G.Adj v₃ v₅) :
    SingleVertexConfig G := by
  obtain ⟨d12, d13, d14, d15, d23, d24, d25, d34, d35, d45⟩ :=
    distinct_five_fifteen v₁ v₂ v₃ v₄ v₅ hcard5
  -- Generic cherry closers, one per consecutive triple, for an arbitrary hub pair.
  have mg1 : ∀ ha hb : Fin 15, G.degree ha = 4 → G.degree hb = 4 → ha ≠ hb →
      G.Adj t ha → G.Adj t hb →
      ¬G.Adj ha v₁ → ¬G.Adj ha v₂ → ¬G.Adj ha v₃ →
      ¬G.Adj hb v₁ → ¬G.Adj hb v₂ → ¬G.Adj hb v₃ → SingleVertexConfig G :=
    fun ha hb hca hcb hcne hta htb a1 a2 a3 b1 b2 b3 =>
      assemble_single_vertex_config G t ha hb v₁ v₂ v₃ ht3 htiso hca hcb hcne hta htb
        hd1 hd2 hd3 e12 e23 d13 n13 a1 a2 a3 b1 b2 b3
  have mg2 : ∀ ha hb : Fin 15, G.degree ha = 4 → G.degree hb = 4 → ha ≠ hb →
      G.Adj t ha → G.Adj t hb →
      ¬G.Adj ha v₂ → ¬G.Adj ha v₃ → ¬G.Adj ha v₄ →
      ¬G.Adj hb v₂ → ¬G.Adj hb v₃ → ¬G.Adj hb v₄ → SingleVertexConfig G :=
    fun ha hb hca hcb hcne hta htb a1 a2 a3 b1 b2 b3 =>
      assemble_single_vertex_config G t ha hb v₂ v₃ v₄ ht3 htiso hca hcb hcne hta htb
        hd2 hd3 hd4 e23 e34 d24 n24 a1 a2 a3 b1 b2 b3
  have mg3 : ∀ ha hb : Fin 15, G.degree ha = 4 → G.degree hb = 4 → ha ≠ hb →
      G.Adj t ha → G.Adj t hb →
      ¬G.Adj ha v₃ → ¬G.Adj ha v₄ → ¬G.Adj ha v₅ →
      ¬G.Adj hb v₃ → ¬G.Adj hb v₄ → ¬G.Adj hb v₅ → SingleVertexConfig G :=
    fun ha hb hca hcb hcne hta htb a1 a2 a3 b1 b2 b3 =>
      assemble_single_vertex_config G t ha hb v₃ v₄ v₅ ht3 htiso hca hcb hcne hta htb
        hd3 hd4 hd5 e34 e45 d35 n35 a1 a2 a3 b1 b2 b3
  have mg4 : ∀ ha hb : Fin 15, G.degree ha = 4 → G.degree hb = 4 → ha ≠ hb →
      G.Adj t ha → G.Adj t hb →
      ¬G.Adj ha v₄ → ¬G.Adj ha v₅ → ¬G.Adj ha v₁ →
      ¬G.Adj hb v₄ → ¬G.Adj hb v₅ → ¬G.Adj hb v₁ → SingleVertexConfig G :=
    fun ha hb hca hcb hcne hta htb a1 a2 a3 b1 b2 b3 =>
      assemble_single_vertex_config G t ha hb v₄ v₅ v₁ ht3 htiso hca hcb hcne hta htb
        hd4 hd5 hd1 e45 e51 d14.symm (fun h => n14 h.symm) a1 a2 a3 b1 b2 b3
  have mg5 : ∀ ha hb : Fin 15, G.degree ha = 4 → G.degree hb = 4 → ha ≠ hb →
      G.Adj t ha → G.Adj t hb →
      ¬G.Adj ha v₅ → ¬G.Adj ha v₁ → ¬G.Adj ha v₂ →
      ¬G.Adj hb v₅ → ¬G.Adj hb v₁ → ¬G.Adj hb v₂ → SingleVertexConfig G :=
    fun ha hb hca hcb hcne hta htb a1 a2 a3 b1 b2 b3 =>
      assemble_single_vertex_config G t ha hb v₅ v₁ v₂ ht3 htiso hca hcb hcne hta htb
        hd5 hd1 hd2 e51 e12 d25.symm (fun h => n25 h.symm) a1 a2 a3 b1 b2 b3
  have hB := hub_cycle_cases_fifteen G hT hC4 h₁ v₁ v₂ v₃ v₄ v₅ hh₁4 hd1 hd2 hd3 hd4 hd5
    e12 e23 e34 e45 e51 n13 n14 n24 n25 n35 d12 d13 d14 d15 d23 d24 d25 d34 d35 d45
  have hC := hub_cycle_cases_fifteen G hT hC4 h₂ v₁ v₂ v₃ v₄ v₅ hh₂4 hd1 hd2 hd3 hd4 hd5
    e12 e23 e34 e45 e51 n13 n14 n24 n25 n35 d12 d13 d14 d15 d23 d24 d25 d34 d35 d45
  have hD := hub_cycle_cases_fifteen G hT hC4 h₃ v₁ v₂ v₃ v₄ v₅ hh₃4 hd1 hd2 hd3 hd4 hd5
    e12 e23 e34 e45 e51 n13 n14 n24 n25 n35 d12 d13 d14 d15 d23 d24 d25 d34 d35 d45
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

/-- **Shared degree-`4` hub when there is no degree-`5` vertex (`n = 15`).**  Every hub then has
degree exactly `4`, so `|D| = 8`, `|Hub₄| = 7`, and each of the `≥ 3` `M`-isolated twins meets all
three of its hub-neighbours inside `Hub₄`; the pigeonhole (`3·3 = 9 > 7`) yields a shared
degree-`4` hub. -/
theorem shared_deg4_hub_nodeg5_fifteen (G : SimpleGraph (Fin 15))
    (hm : G.edgeFinset.card = 26) (h3 : ∀ v : Fin 15, 3 ≤ G.degree v)
    (h2k2 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hno5 : ∀ v : Fin 15, G.degree v ≤ 4)
    (hs8 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card ≤ 8) :
    ∃ h t₁ t₂ : Fin 15, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 15, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 15, G.Adj t₂ w → G.degree w ≠ 3) := by
  classical
  set D : Finset (Fin 15) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 15, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub4 : Finset (Fin 15) := Finset.univ.filter (fun v => G.degree v = 4) with hHub4def
  have hmemHub4 : ∀ v : Fin 15, v ∈ Hub4 ↔ G.degree v = 4 := by intro v; rw [hHub4def]; simp
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
  have hsum48 : ∑ v : Fin 15, G.degree v = 52 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 52 := by
    rw [Finset.sum_add_sum_compl]; exact hsum48
  have hcc : D.card + Dᶜ.card = 15 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h
    exact h
  have hD8 : D.card = 8 := by rw [hsumD, hsumDc] at hsplit; omega
  have hHub4card : Hub4.card = 7 := by rw [hHub4eqDc]; omega
  set Iso : Finset (Fin 15) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 15, G.Adj v w → G.degree w ≠ 3 := by
    intro v hv
    rw [hIsodef, Finset.mem_filter] at hv
    obtain ⟨hvD, hv0⟩ := hv
    refine ⟨(hmemD v).mp hvD, fun w hadj hw3 => ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
    exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
  have hIso3 : 3 ≤ Iso.card := by
    have hnb := nonisolated_component_bound G D hmemD h2k2
    have hpart := Finset.card_filter_add_card_filter_not (s := D)
      (fun v => (G.neighborFinset v ∩ D).card = 0)
    rw [← hIsodef] at hpart
    omega
  have hcount : Hub4.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
    have hthree : ∀ v ∈ Iso, 3 ≤ (G.neighborFinset v ∩ Hub4).card := by
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
      have heq : G.neighborFinset v ∩ Hub4 = G.neighborFinset v := Finset.inter_eq_left.mpr hsub
      rw [heq, G.card_neighborFinset_eq_degree, hvdeg3]
    have hge9 : 9 ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
      have h3iso : 3 * Iso.card ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
        have := Finset.card_nsmul_le_sum Iso
          (fun v => (G.neighborFinset v ∩ Hub4).card) 3 hthree
        simpa [smul_eq_mul, mul_comm] using this
      omega
    omega
  exact shared_deg4_hub_from_count_fifteen G Iso Hub4 hIsoiso hHub4deg hcount

/-- **Shared degree-`4` hub in the degree-`5` regime (`n = 15`).**  When a degree-`≥ 5` vertex `g`
exists, the residual is `|D| ∈ {9, 10}` with at most `|D| − 8 ≤ 2` degree-`≥ 5` hubs.  Each of the
`≥ |D| − 6` `M`-isolated twins meets `≥ 3 − |H₅|` degree-`4` hubs, and the pigeonhole
`|Hub₄| < ∑ |N ∩ Hub₄|` (checked for `|H₅| ∈ {1, 2}`) forces two twins to share a degree-`4`
hub. -/
theorem shared_deg4_hub_deg5_fifteen (G : SimpleGraph (Fin 15))
    (hm : G.edgeFinset.card = 26) (h3 : ∀ v : Fin 15, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 15, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (h2k2 : ¬∃ a b c d : Fin 15, ({a, b, c, d} : Finset (Fin 15)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (g : Fin 15) (hg5 : 5 ≤ G.degree g) :
    ∃ h t₁ t₂ : Fin 15, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 15, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 15, G.Adj t₂ w → G.degree w ≠ 3) := by
  classical
  set D : Finset (Fin 15) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 15, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 15) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 15, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  set Hub4 : Finset (Fin 15) := Finset.univ.filter (fun v => G.degree v = 4) with hHub4def
  have hmemHub4 : ∀ v : Fin 15, v ∈ Hub4 ↔ G.degree v = 4 := by intro v; rw [hHub4def]; simp
  have hHub4deg : ∀ h ∈ Hub4, G.degree h = 4 := fun h hh => (hmemHub4 h).mp hh
  set H5 : Finset (Fin 15) := Finset.univ.filter (fun v => 5 ≤ G.degree v) with hH5def
  have hmemH5 : ∀ v : Fin 15, v ∈ H5 ↔ 5 ≤ G.degree v := by intro v; rw [hH5def]; simp
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  have hDcdeg : ∀ v ∈ Dᶜ, 4 ≤ G.degree v := by
    intro v hv; rw [Finset.mem_compl, hmemD] at hv; have := h3 v; omega
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsum52 : ∑ v : Fin 15, G.degree v = 52 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 52 := by
    rw [Finset.sum_add_sum_compl]; exact hsum52
  have hcc : D.card + Dᶜ.card = 15 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h; exact h
  have hgDc : g ∈ Dᶜ := by rw [Finset.mem_compl, hmemD]; omega
  -- `|D| ≥ 9` from `g`'s excess.
  have hD9 : 9 ≤ D.card := by
    have hsg := (Finset.add_sum_erase Dᶜ (fun v => G.degree v) hgDc).symm
    have hrest : 4 * (Dᶜ.erase g).card ≤ ∑ v ∈ Dᶜ.erase g, G.degree v := by
      have hb : ∀ x ∈ Dᶜ.erase g, 4 ≤ G.degree x :=
        fun x hx => hDcdeg x (Finset.mem_of_mem_erase hx)
      have := Finset.card_nsmul_le_sum (Dᶜ.erase g) (fun v => G.degree v) 4 hb
      simpa [smul_eq_mul, mul_comm] using this
    have hcg : (Dᶜ.erase g).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hgDc
    have hpos : 1 ≤ Dᶜ.card := Finset.card_pos.mpr ⟨g, hgDc⟩
    omega
  -- `|D| ≤ 10` from the cross count.
  have hdegsplit : ∀ v : Fin 15,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
    intro v
    have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dᶜ) :=
      Finset.disjoint_left.mpr (fun a ha ha' => by
        rw [Finset.mem_inter] at ha ha'; exact (Finset.mem_compl.mp ha'.2) ha.2)
    have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dᶜ) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
  have heM10 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 10 :=
    eM_le_five G D hmemD hT hC4 h2k2
  have hD10 : D.card ≤ 10 := by
    have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
        = ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card := cross_count G D Dᶜ
    have hsumDND : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
        = 3 * D.card - ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by
      have hcong : ∑ v ∈ D, ((G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card)
          = ∑ v ∈ D, G.degree v :=
        Finset.sum_congr rfl (fun v _ => hdegsplit v)
      rw [Finset.sum_add_distrib, hsumD] at hcong; omega
    have hle : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card ≤ ∑ w ∈ Dᶜ, G.degree w := by
      apply Finset.sum_le_sum
      intro w _
      calc (G.neighborFinset w ∩ D).card ≤ (G.neighborFinset w).card :=
            Finset.card_le_card Finset.inter_subset_left
        _ = G.degree w := G.card_neighborFinset_eq_degree w
    omega
  -- `|H₅| ≤ |D| − 8`.
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
  -- `|Iso| ≥ |D| − 6`.
  set Iso : Finset (Fin 15) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 15, G.Adj v w → G.degree w ≠ 3 := by
    intro v hv
    rw [hIsodef, Finset.mem_filter] at hv
    obtain ⟨hvD, hv0⟩ := hv
    refine ⟨(hmemD v).mp hvD, fun w hadj hw3 => ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
    exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
  have hIsoge : D.card - 6 ≤ Iso.card := by
    have hnb := nonisolated_component_bound G D hmemD h2k2
    have hpart := Finset.card_filter_add_card_filter_not (s := D)
      (fun v => (G.neighborFinset v ∩ D).card = 0)
    rw [← hIsodef] at hpart
    omega
  -- `Hub₄` and `H₅` partition `Hub = Dᶜ`.
  have hdisjHub : Disjoint Hub4 H5 :=
    Finset.disjoint_left.mpr (fun a ha ha' => by
      have := (hmemHub4 a).mp ha; have := (hmemH5 a).mp ha'; omega)
  have huHub : Hub4 ∪ H5 = Hub := by
    ext w; rw [Finset.mem_union, hmemHub4, hmemH5, hmemHub]; omega
  have hHubpart : Hub4.card + H5.card = Dᶜ.card := by
    rw [← hHubeqDc, ← huHub, Finset.card_union_of_disjoint hdisjHub]
  -- Pigeonhole.
  have hcount : Hub4.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
    have hH5pos : 1 ≤ H5.card := Finset.card_pos.mpr ⟨g, (hmemH5 g).mpr hg5⟩
    have heach : ∀ v ∈ Iso, 3 - H5.card ≤ (G.neighborFinset v ∩ Hub4).card := by
      intro v hv
      rw [hIsodef, Finset.mem_filter] at hv
      obtain ⟨hvD, hv0⟩ := hv
      have h3hub := each_iso_three_hubs G D Hub hmemD hmemHub h3 v hvD hv0
      have hdisj : Disjoint (G.neighborFinset v ∩ Hub4) (G.neighborFinset v ∩ H5) :=
        Finset.disjoint_left.mpr (fun a ha ha' => by
          rw [Finset.mem_inter] at ha ha'
          have := (hmemHub4 a).mp ha.2; have := (hmemH5 a).mp ha'.2; omega)
      have hun : (G.neighborFinset v ∩ Hub4) ∪ (G.neighborFinset v ∩ H5)
          = G.neighborFinset v ∩ Hub := by
        rw [← Finset.inter_union_distrib_left, huHub]
      have hsumcard : (G.neighborFinset v ∩ Hub4).card + (G.neighborFinset v ∩ H5).card = 3 := by
        rw [← Finset.card_union_of_disjoint hdisj, hun, h3hub]
      have hH5sub : (G.neighborFinset v ∩ H5).card ≤ H5.card :=
        Finset.card_le_card Finset.inter_subset_right
      omega
    have hge : (3 - H5.card) * Iso.card ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
      have := Finset.card_nsmul_le_sum Iso
        (fun v => (G.neighborFinset v ∩ Hub4).card) (3 - H5.card) heach
      simpa [smul_eq_mul, mul_comm] using this
    have hH5cases : H5.card = 1 ∨ H5.card = 2 := by omega
    rcases hH5cases with h1 | h2
    · rw [h1] at hge hHubpart; norm_num at hge; omega
    · rw [h2] at hge hHubpart; norm_num at hge; omega
  exact shared_deg4_hub_from_count_fifteen G Iso Hub4 hIsoiso hHub4deg hcount

end N15

end ACMax
