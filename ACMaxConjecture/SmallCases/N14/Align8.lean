import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N14.Core
import ACMaxConjecture.SmallCases.N14.Align
import ACMaxConjecture.SmallCases.N14.Doublestar
import ACMaxConjecture.SmallCases.N14.Deg5
import ACMaxConjecture.SmallCases.N14.C5
import ACMaxConjecture.SmallCases.N14.Align6

/-!
# Three-way alignment dichotomy for `e(M) ≥ 4` (`s ≥ 8`, `n = 14`)

This file supplies `halign8`, the structural-selection helper feeding the `s ≥ 8` branch of
`exists_twin_signed_cert_fourteen` (in `TwinCert14`).  At `e(M) ≥ 4` the residual graph
(`δ ≥ 3`, no good triangle / `2K₂` / `C₄` / `K_{2,3}`) admits one of the three signed-cut
configurations `SingleVertexConfig`, `TwoTwinConfig`, `TwoHubConfig` (the same covering combination
used for `s = 6`), verified by enumeration over all such graphs.

The single-vertex paths reuse the proved deg-`4` selectors from `TwinCert14Doublestar`/`TwinCert14C5`,
re-routed through `assemble_single_vertex_config` (which additionally tracks the cherry's
non-adjacency `¬x∼z`, freely available in the double-star / `C₅` constructions).  The two
genuinely-hard alignment sub-cases are now closed via the `TwoTwinConfig` branch: the `e(M) = 4`
dominating `(3,2)` double star, and the degree-`5` residual (the ≈ 91 graphs whose unique degree-`5`
hub forces a `TwoTwinConfig` of two `M`-isolated twins sharing a degree-`4` hub).  Both route a
pigeonholed shared degree-`4` hub through a fat-centre claw (or, in the residual induced-`C₅` case, a
cycle cherry) into `TwoTwinConfig`.
-/

namespace ACMax

open scoped Classical

namespace N14

/-- **Single-vertex configuration assembly.**  Packages a degree-`3` vertex `v = t` with two
degree-`4` hub-neighbours `h₁, h₂` and a cherry (induced `P₃`) `x–y–z` of degree-`3` vertices,
all mutually non-adjacent across `{t, h₁, h₂} × {x, y, z}` and with `¬x∼z`, into a
`SingleVertexConfig`.  The cross/hub side condition holds because every hub–cherry incidence is
absent, so the weighted sum vanishes and `deg h₁ + deg h₂ = 8 ≤ 8 + 2·[h₁∼h₂]`. -/
theorem assemble_single_vertex_config (G : SimpleGraph (Fin 14))
    (t h₁ h₂ x y z : Fin 14)
    (ht3 : G.degree t = 3) (htiso : ∀ w : Fin 14, G.Adj t w → G.degree w ≠ 3)
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
  have hsum0 : ∑ p ∈ ({t, h₁, h₂} : Finset (Fin 14)),
      (G.neighborFinset p ∩ ({x, y, z} : Finset (Fin 14))).card = 0 := by
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
  have hside : 2 * (∑ p ∈ ({t, h₁, h₂} : Finset (Fin 14)),
      (G.neighborFinset p ∩ ({x, y, z} : Finset (Fin 14))).card)
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

/-- **Single-vertex double-star alignment by leaf counting.**  The `SingleVertexConfig` analogue of
`single_twin_doublestar_count`: the same all-degree-`4`-hub double-star selection, but routed through
`assemble_single_vertex_config` (recording the cherry non-adjacency `¬leaf∼c'`). -/
theorem single_vertex_doublestar_count (G : SimpleGraph (Fin 14)) (D : Finset (Fin 14))
    (hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (t a b c : Fin 14) (ht3 : G.degree t = 3)
    (htiso : ∀ w : Fin 14, G.Adj t w → G.degree w ≠ 3)
    (hda : G.degree a = 4) (hdb : G.degree b = 4) (hdc : G.degree c = 4)
    (habne : a ≠ b) (hacne : a ≠ c) (hbcne : b ≠ c)
    (hta : G.Adj t a) (htb : G.Adj t b) (htc : G.Adj t c)
    (c₁ c₂ : Fin 14) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 3) (hin2 : (G.neighborFinset c₂ ∩ D).card = 3)
    (hdom : ∀ p q : Fin 14, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂) :
    SingleVertexConfig G := by
  classical
  have hc1deg : G.degree c₁ = 3 := (hmemD c₁).mp hc1D
  have hc2deg : G.degree c₂ = 3 := (hmemD c₂).mp hc2D
  obtain ⟨ℓ₁, ℓ₂, ℓ₃, ℓ₄, hd1, hd2, hd3, hd4, hcard6,
      hac1, hac2, hac3, hac4, hND1, hND2, hND3, hND4, hn1, hn2, hn3, hn4, hℓ12, hℓ34⟩ :=
    dom_doublestar_leaves G D hmemD hT c₁ c₂ hc1D hc2D hc12 hin1 hin2 hdom
  have leafdeg : ∀ w : Fin 14, (w = ℓ₁ ∨ w = ℓ₂ ∨ w = ℓ₃ ∨ w = ℓ₄) → G.degree w = 3 := by
    rintro w (rfl | rfl | rfl | rfl) <;> assumption
  have leafD : ∀ w : Fin 14, (w = ℓ₁ ∨ w = ℓ₂ ∨ w = ℓ₃ ∨ w = ℓ₄) → w ∈ D :=
    fun w hw => (hmemD w).mpr (leafdeg w hw)
  have hlne : ∀ w cen oth : Fin 14, G.neighborFinset w ∩ D = {cen} →
      (G.neighborFinset oth ∩ D).card = 3 → w ≠ oth := by
    intro w cen oth hw hoth e
    subst e
    rw [hw, Finset.card_singleton] at hoth
    omega
  have hleafnec : ∀ w : Fin 14, (w = ℓ₁ ∨ w = ℓ₂ ∨ w = ℓ₃ ∨ w = ℓ₄) → w ≠ c₁ ∧ w ≠ c₂ := by
    rintro w (rfl | rfl | rfl | rfl)
    · exact ⟨(G.ne_of_adj hac1).symm, hlne w c₁ c₂ hND1 hin2⟩
    · exact ⟨(G.ne_of_adj hac2).symm, hlne w c₁ c₂ hND2 hin2⟩
    · exact ⟨hlne w c₂ c₁ hND3 hin1, (G.ne_of_adj hac3).symm⟩
    · exact ⟨hlne w c₂ c₁ hND4 hin1, (G.ne_of_adj hac4).symm⟩
  have hleafnonadj : ∀ u v : Fin 14, (u = ℓ₁ ∨ u = ℓ₂ ∨ u = ℓ₃ ∨ u = ℓ₄) →
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
  have hubcen : ∀ hh : Fin 14, (hh = a ∨ hh = b ∨ hh = c) →
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
  have hpair : ∀ hh : Fin 14, G.degree hh = 4 →
      ¬(G.Adj hh ℓ₁ ∧ G.Adj hh ℓ₂) ∧ ¬(G.Adj hh ℓ₃ ∧ G.Adj hh ℓ₄) := by
    intro hh hh4
    refine ⟨?_, ?_⟩
    · exact (hub_meets_path_le_one_fourteen G hT hC4 hh4 hd1 hc1deg hd2
        hac1.symm hac2
        (hleafnonadj ℓ₁ ℓ₂ (Or.inl rfl) (Or.inr (Or.inl rfl)) hℓ12)
        (G.ne_of_adj hac1).symm (G.ne_of_adj hac2) hℓ12).2.2
    · exact (hub_meets_path_le_one_fourteen G hT hC4 hh4 hd3 hc2deg hd4
        hac3.symm hac4
        (hleafnonadj ℓ₃ ℓ₄ (Or.inr (Or.inr (Or.inl rfl)))
          (Or.inr (Or.inr (Or.inr rfl))) hℓ34)
        (G.ne_of_adj hac3).symm (G.ne_of_adj hac4) hℓ34).2.2
  obtain ⟨hpa12, hpa34⟩ := hpair a hda
  obtain ⟨hpb12, hpb34⟩ := hpair b hdb
  obtain ⟨hpc12, hpc34⟩ := hpair c hdc
  -- Counting: some leaf is met by at most one of the three hubs.
  have keyleaf : ∃ w : Fin 14, (w = ℓ₁ ∨ w = ℓ₂ ∨ w = ℓ₃ ∨ w = ℓ₄) ∧
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
  have key : ∃ w' h₁ h₂ : Fin 14, (w' = ℓ₁ ∨ w' = ℓ₂ ∨ w' = ℓ₃ ∨ w' = ℓ₄) ∧
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
theorem single_vertex_config_from_C5_three_hubs (G : SimpleGraph (Fin 14))
    (hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (t h₁ h₂ h₃ : Fin 14) (ht3 : G.degree t = 3)
    (htiso : ∀ w : Fin 14, G.Adj t w → G.degree w ≠ 3)
    (hh₁4 : G.degree h₁ = 4) (hh₂4 : G.degree h₂ = 4) (hh₃4 : G.degree h₃ = 4)
    (hne12 : h₁ ≠ h₂) (hne13 : h₁ ≠ h₃) (hne23 : h₂ ≠ h₃)
    (htg₁ : G.Adj t h₁) (htg₂ : G.Adj t h₂) (htg₃ : G.Adj t h₃)
    (v₁ v₂ v₃ v₄ v₅ : Fin 14)
    (hd1 : G.degree v₁ = 3) (hd2 : G.degree v₂ = 3) (hd3 : G.degree v₃ = 3)
    (hd4 : G.degree v₄ = 3) (hd5 : G.degree v₅ = 3)
    (hcard5 : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 14)).card = 5)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e34 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁)
    (n13 : ¬G.Adj v₁ v₃) (n14 : ¬G.Adj v₁ v₄) (n24 : ¬G.Adj v₂ v₄)
    (n25 : ¬G.Adj v₂ v₅) (n35 : ¬G.Adj v₃ v₅) :
    SingleVertexConfig G := by
  obtain ⟨d12, d13, d14, d15, d23, d24, d25, d34, d35, d45⟩ :=
    distinct_five_fourteen v₁ v₂ v₃ v₄ v₅ hcard5
  -- Generic cherry closers, one per consecutive triple, for an arbitrary hub pair.
  have mg1 : ∀ ha hb : Fin 14, G.degree ha = 4 → G.degree hb = 4 → ha ≠ hb →
      G.Adj t ha → G.Adj t hb →
      ¬G.Adj ha v₁ → ¬G.Adj ha v₂ → ¬G.Adj ha v₃ →
      ¬G.Adj hb v₁ → ¬G.Adj hb v₂ → ¬G.Adj hb v₃ → SingleVertexConfig G :=
    fun ha hb hca hcb hcne hta htb a1 a2 a3 b1 b2 b3 =>
      assemble_single_vertex_config G t ha hb v₁ v₂ v₃ ht3 htiso hca hcb hcne hta htb
        hd1 hd2 hd3 e12 e23 d13 n13 a1 a2 a3 b1 b2 b3
  have mg2 : ∀ ha hb : Fin 14, G.degree ha = 4 → G.degree hb = 4 → ha ≠ hb →
      G.Adj t ha → G.Adj t hb →
      ¬G.Adj ha v₂ → ¬G.Adj ha v₃ → ¬G.Adj ha v₄ →
      ¬G.Adj hb v₂ → ¬G.Adj hb v₃ → ¬G.Adj hb v₄ → SingleVertexConfig G :=
    fun ha hb hca hcb hcne hta htb a1 a2 a3 b1 b2 b3 =>
      assemble_single_vertex_config G t ha hb v₂ v₃ v₄ ht3 htiso hca hcb hcne hta htb
        hd2 hd3 hd4 e23 e34 d24 n24 a1 a2 a3 b1 b2 b3
  have mg3 : ∀ ha hb : Fin 14, G.degree ha = 4 → G.degree hb = 4 → ha ≠ hb →
      G.Adj t ha → G.Adj t hb →
      ¬G.Adj ha v₃ → ¬G.Adj ha v₄ → ¬G.Adj ha v₅ →
      ¬G.Adj hb v₃ → ¬G.Adj hb v₄ → ¬G.Adj hb v₅ → SingleVertexConfig G :=
    fun ha hb hca hcb hcne hta htb a1 a2 a3 b1 b2 b3 =>
      assemble_single_vertex_config G t ha hb v₃ v₄ v₅ ht3 htiso hca hcb hcne hta htb
        hd3 hd4 hd5 e34 e45 d35 n35 a1 a2 a3 b1 b2 b3
  have mg4 : ∀ ha hb : Fin 14, G.degree ha = 4 → G.degree hb = 4 → ha ≠ hb →
      G.Adj t ha → G.Adj t hb →
      ¬G.Adj ha v₄ → ¬G.Adj ha v₅ → ¬G.Adj ha v₁ →
      ¬G.Adj hb v₄ → ¬G.Adj hb v₅ → ¬G.Adj hb v₁ → SingleVertexConfig G :=
    fun ha hb hca hcb hcne hta htb a1 a2 a3 b1 b2 b3 =>
      assemble_single_vertex_config G t ha hb v₄ v₅ v₁ ht3 htiso hca hcb hcne hta htb
        hd4 hd5 hd1 e45 e51 d14.symm (fun h => n14 h.symm) a1 a2 a3 b1 b2 b3
  have mg5 : ∀ ha hb : Fin 14, G.degree ha = 4 → G.degree hb = 4 → ha ≠ hb →
      G.Adj t ha → G.Adj t hb →
      ¬G.Adj ha v₅ → ¬G.Adj ha v₁ → ¬G.Adj ha v₂ →
      ¬G.Adj hb v₅ → ¬G.Adj hb v₁ → ¬G.Adj hb v₂ → SingleVertexConfig G :=
    fun ha hb hca hcb hcne hta htb a1 a2 a3 b1 b2 b3 =>
      assemble_single_vertex_config G t ha hb v₅ v₁ v₂ ht3 htiso hca hcb hcne hta htb
        hd5 hd1 hd2 e51 e12 d25.symm (fun h => n25 h.symm) a1 a2 a3 b1 b2 b3
  have hB := hub_cycle_cases G hT hC4 h₁ v₁ v₂ v₃ v₄ v₅ hh₁4 hd1 hd2 hd3 hd4 hd5
    e12 e23 e34 e45 e51 n13 n14 n24 n25 n35 d12 d13 d14 d15 d23 d24 d25 d34 d35 d45
  have hC := hub_cycle_cases G hT hC4 h₂ v₁ v₂ v₃ v₄ v₅ hh₂4 hd1 hd2 hd3 hd4 hd5
    e12 e23 e34 e45 e51 n13 n14 n24 n25 n35 d12 d13 d14 d15 d23 d24 d25 d34 d35 d45
  have hD := hub_cycle_cases G hT hC4 h₃ v₁ v₂ v₃ v₄ v₅ hh₃4 hd1 hd2 hd3 hd4 hd5
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

/-- **Shared degree-`4` hub by pigeonhole.**  If the degree-`4` hub set `Hub4` carries strictly
more twin-incidences from the `M`-isolated set `Iso` than it has vertices, some hub is adjacent to
two distinct `M`-isolated degree-`3` twins. -/
theorem shared_deg4_hub_from_count (G : SimpleGraph (Fin 14)) (Iso Hub4 : Finset (Fin 14))
    (hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 14, G.Adj v w → G.degree w ≠ 3)
    (hHub4deg : ∀ h ∈ Hub4, G.degree h = 4)
    (hcount : Hub4.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card) :
    ∃ h t₁ t₂ : Fin 14, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 14, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 14, G.Adj t₂ w → G.degree w ≠ 3) := by
  classical
  have hincid : ∃ h ∈ Hub4, 2 ≤ (Iso.filter (fun v => G.Adj v h)).card := by
    by_contra hcon
    push Not at hcon
    have hsum1 : ∑ h ∈ Hub4, (Iso.filter (fun v => G.Adj v h)).card ≤ Hub4.card := by
      calc ∑ h ∈ Hub4, (Iso.filter (fun v => G.Adj v h)).card
          ≤ ∑ _h ∈ Hub4, 1 := Finset.sum_le_sum (fun h hh => by have := hcon h hh; omega)
        _ = Hub4.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    have hswap : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card
        = ∑ h ∈ Hub4, (Iso.filter (fun v => G.Adj v h)).card := by
      have hL : ∀ v : Fin 14, (G.neighborFinset v ∩ Hub4).card
          = (Hub4.filter (fun h => G.Adj v h)).card := by
        intro v
        congr 1
        ext h
        simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_filter]
        tauto
      simp_rw [hL, Finset.card_filter]
      rw [Finset.sum_comm]
    omega
  obtain ⟨h, hhHub4, hh2⟩ := hincid
  obtain ⟨t₁, ht1, t₂, ht2, ht12⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (Iso.filter (fun v => G.Adj v h)).card)
  rw [Finset.mem_filter] at ht1 ht2
  obtain ⟨ht1Iso, hAt1h⟩ := ht1
  obtain ⟨ht2Iso, hAt2h⟩ := ht2
  obtain ⟨ht1deg, ht1iso⟩ := hIsoiso t₁ ht1Iso
  obtain ⟨ht2deg, ht2iso⟩ := hIsoiso t₂ ht2Iso
  exact ⟨h, t₁, t₂, hHub4deg h hhHub4, ht12, ht1deg, ht2deg, hAt1h, hAt2h, ht1iso, ht2iso⟩

/-- **Fat-dominating claw assembly.**  A degree-`3` centre `c` whose three neighbours are all
degree-`3` (in-`M`-degree `3`, hence hub-free), together with a degree-`4` hub `h` adjacent to two
distinct `M`-isolated degree-`3` twins `t₁, t₂`, yields a `TwoTwinConfig`: `h` meets at most one of
`c`'s neighbours (two hits form an induced `C₄`), so two free neighbours and `c` form a cherry
avoiding `h`. -/
theorem claw_shared_two_twin (G : SimpleGraph (Fin 14)) (D : Finset (Fin 14))
    (hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (c t₁ t₂ h : Fin 14) (hcD : c ∈ D)
    (hcge : 3 ≤ (G.neighborFinset c ∩ D).card)
    (ht1deg : G.degree t₁ = 3) (ht2deg : G.degree t₂ = 3) (hhdeg4 : G.degree h = 4)
    (ht12 : t₁ ≠ t₂) (hAt1h : G.Adj t₁ h) (hAt2h : G.Adj t₂ h)
    (ht1iso : ∀ w : Fin 14, G.Adj t₁ w → G.degree w ≠ 3)
    (ht2iso : ∀ w : Fin 14, G.Adj t₂ w → G.degree w ≠ 3) :
    TwoTwinConfig G := by
  classical
  have hdegD : ∀ v : Fin 14, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
  have hc3 : G.degree c = 3 := hdegD c hcD
  have hle : (G.neighborFinset c ∩ D).card ≤ 3 := by
    calc (G.neighborFinset c ∩ D).card ≤ (G.neighborFinset c).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree c := G.card_neighborFinset_eq_degree c
      _ = 3 := hc3
  have heq3 : (G.neighborFinset c ∩ D).card = 3 := le_antisymm hle hcge
  obtain ⟨n₁, n₂, n₃, hne12, hne13, hne23, hset⟩ := Finset.card_eq_three.mp heq3
  have hcardeq : (G.neighborFinset c).card = (G.neighborFinset c ∩ D).card := by
    rw [G.card_neighborFinset_eq_degree, hc3, heq3]
  have hNsubeq : G.neighborFinset c ∩ D = G.neighborFinset c :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq hcardeq)
  have hmem_i : ∀ w : Fin 14, w ∈ ({n₁, n₂, n₃} : Finset (Fin 14)) → G.Adj c w ∧ w ∈ D := by
    intro w hw
    have hw' : w ∈ G.neighborFinset c ∩ D := hset ▸ hw
    exact ⟨(G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hw').1,
      (Finset.mem_inter.mp hw').2⟩
  obtain ⟨a1, hn1D⟩ := hmem_i n₁ (by simp)
  obtain ⟨a2, hn2D⟩ := hmem_i n₂ (by simp)
  obtain ⟨a3, hn3D⟩ := hmem_i n₃ (by simp)
  have hd1 : G.degree n₁ = 3 := hdegD n₁ hn1D
  have hd2 : G.degree n₂ = 3 := hdegD n₂ hn2D
  have hd3 : G.degree n₃ = 3 := hdegD n₃ hn3D
  have hcnbhd : ∀ w : Fin 14, G.Adj c w → w = n₁ ∨ w = n₂ ∨ w = n₃ := by
    intro w hw
    have hw' : w ∈ G.neighborFinset c ∩ D := by
      rw [hNsubeq]; exact (G.mem_neighborFinset _ _).mpr hw
    rw [hset] at hw'; simpa using hw'
  have hhc : ¬G.Adj h c := by
    intro hadj
    rcases hcnbhd h hadj.symm with e | e | e <;> rw [e] at hhdeg4 <;> omega
  have hmeet : ∀ i j : Fin 14, G.degree i = 3 → G.degree j = 3 →
      G.Adj c i → G.Adj c j → i ≠ j → ¬(G.Adj h i ∧ G.Adj h j) := by
    rintro i j hi3 hj3 ci cj hij ⟨hhi, hhj⟩
    have nij : ¬G.Adj i j := fun aij =>
      hT ⟨c, i, j, ci.ne, hij, cj.ne, ci, aij, cj, by omega⟩
    exact hC4 ⟨h, i, c, j,
      card_four_fourteen h i c j (by rintro rfl; omega) (by rintro rfl; omega)
        (by rintro rfl; omega) ci.ne.symm hij cj.ne,
      hhi, ci.symm, cj, hhj.symm, hhc, nij, by omega⟩
  have not12 := hmeet n₁ n₂ hd1 hd2 a1 a2 hne12
  have not13 := hmeet n₁ n₃ hd1 hd3 a1 a3 hne13
  have not23 := hmeet n₂ n₃ hd2 hd3 a2 a3 hne23
  by_cases hb1 : G.Adj h n₁
  · exact dense_two_twin_assemble G t₁ t₂ h n₂ c n₃ ht1deg ht2deg hhdeg4
      hd2 hc3 hd3 hAt1h hAt2h a2.symm a3 ht1iso ht2iso
      (fun hv => not12 ⟨hb1, hv⟩) hhc (fun hv => not13 ⟨hb1, hv⟩) ht12
      a2.symm.ne a3.ne hne23
  · by_cases hb2 : G.Adj h n₂
    · exact dense_two_twin_assemble G t₁ t₂ h n₁ c n₃ ht1deg ht2deg hhdeg4
        hd1 hc3 hd3 hAt1h hAt2h a1.symm a3 ht1iso ht2iso
        hb1 hhc (fun hv => not23 ⟨hb2, hv⟩) ht12 a1.symm.ne a3.ne hne13
    · exact dense_two_twin_assemble G t₁ t₂ h n₁ c n₂ ht1deg ht2deg hhdeg4
        hd1 hc3 hd2 hAt1h hAt2h a1.symm a2 ht1iso ht2iso
        hb1 hhc hb2 ht12 a1.symm.ne a2.ne hne12

/-- **Dominating-edge fat-centre dispatch.**  Given a dominating edge `c₁ ∼ c₂` (every `M`-edge
meets it) with `∑_{v∈D}|N v ∩ D| ≥ 8`, the in-`M`-degree formula forces one endpoint to have
in-`M`-degree `3` (a fat centre); routing the shared degree-`4` hub through `claw_shared_two_twin`
yields a `TwoTwinConfig`. -/
theorem dom_fat_centre_two_twin (G : SimpleGraph (Fin 14)) (D : Finset (Fin 14))
    (hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (c₁ c₂ : Fin 14) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hcov : ∀ p q : Fin 14, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hge : 8 ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card)
    (hindle : ∀ x : Fin 14, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3)
    (k t₁ t₂ : Fin 14) (hhdeg4 : G.degree k = 4) (ht12 : t₁ ≠ t₂)
    (ht1deg : G.degree t₁ = 3) (ht2deg : G.degree t₂ = 3)
    (hAt1k : G.Adj t₁ k) (hAt2k : G.Adj t₂ k)
    (ht1iso : ∀ w : Fin 14, G.Adj t₁ w → G.degree w ≠ 3)
    (ht2iso : ∀ w : Fin 14, G.Adj t₂ w → G.degree w ≠ 3) :
    TwoTwinConfig G := by
  have hform := thin_eM_formula_fourteen G D c₁ c₂ hc1D hc2D hc12 hcov
  have hle1 := hindle c₁ hc1D
  have hle2 := hindle c₂ hc2D
  by_cases hc1 : 3 ≤ (G.neighborFinset c₁ ∩ D).card
  · exact claw_shared_two_twin G D hmemD hT hC4 c₁ t₁ t₂ k hc1D hc1 ht1deg ht2deg hhdeg4
      ht12 hAt1k hAt2k ht1iso ht2iso
  · have hc2 : 3 ≤ (G.neighborFinset c₂ ∩ D).card := by omega
    exact claw_shared_two_twin G D hmemD hT hC4 c₂ t₁ t₂ k hc2D hc2 ht1deg ht2deg hhdeg4
      ht12 hAt1k hAt2k ht1iso ht2iso

/-- **Induced-`C₅` two-twin assembly.**  A degree-`4` hub `k` adjacent to two distinct `M`-isolated
degree-`3` twins, together with an induced `C₅` of degree-`3` vertices, yields a `TwoTwinConfig`:
`hub_cycle_cases` gives a consecutive triple of the cycle that `k` avoids, forming the cherry. -/
theorem c5_shared_two_twin (G : SimpleGraph (Fin 14))
    (hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (k t₁ t₂ : Fin 14) (hhdeg4 : G.degree k = 4) (ht12 : t₁ ≠ t₂)
    (ht1deg : G.degree t₁ = 3) (ht2deg : G.degree t₂ = 3)
    (hAt1k : G.Adj t₁ k) (hAt2k : G.Adj t₂ k)
    (ht1iso : ∀ w : Fin 14, G.Adj t₁ w → G.degree w ≠ 3)
    (ht2iso : ∀ w : Fin 14, G.Adj t₂ w → G.degree w ≠ 3)
    (v₁ v₂ v₃ v₄ v₅ : Fin 14)
    (hd1 : G.degree v₁ = 3) (hd2 : G.degree v₂ = 3) (hd3 : G.degree v₃ = 3)
    (hd4 : G.degree v₄ = 3) (hd5 : G.degree v₅ = 3)
    (hcard5 : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 14)).card = 5)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e34 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁)
    (n13 : ¬G.Adj v₁ v₃) (n14 : ¬G.Adj v₁ v₄) (n24 : ¬G.Adj v₂ v₄)
    (n25 : ¬G.Adj v₂ v₅) (n35 : ¬G.Adj v₃ v₅) :
    TwoTwinConfig G := by
  obtain ⟨d12, d13, d14, d15, d23, d24, d25, d34, d35, d45⟩ :=
    distinct_five_fourteen v₁ v₂ v₃ v₄ v₅ hcard5
  have hB := hub_cycle_cases G hT hC4 k v₁ v₂ v₃ v₄ v₅ hhdeg4 hd1 hd2 hd3 hd4 hd5
    e12 e23 e34 e45 e51 n13 n14 n24 n25 n35 d12 d13 d14 d15 d23 d24 d25 d34 d35 d45
  rcases hB with ⟨p1, p2, p3, p4, p5⟩ | ⟨p2, p3, p4, p5⟩ | ⟨p1, p3, p4, p5⟩ |
    ⟨p1, p2, p4, p5⟩ | ⟨p1, p2, p3, p5⟩ | ⟨p1, p2, p3, p4⟩
  · exact dense_two_twin_assemble G t₁ t₂ k v₁ v₂ v₃ ht1deg ht2deg hhdeg4 hd1 hd2 hd3
      hAt1k hAt2k e12 e23 ht1iso ht2iso p1 p2 p3 ht12 d12 d23 d13
  · exact dense_two_twin_assemble G t₁ t₂ k v₂ v₃ v₄ ht1deg ht2deg hhdeg4 hd2 hd3 hd4
      hAt1k hAt2k e23 e34 ht1iso ht2iso p2 p3 p4 ht12 d23 d34 d24
  · exact dense_two_twin_assemble G t₁ t₂ k v₃ v₄ v₅ ht1deg ht2deg hhdeg4 hd3 hd4 hd5
      hAt1k hAt2k e34 e45 ht1iso ht2iso p3 p4 p5 ht12 d34 d45 d35
  · exact dense_two_twin_assemble G t₁ t₂ k v₄ v₅ v₁ ht1deg ht2deg hhdeg4 hd4 hd5 hd1
      hAt1k hAt2k e45 e51 ht1iso ht2iso p4 p5 p1 ht12 d45 d15.symm d14.symm
  · exact dense_two_twin_assemble G t₁ t₂ k v₁ v₂ v₃ ht1deg ht2deg hhdeg4 hd1 hd2 hd3
      hAt1k hAt2k e12 e23 ht1iso ht2iso p1 p2 p3 ht12 d12 d23 d13
  · exact dense_two_twin_assemble G t₁ t₂ k v₁ v₂ v₃ ht1deg ht2deg hhdeg4 hd1 hd2 hd3
      hAt1k hAt2k e12 e23 ht1iso ht2iso p1 p2 p3 ht12 d12 d23 d13

/-- **Shared degree-`4` hub in the degree-`5` regime.**  When a degree-`5` vertex `g` exists, the
rigid structure (`|D| = 9`, unique degree-`5` hub `g`, four degree-`4` hubs) plus the pigeonhole on
the `≥ 3` `M`-isolated twins (each meeting `≥ 2` of the four degree-`4` hubs) forces two twins to
share a degree-`4` hub. -/
theorem shared_deg4_hub_deg5 (G : SimpleGraph (Fin 14))
    (hm : G.edgeFinset.card = 24) (h3 : ∀ v : Fin 14, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (h2k2 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (g : Fin 14) (hg5 : 5 ≤ G.degree g) :
    ∃ h t₁ t₂ : Fin 14, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 14, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 14, G.Adj t₂ w → G.degree w ≠ 3) := by
  classical
  set D : Finset (Fin 14) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have heM10 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 10 :=
    eM_le_five G D hmemD hT hC4 h2k2
  obtain ⟨hD9, hHubcard, hg5eq, hother⟩ := single_twin_deg5_structure G hm h3 heM10 g hg5
  rw [← hDdef] at hD9
  set Hub : Finset (Fin 14) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 14, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  have hgHub : g ∈ Hub := (hmemHub g).mpr (by omega)
  set Hub4 : Finset (Fin 14) := Finset.univ.filter (fun v => G.degree v = 4) with hHub4def
  have hmemHub4 : ∀ v : Fin 14, v ∈ Hub4 ↔ G.degree v = 4 := by intro v; rw [hHub4def]; simp
  have hHub4deg : ∀ h ∈ Hub4, G.degree h = 4 := fun h hh => (hmemHub4 h).mp hh
  have hHub4eq : Hub4 = Hub.erase g := by
    ext w
    rw [hmemHub4, Finset.mem_erase, hmemHub]
    constructor
    · intro hw4
      exact ⟨fun e => by rw [e] at hw4; omega, by omega⟩
    · rintro ⟨hwg, hwge4⟩
      exact hother w (by omega) hwg
  have hHub4card : Hub4.card = 4 := by
    rw [hHub4eq, Finset.card_erase_of_mem hgHub, hHubcard]
  set Iso : Finset (Fin 14) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 14, G.Adj v w → G.degree w ≠ 3 := by
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
    have htwo : ∀ v ∈ Iso, 2 ≤ (G.neighborFinset v ∩ Hub4).card := by
      intro v hv
      obtain ⟨hvdeg3, _⟩ := hIsoiso v hv
      have hvD : v ∈ D := (hmemD v).mpr hvdeg3
      have hv0 : (G.neighborFinset v ∩ D).card = 0 := by
        rw [hIsodef, Finset.mem_filter] at hv; exact hv.2
      have h3hub := each_iso_three_hubs G D Hub hmemD hmemHub h3 v hvD hv0
      have hsub : G.neighborFinset v ∩ Hub ⊆ insert g (G.neighborFinset v ∩ Hub4) := by
        intro w hw
        rw [Finset.mem_inter] at hw
        by_cases hwg : w = g
        · rw [hwg]; exact Finset.mem_insert_self _ _
        · have hwge4 : 4 ≤ G.degree w := (hmemHub w).mp hw.2
          refine Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hw.1, ?_⟩)
          rw [hmemHub4]; exact hother w (by omega) hwg
      have hc := Finset.card_le_card hsub
      have hc2 := Finset.card_insert_le g (G.neighborFinset v ∩ Hub4)
      rw [h3hub] at hc
      omega
    have hge6 : 6 ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
      have h2iso : 2 * Iso.card ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
        have := Finset.card_nsmul_le_sum Iso
          (fun v => (G.neighborFinset v ∩ Hub4).card) 2 htwo
        simpa [smul_eq_mul, mul_comm] using this
      omega
    omega
  exact shared_deg4_hub_from_count G Iso Hub4 hIsoiso hHub4deg hcount

/-- **Shared degree-`4` hub when there is no degree-`5` vertex.**  Every hub then has degree exactly
`4`, so `|D| = 8`, `|Hub₄| = 6`, and each of the `≥ 3` `M`-isolated twins meets all three of its
hub-neighbours inside `Hub₄`; the pigeonhole (`3·3 = 9 > 6`) yields a shared degree-`4` hub. -/
theorem shared_deg4_hub_nodeg5 (G : SimpleGraph (Fin 14))
    (hm : G.edgeFinset.card = 24) (h3 : ∀ v : Fin 14, 3 ≤ G.degree v)
    (h2k2 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hno5 : ∀ v : Fin 14, G.degree v ≤ 4)
    (hs8 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card ≤ 8) :
    ∃ h t₁ t₂ : Fin 14, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 14, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 14, G.Adj t₂ w → G.degree w ≠ 3) := by
  classical
  set D : Finset (Fin 14) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub4 : Finset (Fin 14) := Finset.univ.filter (fun v => G.degree v = 4) with hHub4def
  have hmemHub4 : ∀ v : Fin 14, v ∈ Hub4 ↔ G.degree v = 4 := by intro v; rw [hHub4def]; simp
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
  have hsum48 : ∑ v : Fin 14, G.degree v = 48 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 48 := by
    rw [Finset.sum_add_sum_compl]; exact hsum48
  have hcc : D.card + Dᶜ.card = 14 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h
    exact h
  have hD8 : D.card = 8 := by rw [hsumD, hsumDc] at hsplit; omega
  have hHub4card : Hub4.card = 6 := by rw [hHub4eqDc]; omega
  set Iso : Finset (Fin 14) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 14, G.Adj v w → G.degree w ≠ 3 := by
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
  exact shared_deg4_hub_from_count G Iso Hub4 hIsoiso hHub4deg hcount

/-- **Three-way alignment dichotomy at `e(M) ≥ 4` (`s ≥ 8`).**  In the residual regime
(`δ ≥ 3`, no good triangle / `2K₂` / `C₄` / `K_{2,3}`) with `∑_{v∈D}|N v ∩ D| ≥ 8`, the graph
admits one of the three signed-cut configurations.

Take an `M`-isolated degree-`3` twin `t` with neighbours `p, q, r` (each degree `≥ 4`).  If all
three are degree `4`, dispatch on `dominating_edge_or_induced_C5`: the dominating-edge `∑ = 10`
double star yields a `SingleVertexConfig` via `single_vertex_doublestar_count`; the induced `C₅`
yields one via `single_vertex_config_from_C5_three_hubs`.  The remaining two sub-cases land
`TwoTwinConfig` via `dom_fat_centre_two_twin` / `c5_shared_two_twin`: the `∑ = 8` dominating `(3,2)`
double star, and the degree-`5`-hub residual (two `M`-isolated twins sharing a degree-`4` hub). -/
theorem halign8 (G : SimpleGraph (Fin 14))
    (hm : G.edgeFinset.card = 24) (h3 : ∀ v : Fin 14, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 14, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 14, ({a, b, c, d} : Finset (Fin 14)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 13)
    (_hK23 : ¬∃ a b c d e : Fin 14, ({a, b, c, d, e} : Finset (Fin 14)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hiso : ∃ t : Fin 14, G.degree t = 3 ∧ ∀ w : Fin 14, G.Adj t w → G.degree w ≠ 3)
    (hge : 8 ≤ ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G := by
  classical
  set D : Finset (Fin 14) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 14, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hindle : ∀ x : Fin 14, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := (hmemD x).mp hx
  obtain ⟨t, ht3, htiso⟩ := hiso
  have htcard : (G.neighborFinset t).card = 3 := by
    rw [G.card_neighborFinset_eq_degree, ht3]
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp htcard
  have htp : G.Adj t p := by
    have : p ∈ G.neighborFinset t := by rw [hset]; simp
    exact (G.mem_neighborFinset _ _).mp this
  have htq : G.Adj t q := by
    have : q ∈ G.neighborFinset t := by rw [hset]; simp
    exact (G.mem_neighborFinset _ _).mp this
  have htr : G.Adj t r := by
    have : r ∈ G.neighborFinset t := by rw [hset]; simp
    exact (G.mem_neighborFinset _ _).mp this
  by_cases hall : G.degree p = 4 ∧ G.degree q = 4 ∧ G.degree r = 4
  · obtain ⟨hp4', hq4', hr4'⟩ := hall
    have hne : ∃ a b : Fin 14, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
      by_contra hcon
      push Not at hcon
      have hz : ∀ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := by
        intro v hv
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro w hw
        rw [Finset.mem_inter, G.mem_neighborFinset] at hw
        exact hcon v w hv hw.2 hw.1
      have hsum0 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := Finset.sum_eq_zero hz
      omega
    rcases dominating_edge_or_induced_C5 G D hmemD hT hC4 h2k2 hne with hdom | hC5
    · obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hdom
      by_cases hsum10 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 10
      · obtain ⟨hin1, hin2⟩ :=
          dom_centres_indeg3 G D c₁ c₂ hc1D hc2D hc12 hindle hcov hsum10
        exact Or.inl (single_vertex_doublestar_count G D hmemD hT hC4 t p q r
          ht3 htiso hp4' hq4' hr4' hpq hpr hqr htp htq htr c₁ c₂ hc1D hc2D hc12 hin1 hin2 hcov)
      · -- `∑ = 8` (`e(M) = 4`): the dominating `(3, 2)` double-star.  One centre is a fat centre
        -- (in-`M`-degree `3`); a shared degree-`4` hub of two `M`-isolated twins lands `TwoTwinConfig`.
        have hform := thin_eM_formula_fourteen G D c₁ c₂ hc1D hc2D hc12 hcov
        have hsle1 := hindle c₁ hc1D
        have hsle2 := hindle c₂ hc2D
        have hs8 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 8 := by omega
        have hshare : ∃ h t₁ t₂ : Fin 14, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
            G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
            (∀ w : Fin 14, G.Adj t₁ w → G.degree w ≠ 3) ∧
            (∀ w : Fin 14, G.Adj t₂ w → G.degree w ≠ 3) := by
          by_cases hg5 : ∃ g : Fin 14, 5 ≤ G.degree g
          · obtain ⟨g, hg5'⟩ := hg5
            exact shared_deg4_hub_deg5 G hm h3 hT hC4 h2k2 g hg5'
          · push Not at hg5
            exact shared_deg4_hub_nodeg5 G hm h3 h2k2 (fun v => by have := hg5 v; omega) hs8
        obtain ⟨k, tw1, tw2, hkdeg4, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso,
          htw2iso⟩ := hshare
        exact Or.inr (Or.inl (dom_fat_centre_two_twin G D hmemD hT hC4 c₁ c₂ hc1D hc2D hc12
          hcov hge hindle k tw1 tw2 hkdeg4 htw12 htw1deg htw2deg hAtw1k hAtw2k htw1iso htw2iso))
    · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
        e12, e23, e34, e45, e51, n13, n14, n24, n25, n35, _⟩ := hC5
      exact Or.inl (single_vertex_config_from_C5_three_hubs G hT hC4 t p q r
        ht3 htiso hp4' hq4' hr4' hpq hpr hqr htp htq htr v₁ v₂ v₃ v₄ v₅
        ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
        ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5
        e12 e23 e34 e45 e51 n13 n14 n24 n25 n35)
  · -- A hub of `t` has degree `≥ 5`: the degree-`5`-hub residual.  By `single_twin_deg5_structure`
    -- there is a unique degree-`5` hub `g` and four degree-`4` hubs; a pigeonhole on the three
    -- `M`-isolated twins forces two to share a degree-`4` hub `k`.  The residual graph then has a
    -- dominating edge (fat centre, claw) or an induced `C₅`; either feeds `TwoTwinConfig`.
    have hpge4 : 4 ≤ G.degree p := by have := htiso p htp; have := h3 p; omega
    have hqge4 : 4 ≤ G.degree q := by have := htiso q htq; have := h3 q; omega
    have hrge4 : 4 ≤ G.degree r := by have := htiso r htr; have := h3 r; omega
    have hg5 : ∃ g : Fin 14, 5 ≤ G.degree g := by
      by_contra hcon
      push Not at hcon
      exact hall ⟨by have := hcon p; omega, by have := hcon q; omega, by have := hcon r; omega⟩
    obtain ⟨g, hg5'⟩ := hg5
    obtain ⟨k, tw1, tw2, hkdeg4, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso,
      htw2iso⟩ := shared_deg4_hub_deg5 G hm h3 hT hC4 h2k2 g hg5'
    have hne : ∃ a b : Fin 14, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
      by_contra hcon
      push Not at hcon
      have hz : ∀ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := by
        intro v hv
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro w hw
        rw [Finset.mem_inter, G.mem_neighborFinset] at hw
        exact hcon v w hv hw.2 hw.1
      have hsum0 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := Finset.sum_eq_zero hz
      omega
    rcases dominating_edge_or_induced_C5 G D hmemD hT hC4 h2k2 hne with hdom | hC5
    · obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hdom
      exact Or.inr (Or.inl (dom_fat_centre_two_twin G D hmemD hT hC4 c₁ c₂ hc1D hc2D hc12
        hcov hge hindle k tw1 tw2 hkdeg4 htw12 htw1deg htw2deg hAtw1k hAtw2k htw1iso htw2iso))
    · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
        e12, e23, e34, e45, e51, n13, n14, n24, n25, n35, _⟩ := hC5
      exact Or.inr (Or.inl (c5_shared_two_twin G hT hC4 k tw1 tw2 hkdeg4 htw12 htw1deg htw2deg
        hAtw1k hAtw2k htw1iso htw2iso v₁ v₂ v₃ v₄ v₅
        ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
        ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5
        e12 e23 e34 e45 e51 n13 n14 n24 n25 n35))

end N14

end ACMax
