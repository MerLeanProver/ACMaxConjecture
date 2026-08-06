import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.Dense
import ACMaxConjecture.SmallCases.N20.HubTriangleFatStar

/-!
# Asymmetric dominating-edge double-star structure for `n = 20`, `e(M) = 4`, `|D| = 8`

This file supplies `fatstar_structure_eM4_D8_twenty`, the structural dispatcher used to close the
`halign8_eM4_twenty` dominating-edge `|D| = 8` branch.  The branch already establishes `|D| = 8`
upstream, so the dispatcher receives it directly.  Given the `e(M) = 4` dominating edge `c₁–c₂`
(covering hypothesis `hcov`), the handshake (`∑ deg = 72`, `∑_D deg = 24`) forces all twelve hubs
to degree `4`, and the in-`M`-degrees split asymmetrically `(3, 2)` (one fat centre with two leaves,
one thin centre with one leaf), via `thin_eM_formula_twenty`.  The fat double-star
`L₁, L₁' – c₁ – c₂ – L₂` is extracted exactly and fed to `exists_hub_triangle_config_fatstar_twenty`.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **Asymmetric fat double-star ⇒ `HubTriangleConfig`.**  Given the dominating edge `c₁–c₂` with the
fat centre `c₁` of in-`M`-degree `3` and the thin centre `c₂` of in-`M`-degree `2`, all hubs degree
`4` and `|D| = 8`, extract the exact double-star `L₁, L₁' – c₁ – c₂ – L₂` and dispatch the
`¬SingleVertex/¬TwoTwin/¬TwoHub` residual to `exists_hub_triangle_config_fatstar_twenty`. -/
theorem fatstar_from_fat_thin_twenty (G : SimpleGraph (Fin 20)) (D : Finset (Fin 20))
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (c₁ c₂ : Fin 20) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hcov : ∀ p q : Fin 20, p ∈ D → q ∈ D → G.Adj p q → p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 3) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hdeg4 : ∀ w : Fin 20, w ∈ Dᶜ → G.degree w = 4) (hD8 : D.card = 8)
    (hsv : ¬SingleVertexConfig G) (htt : ¬TwoTwinConfig G) (hth : ¬TwoHubConfig G) :
    HubTriangleConfig G := by
  classical
  have hc1deg : G.degree c₁ = 3 := (hmemD c₁).mp hc1D
  have hc2deg : G.degree c₂ = 3 := (hmemD c₂).mp hc2D
  have hc2mem1 : c₂ ∈ G.neighborFinset c₁ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
  have hc1mem2 : c₁ ∈ G.neighborFinset c₂ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
  have herase1 : ((G.neighborFinset c₁ ∩ D).erase c₂).card = 2 := by
    rw [Finset.card_erase_of_mem hc2mem1, hin1]
  have herase2 : ((G.neighborFinset c₂ ∩ D).erase c₁).card = 1 := by
    rw [Finset.card_erase_of_mem hc1mem2, hin2]
  obtain ⟨L₁, L₁', hL1nL1', hLset1⟩ := Finset.card_eq_two.mp herase1
  obtain ⟨L₂, hLset2⟩ := Finset.card_eq_one.mp herase2
  have hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁, L₁'} := by
    rw [← Finset.insert_erase hc2mem1, hLset1]
  have hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂} := by
    rw [← Finset.insert_erase hc1mem2, hLset2]
  have hL1mem : L₁ ∈ (G.neighborFinset c₁ ∩ D).erase c₂ := by rw [hLset1]; simp
  have hL1'mem : L₁' ∈ (G.neighborFinset c₁ ∩ D).erase c₂ := by rw [hLset1]; simp
  have hL2mem : L₂ ∈ (G.neighborFinset c₂ ∩ D).erase c₁ := by rw [hLset2]; simp
  rw [Finset.mem_erase] at hL1mem hL1'mem hL2mem
  obtain ⟨hL1nc2, hL1ND⟩ := hL1mem
  obtain ⟨hL1'nc2, hL1'ND⟩ := hL1'mem
  obtain ⟨hL2nc1, hL2ND⟩ := hL2mem
  obtain ⟨hL1N, hL1D⟩ := Finset.mem_inter.mp hL1ND
  obtain ⟨hL1'N, hL1'D⟩ := Finset.mem_inter.mp hL1'ND
  obtain ⟨hL2N, hL2D⟩ := Finset.mem_inter.mp hL2ND
  have hac1L1 : G.Adj c₁ L₁ := (G.mem_neighborFinset _ _).mp hL1N
  have hac1L1' : G.Adj c₁ L₁' := (G.mem_neighborFinset _ _).mp hL1'N
  have hac2L2 : G.Adj c₂ L₂ := (G.mem_neighborFinset _ _).mp hL2N
  have hL1deg : G.degree L₁ = 3 := (hmemD L₁).mp hL1D
  have hL1'deg : G.degree L₁' = 3 := (hmemD L₁').mp hL1'D
  have hL2deg : G.degree L₂ = 3 := (hmemD L₂).mp hL2D
  -- The four cherry non-adjacencies, each from a forbidden low-degree triangle (`hT`).
  have hnL1L1' : ¬G.Adj L₁ L₁' := fun hadj =>
    hT ⟨c₁, L₁, L₁', hac1L1.ne, hL1nL1', hac1L1'.ne, hac1L1, hadj, hac1L1', by
      rw [hc1deg, hL1deg, hL1'deg]; omega⟩
  have hnL1c2 : ¬G.Adj L₁ c₂ := fun hadj =>
    hT ⟨c₁, L₁, c₂, hac1L1.ne, hL1nc2, hc12.ne, hac1L1, hadj, hc12, by
      rw [hc1deg, hL1deg, hc2deg]; omega⟩
  have hnL1'c2 : ¬G.Adj L₁' c₂ := fun hadj =>
    hT ⟨c₁, L₁', c₂, hac1L1'.ne, hL1'nc2, hc12.ne, hac1L1', hadj, hc12, by
      rw [hc1deg, hL1'deg, hc2deg]; omega⟩
  have hnc1L2 : ¬G.Adj c₁ L₂ := fun hadj =>
    hT ⟨c₂, L₂, c₁, hac2L2.ne, hL2nc1, hc12.ne.symm, hac2L2, hadj.symm, hc12.symm, by
      rw [hc2deg, hL2deg, hc1deg]; omega⟩
  -- Exact leaf neighbourhoods via the covering property.
  have hNL1D : G.neighborFinset L₁ ∩ D = {c₁} := by
    apply Finset.Subset.antisymm
    · intro w hw
      obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
      have hadj : G.Adj L₁ w := (G.mem_neighborFinset _ _).mp hwN
      rcases hcov L₁ w hL1D hwD hadj with e | e | e | e
      · exact absurd e hac1L1.ne'
      · exact absurd e hL1nc2
      · rw [e]; simp
      · exact absurd (e ▸ hadj) hnL1c2
    · intro w hw; rw [Finset.mem_singleton] at hw; subst hw
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac1L1.symm, hc1D⟩
  have hNL1'D : G.neighborFinset L₁' ∩ D = {c₁} := by
    apply Finset.Subset.antisymm
    · intro w hw
      obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
      have hadj : G.Adj L₁' w := (G.mem_neighborFinset _ _).mp hwN
      rcases hcov L₁' w hL1'D hwD hadj with e | e | e | e
      · exact absurd e hac1L1'.ne'
      · exact absurd e hL1'nc2
      · rw [e]; simp
      · exact absurd (e ▸ hadj) hnL1'c2
    · intro w hw; rw [Finset.mem_singleton] at hw; subst hw
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac1L1'.symm, hc1D⟩
  have hNL2D : G.neighborFinset L₂ ∩ D = {c₂} := by
    apply Finset.Subset.antisymm
    · intro w hw
      obtain ⟨hwN, hwD⟩ := Finset.mem_inter.mp hw
      have hadj : G.Adj L₂ w := (G.mem_neighborFinset _ _).mp hwN
      rcases hcov L₂ w hL2D hwD hadj with e | e | e | e
      · exact absurd e hL2nc1
      · exact absurd e hac2L2.ne'
      · exact absurd (e ▸ hadj).symm hnc1L2
      · rw [e]; simp
    · intro w hw; rw [Finset.mem_singleton] at hw; subst hw
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac2L2.symm, hc2D⟩
  -- Leaf distinctness between the two stars.
  have hL1nL2 : L₁ ≠ L₂ := by
    intro e
    have hmem : c₁ ∈ G.neighborFinset L₂ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hac1L1).symm, hc1D⟩
    rw [hNL2D, Finset.mem_singleton] at hmem
    exact hc12.ne hmem
  have hL1'nL2 : L₁' ≠ L₂ := by
    intro e
    have hmem : c₁ ∈ G.neighborFinset L₂ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hac1L1').symm, hc1D⟩
    rw [hNL2D, Finset.mem_singleton] at hmem
    exact hc12.ne hmem
  -- `Iso` and its characterisation.
  set Iso : Finset (Fin 20) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3) := by
    intro v hv
    rw [hIsodef, Finset.mem_filter] at hv
    obtain ⟨hvD, hv0⟩ := hv
    refine ⟨(hmemD v).mp hvD, fun w hadj hw3 => ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
    exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
  have hisochar : ∀ w : Fin 20, w ∈ D → w ≠ c₁ → w ≠ c₂ → w ≠ L₁ → w ≠ L₁' → w ≠ L₂ → w ∈ Iso := by
    intro w hwD hwc1 hwc2 hwL1 hwL1' hwL2
    rw [hIsodef, Finset.mem_filter]
    refine ⟨hwD, ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro u hu
    rw [Finset.mem_inter, G.mem_neighborFinset] at hu
    obtain ⟨hwu, huD⟩ := hu
    rcases hcov w u hwD huD hwu with e | e | e | e
    · exact hwc1 e
    · exact hwc2 e
    · have hmem : w ∈ G.neighborFinset c₁ ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hwu).symm, hwD⟩
      rw [hNc1D] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h' | h'
      · exact hwc2 h'
      · exact hwL1 h'
      · exact hwL1' h'
    · have hmem : w ∈ G.neighborFinset c₂ ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hwu).symm, hwD⟩
      rw [hNc2D] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h'
      · exact hwc1 h'
      · exact hwL2 h'
  exact exists_hub_triangle_config_fatstar_twenty G D Iso c₁ c₂ L₁ L₁' L₂ hT hC4 hmemD hIsodef
    hIsoprop hisochar hNc1D hNc2D hNL1D hNL1'D hNL2D hc1deg hc2deg hL1deg hL1'deg hL2deg
    hac1L1 hac1L1' hc12 hac2L2 hnL1L1' hnL1c2 hnL1'c2 hnc1L2 hL1nL1' hL1nc2 hL1'nc2 hL2nc1
    hL1nL2 hL1'nL2 hdeg4 hD8 hsv htt hth

/-- **Fat double-star structural dispatcher (`n = 20`, `e(M) = 4`, dominating edge, `|D| = 8`).**
Routes the `halign8_eM4_twenty` dominating-edge `|D| = 8` branch: the handshake forces all twelve
hubs to degree `4`, and the in-`M`-degree split is `(3, 2)` (`thin_eM_formula_twenty`), giving a
fat double-star fed to `exists_hub_triangle_config_fatstar_twenty`. -/
theorem fatstar_structure_eM4_D8_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (D : Finset (Fin 20)) (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hD8 : D.card = 8)
    (c₁ c₂ : Fin 20) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hcov : ∀ p q : Fin 20, p ∈ D → q ∈ D → G.Adj p q → p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hindle : ∀ x : Fin 20, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3)
    (hsum8 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 8)
    (hsv : ¬SingleVertexConfig G) (htt : ¬TwoTwinConfig G) (hth : ¬TwoHubConfig G) :
    HubTriangleConfig G := by
  classical
  -- Handshake: `∑ deg = 72`, `∑_D deg = 24`, so `∑_{Dᶜ} deg = 48` over the twelve hubs.
  have hsum72 : ∑ v : Fin 20, G.degree v = 72 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul, mul_comm]
  have hsplit72 : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 72 := by
    rw [Finset.sum_add_sum_compl]; exact hsum72
  -- All hubs degree `4`.
  have hDcdeg : ∀ w ∈ Dᶜ, 4 ≤ G.degree w := by
    intro w hw; rw [Finset.mem_compl, hmemD] at hw; have := h3 w; omega
  have hDccard : Dᶜ.card = 12 := by rw [Finset.card_compl, Fintype.card_fin, hD8]
  have hdeg4 : ∀ w : Fin 20, w ∈ Dᶜ → G.degree w = 4 := by
    intro w hw
    have hspl := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hw
    have hrest : 4 * (Dᶜ.erase w).card ≤ ∑ v ∈ Dᶜ.erase w, G.degree v := by
      have hb : ∀ i ∈ Dᶜ.erase w, 4 ≤ G.degree i :=
        fun i hi => hDcdeg i (Finset.mem_of_mem_erase hi)
      have := Finset.card_nsmul_le_sum (Dᶜ.erase w) (fun v => G.degree v) 4 hb
      simpa [smul_eq_mul, mul_comm] using this
    have hec : (Dᶜ.erase w).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hw
    have hsum48 : ∑ v ∈ Dᶜ, G.degree v = 48 := by omega
    have hd4 := hDcdeg w hw
    rw [hsum48] at hspl
    omega
  -- In-`M`-degree split `(3, 2)` from `e(M) = 4`.
  have hc2mem1 : c₂ ∈ G.neighborFinset c₁ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
  have hc1mem2 : c₁ ∈ G.neighborFinset c₂ ∩ D :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
  have hform := thin_eM_formula_twenty G D c₁ c₂ hc1D hc2D hc12 hcov
  rw [hsum8] at hform
  have hi1le := hindle c₁ hc1D
  have hi2le := hindle c₂ hc2D
  have hi1pos : 1 ≤ (G.neighborFinset c₁ ∩ D).card := Finset.card_pos.mpr ⟨c₂, hc2mem1⟩
  have hi2pos : 1 ≤ (G.neighborFinset c₂ ∩ D).card := Finset.card_pos.mpr ⟨c₁, hc1mem2⟩
  by_cases hfat : (G.neighborFinset c₁ ∩ D).card = 3
  · have hi2 : (G.neighborFinset c₂ ∩ D).card = 2 := by omega
    exact fatstar_from_fat_thin_twenty G D hmemD hT hC4 c₁ c₂ hc1D hc2D hc12 hcov hfat hi2
      hdeg4 hD8 hsv htt hth
  · have hi1 : (G.neighborFinset c₁ ∩ D).card = 2 := by omega
    have hi2 : (G.neighborFinset c₂ ∩ D).card = 3 := by omega
    have hcov' : ∀ p q : Fin 20, p ∈ D → q ∈ D → G.Adj p q →
        p = c₂ ∨ p = c₁ ∨ q = c₂ ∨ q = c₁ := by
      intro p q hp hq hpq
      rcases hcov p q hp hq hpq with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
    exact fatstar_from_fat_thin_twenty G D hmemD hT hC4 c₂ c₁ hc2D hc1D hc12.symm hcov' hi2 hi1
      hdeg4 hD8 hsv htt hth

end N20

end ACMax
