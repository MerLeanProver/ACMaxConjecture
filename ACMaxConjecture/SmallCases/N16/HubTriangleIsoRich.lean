import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N16.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N16.HubTriangleStruct
import ACMaxConjecture.SmallCases.N16.HubTriangleActive
import ACMaxConjecture.SmallCases.N16.HubTriangleFF
import ACMaxConjecture.SmallCases.N16.HubTriangleIsoRich3

/-!
# Iso-rich triangle forcing for the `n = 16`, `e(M) = 3`, `|D| = 8` hub-triangle corner

This file closes the genuinely new `n = 16` obligation `iso_rich_force_sixteen`: under the residual
hypotheses, assuming neither cherry admits a triangle of pairwise-adjacent avoiding hubs, the
fully-free hub count `|FF| ∈ {2, 3, 4}` (from `active_hub_budget_sixteen`) is contradictory.

* `|FF| = 4`: `ff_four_triangle` gives a Mantel triangle among the four fully-free hubs (all
  avoiding cherry `{c₁, c₂, L₂}`), directly contradicting `htri2`.
* `|FF| = 2`: the **inactive-hub** argument.  The inclusion–exclusion budget forces
  `|A1| = |A2| = 4`, so the two inactive hubs `B = Dᶜ \ (A1 ∪ A2)` carry `int = 0`.  Being inactive
  each touches a cherry, so `path ≥ 1` and hence `iso = 4 − path − int ≤ 3`; the iso budget
  (`∑ iso = 12`, avoider `iso ≤ 1`) forces both inactive hubs to `iso = 3`.  Two non-adjacent
  hubs of iso-degree `3` share `≥ 3 + 3 − 4 = 2` of the four twins, contradicting
  `nonadj_hubs_share_le_one_iso` (share `≤ 1`).
* `|FF| = 3`: documented `sorry` (one genuine sub-case; see the inline note).
-/

namespace ACMax

open scoped Classical

namespace N16

/-- **No avoider triangle ⇒ contradiction (the `n = 16` iso-rich core).**  Full replacement for the
`core_triangle_force_sixteen` obligation: dispatches on `|FF| ∈ {2, 3, 4}`, closing `|FF| = 4`
(Mantel) and `|FF| = 2` (inactive-hub share bound), with the `|FF| = 3` sub-case left as one
documented `sorry`. -/
theorem iso_rich_force_sixteen (G : SimpleGraph (Fin 16))
    (D Iso : Finset (Fin 16)) (L₁ c₁ c₂ L₂ : Fin 16)
    (_hT : ¬∃ x y z : Fin 16, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 16, ({a, b, c, d, e} : Finset (Fin 16)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18)
    (hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3)
    (hIsodef : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 16, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 16, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (_hcov : ∀ p q : Fin 16, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (_hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (_hc1deg : G.degree c₁ = 3) (_hc2deg : G.degree c₂ = 3)
    (_hL1deg : G.degree L₁ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (_hnL1c2 : ¬G.Adj L₁ c₂) (hnc1L2 : ¬G.Adj c₁ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hdeg4 : ∀ w : Fin 16, w ∈ Dᶜ → G.degree w = 4)
    (_hD8 : D.card = 8) (hth : ¬TwoHubConfig G)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hW : ∀ g : Fin 16, g ∈ Dᶜ →
      ((¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) ∨
        (¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)) →
      (G.neighborFinset g ∩ Iso).card ≤ 1)
    (hA : ∀ t : Fin 16, t ∈ Iso → ∀ p q : Fin 16, p ≠ q →
      G.Adj t p → G.Adj t q →
      ¬((¬G.Adj p L₁ ∧ ¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧
          ¬G.Adj q L₁ ∧ ¬G.Adj q c₁ ∧ ¬G.Adj q c₂) ∨
        (¬G.Adj p c₁ ∧ ¬G.Adj p c₂ ∧ ¬G.Adj p L₂ ∧
          ¬G.Adj q c₁ ∧ ¬G.Adj q c₂ ∧ ¬G.Adj q L₂)))
    (hDc8 : Dᶜ.card = 8) (hIso4 : Iso.card = 4)
    (hcard_c1 : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hcard_c2 : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hcard_L1 : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hcard_L2 : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hSum14 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 14)
    (_htri1 : ¬∃ a b c : Fin 16, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂))
    (htri2 : ¬∃ a b c : Fin 16, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂)) :
    False := by
  classical
  -- Distinctness among the four path vertices.
  have hL1c1 : L₁ ≠ c₁ := (G.ne_of_adj hac1L1).symm
  have hc1c2 : c₁ ≠ c₂ := G.ne_of_adj hc12
  have hc2L2 : c₂ ≠ L₂ := G.ne_of_adj hac2L2
  have hc1L2 : c₁ ≠ L₂ := hL2nc1.symm
  have hL1L2 : L₁ ≠ L₂ := by rintro rfl; exact hnc1L2 hac1L1
  -- Path / Iso partition of `D`.
  obtain ⟨hDeq, _hdisj⟩ :=
    path_iso_partition G D Iso L₁ c₁ c₂ L₂ hIsodef hisochar hL1D hc1D hc2D hL2D hac1L1 hc12 hac2L2
  have hclassP : ∀ x : Fin 16, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso := by
    intro x hx
    rw [← hDeq] at hx
    rcases Finset.mem_union.mp hx with h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h; tauto
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hIsoD : Iso ⊆ D := by rw [hIsodef]; exact Finset.filter_subset _ _
  -- The two cherry-avoider sets and `FF = A1 ∩ A2`.
  set A1 := Dᶜ.filter (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) with hA1def
  set A2 := Dᶜ.filter (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) with hA2def
  set FF := A1 ∩ A2 with hFFdef
  have hA1sub : A1 ⊆ Dᶜ := by rw [hA1def]; exact Finset.filter_subset _ _
  have hA2sub : A2 ⊆ Dᶜ := by rw [hA2def]; exact Finset.filter_subset _ _
  have hFFsubA1 : FF ⊆ A1 := by rw [hFFdef]; exact Finset.inter_subset_left
  have hFFsubA2 : FF ⊆ A2 := by rw [hFFdef]; exact Finset.inter_subset_right
  have hFFsub : FF ⊆ Dᶜ := hFFsubA1.trans hA1sub
  -- Avoider internal degree `≥ 2`; fully-free internal degree `≥ 3`.
  have hA1int : ∀ g ∈ A1, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    rw [hA1def, Finset.mem_filter] at hg
    obtain ⟨hgDc, hgL1, hgc1, hgc2⟩ := hg
    refine avoider_internal_ge_two G D Iso g L₂ (hdeg4 g hgDc)
      (hW g hgDc (Or.inl ⟨hgL1, hgc1, hgc2⟩)) ?_
    intro x hadj hxD
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact Or.inl h
    · exact Or.inr h
  have hA2int : ∀ g ∈ A2, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    rw [hA2def, Finset.mem_filter] at hg
    obtain ⟨hgDc, hgc1, hgc2, hgL2⟩ := hg
    refine avoider_internal_ge_two G D Iso g L₁ (hdeg4 g hgDc)
      (hW g hgDc (Or.inr ⟨hgc1, hgc2, hgL2⟩)) ?_
    intro x hadj hxD
    rcases hclassP x hxD with h | h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact Or.inr h
  have hFFint : ∀ g ∈ FF, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
    intro g hg
    have hgA1 := hFFsubA1 hg
    have hgA2 := hFFsubA2 hg
    rw [hA1def, Finset.mem_filter] at hgA1
    rw [hA2def, Finset.mem_filter] at hgA2
    obtain ⟨hgDc, hgL1, hgc1, hgc2⟩ := hgA1
    obtain ⟨_, _, _, hgL2⟩ := hgA2
    refine fully_free_internal_ge_three G D Iso g (hdeg4 g hgDc)
      (hW g hgDc (Or.inl ⟨hgL1, hgc1, hgc2⟩)) ?_
    intro x hadj hxD
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact h
  -- Each cherry has `≥ 4` avoiders.
  obtain ⟨hA1card, hA2card⟩ :=
    cherry_avoiders_ge_four G D L₁ c₁ c₂ L₂ hDc8 hcard_c1 hcard_c2 hcard_L1 hcard_L2
  rw [← hA1def] at hA1card
  rw [← hA2def] at hA2card
  -- Inclusion–exclusion budget: `|FF| ∈ {2, 3, 4}`.
  obtain ⟨hFFlb, hFFub⟩ :=
    active_hub_budget_sixteen Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card)
      hA1sub hA2sub hFFdef hA1card hA2card hA1int hA2int hFFint hSum14
  -- Residual incidence sums (path / iso totals and the per-hub split).
  obtain ⟨hsumP, hsumI, hper⟩ :=
    residual_incidence_sums G D Iso L₁ c₁ c₂ L₂ hIsodef hIsoprop hisochar hL1D hc1D hc2D hL2D
      hac1L1 hc12 hac2L2 hnc1L2 hdeg4 hcard_c1 hcard_c2 hcard_L1 hcard_L2 hIso4 hL1nc2 hL2nc1
  -- Dispatch on `|FF|`.
  have hFFcases : FF.card = 4 ∨ FF.card = 2 ∨ FF.card = 3 := by omega
  rcases hFFcases with hFF4 | hFF23
  · -- **`|FF| = 4`:** a Mantel triangle among the four fully-free hubs (all in `A2`).
    obtain ⟨a, b, c, haFF, hbFF, hcFF, hab, hac, hbc⟩ :=
      ff_four_triangle G Dᶜ FF hFFsub hFF4 hFFint hSum14
    have getA2 : ∀ g : Fin 16, g ∈ FF →
        g ∈ Dᶜ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂ := by
      intro g hg
      have hgA2 := hFFsubA2 hg
      rw [hA2def, Finset.mem_filter] at hgA2
      exact hgA2
    obtain ⟨haDc, hac1, hac2, haL2⟩ := getA2 a haFF
    obtain ⟨hbDc, hbc1, hbc2, hbL2⟩ := getA2 b hbFF
    obtain ⟨hcDc, hcc1, hcc2, hcL2⟩ := getA2 c hcFF
    exact htri2 ⟨a, b, c, haDc, hbDc, hcDc, hab, hac, hbc,
      ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩⟩
  · -- **`|FF| ∈ {2, 3}`: the inactive-hub argument.**
    -- The inactive hubs `B = Dᶜ \ (A1 ∪ A2)`.
    set B := Dᶜ \ (A1 ∪ A2) with hBdef
    have hUsub : A1 ∪ A2 ⊆ Dᶜ := Finset.union_subset hA1sub hA2sub
    -- Internal-degree partition `∑_B int + ∑_{A1∪A2} int = 14`.
    have hBpart : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card)
        + ∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Dᶜ).card = 14 := by
      rw [hBdef, Finset.sum_sdiff hUsub, hSum14]
    -- `∑_{A1∪A2} int = ∑_{A1} int + ∑_{A2\A1} int`.
    have hdisj : Disjoint A1 (A2 \ A1) := Finset.disjoint_sdiff
    have hunion_eq : A1 ∪ (A2 \ A1) = A1 ∪ A2 := Finset.union_sdiff_self_eq_union
    have hABsplit : (∑ g ∈ A1, (G.neighborFinset g ∩ Dᶜ).card)
        + ∑ g ∈ A2 \ A1, (G.neighborFinset g ∩ Dᶜ).card
        = ∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Dᶜ).card := by
      rw [← hunion_eq, Finset.sum_union hdisj]
    -- `∑_{A1} int = ∑_{A1\FF} int + ∑_FF int`.
    have hA1split : (∑ g ∈ A1 \ FF, (G.neighborFinset g ∩ Dᶜ).card)
        + ∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card
        = ∑ g ∈ A1, (G.neighborFinset g ∩ Dᶜ).card := Finset.sum_sdiff hFFsubA1
    -- Internal-degree lower bounds on the pieces.
    have hFFsum_ge : 3 * FF.card ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ Dᶜ).card := by
      have := Finset.card_nsmul_le_sum FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) 3 hFFint
      simpa [smul_eq_mul, Nat.mul_comm] using this
    have hA1mf_ge : 2 * (A1 \ FF).card
        ≤ ∑ g ∈ A1 \ FF, (G.neighborFinset g ∩ Dᶜ).card := by
      have := Finset.card_nsmul_le_sum (A1 \ FF) (fun g => (G.neighborFinset g ∩ Dᶜ).card) 2
        (fun g hg => hA1int g ((Finset.mem_sdiff.mp hg).1))
      simpa [smul_eq_mul, Nat.mul_comm] using this
    have hA2mA1_ge : 2 * (A2 \ A1).card
        ≤ ∑ g ∈ A2 \ A1, (G.neighborFinset g ∩ Dᶜ).card := by
      have := Finset.card_nsmul_le_sum (A2 \ A1) (fun g => (G.neighborFinset g ∩ Dᶜ).card) 2
        (fun g hg => hA2int g ((Finset.mem_sdiff.mp hg).1))
      simpa [smul_eq_mul, Nat.mul_comm] using this
    -- Cardinality bookkeeping.
    have hA1FFinter : (A1 ∩ FF).card = FF.card := by
      rw [Finset.inter_eq_right.mpr hFFsubA1]
    have hA1mfcard : (A1 \ FF).card + FF.card = A1.card := by
      rw [← hA1FFinter]; exact Finset.card_sdiff_add_card_inter A1 FF
    have hA2A1FF : (A2 ∩ A1).card = FF.card := by rw [hFFdef, Finset.inter_comm]
    have hA2mA1card : (A2 \ A1).card + FF.card = A2.card := by
      rw [← hA2A1FF]; exact Finset.card_sdiff_add_card_inter A2 A1
    -- Union size and inactive-hub count.
    have hUcard : (A1 ∪ A2).card + FF.card = A1.card + A2.card := by
      rw [hFFdef]; exact Finset.card_union_add_card_inter A1 A2
    have hBcard_eq : B.card + (A1 ∪ A2).card = Dᶜ.card := by
      rw [hBdef, Finset.card_sdiff_add_card, Finset.union_eq_left.mpr hUsub]
    -- The key inequality: `2|A1| + 2|A2| ≤ ∑_{A1∪A2} int + |FF|`.
    have hABge : 2 * A1.card + 2 * A2.card
        ≤ (∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Dᶜ).card) + FF.card := by
      omega
    -- Iso-degree partition `∑_B iso + ∑_{A1∪A2} iso = 12`, with avoiders carrying `iso ≤ 1`.
    have hIsoBpart : (∑ g ∈ B, (G.neighborFinset g ∩ Iso).card)
        + ∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Iso).card = 12 := by
      rw [hBdef, Finset.sum_sdiff hUsub, hsumI]
    have hisoAB : ∀ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Iso).card ≤ 1 := by
      intro g hg
      rcases Finset.mem_union.mp hg with hg1 | hg2
      · rw [hA1def, Finset.mem_filter] at hg1
        exact hW g hg1.1 (Or.inl hg1.2)
      · rw [hA2def, Finset.mem_filter] at hg2
        exact hW g hg2.1 (Or.inr hg2.2)
    have hIsoAB_le : (∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Iso).card) ≤ (A1 ∪ A2).card := by
      calc (∑ g ∈ A1 ∪ A2, (G.neighborFinset g ∩ Iso).card)
          ≤ ∑ _g ∈ A1 ∪ A2, 1 := Finset.sum_le_sum hisoAB
        _ = (A1 ∪ A2).card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    -- Each inactive hub touches a cherry, so `path ≥ 1`.
    have hpath1 : ∀ h ∈ B,
        1 ≤ (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 16))).card := by
      intro h hh
      rw [hBdef, Finset.mem_sdiff] at hh
      obtain ⟨hhDc, hhU⟩ := hh
      have hhA1 : h ∉ A1 := fun hmem => hhU (Finset.mem_union_left _ hmem)
      have hpred : ¬(¬G.Adj h L₁ ∧ ¬G.Adj h c₁ ∧ ¬G.Adj h c₂) := by
        intro hp
        exact hhA1 (by rw [hA1def, Finset.mem_filter]; exact ⟨hhDc, hp⟩)
      apply Finset.card_pos.mpr
      push Not at hpred
      by_cases h1 : G.Adj h L₁
      · exact ⟨L₁, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1, by simp⟩⟩
      · by_cases h2 : G.Adj h c₁
        · exact ⟨c₁, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h2, by simp⟩⟩
        · exact ⟨c₂, Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset _ _).mpr (hpred h1 h2), by simp⟩⟩
    rcases hFF23 with hFF2 | hFF3
    · -- **`|FF| = 2`:** `|A1| = |A2| = 4`, `|B| = 2`, both inactive hubs `iso = 3`.
      have hA1eq : A1.card = 4 := by omega
      have hA2eq : A2.card = 4 := by omega
      have hBcard : B.card = 2 := by omega
      have hBint0 : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card) = 0 := by omega
      have hIsoB_ge : 6 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by omega
      -- Extract the two inactive hubs.
      obtain ⟨h₁, h₂, hh12, hBeq⟩ := Finset.card_eq_two.mp hBcard
      have hh1B : h₁ ∈ B := by rw [hBeq]; simp
      have hh2B : h₂ ∈ B := by rw [hBeq]; simp
      have hh1Dc : h₁ ∈ Dᶜ := (Finset.mem_sdiff.mp (hBdef ▸ hh1B)).1
      have hh2Dc : h₂ ∈ Dᶜ := (Finset.mem_sdiff.mp (hBdef ▸ hh2B)).1
      -- Sum over the pair.
      have hintpair : (G.neighborFinset h₁ ∩ Dᶜ).card + (G.neighborFinset h₂ ∩ Dᶜ).card
          = ∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card := by rw [hBeq, Finset.sum_pair hh12]
      have hint1 : (G.neighborFinset h₁ ∩ Dᶜ).card = 0 := by omega
      have hint2 : (G.neighborFinset h₂ ∩ Dᶜ).card = 0 := by omega
      -- `path + iso + int = 4` per hub; `int = 0`, `path ≥ 1` ⇒ `iso ≤ 3`; sum `≥ 6` ⇒ both `= 3`.
      have hper1 := hper h₁ hh1Dc
      have hper2 := hper h₂ hh2Dc
      have hp1 := hpath1 h₁ hh1B
      have hp2 := hpath1 h₂ hh2B
      have hisosum : (G.neighborFinset h₁ ∩ Iso).card + (G.neighborFinset h₂ ∩ Iso).card
          = ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by rw [hBeq, Finset.sum_pair hh12]
      have hiso1 : (G.neighborFinset h₁ ∩ Iso).card = 3 := by omega
      have hiso2 : (G.neighborFinset h₂ ∩ Iso).card = 3 := by omega
      -- The two inactive hubs are non-adjacent (`int = 0`).
      have hnadj : ¬G.Adj h₁ h₂ := by
        intro hadj
        have hmem : h₂ ∈ G.neighborFinset h₁ ∩ Dᶜ :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hh2Dc⟩
        rw [Finset.card_eq_zero] at hint1
        rw [hint1] at hmem; exact (Finset.notMem_empty _) hmem
      -- Share bound: two non-adjacent hubs share `≤ 1` twin.
      have hshare := nonadj_hubs_share_le_one_iso G D Iso hC4 hIsoD hIsoprop hdeg4
        h₁ h₂ hh1Dc hh2Dc hh12 hnadj
      -- But two `iso = 3` neighbourhoods in `Iso` (`|Iso| = 4`) share `≥ 2`.
      have hsub1 : G.neighborFinset h₁ ∩ Iso ⊆ Iso := Finset.inter_subset_right
      have hsub2 : G.neighborFinset h₂ ∩ Iso ⊆ Iso := Finset.inter_subset_right
      have hunion_le : ((G.neighborFinset h₁ ∩ Iso) ∪ (G.neighborFinset h₂ ∩ Iso)).card ≤ 4 := by
        calc ((G.neighborFinset h₁ ∩ Iso) ∪ (G.neighborFinset h₂ ∩ Iso)).card
            ≤ Iso.card := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
          _ = 4 := hIso4
      have hincl := Finset.card_union_add_card_inter
        (G.neighborFinset h₁ ∩ Iso) (G.neighborFinset h₂ ∩ Iso)
      have hinter_eq : (G.neighborFinset h₁ ∩ Iso) ∩ (G.neighborFinset h₂ ∩ Iso)
          = (G.neighborFinset h₁ ∩ G.neighborFinset h₂) ∩ Iso := by
        rw [Finset.inter_inter_inter_comm, Finset.inter_self]
      rw [hiso1, hiso2, hinter_eq] at hincl
      omega
    · -- **`|FF| = 3`: the inactive-hub `TwoHubConfig` extraction.**  The budget forces
      -- `|A1| = |A2| = 4`, `|B| = 3`, with `∑_B int ≤ 1` and `∑_B iso ≥ 7`; from this
      -- `ff3_extract_twohub` builds a `TwoHubConfig G`, contradicting `hth`.
      have hA1eq : A1.card = 4 := by omega
      have hA2eq : A2.card = 4 := by omega
      have hBcard : B.card = 3 := by omega
      have hBint1 : (∑ g ∈ B, (G.neighborFinset g ∩ Dᶜ).card) ≤ 1 := by omega
      have hBiso7 : 7 ≤ ∑ g ∈ B, (G.neighborFinset g ∩ Iso).card := by omega
      have hBsub : B ⊆ Dᶜ := by rw [hBdef]; exact Finset.sdiff_subset
      exact ff3_extract_twohub G D Iso L₁ c₁ c₂ L₂ B hth hC4 hIsoD hIsoprop hdeg4
        (fun v hv => (hmemD v).mp hv) hDeq hBsub hBcard hBint1 hBiso7 hper hpath1

end N16

end ACMax
