import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.Align8Helpers
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleShare
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleForceD9FF4
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleForceD10CleanBudget

/-!
# The `n = 20`, `P₄`-cherry, `|D| = 10`-clean saturation kill

At the `|D| = 10` clean frontier the ten hubs `Dᶜ` all have degree `∈ {4, 5}` with `∑ deg = 42`
(exactly two degree-`5` hubs) and total internal incidence `18`.  Two `≥ 6`-element avoider
families `A1, A2` (the vertices avoiding `{L₁, c₁, c₂}` resp. `{c₁, c₂, L₂}`) with common part
`FF = A1 ∩ A2` carrying internal incidence `≥ 3` each saturate the budget: by
`d10_clean_nonff_isolated` the six members of `FF` consume all `18` internal incidences, so the
four non-`FF` hubs are isolated in `Dᶜ`, and at least two of them have degree `4`.

Those two isolated degree-`4` hubs feed the ported `n = 19` machinery: `isolated_pair_iso_rich_twenty`
makes one of them `Iso`-rich, and `two_isolated_hub_twohubconfig_d9_ff4` packages it with its
companion into a `TwoHubConfig`, contradicting `hth`.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **The `|D| = 10`-clean saturation kill.**  In the `n = 20` `P₄`-cherry residual with the ten
degree-`{4, 5}` hubs saturated (`∑ internal = 18`, `∑ deg = 42`), the two `≥ 6`-avoider families
force a `TwoHubConfig`, contradicting the no-two-hub hypothesis `hth`. -/
theorem d10_clean_force_twenty (G : SimpleGraph (Fin 20)) (D Iso : Finset (Fin 20))
    (L₁ c₁ c₂ L₂ : Fin 20)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3) (hIsoD : Iso ⊆ D)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hclassP : ∀ x ∈ D, x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso)
    (hL1 : G.degree L₁ = 3) (hc1 : G.degree c₁ = 3) (hc2 : G.degree c₂ = 3) (hL2 : G.degree L₂ = 3)
    (hp1 : G.Adj L₁ c₁) (hp2 : G.Adj c₁ c₂) (hp3 : G.Adj c₂ L₂)
    (hind1 : ¬G.Adj L₁ c₂) (hind2 : ¬G.Adj L₁ L₂) (hind3 : ¬G.Adj c₁ L₂)
    (hDc10 : Dᶜ.card = 10) (hint18 : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 18)
    (hge4 : ∀ g ∈ Dᶜ, 4 ≤ G.degree g) (hdeg5 : ∀ g ∈ Dᶜ, G.degree g ≤ 5)
    (hexc : ∑ g ∈ Dᶜ, G.degree g = 42)
    (hA1 : 6 ≤ (Dᶜ.filter (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂)).card)
    (hA2 : 6 ≤ (Dᶜ.filter (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)).card)
    (hint2 : ∀ g ∈ Dᶜ.filter (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂),
      2 ≤ (G.neighborFinset g ∩ Dᶜ).card)
    (hint2' : ∀ g ∈ Dᶜ.filter (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂),
      2 ≤ (G.neighborFinset g ∩ Dᶜ).card)
    (hint3 : ∀ g ∈ (Dᶜ.filter (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂)) ∩
        (Dᶜ.filter (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)),
      3 ≤ (G.neighborFinset g ∩ Dᶜ).card)
    (hth : ¬TwoHubConfig G) : False := by
  classical
  set A1 : Finset (Fin 20) := Dᶜ.filter (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂)
    with hA1def
  set A2 : Finset (Fin 20) := Dᶜ.filter (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂)
    with hA2def
  set FF : Finset (Fin 20) := A1 ∩ A2 with hFFdef
  have hA1subDc : A1 ⊆ Dᶜ := by rw [hA1def]; exact Finset.filter_subset _ _
  have hA2subDc : A2 ⊆ Dᶜ := by rw [hA2def]; exact Finset.filter_subset _ _
  have hFFsubDc : FF ⊆ Dᶜ := by rw [hFFdef]; exact Finset.inter_subset_left.trans hA1subDc
  -- The saturation budget forces `FF` to carry all internal incidences.
  obtain ⟨_hA1FF, _hA2FF, hFF6, hzero⟩ := d10_clean_nonff_isolated Dᶜ A1 A2 FF
    (fun g => (G.neighborFinset g ∩ Dᶜ).card)
    hA1subDc hA2subDc hFFdef hDc10 hA1 hA2 hint2 hint2' hint3 hint18
  -- The four non-`FF` hubs are isolated in `Dᶜ`; at least two have degree `4`.
  have hTcard : (Dᶜ \ FF).card = 4 := by rw [Finset.card_sdiff_of_subset hFFsubDc, hDc10, hFF6]
  have hTsub : Dᶜ \ FF ⊆ Dᶜ := Finset.sdiff_subset
  have hdeg5count : (Dᶜ.filter (fun g => G.degree g = 5)).card = 2 := by
    have hpart := Finset.sum_filter_add_sum_filter_not Dᶜ (fun g => G.degree g = 5)
      (fun g => G.degree g)
    have h4 : ∀ g ∈ Dᶜ.filter (fun g => ¬ G.degree g = 5), G.degree g = 4 := by
      intro g hg
      rw [Finset.mem_filter] at hg
      have := hge4 g hg.1; have := hdeg5 g hg.1; omega
    have h5 : ∀ g ∈ Dᶜ.filter (fun g => G.degree g = 5), G.degree g = 5 := by
      intro g hg; exact (Finset.mem_filter.mp hg).2
    rw [Finset.sum_congr rfl h5, Finset.sum_congr rfl h4, Finset.sum_const, Finset.sum_const,
      smul_eq_mul, smul_eq_mul] at hpart
    have hcc : (Dᶜ.filter (fun g => G.degree g = 5)).card
        + (Dᶜ.filter (fun g => ¬ G.degree g = 5)).card = 10 := by
      rw [Finset.card_filter_add_card_filter_not]; exact hDc10
    rw [hexc] at hpart; omega
  have hle5 : ((Dᶜ \ FF).filter (fun g => G.degree g = 5)).card ≤ 2 := by
    rw [← hdeg5count]; exact Finset.card_le_card (Finset.filter_subset_filter _ hTsub)
  have h45 : (Dᶜ \ FF).filter (fun g => ¬ G.degree g = 5)
      = (Dᶜ \ FF).filter (fun g => G.degree g = 4) := by
    apply Finset.filter_congr
    intro g hg
    have hgDc := hTsub hg
    have := hge4 g hgDc; have := hdeg5 g hgDc
    constructor <;> intro <;> omega
  have hpartT := Finset.card_filter_add_card_filter_not (s := Dᶜ \ FF)
    (p := fun g => G.degree g = 5)
  rw [h45] at hpartT
  obtain ⟨h₁, h1mem, h₂, h2mem, hne⟩ := Finset.one_lt_card.mp
    (by omega : 1 < ((Dᶜ \ FF).filter (fun g => G.degree g = 4)).card)
  rw [Finset.mem_filter] at h1mem h2mem
  obtain ⟨hh1Dc, hh1nFF⟩ := Finset.mem_sdiff.mp h1mem.1
  obtain ⟨hh2Dc, hh2nFF⟩ := Finset.mem_sdiff.mp h2mem.1
  have hh10 : G.neighborFinset h₁ ∩ Dᶜ = ∅ := Finset.card_eq_zero.mp (hzero h₁ hh1Dc hh1nFF)
  have hh20 : G.neighborFinset h₂ ∩ Dᶜ = ∅ := Finset.card_eq_zero.mp (hzero h₂ hh2Dc hh2nFF)
  -- Path-cherry distinctness needed by the ported extraction.
  have hL1nc2 : L₁ ≠ c₂ := by rintro rfl; exact hind2 hp3
  have hL2nc1 : L₂ ≠ c₁ := by rintro rfl; exact hind2 hp1
  -- One of the two isolated degree-`4` hubs is `Iso`-rich.
  have hrich := isolated_pair_iso_rich_twenty G D Iso L₁ c₁ c₂ L₂ h₁ h₂ hT hC4 hclassP hIsoprop
    hp1.symm hp2 hp3 hind3 (fun h => hind1 h.symm) hL1nc2 hL2nc1 hL1 hc1 hc2 hL2
    hh2Dc h1mem.2 h2mem.2 hh10 hh20 hne hind2
  rcases hrich with hr | hr
  · exact hth (two_isolated_hub_twohubconfig_d9_ff4 G D Iso L₁ c₁ c₂ L₂ h₁ h₂ hC4 hmemD hIsoD
      hclassP hIsoprop hp1.symm hp2 hp3 hc1 hc2 hh1Dc hh2Dc h1mem.2 h2mem.2 hh10 hh20 hne hr)
  · exact hth (two_isolated_hub_twohubconfig_d9_ff4 G D Iso L₁ c₁ c₂ L₂ h₂ h₁ hC4 hmemD hIsoD
      hclassP hIsoprop hp1.symm hp2 hp3 hc1 hc2 hh2Dc hh1Dc h2mem.2 h1mem.2 hh20 hh10 hne.symm hr)

end N20

end ACMax
