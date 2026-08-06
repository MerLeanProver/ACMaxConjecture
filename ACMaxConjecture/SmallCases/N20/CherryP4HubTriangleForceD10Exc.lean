import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.Align8Helpers
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleShare
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleForceD9FF4
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleForceD10CleanBudget

/-!
# The `n = 20`, `P₄`-cherry, `|D| = 10` *exceptional* (degree-`6` hub) saturation kill

This is the `deg ≤ 5` companion of `d10_clean_force_twenty`.  Here the ten hubs `Dᶜ` still carry
`∑ deg = 42` and total internal incidence `18`, but the excess is spent on a *single* degree-`6`
hub `h₆`; the remaining nine hubs are then degree-`4` exactly (`42 − 6 = 36 = 4 · 9`), which we
derive from `hge4`, `hd₆`, and `hexc`.

The saturation argument is degree-blind: `d10_clean_nonff_isolated` still forces the two `≥ 6`
avoider families to coincide with their `6`-element intersection `FF`, so the four non-`FF` hubs
are isolated in `Dᶜ`.  Because `h₆` is the *only* non-degree-`4` hub, at least three of those four
non-`FF` hubs have degree `4`; picking two of them feeds the ported `n = 19` machinery
(`isolated_pair_iso_rich_twenty` + `two_isolated_hub_twohubconfig_d9_ff4`) to build a
`TwoHubConfig`, contradicting `hth`.  The degree-`6` hub only matters for the degree bookkeeping.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **The `|D| = 10` exceptional (degree-`6` hub) saturation kill.**  In the `n = 20` `P₄`-cherry
residual with ten hubs (`∑ deg = 42`, `∑ internal = 18`) whose excess is concentrated in a single
degree-`6` hub `h₆` (all other hubs degree `4`), the two `≥ 6`-avoider families force a
`TwoHubConfig`, contradicting the no-two-hub hypothesis `hth`. -/
theorem d10_exc_force_twenty (G : SimpleGraph (Fin 20)) (D Iso : Finset (Fin 20))
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
    (hge4 : ∀ g ∈ Dᶜ, 4 ≤ G.degree g) (hexc : ∑ g ∈ Dᶜ, G.degree g = 42)
    (h₆ : Fin 20) (hh₆ : h₆ ∈ Dᶜ) (hd₆ : G.degree h₆ = 6)
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
  -- The excess is spent on `h₆`, so every other hub has degree exactly `4`.
  have hd4 : ∀ g ∈ Dᶜ, g ≠ h₆ → G.degree g = 4 := by
    intro g₀ hg₀Dc hg₀ne
    have hpair_sub : ({h₆, g₀} : Finset (Fin 20)) ⊆ Dᶜ := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hh₆
      · exact hg₀Dc
    have hpair_card : ({h₆, g₀} : Finset (Fin 20)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hg₀ne]), Finset.card_singleton]
    have hsplit : (∑ x ∈ Dᶜ \ ({h₆, g₀} : Finset (Fin 20)), G.degree x)
        + ∑ x ∈ ({h₆, g₀} : Finset (Fin 20)), G.degree x = ∑ x ∈ Dᶜ, G.degree x :=
      Finset.sum_sdiff hpair_sub
    have hpair_sum : ∑ x ∈ ({h₆, g₀} : Finset (Fin 20)), G.degree x
        = G.degree h₆ + G.degree g₀ := by
      rw [Finset.sum_insert (by simp [Ne.symm hg₀ne]), Finset.sum_singleton]
    have hrest_card : (Dᶜ \ ({h₆, g₀} : Finset (Fin 20))).card = 8 := by
      rw [Finset.card_sdiff_of_subset hpair_sub, hDc10, hpair_card]
    have hrest_lb : 4 * (Dᶜ \ ({h₆, g₀} : Finset (Fin 20))).card
        ≤ ∑ x ∈ Dᶜ \ ({h₆, g₀} : Finset (Fin 20)), G.degree x := by
      have := Finset.card_nsmul_le_sum (Dᶜ \ ({h₆, g₀} : Finset (Fin 20)))
        (fun x => G.degree x) 4 (fun x hx => hge4 x (Finset.mem_sdiff.mp hx).1)
      simpa [smul_eq_mul, Nat.mul_comm] using this
    have hg₀ge := hge4 g₀ hg₀Dc
    rw [hexc, hpair_sum, hd₆] at hsplit
    omega
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
  have hTcard : (Dᶜ \ FF).card = 4 := by rw [Finset.card_sdiff_of_subset hFFsubDc, hDc10, hFF6]
  have hTsub : Dᶜ \ FF ⊆ Dᶜ := Finset.sdiff_subset
  -- `h₆` is the only non-degree-`4` hub, so at least three of the four non-`FF` hubs are degree `4`.
  have hbig : ((Dᶜ \ FF) \ ({h₆} : Finset (Fin 20))) ⊆
      (Dᶜ \ FF).filter (fun g => G.degree g = 4) := by
    intro g hg
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hg
    obtain ⟨hgT, hgne⟩ := hg
    rw [Finset.mem_filter]
    exact ⟨hgT, hd4 g (hTsub hgT) hgne⟩
  have hbigcard : 3 ≤ ((Dᶜ \ FF) \ ({h₆} : Finset (Fin 20))).card := by
    have hle := Finset.le_card_sdiff ({h₆} : Finset (Fin 20)) (Dᶜ \ FF)
    rw [hTcard, Finset.card_singleton] at hle
    omega
  obtain ⟨h₁, h1mem, h₂, h2mem, hne⟩ := Finset.one_lt_card.mp
    (by
      have hcard := Finset.card_le_card hbig
      omega : 1 < ((Dᶜ \ FF).filter (fun g => G.degree g = 4)).card)
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
