import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.N17.HubTriangleStruct
import ACMaxConjecture.SmallCases.N17.HubTriangleFF
import ACMaxConjecture.SmallCases.N17.CherryP4HubTriangleWA

/-!
# `|FF|`-style force for the `n = 17`, `P₄`-cherry `|D| ∈ {9, 10}` hub-triangle core

`iso_rich_force_p4_seventeen` is the `|D| ∈ {9, 10}` analog of `iso_rich_force_seventeen`: under the
residual structural counts and the falsity of `TwoTwinConfig`, the assumption that neither cherry
admits a pairwise-adjacent avoider triple of degree sum `≤ 13` (`hntri1`, `hntri2`) is
contradictory.

The two `|D|` values are dispatched separately.

* `|D| = 9` (`8` hubs, `∑ int = 12`, all hubs degree `≤ 5`): the avoider internal-degree budget
  forces `A1 = A2 = FF` with `|FF| = 4` and `∑_FF int = 12`, so the in-`FF` edge mass is `≥ 12`, a
  Mantel-`4` triangle inside `A2` of degree sum `≤ 13` — contradicting `hntri2`.
* `|D| = 10` (`7` hubs, `∑ int = 6`): a pure counting contradiction.  When every hub has degree
  `≤ 5`, the budget forces `A1 = A2 = FF` with `|FF| = 3` and `∑_FF int ≥ 9 > 6`.  The lone
  degree-`6` hub is routed by its membership among the avoiders; the only surviving corner
  (degree-`6` hub fully-free) collapses because the two degree-`4` fully-free hubs would need
  internal degree `3` with no available neighbours.
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **No degree-`≤ 13` avoider triangle ⇒ contradiction (`n = 17`, `P₄`, `|D| ∈ {9, 10}`).** -/
theorem iso_rich_force_p4_seventeen (G : SimpleGraph (Fin 17))
    (D Iso : Finset (Fin 17)) (L₁ c₁ c₂ L₂ : Fin 17)
    (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hL1D : L₁ ∈ D) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hL2D : L₂ ∈ D)
    (hd_lb : 9 ≤ D.card) (hd_ub : D.card ≤ 10) (htt : ¬TwoTwinConfig G)
    (hDccard : Dᶜ.card = 17 - D.card) (_hIsocard : Iso.card = D.card - 4)
    (hc1hub : (G.neighborFinset c₁ ∩ Dᶜ).card = 1)
    (hc2hub : (G.neighborFinset c₂ ∩ Dᶜ).card = 1)
    (hL1hub : (G.neighborFinset L₁ ∩ Dᶜ).card = 2)
    (hL2hub : (G.neighborFinset L₂ ∩ Dᶜ).card = 2)
    (hsumPath : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 17))).card = 6)
    (hsumIso : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Iso).card = 3 * (D.card - 4))
    (hsumInternal : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 66 - 6 * D.card)
    (hper : ∀ g : Fin 17, g ∈ Dᶜ →
      (G.neighborFinset g ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 17))).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card = G.degree g)
    (_hntri1 : ¬∃ a b c : Fin 17, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13)
    (hntri2 : ¬∃ a b c : Fin 17, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13) :
    False := by
  classical
  set P : Finset (Fin 17) := {L₁, c₁, c₂, L₂} with hPdef
  -- Every hub has degree `≥ 4`.
  have hge4 : ∀ g : Fin 17, g ∈ Dᶜ → 4 ≤ G.degree g := by
    intro g hg
    have hgD : g ∉ D := Finset.mem_compl.mp hg
    have : G.degree g ≠ 3 := fun he => hgD ((hmemD g).mpr he)
    have := h3 g
    omega
  -- Hub degree total `∑_{Dᶜ} deg = 60 − 3|D|`.
  have hsumdeg : ∑ g ∈ Dᶜ, G.degree g = 60 - 3 * D.card := by
    have hcong : ∑ g ∈ Dᶜ, ((G.neighborFinset g ∩ P).card
        + (G.neighborFinset g ∩ Iso).card + (G.neighborFinset g ∩ Dᶜ).card)
        = ∑ g ∈ Dᶜ, G.degree g := Finset.sum_congr rfl hper
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumPath, hsumIso, hsumInternal] at hcong
    omega
  -- The (W) fact for degree-`≤ 5` hubs.
  have hW := cherry_p4_W_facts_seventeen G D Iso L₁ c₁ c₂ L₂ hIsoprop hL1deg hc1deg hc2deg hL2deg
    hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hL1D hc1D hc2D hL2D htt
  -- Classification of `D`.
  have hclassP : ∀ x : Fin 17, x ∈ D → x = L₁ ∨ x = c₁ ∨ x = c₂ ∨ x = L₂ ∨ x ∈ Iso := by
    intro x hx
    by_cases h1 : x = L₁
    · exact Or.inl h1
    by_cases h2 : x = c₁
    · exact Or.inr (Or.inl h2)
    by_cases h3' : x = c₂
    · exact Or.inr (Or.inr (Or.inl h3'))
    by_cases h4 : x = L₂
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hisochar x hx h1 h2 h3' h4))))
  -- The two cherry-avoider sets and `FF`.
  set A1 := Dᶜ.filter (fun g => ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂) with hA1def
  set A2 := Dᶜ.filter (fun g => ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂) with hA2def
  set FF := A1 ∩ A2 with hFFdef
  have hA1sub : A1 ⊆ Dᶜ := by rw [hA1def]; exact Finset.filter_subset _ _
  have hA2sub : A2 ⊆ Dᶜ := by rw [hA2def]; exact Finset.filter_subset _ _
  have hFFsubA1 : FF ⊆ A1 := by rw [hFFdef]; exact Finset.inter_subset_left
  have hFFsubA2 : FF ⊆ A2 := by rw [hFFdef]; exact Finset.inter_subset_right
  have hFFsub : FF ⊆ Dᶜ := hFFsubA1.trans hA1sub
  -- Avoider counts.
  have hA1card_lb : Dᶜ.card - 4 ≤ A1.card := by
    have := avoiders_ge_gen G D L₁ c₁ c₂ (by rw [hL1hub, hc1hub, hc2hub])
    rwa [← hA1def] at this
  have hA2card_lb : Dᶜ.card - 4 ≤ A2.card := by
    have := avoiders_ge_gen G D c₁ c₂ L₂ (by rw [hc1hub, hc2hub, hL2hub])
    rwa [← hA2def] at this
  -- `hclass` packagers for the internal-degree lemmas.
  have hclassA1 : ∀ g : Fin 17, g ∈ A1 → ∀ x : Fin 17, G.Adj g x → x ∈ D → x = L₂ ∨ x ∈ Iso := by
    intro g hg x hadj hxD
    rw [hA1def, Finset.mem_filter] at hg
    obtain ⟨_, hgL1, hgc1, hgc2⟩ := hg
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact Or.inl h
    · exact Or.inr h
  have hclassA2 : ∀ g : Fin 17, g ∈ A2 → ∀ x : Fin 17, G.Adj g x → x ∈ D → x = L₁ ∨ x ∈ Iso := by
    intro g hg x hadj hxD
    rw [hA2def, Finset.mem_filter] at hg
    obtain ⟨_, hgc1, hgc2, hgL2⟩ := hg
    rcases hclassP x hxD with h | h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact Or.inr h
  have hclassFF : ∀ g : Fin 17, g ∈ FF → ∀ x : Fin 17, G.Adj g x → x ∈ D → x ∈ Iso := by
    intro g hg x hadj hxD
    have hgA1 := hFFsubA1 hg
    have hgA2 := hFFsubA2 hg
    rw [hA1def, Finset.mem_filter] at hgA1
    rw [hA2def, Finset.mem_filter] at hgA2
    obtain ⟨_, hgL1, hgc1, hgc2⟩ := hgA1
    obtain ⟨_, _, _, hgL2⟩ := hgA2
    rcases hclassP x hxD with h | h | h | h | h
    · exact absurd (h ▸ hadj) hgL1
    · exact absurd (h ▸ hadj) hgc1
    · exact absurd (h ▸ hadj) hgc2
    · exact absurd (h ▸ hadj) hgL2
    · exact h
  -- Membership extractors into the avoider predicates.
  have getA2pred : ∀ g : Fin 17, g ∈ A2 →
      ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ ∧ ¬G.Adj g L₂ := by
    intro g hg; rw [hA2def, Finset.mem_filter] at hg; exact hg.2
  have getA1pred : ∀ g : Fin 17, g ∈ A1 →
      ¬G.Adj g L₁ ∧ ¬G.Adj g c₁ ∧ ¬G.Adj g c₂ := by
    intro g hg; rw [hA1def, Finset.mem_filter] at hg; exact hg.2
  -- Dispatch on `|D|`.
  rcases (by omega : D.card = 9 ∨ D.card = 10) with hD9 | hD10
  · -- **`|D| = 9`.**
    have hDc8 : Dᶜ.card = 8 := by rw [hDccard, hD9]
    have hint12 : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 12 := by rw [hsumInternal, hD9]
    have hdeg33 : ∑ g ∈ Dᶜ, G.degree g = 33 := by rw [hsumdeg, hD9]
    have hdeg_le5 : ∀ g : Fin 17, g ∈ Dᶜ → G.degree g ≤ 5 := by
      intro g hg
      have := hub_deg_upper_pt Dᶜ (fun v => G.degree v) 33 hge4 hdeg33 g hg
      rw [hDc8] at this; omega
    -- Internal-degree bounds.
    have hA1int : ∀ g ∈ A1, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
      intro g hg
      exact avoider_internal_ge_two_pt G D Iso g L₂ (hge4 g (hA1sub hg))
        (hW g (hA1sub hg) (hdeg_le5 g (hA1sub hg)) (Or.inl (getA1pred g hg))) (hclassA1 g hg)
    have hA2int : ∀ g ∈ A2, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
      intro g hg
      exact avoider_internal_ge_two_pt G D Iso g L₁ (hge4 g (hA2sub hg))
        (hW g (hA2sub hg) (hdeg_le5 g (hA2sub hg)) (Or.inr (getA2pred g hg))) (hclassA2 g hg)
    have hFFint : ∀ g ∈ FF, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
      intro g hg
      exact fully_free_internal_ge_three_pt G D Iso g (hge4 g (hFFsub hg))
        (hW g (hFFsub hg) (hdeg_le5 g (hFFsub hg))
          (Or.inl (getA1pred g (hFFsubA1 hg)))) (hclassFF g hg)
    -- Budget: `A1 = A2 = FF`, `|FF| = 4`, `∑_FF int = 12`.
    obtain ⟨hA1c4, hA2c4, hFFc4, hFFint12⟩ := budget_force_nine Dᶜ A1 A2 FF
      (fun g => (G.neighborFinset g ∩ Dᶜ).card) hA1sub hA2sub hFFdef
      hA1card_lb hA2card_lb hA1int hA2int hFFint hint12 hDc8
    -- `FF = A2`.
    have hFFeqA2 : FF = A2 := Finset.eq_of_subset_of_card_le hFFsubA2 (by rw [hFFc4, hA2c4])
    -- Mantel-`4` triangle inside `FF`.
    have hedge : 10 ≤ ∑ g ∈ FF, (G.neighborFinset g ∩ FF).card := by
      have hlb := ff_internal_edge_lb_gen G Dᶜ FF 12 hFFsub hint12
      omega
    obtain ⟨a, b, c, haFF, hbFF, hcFF, hab, hac, hbc⟩ := mantel_four_triangle G FF hFFc4 hedge
    have haA2 := hFFeqA2 ▸ haFF
    have hbA2 := hFFeqA2 ▸ hbFF
    have hcA2 := hFFeqA2 ▸ hcFF
    obtain ⟨hac1, hac2, haL2⟩ := getA2pred a haA2
    obtain ⟨hbc1, hbc2, hbL2⟩ := getA2pred b hbA2
    obtain ⟨hcc1, hcc2, hcL2⟩ := getA2pred c hcA2
    have hdsum := hub_deg3_upper Dᶜ (fun v => G.degree v) 33 hge4 hdeg33 a b c
      (hFFsub haFF) (hFFsub hbFF) (hFFsub hcFF)
      (G.ne_of_adj hab) (G.ne_of_adj hac) (G.ne_of_adj hbc)
    rw [hDc8] at hdsum
    exact hntri2 ⟨a, b, c, hFFsub haFF, hFFsub hbFF, hFFsub hcFF, hab, hac, hbc,
      ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩, by omega⟩
  · -- **`|D| = 10`.**
    have hDc7 : Dᶜ.card = 7 := by rw [hDccard, hD10]
    have hint6 : ∑ g ∈ Dᶜ, (G.neighborFinset g ∩ Dᶜ).card = 6 := by rw [hsumInternal, hD10]
    have hdeg30 : ∑ g ∈ Dᶜ, G.degree g = 30 := by rw [hsumdeg, hD10]
    have hA1card3 : 3 ≤ A1.card := by rw [hDc7] at hA1card_lb; omega
    have hA2card3 : 3 ≤ A2.card := by rw [hDc7] at hA2card_lb; omega
    have hdeg_le6 : ∀ g : Fin 17, g ∈ Dᶜ → G.degree g ≤ 6 := by
      intro g hg
      have := hub_deg_upper_pt Dᶜ (fun v => G.degree v) 30 hge4 hdeg30 g hg
      rw [hDc7] at this; omega
    by_cases hex6 : ∃ h6 : Fin 17, h6 ∈ Dᶜ ∧ 6 ≤ G.degree h6
    · -- A lone degree-`6` hub `h6`; all other hubs are degree `4`.
      obtain ⟨h6, hh6Dc, hh6deg6⟩ := hex6
      have hh6eq6 : G.degree h6 = 6 := le_antisymm (hdeg_le6 h6 hh6Dc) hh6deg6
      have hother4 : ∀ g : Fin 17, g ∈ Dᶜ → g ≠ h6 → G.degree g = 4 := by
        intro g hg hgne
        have herase : ∑ x ∈ Dᶜ.erase h6, G.degree x = 24 := by
          have h := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hh6Dc
          simp only [hh6eq6] at h
          rw [hdeg30] at h; omega
        have hcard6 : (Dᶜ.erase h6).card = 6 := by rw [Finset.card_erase_of_mem hh6Dc, hDc7]
        have hub := hub_deg_upper_pt (Dᶜ.erase h6) (fun v => G.degree v) 24
          (fun x hx => hge4 x (Finset.mem_of_mem_erase hx)) herase g
          (Finset.mem_erase.mpr ⟨hgne, hg⟩)
        rw [hcard6] at hub
        have := hge4 g hg
        omega
      -- Internal-degree bounds for the degree-`4` (i.e. non-`h6`) avoiders.
      have hA1int' : ∀ g : Fin 17, g ∈ A1 → g ≠ h6 → 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg hgne
        exact avoider_internal_ge_two_pt G D Iso g L₂ (hge4 g (hA1sub hg))
          (hW g (hA1sub hg) (by have := hother4 g (hA1sub hg) hgne; omega)
            (Or.inl (getA1pred g hg))) (hclassA1 g hg)
      have hA2int' : ∀ g : Fin 17, g ∈ A2 → g ≠ h6 → 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg hgne
        exact avoider_internal_ge_two_pt G D Iso g L₁ (hge4 g (hA2sub hg))
          (hW g (hA2sub hg) (by have := hother4 g (hA2sub hg) hgne; omega)
            (Or.inr (getA2pred g hg))) (hclassA2 g hg)
      have hFFint' : ∀ g : Fin 17, g ∈ FF → g ≠ h6 → 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg hgne
        exact fully_free_internal_ge_three_pt G D Iso g (hge4 g (hFFsub hg))
          (hW g (hFFsub hg) (by have := hother4 g (hFFsub hg) hgne; omega)
            (Or.inl (getA1pred g (hFFsubA1 hg)))) (hclassFF g hg)
      by_cases hh6A1 : h6 ∈ A1
      · by_cases hh6A2 : h6 ∈ A2
        · -- `h6 ∈ FF`: the resistant fully-free corner.
          have hh6FF : h6 ∈ FF := by rw [hFFdef]; exact Finset.mem_inter.mpr ⟨hh6A1, hh6A2⟩
          set f : Fin 17 → ℕ := fun g => (G.neighborFinset g ∩ Dᶜ).card with hfdef
          set U : Finset (Fin 17) := A1 ∪ A2 with hUdef
          have hUsub : U ⊆ Dᶜ := Finset.union_subset hA1sub hA2sub
          have hFFsubU : FF ⊆ U := hFFsubA1.trans Finset.subset_union_left
          have hh6U : h6 ∈ U := hFFsubU hh6FF
          -- Pointwise lower bounds (every avoider `≠ h6` has internal degree `≥ 2`/`≥ 3`).
          have hUFFlb : ∀ g ∈ U \ FF, 2 ≤ f g := by
            intro g hg
            rw [Finset.mem_sdiff] at hg
            obtain ⟨hgU, hgFF⟩ := hg
            have hgne : g ≠ h6 := fun e => hgFF (e ▸ hh6FF)
            rcases Finset.mem_union.mp hgU with hg1 | hg2
            · exact hA1int' g hg1 hgne
            · exact hA2int' g hg2 hgne
          have hFFelb : ∀ g ∈ FF.erase h6, 3 ≤ f g := by
            intro g hg
            exact hFFint' g (Finset.mem_of_mem_erase hg) (Finset.ne_of_mem_erase hg)
          -- Sum decompositions.
          have hUsplit : (∑ g ∈ U \ FF, f g) + ∑ g ∈ FF, f g = ∑ g ∈ U, f g :=
            Finset.sum_sdiff hFFsubU
          have hFFsplit : f h6 + ∑ g ∈ FF.erase h6, f g = ∑ g ∈ FF, f g :=
            Finset.add_sum_erase FF f hh6FF
          have hUFF_ge : 2 * (U \ FF).card ≤ ∑ g ∈ U \ FF, f g := by
            have := Finset.card_nsmul_le_sum (U \ FF) f 2 hUFFlb
            simpa [smul_eq_mul, Nat.mul_comm] using this
          have hFFe_ge : 3 * (FF.erase h6).card ≤ ∑ g ∈ FF.erase h6, f g := by
            have := Finset.card_nsmul_le_sum (FF.erase h6) f 3 hFFelb
            simpa [smul_eq_mul, Nat.mul_comm] using this
          have hUle : ∑ g ∈ U, f g ≤ 6 := by
            rw [← hint6]
            exact Finset.sum_le_sum_of_subset_of_nonneg hUsub (fun _ _ _ => Nat.zero_le _)
          have hFFle : ∑ g ∈ FF, f g ≤ 6 := by
            rw [← hint6]
            exact Finset.sum_le_sum_of_subset_of_nonneg hFFsub (fun _ _ _ => Nat.zero_le _)
          -- Card relations.
          have hFFe_card : (FF.erase h6).card + 1 = FF.card := Finset.card_erase_add_one hh6FF
          have hUFF_card : (U \ FF).card + FF.card = U.card := by
            have := Finset.card_sdiff_add_card_inter U FF
            rwa [Finset.inter_eq_right.mpr hFFsubU] at this
          have hUcard_eq : U.card + FF.card = A1.card + A2.card := by
            rw [hUdef, hFFdef]; exact Finset.card_union_add_card_inter A1 A2
          have hFFleA1 : FF.card ≤ A1.card := Finset.card_le_card hFFsubA1
          have hFFleA2 : FF.card ≤ A2.card := Finset.card_le_card hFFsubA2
          have hFFpos : 1 ≤ FF.card := Finset.card_pos.mpr ⟨h6, hh6FF⟩
          -- Solve the budget: `|FF| = 3`, `f h6 = 0`, `∑_FF f = 6`.
          have hFFc3 : FF.card = 3 := by omega
          have hfh6 : f h6 = 0 := by omega
          have hFFsum6 : ∑ g ∈ FF, f g = 6 := by omega
          -- The two degree-`4` fully-free hubs `p, q` (`FF = {h6, p, q}`).
          have hFFe2 : (FF.erase h6).card = 2 := by omega
          obtain ⟨pp, qq, hpqne, hFFeeq⟩ := Finset.card_eq_two.mp hFFe2
          have hppFFe : pp ∈ FF.erase h6 := by rw [hFFeeq]; exact Finset.mem_insert_self _ _
          have hqqFFe : qq ∈ FF.erase h6 := by rw [hFFeeq]; simp
          have hppFF : pp ∈ FF := Finset.mem_of_mem_erase hppFFe
          have hppne : pp ≠ h6 := Finset.ne_of_mem_erase hppFFe
          have hqqne : qq ≠ h6 := Finset.ne_of_mem_erase hqqFFe
          -- `f p = 3` (internal degree of `p`).
          have hFFpair : f pp + f qq = ∑ g ∈ FF.erase h6, f g := by
            rw [hFFeeq, Finset.sum_insert (by simp [hpqne]), Finset.sum_singleton]
          have hfp3 : f pp = 3 := by
            have hp : 3 ≤ f pp := hFFint' pp hppFF hppne
            have hq : 3 ≤ f qq := hFFint' qq (Finset.mem_of_mem_erase hqqFFe) hqqne
            omega
          -- Outside `FF`, every hub is internally isolated.
          have hzeropart : (∑ g ∈ Dᶜ \ FF, f g) + ∑ g ∈ FF, f g = 6 := by
            rw [Finset.sum_sdiff hFFsub, hint6]
          have hzerosum : ∑ g ∈ Dᶜ \ FF, f g = 0 := by omega
          have hzero : ∀ g : Fin 17, g ∈ Dᶜ → g ∉ FF → G.neighborFinset g ∩ Dᶜ = ∅ := by
            intro g hgDc hgFF
            have : f g = 0 :=
              (Finset.sum_eq_zero_iff.mp hzerosum) g (Finset.mem_sdiff.mpr ⟨hgDc, hgFF⟩)
            exact Finset.card_eq_zero.mp this
          -- `p`'s internal neighbours all collapse to `q`, so `f p ≤ 1`, contradicting `f p = 3`.
          have hppDc : pp ∈ Dᶜ := hFFsub hppFF
          have hh6empty : G.neighborFinset h6 ∩ Dᶜ = ∅ := Finset.card_eq_zero.mp hfh6
          have hnsub : G.neighborFinset pp ∩ Dᶜ ⊆ {qq} := by
            intro h' hh'
            rw [Finset.mem_inter, G.mem_neighborFinset] at hh'
            obtain ⟨hadj, hh'Dc⟩ := hh'
            have hppmem : pp ∈ G.neighborFinset h' ∩ Dᶜ :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj.symm, hppDc⟩
            have hh'FF : h' ∈ FF := by
              by_contra hh'nFF
              rw [hzero h' hh'Dc hh'nFF] at hppmem
              exact (Finset.notMem_empty _) hppmem
            have hh'ne_pp : h' ≠ pp := fun e => (G.irrefl (e ▸ hadj))
            have hh'ne_h6 : h' ≠ h6 := by
              rintro rfl
              rw [hh6empty] at hppmem
              exact (Finset.notMem_empty _) hppmem
            have hh'mem : h' ∈ FF.erase h6 := Finset.mem_erase.mpr ⟨hh'ne_h6, hh'FF⟩
            rw [hFFeeq] at hh'mem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hh'mem
            rcases hh'mem with rfl | rfl
            · exact absurd rfl hh'ne_pp
            · exact Finset.mem_singleton_self _
          have : f pp ≤ 1 := by
            calc f pp = (G.neighborFinset pp ∩ Dᶜ).card := rfl
              _ ≤ ({qq} : Finset (Fin 17)).card := Finset.card_le_card hnsub
              _ = 1 := Finset.card_singleton _
          omega
        · -- `h6 ∉ A2`: clean counting with `A = A2`.
          exact ten_avoider_clean_contra Dᶜ A2 A1 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) h6
            hA2sub hA1sub (by rw [hFFdef, Finset.inter_comm])
            (fun g hg => hA2int' g hg (fun e => hh6A2 (e ▸ hg)))
            (fun g hg => hFFint' g hg (fun e => hh6A2 (e ▸ hFFsubA2 hg)))
            (fun g hg hgne => hA1int' g hg hgne) hh6A2 hA2card3 hA1card3 hint6
      · -- `h6 ∉ A1`: clean counting with `A = A1`.
        exact ten_avoider_clean_contra Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card) h6
          hA1sub hA2sub hFFdef
          (fun g hg => hA1int' g hg (fun e => hh6A1 (e ▸ hg)))
          (fun g hg => hFFint' g hg (fun e => hh6A1 (e ▸ hFFsubA1 hg)))
          (fun g hg hgne => hA2int' g hg hgne) hh6A1 hA1card3 hA2card3 hint6
    · -- No degree-`6` hub: every hub has degree `≤ 5`, so `(W)` applies everywhere.
      push Not at hex6
      have hdeg_le5 : ∀ g : Fin 17, g ∈ Dᶜ → G.degree g ≤ 5 :=
        fun g hg => by have := hex6 g hg; omega
      have hA1int : ∀ g ∈ A1, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg
        exact avoider_internal_ge_two_pt G D Iso g L₂ (hge4 g (hA1sub hg))
          (hW g (hA1sub hg) (hdeg_le5 g (hA1sub hg)) (Or.inl (getA1pred g hg))) (hclassA1 g hg)
      have hA2int : ∀ g ∈ A2, 2 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg
        exact avoider_internal_ge_two_pt G D Iso g L₁ (hge4 g (hA2sub hg))
          (hW g (hA2sub hg) (hdeg_le5 g (hA2sub hg)) (Or.inr (getA2pred g hg))) (hclassA2 g hg)
      have hFFint : ∀ g ∈ FF, 3 ≤ (G.neighborFinset g ∩ Dᶜ).card := by
        intro g hg
        exact fully_free_internal_ge_three_pt G D Iso g (hge4 g (hFFsub hg))
          (hW g (hFFsub hg) (hdeg_le5 g (hFFsub hg))
            (Or.inl (getA1pred g (hFFsubA1 hg)))) (hclassFF g hg)
      exact budget_contra_ten Dᶜ A1 A2 FF (fun g => (G.neighborFinset g ∩ Dᶜ).card)
        hA1sub hA2sub hFFdef hA1card3 hA2card3 hA1int hA2int hFFint hint6

end N17

end ACMax
