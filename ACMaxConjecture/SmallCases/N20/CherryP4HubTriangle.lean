import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.CherryCore
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleStruct
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleShare
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleWA
import ACMaxConjecture.SmallCases.N20.CherryP4HubTriangleForce

/-!
# `n = 19`, `e(M) = 3`, `P₄`-cherry, `|D| ∈ {9, 10, 11}` hub-triangle existence

This file isolates the hub-triangle existence obligation in the `|D| ∈ {9, 10, 11}`
(`|Hub| ∈ {9, 8, 7}`) both-leaf residual of the `e(M) = 3` `P₄` dispatch for `n = 19`, reached
after the `SingleVertex`/`TwoTwin`/`TwoHub` routes have all been excluded.  It is the `n = 19`
analog of `exists_hub_triangle_config_p4_D9D10_seventeen`.

## The `n = 19` obstruction (why this is a documented `sorry`)

Unlike `n = 17`, the extra hub in each `|D|`-class (`|Hub| = 18 − |D|` instead of `17 − |D|`)
raises the hub-internal total to `∑ int = 70 − 6|D|` (`16`/`10`/`4` for `|D| = 9`/`10`/`11`, versus
`12`/`6`/`0` for `n = 17`).  This dilutes every `n = 17` counting bound below its threshold:

* `|D| = 11` (`7` hubs, `∑ int = 4`, avoiders `≥ 3`): the avoider internal-degree budget gives
  `∑_{A₁∪A₂} f ≥ 2|A₁| + |A₂| ≥ 9 > 4` — a *clean counting contradiction* (the both-leaf config is
  impossible), modulo routing the lone possible degree-`≥ 6` hub.
* `|D| = 10` (`8` hubs, `∑ int = 10`, avoiders `≥ 4`): clean contradiction `≥ 12 > 10` when all
  hubs are degree `≤ 5`; the lone degree-`6` fully-free corner survives as in `n = 17`.
* `|D| = 9` (`9` hubs, `∑ int = 16`, avoiders `≥ 5`, all degree `≤ 5`): the budget forces
  `|A₁| = |A₂| = 5` and `|FF| ∈ {4, 5}`.  The `|FF| = 5` branch Mantel-`5`-forces a triangle, but
  the `|FF| = 4` branch admits a triangle-free bipartite escape (`C₄ + 2` apexes on opposite
  vertices, the `K_{3,3}`-minus-matching) whose induced `C₄` has `Σ deg ≥ 16 > 14`, so **`hC4`
  does not exclude it** — closing it needs the genuine direct-construction structural argument
  (the `n = 14/15` reliability lesson: only per-structure construction is trustworthy here).

## Decomposition (proposed helper nodes to discharge the `sorry`)

* `hub_triangle_force_p4_D11_twenty` — clean counting contradiction at `|D| = 11`
  (`Dᶜ.card = 7`, `∑ int = 4`); deps: the WA per-hub lemmas, `shared_hub_le5`-style routing of the
  single degree-`≥ 6` hub.  File: `TwinCert20CherryP4HubTriangleForce.lean`.
* `hub_triangle_force_p4_D10_twenty` — `|D| = 10` (`∑ int = 10`): clean contradiction off the
  fully-free degree-`6` corner, which collapses as in `n = 17 ten_avoider_clean_contra`.  Same file.
* `hub_triangle_force_p4_D9_twenty` — `|D| = 9` (`∑ int = 16`): the `|FF| = 5` Mantel-`5`
  branch (needs a `mantel_five_triangle` lemma) plus the `|FF| = 4` bipartite-escape branch (the
  genuinely hard, direct-construction corner).  Deps: `mantel_five_triangle`,
  `nonadj_deg4_hubs_share_le_one_iso_pointwise_twenty`.  File:
  `TwinCert20CherryP4HubTriangleForce.lean`.
-/

namespace ACMax

open scoped Classical

namespace N20

set_option linter.unusedVariables false in
/-- **Hub-triangle existence in the `n = 19`, `|D| ∈ {9, 10, 11}`, `e(M) = 3`, `P₄` both-leaf
residual corner.**  Under the residual path/`|D|` structure (`9 ≤ |D| ≤ 11`, the `P₄` cherry
`L₁–c₁–c₂–L₂`, the both-leaf degree-`≤ 5` hub `h` with two `M`-isolated twins), the cherry/`C₄`
certificates, and the falsity of `SingleVertexConfig`/`TwoTwinConfig`/`TwoHubConfig`, the graph
contains three pairwise-adjacent hubs avoiding a cherry, packaged as `HubTriangleConfig G`.

The previously open `|D| = 9`, `|FF| = 4` bipartite escape (the `n = 19` internal-total dilution
that defeats the `n = 17` Mantel/budget force, not excluded by `hC4` alone) is now closed in
`TwinCert20CherryP4HubTriangleForceD9FF4` by extracting a `TwoHubConfig` from two isolated
degree-`4` hubs, so this declaration is fully proved (axiom-clean). -/
theorem exists_hub_triangle_config_p4_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (L₁ c₁ c₂ L₂ h t₁ t₂ : Fin 20) (D Iso : Finset (Fin 20))
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 20, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6)
    (hd_lb : 9 ≤ D.card) (hd_ub : D.card ≤ 11)
    (hhDc : h ∈ Dᶜ) (hhdeg5 : G.degree h ≤ 5)
    (hhnc1 : ¬G.Adj h c₁) (hhnc2 : ¬G.Adj h c₂)
    (hhL1 : G.Adj h L₁) (hhL2 : G.Adj h L₂)
    (ht12 : t₁ ≠ t₂) (ht1Iso : t₁ ∈ Iso) (ht2Iso : t₂ ∈ Iso)
    (hAt1h : G.Adj h t₁) (hAt2h : G.Adj h t₂)
    (hsv : ¬SingleVertexConfig G) (htt : ¬TwoTwinConfig G) (hth : ¬TwoHubConfig G) :
    HubTriangleConfig G := by
  classical
  have hT10 : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10 := by
    rintro ⟨x, y, z, hxy, hyz, hxz, ha, hb, hc, hs⟩
    exact hT ⟨x, y, z, hxy, hyz, hxz, ha, hb, hc, by omega⟩
  -- Path vertices live in `D`; basic distinctness.
  have hL1D : L₁ ∈ D := (hmemD L₁).mpr hL1deg
  have hc1D : c₁ ∈ D := (hmemD c₁).mpr hc1deg
  have hc2D : c₂ ∈ D := (hmemD c₂).mpr hc2deg
  have hL2D : L₂ ∈ D := (hmemD L₂).mpr hL2deg
  have hL1c1 : L₁ ≠ c₁ := (G.ne_of_adj hac1L1).symm
  have hc1c2 : c₁ ≠ c₂ := G.ne_of_adj hc12
  have hc2L2 : c₂ ≠ L₂ := G.ne_of_adj hac2L2
  have hc1L2 : c₁ ≠ L₂ := Ne.symm hL2nc1
  -- Hubs are disjoint from the path vertices.
  have hubne : ∀ g : Fin 20, g ∈ Dᶜ → g ≠ L₁ ∧ g ≠ c₁ ∧ g ≠ c₂ ∧ g ≠ L₂ := by
    intro g hg
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
    · exact (Finset.mem_compl.mp hg) hL1D
    · exact (Finset.mem_compl.mp hg) hc1D
    · exact (Finset.mem_compl.mp hg) hc2D
    · exact (Finset.mem_compl.mp hg) hL2D
  -- Generalised structural counts.
  obtain ⟨hDccard, hIsocard, hc1hub, hc2hub, hL1hub, hL2hub, hsumPath, hsumIso, hsumInternal,
    hper⟩ := cherry_p4_hub_struct_twenty G hm L₁ c₁ c₂ L₂ D Iso hT10 hmemD hIsoprop hisochar
    hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hin1 hin2 hs6
  -- **Branch 1: an avoider triangle for cherry `{L₁, c₁, c₂}` with degree sum `≤ 13`.**
  by_cases htri1 : ∃ a b c : Fin 20, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13
  · obtain ⟨a, b, c, haDc, hbDc, hcDc, hab, hac, hbc,
      ⟨haL1, hac1, hac2⟩, ⟨hbL1, hbc1, hbc2⟩, ⟨hcL1, hcc1, hcc2⟩, hdsum⟩ := htri1
    obtain ⟨haneL1, hanec1, hanec2, _⟩ := hubne a haDc
    obtain ⟨hbneL1, hbnec1, hbnec2, _⟩ := hubne b hbDc
    obtain ⟨hcneL1, hcnec1, hcnec2, _⟩ := hubne c hcDc
    exact ⟨a, b, c, L₁, c₁, c₂, hL1deg, hc1deg, hc2deg, hab, hac, hbc,
      hac1L1.symm, hc12, haL1, hac1, hac2, hbL1, hbc1, hbc2, hcL1, hcc1, hcc2, hdsum,
      haneL1, hanec1, hanec2, hbneL1, hbnec1, hbnec2, hcneL1, hcnec1, hcnec2,
      hL1c1, hc1c2, hL1nc2⟩
  -- **Branch 2: an avoider triangle for cherry `{c₁, c₂, L₂}` with degree sum `≤ 13`.**
  by_cases htri2 : ∃ a b c : Fin 20, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13
  · obtain ⟨a, b, c, haDc, hbDc, hcDc, hab, hac, hbc,
      ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩, hdsum⟩ := htri2
    obtain ⟨_, hanec1, hanec2, haneL2⟩ := hubne a haDc
    obtain ⟨_, hbnec1, hbnec2, hbneL2⟩ := hubne b hbDc
    obtain ⟨_, hcnec1, hcnec2, hcneL2⟩ := hubne c hcDc
    exact ⟨a, b, c, c₁, c₂, L₂, hc1deg, hc2deg, hL2deg, hab, hac, hbc,
      hc12, hac2L2, hac1, hac2, haL2, hbc1, hbc2, hbL2, hcc1, hcc2, hcL2, hdsum,
      hanec1, hanec2, haneL2, hbnec1, hbnec2, hbneL2, hcnec1, hcnec2, hcneL2,
      hc1c2, hc2L2, hc1L2⟩
  -- **Branch 3: no small-degree avoider triangle ⇒ contradiction (the `|FF|`-dispatch core).**
  exfalso
  exact iso_rich_force_p4_twenty G D Iso L₁ c₁ c₂ L₂ h3 hmemD hIsoprop hisochar
    hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hL1D hc1D hc2D hL2D
    hd_lb hd_ub htt hth hsv hT hC4 hK23 hDccard hIsocard hc1hub hc2hub hL1hub hL2hub hsumPath
    hsumIso hsumInternal hper htri1 htri2

/-- **`P₄` cherry force to `HubTriangleConfig` (`|D| ∈ {9, 10}` reroute, no both-leaf hub).**
Under `¬SingleVertexConfig`, `¬TwoTwinConfig`, `¬TwoHubConfig`, either an avoider triangle for one
of the two `P₃` sub-cherries (`L₁–c₁–c₂` or `c₁–c₂–L₂`) yields a `HubTriangleConfig` directly, or
the `|FF|`-dispatch core `iso_rich_force_p4_twenty` derives a contradiction. -/
theorem cherry_p4_force_htc_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (L₁ c₁ c₂ L₂ : Fin 20) (D Iso : Finset (Fin 20))
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 20, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6)
    (hd_lb : 9 ≤ D.card) (hd_ub : D.card ≤ 11)
    (hsv : ¬SingleVertexConfig G) (htt : ¬TwoTwinConfig G) (hth : ¬TwoHubConfig G) :
    HubTriangleConfig G := by
  classical
  have hT10 : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10 := by
    rintro ⟨x, y, z, hxy, hyz, hxz, ha, hb, hc, hs⟩
    exact hT ⟨x, y, z, hxy, hyz, hxz, ha, hb, hc, by omega⟩
  have hL1D : L₁ ∈ D := (hmemD L₁).mpr hL1deg
  have hc1D : c₁ ∈ D := (hmemD c₁).mpr hc1deg
  have hc2D : c₂ ∈ D := (hmemD c₂).mpr hc2deg
  have hL2D : L₂ ∈ D := (hmemD L₂).mpr hL2deg
  have hL1c1 : L₁ ≠ c₁ := (G.ne_of_adj hac1L1).symm
  have hc1c2 : c₁ ≠ c₂ := G.ne_of_adj hc12
  have hc2L2 : c₂ ≠ L₂ := G.ne_of_adj hac2L2
  have hc1L2 : c₁ ≠ L₂ := Ne.symm hL2nc1
  have hubne : ∀ g : Fin 20, g ∈ Dᶜ → g ≠ L₁ ∧ g ≠ c₁ ∧ g ≠ c₂ ∧ g ≠ L₂ := by
    intro g hg
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
    · exact (Finset.mem_compl.mp hg) hL1D
    · exact (Finset.mem_compl.mp hg) hc1D
    · exact (Finset.mem_compl.mp hg) hc2D
    · exact (Finset.mem_compl.mp hg) hL2D
  obtain ⟨hDccard, hIsocard, hc1hub, hc2hub, hL1hub, hL2hub, hsumPath, hsumIso, hsumInternal,
    hper⟩ := cherry_p4_hub_struct_twenty G hm L₁ c₁ c₂ L₂ D Iso hT10 hmemD hIsoprop hisochar
    hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hin1 hin2 hs6
  by_cases htri1 : ∃ a b c : Fin 20, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a L₁ ∧ ¬G.Adj a c₁ ∧ ¬G.Adj a c₂) ∧
      (¬G.Adj b L₁ ∧ ¬G.Adj b c₁ ∧ ¬G.Adj b c₂) ∧
      (¬G.Adj c L₁ ∧ ¬G.Adj c c₁ ∧ ¬G.Adj c c₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13
  · obtain ⟨a, b, c, haDc, hbDc, hcDc, hab, hac, hbc,
      ⟨haL1, hac1, hac2⟩, ⟨hbL1, hbc1, hbc2⟩, ⟨hcL1, hcc1, hcc2⟩, hdsum⟩ := htri1
    obtain ⟨haneL1, hanec1, hanec2, _⟩ := hubne a haDc
    obtain ⟨hbneL1, hbnec1, hbnec2, _⟩ := hubne b hbDc
    obtain ⟨hcneL1, hcnec1, hcnec2, _⟩ := hubne c hcDc
    exact ⟨a, b, c, L₁, c₁, c₂, hL1deg, hc1deg, hc2deg, hab, hac, hbc,
      hac1L1.symm, hc12, haL1, hac1, hac2, hbL1, hbc1, hbc2, hcL1, hcc1, hcc2, hdsum,
      haneL1, hanec1, hanec2, hbneL1, hbnec1, hbnec2, hcneL1, hcnec1, hcnec2,
      hL1c1, hc1c2, hL1nc2⟩
  by_cases htri2 : ∃ a b c : Fin 20, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      (¬G.Adj a c₁ ∧ ¬G.Adj a c₂ ∧ ¬G.Adj a L₂) ∧
      (¬G.Adj b c₁ ∧ ¬G.Adj b c₂ ∧ ¬G.Adj b L₂) ∧
      (¬G.Adj c c₁ ∧ ¬G.Adj c c₂ ∧ ¬G.Adj c L₂) ∧
      G.degree a + G.degree b + G.degree c ≤ 13
  · obtain ⟨a, b, c, haDc, hbDc, hcDc, hab, hac, hbc,
      ⟨hac1, hac2, haL2⟩, ⟨hbc1, hbc2, hbL2⟩, ⟨hcc1, hcc2, hcL2⟩, hdsum⟩ := htri2
    obtain ⟨_, hanec1, hanec2, haneL2⟩ := hubne a haDc
    obtain ⟨_, hbnec1, hbnec2, hbneL2⟩ := hubne b hbDc
    obtain ⟨_, hcnec1, hcnec2, hcneL2⟩ := hubne c hcDc
    exact ⟨a, b, c, c₁, c₂, L₂, hc1deg, hc2deg, hL2deg, hab, hac, hbc,
      hc12, hac2L2, hac1, hac2, haL2, hbc1, hbc2, hbL2, hcc1, hcc2, hcL2, hdsum,
      hanec1, hanec2, haneL2, hbnec1, hbnec2, hbneL2, hcnec1, hcnec2, hcneL2,
      hc1c2, hc2L2, hc1L2⟩
  exfalso
  exact iso_rich_force_p4_twenty G D Iso L₁ c₁ c₂ L₂ h3 hmemD hIsoprop hisochar
    hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hL1D hc1D hc2D hL2D
    hd_lb hd_ub htt hth hsv hT hC4 hK23 hDccard hIsocard hc1hub hc2hub hL1hub hL2hub hsumPath
    hsumIso hsumInternal hper htri1 htri2

end N20

end ACMax
