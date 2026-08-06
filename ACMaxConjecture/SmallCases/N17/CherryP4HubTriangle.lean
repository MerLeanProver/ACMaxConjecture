import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.N17.CherryCore
import ACMaxConjecture.SmallCases.N17.CherryP4HubTriangleStruct
import ACMaxConjecture.SmallCases.N17.CherryP4HubTriangleForce

/-!
# `n = 17`, `e(M) = 3`, `P₄`-cherry, `|D| ∈ {9, 10}` hub-triangle existence

This file isolates the hub-triangle existence obligation in the `|D| ∈ {9, 10}` (`|Hub| ∈ {8, 7}`)
both-leaf residual of the `e(M) = 3` `P₄` dispatch for `n = 17`, reached after the
`SingleVertex`/`TwoTwin`/`TwoHub` routes have all been excluded.  It is the `|D| ∈ {9, 10}` analog
of the fully-closed `|D| = 8` development
`exists_hub_triangle_config_residual_seventeen`
(`TwinCert17HubTriangle{,Struct,FF}.lean`).

## The residual configuration

* `D` = the degree-`3` vertices, `|D| ∈ {9, 10}`; `Dᶜ` = the `8`/`7` hubs.
* `e(M) = 3`: the degree-`3` subgraph is the path `L₁–c₁–c₂–L₂`, plus `|Iso| = |D| − 4 ∈ {5, 6}`
  `M`-isolated degree-`3` twins (`Iso`).
* Hub-internal-edge total `∑ int = 2·e_H = 12` (`|D| = 9`) / `6` (`|D| = 10`).
* `(W)`, `(A)`, `¬TwoHubConfig` as in the `|D| = 8` corner.

## The target

`HubTriangleConfig G`: three pairwise-adjacent hubs all non-adjacent to one cherry; their degree
sum is `≤ 13` (the cut certificate `hub_triangle_cut_certificate` then closes the boundary
arithmetic).

## Status — CLOSED (axiom-clean)

Unlike the `|D| = 8` corner, the hubs here are **not** uniformly degree `4`: handshake forces one
degree-`5` hub for `|D| = 9` (`∑_{Dᶜ} deg = 33` over `8` hubs) and two degree-`5` (or one
degree-`6`) hubs for `|D| = 10` (`∑_{Dᶜ} deg = 30` over `7` hubs).  The no-avoider-triangle core is
discharged by `iso_rich_force_p4_seventeen` (`TwinCert17CherryP4HubTriangleForce`), which dispatches
on `|D|`:

* `|D| = 9` (`8` hubs, `∑ int = 12`): the avoider internal-degree budget (`avoider ≥ 2`,
  fully-free `≥ 3`, avoiders `≥ 4` per cherry) forces `A1 = A2 = FF` with `|FF| = 4` and
  `∑_FF int = 12`, so the in-`FF` edge mass is `≥ 12` — a Mantel-`4` triangle inside `A2`.  Its
  degree sum is `≤ 13` because at most one of the eight hubs is degree `5`, contradicting the
  no-triangle hypothesis.
* `|D| = 10` (`7` hubs, `∑ int = 6`): a pure counting contradiction.  When all hubs are degree
  `≤ 5` the budget collapses `A1 = A2 = FF` to size `3` with `∑_FF int ≥ 9 > 6`.  The lone
  degree-`6` hub is routed by its avoider membership; the fully-free corner collapses because the
  two degree-`4` fully-free hubs would each need internal degree `3` with no available neighbours.

The `(W)` fact (cherry-avoiding degree-`≤ 5` hub has `≤ 1` iso-twin, via `¬TwoTwinConfig`) is the
only configuration assumption used; the good-`C₄` share bound and `SingleVertex`/`TwoHub`
exclusions of the `|D| = 8` port are **not** needed.
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **Hub-triangle existence in the `n = 17`, `|D| ∈ {9, 10}`, `e(M) = 3`, `P₄` both-leaf residual
corner.**  Under the residual path/`|D|` structure (`9 ≤ |D| ≤ 10`, the `P₄` cherry
`L₁–c₁–c₂–L₂`, the both-leaf degree-`≤ 5` hub `h` with two `M`-isolated twins), the cherry/`C₄`
certificates, and the falsity of `SingleVertexConfig`/`TwoTwinConfig`/`TwoHubConfig`, the graph
contains three pairwise-adjacent hubs avoiding a cherry, packaged as `HubTriangleConfig G`.

See the file header for the degree-`5`/`6` obstruction that makes the `|D| = 8` port non-trivial;
the no-avoider-triangle core is discharged axiom-clean by `iso_rich_force_p4_seventeen`. -/
theorem exists_hub_triangle_config_p4_D9D10_seventeen (G : SimpleGraph (Fin 17))
    (hm : G.edgeFinset.card = 30) (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (_hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (L₁ c₁ c₂ L₂ h t₁ t₂ : Fin 17) (D Iso : Finset (Fin 17))
    (hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6)
    (hd_lb : 9 ≤ D.card) (hd_ub : D.card ≤ 10)
    (_hhDc : h ∈ Dᶜ) (_hhdeg5 : G.degree h ≤ 5)
    (hhnc1 : ¬G.Adj h c₁) (hhnc2 : ¬G.Adj h c₂)
    (hhL1 : G.Adj h L₁) (hhL2 : G.Adj h L₂)
    (_ht12 : t₁ ≠ t₂) (_ht1Iso : t₁ ∈ Iso) (_ht2Iso : t₂ ∈ Iso)
    (_hAt1h : G.Adj h t₁) (_hAt2h : G.Adj h t₂)
    (_hsv : ¬SingleVertexConfig G) (htt : ¬TwoTwinConfig G) (_hth : ¬TwoHubConfig G) :
    HubTriangleConfig G := by
  classical
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
  have hubne : ∀ g : Fin 17, g ∈ Dᶜ → g ≠ L₁ ∧ g ≠ c₁ ∧ g ≠ c₂ ∧ g ≠ L₂ := by
    intro g hg
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
    · exact (Finset.mem_compl.mp hg) hL1D
    · exact (Finset.mem_compl.mp hg) hc1D
    · exact (Finset.mem_compl.mp hg) hc2D
    · exact (Finset.mem_compl.mp hg) hL2D
  -- Generalised structural counts (hub count `17 − |D|`, twin count `|D| − 4`, hub-incidence
  -- totals `6`, `3·(|D| − 4)`, `66 − 6·|D|`, and the per-hub degree split).
  obtain ⟨hDccard, hIsocard, hc1hub, hc2hub, hL1hub, hL2hub, hsumPath, hsumIso, hsumInternal,
    hper⟩ := cherry_p4_hub_struct_seventeen G hm L₁ c₁ c₂ L₂ D Iso hT hmemD hIsoprop hisochar
    hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hin1 hin2 hs6
  -- **Branch 1: an avoider triangle for cherry `{L₁, c₁, c₂}` with degree sum `≤ 13`.**
  by_cases htri1 : ∃ a b c : Fin 17, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
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
  by_cases htri2 : ∃ a b c : Fin 17, a ∈ Dᶜ ∧ b ∈ Dᶜ ∧ c ∈ Dᶜ ∧
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
  -- **Branch 3: no small-degree avoider triangle ⇒ contradiction.**
  -- Both cherries lack a pairwise-adjacent avoider triple of degree sum `≤ 13`.  Combined with the
  -- structural counts (`hDccard`, `hsumPath`, `hsumIso`, `hsumInternal`, `hper`) and `¬TwoTwinConfig`
  -- (which yields the per-hub `(W)` fact), this is the `|D| ∈ {9, 10}` analog of the `|D| = 8`
  -- `|FF|`-dispatch, discharged by `iso_rich_force_p4_seventeen`.
  exfalso
  exact iso_rich_force_p4_seventeen G D Iso L₁ c₁ c₂ L₂ h3 hmemD hIsoprop hisochar
    hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hL1D hc1D hc2D hL2D
    hd_lb hd_ub htt hDccard hIsocard hc1hub hc2hub hL1hub hL2hub hsumPath hsumIso hsumInternal
    hper htri1 htri2

end N17

end ACMax
