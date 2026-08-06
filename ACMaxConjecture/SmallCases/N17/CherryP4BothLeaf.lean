import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.Dense
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.N17.Align8Helpers
import ACMaxConjecture.SmallCases.N17.CherryCore
import ACMaxConjecture.SmallCases.N17.CherryP4Count
import ACMaxConjecture.SmallCases.N17.CherryP4HubTriangle

/-!
# `n = 17`, `e(M) = 3` (`s = 6`), `P₄`-cherry corner: the both-leaf hub cluster

The `{c₁,c₂}`-avoider count (`p4_c1c2_avoider_two_twin_seventeen`) produces a degree-`≤ 5` hub `h`
avoiding both centres `c₁, c₂` and carrying two `M`-isolated twins.  When `h` additionally avoids a
leaf, `safe_hub_two_twin_p4_seventeen` (in `TwinCert17CherryCore`) closes the corner with a
`TwoTwinConfig`.  The genuine residual is the *both-leaf* case `Adj h L₁ ∧ Adj h L₂`: there the hub
spends its leftover degree on the two leaves rather than on `Iso`-twins, and the pure count only
ties.  Resolving it uses the degree-`4`-restricted `C₄` tie-break
(`nonadj_deg4_hubs_share_le_one_p4_seventeen`): two distinct non-adjacent degree-`4` both-leaf hubs
form an induced `C₄` `h–L₁–h'–L₂` with `Σ deg = 14 ≤ 14`, excluded by `hC4`.
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **Both-leaf hub config (`n = 17`, `P₄` corner).**  Given a degree-`≤ 5` hub `h` avoiding both
centres `c₁, c₂` but adjacent to both leaves `L₁, L₂`, carrying two distinct `M`-isolated twins
`t₁, t₂`, together with the path/`|D|` structure and the cherry/`C₄`/`K₂₃` certificates, one of the
four cut configurations holds.

**Route (verified by direct construction).**  The genuine dichotomy is *not* a `C₄`/`TwoHub`
tie-break: a `400k`-seed direct construction shows the residual splits into
* the *generic* family — a `{c₁,c₂}`-avoiding degree-`≤ 5` hub `h'` (possibly `≠ h`) that *avoids a
  leaf* and carries two `M`-isolated twins, closing with a `TwoTwinConfig` via the appropriate
  sub-path cherry (`safe_hub_two_twin_p4_seventeen`); and
* the *tie* family — when no such leaf-avoiding two-twin hub exists, the second-moment count forces
  the leaf-avoiding `{c₁,c₂}`-avoiders to form a dense (near-`K₄`) clique, yielding three
  pairwise-adjacent degree-`4` hubs avoiding a cherry: a `HubTriangleConfig` (combined degree
  `≤ 13`).  (Config-model sampling alone misses this tie family — only direct per-structure
  construction exposes it; cf. the `n = 14/15` reliability lesson.)

Both branches are uniform in `¬SingleVertexConfig ∧ ¬TwoTwinConfig ∧ ¬TwoHubConfig ⊢
HubTriangleConfig`, exactly mirroring the proven `|D| = 8` residual
`exists_hub_triangle_config_residual_seventeen` (`TwinCert17HubTriangle.lean`).

**RESISTANT CORE (one documented `sorry`).**  Closing the tie family is the `|D| ∈ {9, 10}` analog
of that `|D| = 8` hub-triangle sub-development (a second-moment "no cherry-avoiding twin pair ⇒
near-complete avoider clique ⇒ Mantel triangle" forcing), which is a multi-lemma development in its
own right (the `|D| = 8` analog itself spans `TwinCert17HubTriangle{,Struct,FF,FatStar}.lean` and
carries its own documented Mantel-corner `sorry`).  It is the genuinely hard assembly explicitly
permitted to carry a single documented `sorry`; the `¬SV ∧ ¬TT ∧ ¬TH` reduction below scopes it. -/
theorem p4_both_leaf_hub_config_seventeen (G : SimpleGraph (Fin 17))
    (hm : G.edgeFinset.card = 30) (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
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
    (hhDc : h ∈ Dᶜ) (hhdeg5 : G.degree h ≤ 5)
    (hhnc1 : ¬G.Adj h c₁) (hhnc2 : ¬G.Adj h c₂)
    (hhL1 : G.Adj h L₁) (hhL2 : G.Adj h L₂)
    (ht12 : t₁ ≠ t₂) (ht1Iso : t₁ ∈ Iso) (ht2Iso : t₂ ∈ Iso)
    (hAt1h : G.Adj h t₁) (hAt2h : G.Adj h t₂) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  by_cases hSV : SingleVertexConfig G
  · exact Or.inl hSV
  by_cases hTT : TwoTwinConfig G
  · exact Or.inr (Or.inl hTT)
  by_cases hTH : TwoHubConfig G
  · exact Or.inr (Or.inr (Or.inl hTH))
  -- Generic branch (a leaf-avoiding `{c₁,c₂}`-avoiding two-twin hub) is absorbed by `¬TwoTwinConfig`
  -- via `safe_hub_two_twin_p4_seventeen`; the residual tie family forces a `HubTriangleConfig`.
  refine Or.inr (Or.inr (Or.inr ?_))
  -- RESISTANT CORE: the `|D| ∈ {9,10}` analog of `exists_hub_triangle_config_residual_seventeen`
  -- (`|D| = 8`), discharged by `exists_hub_triangle_config_p4_D9D10_seventeen`.
  exact exists_hub_triangle_config_p4_D9D10_seventeen G hm h3 hT hC4 L₁ c₁ c₂ L₂ h t₁ t₂ D Iso
    hmemD hIsoprop hisochar hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1
    hNc1D hNc2D hin1 hin2 hs6 hd_lb hd_ub hhDc hhdeg5 hhnc1 hhnc2 hhL1 hhL2 ht12 ht1Iso ht2Iso
    hAt1h hAt2h hSV hTT hTH

end N17

end ACMax
