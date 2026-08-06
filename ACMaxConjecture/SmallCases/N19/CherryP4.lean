import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.CherryCore
import ACMaxConjecture.SmallCases.N19.CherryP4Count
import ACMaxConjecture.SmallCases.N19.CherryP4BothLeaf

/-!
# `n = 19`, `e(M) = 3` (`s = 6`), `P₄`-cherry corners for `|D| ∈ {9, 10, 11}`

The genuinely-new `P₄` corner of the `e(M) = 3` dominating-edge branch
(`exists_align_six_config_nineteen`, `TwinCert19.lean`): the residual degree-`3` graph is the path
`L₁–c₁–c₂–L₂` whose dominating edge `c₁–c₂` has both endpoints of in-`M`-degree `2`, so neither the
fat-centre claw nor the double-star single-vertex selection applies.  This file supplies the three
`|D|`-cardinality sub-corners that the alignment dispatcher needs:

* `cherry_p4_config_D9_nineteen`  (`|D| = 9`,  `|Hub| = 9`);
* `cherry_p4_config_D10_nineteen` (`|D| = 10`, `|Hub| = 8`);
* `cherry_p4_config_D11_nineteen` (`|D| = 11`, `|Hub| = 7`).

All three share the same dichotomy: the `{c₁,c₂}`-avoider count
(`p4_c1c2_avoider_two_twin_nineteen`, which closes for all of `|D| ∈ {9,10,11}` because `n = 19`'s
extra hub keeps the strict pigeonhole margin) yields a degree-`≤ 5` hub `h` avoiding both centres
with two `M`-isolated twins.  If `h` avoids a leaf it assembles a `TwoTwinConfig`
(`safe_hub_two_twin_p4_nineteen`); otherwise the both-leaf residual routes to
`p4_both_leaf_hub_config_nineteen` (hub-triangle existence).
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **`P₄` cherry dichotomy core (`n = 19`, `|D| ∈ {9, 10, 11}`).**  The shared body of the three
`|D|`-corners: extract the `{c₁,c₂}`-avoider with two twins, then split on whether it avoids a
leaf (`TwoTwinConfig`) or hits both (`p4_both_leaf_hub_config_nineteen`). -/
theorem cherry_p4_dichotomy_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (L₁ c₁ c₂ L₂ : Fin 19) (D Iso : Finset (Fin 19))
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6)
    (hd_lb : 9 ≤ D.card) (hd_ub : D.card ≤ 11) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  rcases p4_c1c2_avoider_two_twin_nineteen G hm h3 hT hC4 L₁ c₁ c₂ L₂ D Iso hmemD hIsoprop
      hisochar hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D
      hin1 hin2 hs6 hd_lb hd_ub with
    ⟨h, t₁, t₂, hhDc, hhdeg5, hhnc1, hhnc2, ht12, ht1Iso, ht2Iso, hAt1h, hAt2h⟩ | hesc
  swap
  · exact hesc
  by_cases hcase : ¬G.Adj h L₁ ∨ ¬G.Adj h L₂
  · have hhne_L1 : h ≠ L₁ := fun e => (Finset.mem_compl.mp hhDc) (e ▸ (hmemD L₁).mpr hL1deg)
    have hhne_c1 : h ≠ c₁ := fun e => (Finset.mem_compl.mp hhDc) (e ▸ (hmemD c₁).mpr hc1deg)
    have hhne_c2 : h ≠ c₂ := fun e => (Finset.mem_compl.mp hhDc) (e ▸ (hmemD c₂).mpr hc2deg)
    have hhne_L2 : h ≠ L₂ := fun e => (Finset.mem_compl.mp hhDc) (e ▸ (hmemD L₂).mpr hL2deg)
    exact Or.inr (Or.inl (safe_hub_two_twin_p4_nineteen G Iso L₁ c₁ c₂ L₂ h t₁ t₂ hIsoprop
      hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hhdeg5 hhnc1 hhnc2
      hhne_L1 hhne_c1 hhne_c2 hhne_L2 hcase ht1Iso ht2Iso ht12 hAt1h.symm hAt2h.symm))
  · push Not at hcase
    obtain ⟨hhL1, hhL2⟩ := hcase
    exact p4_both_leaf_hub_config_nineteen G hm h3 hT hC4 L₁ c₁ c₂ L₂ h t₁ t₂ D Iso hmemD
      hIsoprop hisochar hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1
      hNc1D hNc2D hin1 hin2 hs6 hd_lb hd_ub hhDc hhdeg5 hhnc1 hhnc2 hhL1 hhL2
      ht12 ht1Iso ht2Iso hAt1h hAt2h

/-- **`P₄` cherry corner, `|D| = 9` (`|Hub| = 9`, `n = 19`).** -/
theorem cherry_p4_config_D9_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (L₁ c₁ c₂ L₂ : Fin 19) (D Iso : Finset (Fin 19))
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6) (hD9 : D.card = 9) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G :=
  cherry_p4_dichotomy_nineteen G hm h3 hT hC4 L₁ c₁ c₂ L₂ D Iso hmemD hIsoprop hisochar
    hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hin1 hin2 hs6
    (by omega) (by omega)

/-- **`P₄` cherry corner, `|D| = 10` (`|Hub| = 8`, `n = 19`).** -/
theorem cherry_p4_config_D10_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (L₁ c₁ c₂ L₂ : Fin 19) (D Iso : Finset (Fin 19))
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6) (hD10 : D.card = 10) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G :=
  cherry_p4_dichotomy_nineteen G hm h3 hT hC4 L₁ c₁ c₂ L₂ D Iso hmemD hIsoprop hisochar
    hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hin1 hin2 hs6
    (by omega) (by omega)

/-- **`P₄` cherry corner, `|D| = 11` (`|Hub| = 7`, `n = 19`).** -/
theorem cherry_p4_config_D11_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (L₁ c₁ c₂ L₂ : Fin 19) (D Iso : Finset (Fin 19))
    (hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 19, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6) (hD11 : D.card = 11) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G :=
  cherry_p4_dichotomy_nineteen G hm h3 hT hC4 L₁ c₁ c₂ L₂ D Iso hmemD hIsoprop hisochar
    hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hin1 hin2 hs6
    (by omega) (by omega)

end N19

end ACMax
