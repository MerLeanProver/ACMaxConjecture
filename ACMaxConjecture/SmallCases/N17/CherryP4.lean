import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.Dense
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.N17.Align8Helpers
import ACMaxConjecture.SmallCases.N17.CherryCore
import ACMaxConjecture.SmallCases.N17.CherryP4Count
import ACMaxConjecture.SmallCases.N17.CherryP4BothLeaf

/-!
# `n = 17`, `e(M) = 3` (`s = 6`), `P₄`-cherry corner for `|D| ∈ {9, 10, 11}`

The genuinely new `P₄` corner of the `e(M) = 3` dominating-edge branch
(`exists_align_six_config_seventeen`, `TwinCert17.lean`): the residual degree-`3` graph is the path
`L₁–c₁–c₂–L₂` whose dominating edge `c₁–c₂` has both endpoints of in-`M`-degree `2`, so neither the
fat-centre claw nor the double-star single-vertex selection applies.  This file supplies the three
`|D|`-cardinality sub-corners that the alignment dispatcher needs:

* `cherry_p4_config_D9_seventeen`   (`|D| = 9`,  `|Hub| = 8`, hub-internal sum `12`);
* `cherry_p4_two_hub_D10_seventeen` (`|D| = 10`, `|Hub| = 7`, hub-internal sum `6`);
* `cherry_p4_hub6_D11_seventeen`    (`|D| = 11`, `|Hub| = 6`, hub-internal sum `0`).

The shared degree-`4`-restricted `C₄` share bound `nonadj_deg4_hubs_share_le_one_p4_seventeen`
(two non-adjacent degree-`4` hubs sharing two `M`-isolated twins form an induced `C₄` with
`Σ deg = 14 ≤ 14`, excluded by `hC4`) underpins the two-hub assemblies.
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **Hub-internal-sum scaffolding (`n = 17`, `e(M) = 3` `P₄` corner).**  With `s = 6` and
`|D| = d`, the cross count and degree split give the additive identity
`∑_{w∈Dᶜ}|N w ∩ Dᶜ| + 6·d = 66` (i.e. the hub-internal sum is `66 − 6·d`).  This packages the
standard double counts shared by all three `|D|`-cases. -/
theorem cherry_p4_hub_internal_sum_seventeen (G : SimpleGraph (Fin 17))
    (hm : G.edgeFinset.card = 30) (_h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (D : Finset (Fin 17)) (hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6) :
    ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card + 6 * D.card = 66 := by
  classical
  have hdegD : ∀ v : Fin 17, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
  have hsum60 : ∑ v : Fin 17, G.degree v = 60 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDt : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => hdegD v hv), Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 60 := by
    rw [Finset.sum_add_sum_compl]; exact hsum60
  have hdegsplit : ∀ v : Fin 17,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
    intro v
    have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dᶜ) := by
      apply Finset.disjoint_left.mpr
      intro a ha ha'
      rw [Finset.mem_inter] at ha ha'
      exact (Finset.mem_compl.mp ha'.2) ha.2
    have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dᶜ) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
  have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
      = ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card := cross_count G D Dᶜ
  have hcongD : ∑ v ∈ D,
      ((G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card)
      = ∑ v ∈ D, G.degree v := Finset.sum_congr rfl (fun v _ => hdegsplit v)
  rw [Finset.sum_add_distrib, hs6, hsumDt] at hcongD
  have hcongDc : ∑ w ∈ Dᶜ,
      ((G.neighborFinset w ∩ D).card + (G.neighborFinset w ∩ Dᶜ).card)
      = ∑ w ∈ Dᶜ, G.degree w := Finset.sum_congr rfl (fun w _ => hdegsplit w)
  rw [Finset.sum_add_distrib, ← hcross] at hcongDc
  omega

/-- **`P₄` cherry corner, `|D| = 9` (`|Hub| = 8`).**  The residual degree-`3` graph is the path
`L₁–c₁–c₂–L₂` with `c₁, c₂` of in-`M`-degree `2`.  With `|D| = 9` the eight hubs are one degree-`5`
plus seven degree-`4` (degree-excess `1`), the hub-internal sum is `66 − 54 = 12`, and `|Iso| = 5`.
The cherry has hub-incidence `≤ 2 + 1 + 1 + 2 = 6`, so at least `8 − 6 = 2` hubs avoid all four
path vertices.  Either a cherry-avoiding degree-`4` hub carries two `M`-isolated twins
(`TwoTwinConfig`, via `shared_deg4_hub_from_count_seventeen` restricted to the avoider set), or the
avoider incidences saturate and two non-adjacent degree-`4` hubs sharing `≤ 1` twin assemble into
`TwoHubConfig`.  **RESISTANT CORE (one documented `sorry`):** unlike `n = 16` the avoider
`P/Q/R` budget only *ties* (`12 ≤ 12`), so the cherry-avoider extraction needs the tie-breaking
config analysis that is not a one-shot pigeonhole. -/
theorem cherry_p4_config_D9_seventeen (G : SimpleGraph (Fin 17))
    (hm : G.edgeFinset.card = 30) (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (L₁ c₁ c₂ L₂ : Fin 17) (D Iso : Finset (Fin 17))
    (hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6) (hD9 : D.card = 9) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  -- The `{c₁,c₂}`-avoider count gives a degree-`≤ 5` hub `h` avoiding both centres with two twins.
  obtain ⟨h, t₁, t₂, hhDc, hhdeg5, hhnc1, hhnc2, ht12, ht1Iso, ht2Iso, hAt1h, hAt2h⟩ :=
    p4_c1c2_avoider_two_twin_seventeen G hm h3 hT L₁ c₁ c₂ L₂ D Iso hmemD hIsoprop hisochar
      hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hin1 hin2 hs6
      (by omega) (by omega)
  by_cases hcase : ¬G.Adj h L₁ ∨ ¬G.Adj h L₂
  · -- The hub avoids a leaf: a sub-path cherry yields a `TwoTwinConfig`.
    have hhne_L1 : h ≠ L₁ := fun e => (Finset.mem_compl.mp hhDc) (e ▸ (hmemD L₁).mpr hL1deg)
    have hhne_c1 : h ≠ c₁ := fun e => (Finset.mem_compl.mp hhDc) (e ▸ (hmemD c₁).mpr hc1deg)
    have hhne_c2 : h ≠ c₂ := fun e => (Finset.mem_compl.mp hhDc) (e ▸ (hmemD c₂).mpr hc2deg)
    have hhne_L2 : h ≠ L₂ := fun e => (Finset.mem_compl.mp hhDc) (e ▸ (hmemD L₂).mpr hL2deg)
    exact Or.inr (Or.inl (safe_hub_two_twin_p4_seventeen G Iso L₁ c₁ c₂ L₂ h t₁ t₂ hIsoprop
      hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hhdeg5 hhnc1 hhnc2
      hhne_L1 hhne_c1 hhne_c2 hhne_L2 hcase ht1Iso ht2Iso ht12 hAt1h.symm hAt2h.symm))
  · -- Both-leaf hub: the genuine cluster (`C₄` tie-break / `TwoHub` assembly).
    push Not at hcase
    obtain ⟨hhL1, hhL2⟩ := hcase
    exact p4_both_leaf_hub_config_seventeen G hm h3 hT hC4 L₁ c₁ c₂ L₂ h t₁ t₂ D Iso hmemD
      hIsoprop hisochar hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1
      hNc1D hNc2D hin1 hin2 hs6 (by omega) (by omega) hhDc hhdeg5 hhnc1 hhnc2 hhL1 hhL2
      ht12 ht1Iso ht2Iso hAt1h hAt2h

/-- **`P₄` cherry corner, `|D| = 10` (`|Hub| = 7`).**  The path `L₁–c₁–c₂–L₂` residual with
`|D| = 10`: seven hubs, degree-excess `2`, hub-internal sum `66 − 60 = 6`, `|Iso| = 6`.  From
`∑_{w∈Dᶜ}|N w ∩ Dᶜ| = 6` extract `≥ 2` hubs with few `Dᶜ`-neighbours, hence many `Iso`-twins;
two non-adjacent degree-`4` such hubs share `≤ 1` twin (`nonadj_deg4_hubs_share_le_one_p4_seventeen`)
and assemble into `TwoHubConfig` via `dense_two_hub_assemble`.  **RESISTANT CORE (one documented
`sorry`):** isolating two *non-adjacent degree-`4`* hubs each with two *private* twins from the
internal-sum-`6` distribution is the tie-breaking step (the naive count only ties). -/
theorem cherry_p4_two_hub_D10_seventeen (G : SimpleGraph (Fin 17))
    (hm : G.edgeFinset.card = 30) (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (L₁ c₁ c₂ L₂ : Fin 17) (D Iso : Finset (Fin 17))
    (hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6) (hD10 : D.card = 10) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  -- The `{c₁,c₂}`-avoider count gives a degree-`≤ 5` hub `h` avoiding both centres with two twins.
  obtain ⟨h, t₁, t₂, hhDc, hhdeg5, hhnc1, hhnc2, ht12, ht1Iso, ht2Iso, hAt1h, hAt2h⟩ :=
    p4_c1c2_avoider_two_twin_seventeen G hm h3 hT L₁ c₁ c₂ L₂ D Iso hmemD hIsoprop hisochar
      hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D hin1 hin2 hs6
      (by omega) (by omega)
  by_cases hcase : ¬G.Adj h L₁ ∨ ¬G.Adj h L₂
  · -- The hub avoids a leaf: a sub-path cherry yields a `TwoTwinConfig`.
    have hhne_L1 : h ≠ L₁ := fun e => (Finset.mem_compl.mp hhDc) (e ▸ (hmemD L₁).mpr hL1deg)
    have hhne_c1 : h ≠ c₁ := fun e => (Finset.mem_compl.mp hhDc) (e ▸ (hmemD c₁).mpr hc1deg)
    have hhne_c2 : h ≠ c₂ := fun e => (Finset.mem_compl.mp hhDc) (e ▸ (hmemD c₂).mpr hc2deg)
    have hhne_L2 : h ≠ L₂ := fun e => (Finset.mem_compl.mp hhDc) (e ▸ (hmemD L₂).mpr hL2deg)
    exact Or.inr (Or.inl (safe_hub_two_twin_p4_seventeen G Iso L₁ c₁ c₂ L₂ h t₁ t₂ hIsoprop
      hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hhdeg5 hhnc1 hhnc2
      hhne_L1 hhne_c1 hhne_c2 hhne_L2 hcase ht1Iso ht2Iso ht12 hAt1h.symm hAt2h.symm))
  · -- Both-leaf hub: the genuine cluster (`C₄` tie-break / `TwoHub` assembly).
    push Not at hcase
    obtain ⟨hhL1, hhL2⟩ := hcase
    exact p4_both_leaf_hub_config_seventeen G hm h3 hT hC4 L₁ c₁ c₂ L₂ h t₁ t₂ D Iso hmemD
      hIsoprop hisochar hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1
      hNc1D hNc2D hin1 hin2 hs6 (by omega) (by omega) hhDc hhdeg5 hhnc1 hhnc2 hhL1 hhL2
      ht12 ht1Iso ht2Iso hAt1h hAt2h

set_option maxHeartbeats 400000 in
/-- **`P₄` cherry corner, `|D| = 11` (`|Hub| = 6`).**  The path `L₁–c₁–c₂–L₂` residual with
`|D| = 11`: six hubs, degree-excess `3`, hub-internal sum `66 − 66 = 0` (the hubs are independent —
every hub-neighbour lies in `D`), `|Iso| = 7`.  Because the hubs are independent, the `c₁`- and
`c₂`-hub-neighbours are unique and each leaf has `≤ 2` hub-neighbours, so at most four hubs are
adjacent to `c₁`, `c₂`, or both leaves; hence `≥ 2` "safe" hubs avoid `c₁`, `c₂` and at least one
leaf.  As the degree excess is `3`, at most one hub has degree `≥ 6`, so a safe hub `h` of degree
`≤ 5` exists.  Independence gives `|N h ∩ Iso| = deg h − |N h ∩ path| ≥ deg h − 1 ≥ 2`, so `h`
carries two `M`-isolated twins; being safe it avoids the sub-path cherry `L₁–c₁–c₂` (if `¬h∼L₁`) or
`c₁–c₂–L₂` (if `h∼L₁`, hence `¬h∼L₂`), assembling into `TwoTwinConfig`. -/
theorem cherry_p4_hub6_D11_seventeen (G : SimpleGraph (Fin 17))
    (hm : G.edgeFinset.card = 30) (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (_hT : ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (_hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (L₁ c₁ c₂ L₂ : Fin 17) (D Iso : Finset (Fin 17))
    (hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3)
    (hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3))
    (hisochar : ∀ w : Fin 17, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso)
    (hL1deg : G.degree L₁ = 3) (hc1deg : G.degree c₁ = 3)
    (hc2deg : G.degree c₂ = 3) (hL2deg : G.degree L₂ = 3)
    (hac1L1 : G.Adj c₁ L₁) (hc12 : G.Adj c₁ c₂) (hac2L2 : G.Adj c₂ L₂)
    (hL1nc2 : L₁ ≠ c₂) (hL2nc1 : L₂ ≠ c₁)
    (_hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁}) (_hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂})
    (hin1 : (G.neighborFinset c₁ ∩ D).card = 2) (hin2 : (G.neighborFinset c₂ ∩ D).card = 2)
    (hs6 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 6) (hD11 : D.card = 11) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  have hinternal : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card + 6 * D.card = 66 :=
    cherry_p4_hub_internal_sum_seventeen G hm h3 D hmemD hs6
  -- Hub-internal sum is `0`: the six hubs are independent.  A degree-`≤ 5` hub avoiding `c₁, c₂` and
  -- at least one leaf has `≥ 2` `M`-isolated twins and avoids a sub-path cherry, giving `TwoTwin`.
  have hDc6 : Dᶜ.card = 6 := by
    have h := Finset.card_add_card_compl D
    simp only [Fintype.card_fin] at h; omega
  have hintern0 : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ Dᶜ).card = 0 := by rw [hD11] at hinternal; omega
  have hindep : ∀ g : Fin 17, g ∈ Dᶜ → (G.neighborFinset g ∩ Dᶜ).card = 0 :=
    fun g hg => (Finset.sum_eq_zero_iff.mp hintern0) g hg
  have hpartw : ∀ w : Fin 17,
      (G.neighborFinset w ∩ D).card + (G.neighborFinset w ∩ Dᶜ).card = G.degree w := by
    intro w
    have hdisj : Disjoint (G.neighborFinset w ∩ D) (G.neighborFinset w ∩ Dᶜ) :=
      Finset.disjoint_left.mpr (fun a ha ha' =>
        (Finset.mem_compl.mp (Finset.mem_inter.mp ha').2) (Finset.mem_inter.mp ha).2)
    have hun : (G.neighborFinset w ∩ D) ∪ (G.neighborFinset w ∩ Dᶜ) = G.neighborFinset w := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
  have hDcdeg : ∀ w : Fin 17, w ∈ Dᶜ → 4 ≤ G.degree w := by
    intro w hw; rw [Finset.mem_compl, hmemD] at hw; have := h3 w; omega
  have hsumDdeg : ∑ v ∈ D, G.degree v = 33 := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul, hD11]
  have hsum60 : ∑ v : Fin 17, G.degree v = 60 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumDcdeg : ∑ w ∈ Dᶜ, G.degree w = 27 := by
    have hh : ∑ v ∈ D, G.degree v + ∑ w ∈ Dᶜ, G.degree w = 60 := by
      rw [Finset.sum_add_sum_compl]; exact hsum60
    omega
  -- At most one hub has degree `≥ 6` (excess is `27 − 24 = 3`).
  have hbigle : (Dᶜ.filter (fun w => 6 ≤ G.degree w)).card ≤ 1 := by
    set HB := Dᶜ.filter (fun w => 6 ≤ G.degree w) with hHB
    have hsub : HB ⊆ Dᶜ := Finset.filter_subset _ _
    have h1 : 6 * HB.card ≤ ∑ w ∈ HB, G.degree w := by
      have hb : ∀ w ∈ HB, 6 ≤ G.degree w := fun w hw => (Finset.mem_filter.mp hw).2
      have := Finset.card_nsmul_le_sum HB (fun w => G.degree w) 6 hb
      simpa [smul_eq_mul, mul_comm] using this
    have h2 : 4 * (Dᶜ \ HB).card ≤ ∑ w ∈ Dᶜ \ HB, G.degree w := by
      have hb : ∀ w ∈ Dᶜ \ HB, 4 ≤ G.degree w :=
        fun w hw => hDcdeg w (Finset.mem_sdiff.mp hw).1
      have := Finset.card_nsmul_le_sum (Dᶜ \ HB) (fun w => G.degree w) 4 hb
      simpa [smul_eq_mul, mul_comm] using this
    have hsplit : ∑ w ∈ Dᶜ \ HB, G.degree w + ∑ w ∈ HB, G.degree w = 27 := by
      rw [Finset.sum_sdiff hsub]; exact hsumDcdeg
    have hcard : (Dᶜ \ HB).card + HB.card = 6 := by
      rw [Finset.card_sdiff_add_card_eq_card hsub]; exact hDc6
    omega
  -- `c₁, c₂` each have exactly one hub-neighbour; each leaf has at most two.
  have hfc1le : (Dᶜ.filter (fun w => G.Adj w c₁)).card ≤ 1 := by
    have heq : Dᶜ.filter (fun w => G.Adj w c₁) = G.neighborFinset c₁ ∩ Dᶜ := by
      ext w; simp only [Finset.mem_filter, Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩
    rw [heq]; have := hpartw c₁; rw [hin1, hc1deg] at this; omega
  have hfc2le : (Dᶜ.filter (fun w => G.Adj w c₂)).card ≤ 1 := by
    have heq : Dᶜ.filter (fun w => G.Adj w c₂) = G.neighborFinset c₂ ∩ Dᶜ := by
      ext w; simp only [Finset.mem_filter, Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩
    rw [heq]; have := hpartw c₂; rw [hin2, hc2deg] at this; omega
  have hfL1le : (Dᶜ.filter (fun w => G.Adj w L₁)).card ≤ 2 := by
    have heq : Dᶜ.filter (fun w => G.Adj w L₁) = G.neighborFinset L₁ ∩ Dᶜ := by
      ext w; simp only [Finset.mem_filter, Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩
    rw [heq]
    have hge1 : 1 ≤ (G.neighborFinset L₁ ∩ D).card :=
      Finset.card_pos.mpr ⟨c₁, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset L₁ c₁).mpr hac1L1.symm,
        (hmemD c₁).mpr hc1deg⟩⟩
    have := hpartw L₁; rw [hL1deg] at this; omega
  -- The "bad" hubs (adjacent to `c₁` or `c₂` or both leaves) number at most `4`.
  set Bad : Finset (Fin 17) :=
    Dᶜ.filter (fun w => G.Adj w c₁ ∨ G.Adj w c₂ ∨ (G.Adj w L₁ ∧ G.Adj w L₂)) with hBaddef
  have hBadle : Bad.card ≤ 4 := by
    have hsub : Bad ⊆ Dᶜ.filter (fun w => G.Adj w c₁) ∪ Dᶜ.filter (fun w => G.Adj w c₂)
        ∪ Dᶜ.filter (fun w => G.Adj w L₁) := by
      intro w hw; rw [hBaddef, Finset.mem_filter] at hw
      obtain ⟨hwDc, hor⟩ := hw
      rcases hor with h | h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hwDc, h⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hwDc, h⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwDc, h.1⟩)
    have hu1 := Finset.card_union_le (Dᶜ.filter (fun w => G.Adj w c₁) ∪
      Dᶜ.filter (fun w => G.Adj w c₂)) (Dᶜ.filter (fun w => G.Adj w L₁))
    have hu2 := Finset.card_union_le (Dᶜ.filter (fun w => G.Adj w c₁))
      (Dᶜ.filter (fun w => G.Adj w c₂))
    have := Finset.card_le_card hsub
    omega
  -- Hence `≥ 2` "safe" hubs, and `≥ 1` of them has degree `≤ 5`.
  have hsafege : 2 ≤ (Dᶜ \ Bad).card := by
    have hsub : Bad ⊆ Dᶜ := by rw [hBaddef]; exact Finset.filter_subset _ _
    have := Finset.card_sdiff_add_card_eq_card hsub
    omega
  obtain ⟨h, hhmem⟩ : ∃ h, h ∈ (Dᶜ \ Bad) \ Dᶜ.filter (fun w => 6 ≤ G.degree w) := by
    apply Finset.card_pos.mp
    have hsub2 : Dᶜ.filter (fun w => 6 ≤ G.degree w) ⊆ Dᶜ := Finset.filter_subset _ _
    have := Finset.le_card_sdiff (Dᶜ.filter (fun w => 6 ≤ G.degree w)) (Dᶜ \ Bad)
    have hinter : (Dᶜ.filter (fun w => 6 ≤ G.degree w) ∩ (Dᶜ \ Bad)).card
        ≤ (Dᶜ.filter (fun w => 6 ≤ G.degree w)).card :=
      Finset.card_le_card Finset.inter_subset_left
    omega
  rw [Finset.mem_sdiff, Finset.mem_sdiff] at hhmem
  obtain ⟨⟨hhDc, hhnBad⟩, hhnBig⟩ := hhmem
  have hdeg_le5 : G.degree h ≤ 5 := by
    by_contra hc
    exact hhnBig (Finset.mem_filter.mpr ⟨hhDc, by omega⟩)
  have hdeg_ge4 : 4 ≤ G.degree h := hDcdeg h hhDc
  have hhnP : ¬(G.Adj h c₁ ∨ G.Adj h c₂ ∨ (G.Adj h L₁ ∧ G.Adj h L₂)) := by
    intro hor; exact hhnBad (by rw [hBaddef, Finset.mem_filter]; exact ⟨hhDc, hor⟩)
  have hh_nc1 : ¬G.Adj h c₁ := fun ha => hhnP (Or.inl ha)
  have hh_nc2 : ¬G.Adj h c₂ := fun ha => hhnP (Or.inr (Or.inl ha))
  have hh_notboth : ¬(G.Adj h L₁ ∧ G.Adj h L₂) := fun ha => hhnP (Or.inr (Or.inr ha))
  have hND : (G.neighborFinset h ∩ D).card = G.degree h := by
    have := hpartw h; rw [hindep h hhDc] at this; omega
  have hhne_path : ∀ p : Fin 17, p ∈ D → h ≠ p :=
    fun p hp e => (Finset.mem_compl.mp hhDc) (e ▸ hp)
  have hc1D : c₁ ∈ D := (hmemD c₁).mpr hc1deg
  have hc2D : c₂ ∈ D := (hmemD c₂).mpr hc2deg
  have hL1D : L₁ ∈ D := (hmemD L₁).mpr hL1deg
  have hL2D : L₂ ∈ D := (hmemD L₂).mpr hL2deg
  -- Cover `N h ∩ D` by `(N h ∩ Iso) ∪ (N h ∩ path)`.
  have hcover : G.neighborFinset h ∩ D ⊆ (G.neighborFinset h ∩ Iso) ∪
      (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 17))) := by
    intro w hw
    rw [Finset.mem_inter] at hw
    obtain ⟨hwh, hwD⟩ := hw
    by_cases hwp : w ∈ ({L₁, c₁, c₂, L₂} : Finset (Fin 17))
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hwh, hwp⟩)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwp
      exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hwh,
        hisochar w hwD hwp.1 hwp.2.1 hwp.2.2.1 hwp.2.2.2⟩)
  have hcardcover : (G.neighborFinset h ∩ D).card ≤ (G.neighborFinset h ∩ Iso).card
      + (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 17))).card :=
    le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
  -- The path-neighbours of `h` are at most one (`¬h∼c₁, c₂` and not both leaves).
  have hcase : ¬G.Adj h L₁ ∨ ¬G.Adj h L₂ := not_and_or.mp hh_notboth
  have hpath1 : (G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 17))).card ≤ 1 := by
    rcases hcase with hnL1 | hnL2
    · have hsub : G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 17)) ⊆ {L₂} := by
        intro w hw; rw [Finset.mem_inter, G.mem_neighborFinset] at hw
        obtain ⟨hwh, hwp⟩ := hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hwp ⊢
        rcases hwp with rfl | rfl | rfl | rfl
        · exact absurd hwh hnL1
        · exact absurd hwh hh_nc1
        · exact absurd hwh hh_nc2
        · rfl
      calc _ ≤ ({L₂} : Finset (Fin 17)).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton _
    · have hsub : G.neighborFinset h ∩ ({L₁, c₁, c₂, L₂} : Finset (Fin 17)) ⊆ {L₁} := by
        intro w hw; rw [Finset.mem_inter, G.mem_neighborFinset] at hw
        obtain ⟨hwh, hwp⟩ := hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hwp ⊢
        rcases hwp with rfl | rfl | rfl | rfl
        · rfl
        · exact absurd hwh hh_nc1
        · exact absurd hwh hh_nc2
        · exact absurd hwh hnL2
      calc _ ≤ ({L₁} : Finset (Fin 17)).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton _
  have hiso2 : 2 ≤ (G.neighborFinset h ∩ Iso).card := by omega
  obtain ⟨t₁, ht1, t₂, ht2, ht12⟩ := Finset.one_lt_card.mp hiso2
  exact Or.inr (Or.inl (safe_hub_two_twin_p4_seventeen G Iso L₁ c₁ c₂ L₂ h t₁ t₂ hIsoprop
    hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hdeg_le5 hh_nc1 hh_nc2
    (hhne_path L₁ hL1D) (hhne_path c₁ hc1D) (hhne_path c₂ hc2D) (hhne_path L₂ hL2D) hcase
    (Finset.mem_inter.mp ht1).2 (Finset.mem_inter.mp ht2).2 ht12
    ((G.mem_neighborFinset h t₁).mp (Finset.mem_inter.mp ht1).1).symm
    ((G.mem_neighborFinset h t₂).mp (Finset.mem_inter.mp ht2).1).symm))

end N17

end ACMax
