import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.Dense
import ACMaxConjecture.SmallCases.N17.Align8Helpers
import ACMaxConjecture.SmallCases.N17.HubTriangle
import ACMaxConjecture.SmallCases.N17.HubTriangleCherry
import ACMaxConjecture.SmallCases.N17.TwoHubHub6
import ACMaxConjecture.SmallCases.N17.Align8Mid
import ACMaxConjecture.SmallCases.N17.FatStarStruct

/-!
# Dense `e(M) ≥ 4` alignment dichotomy for `n = 17` (`halign8` helpers)

This file ports the proved-axiom-clean `n = 16` `halign8_sixteen` dispatch (`TwinCert16.lean`) to
`Fin 17`, split by the value of `e(M)` because — unlike `n = 16`, where `halign8` could call
`shared_deg4_hub_deg5_sixteen` up to `s ≤ 8` — the `n = 17` shared-`deg-4`-hub pigeonhole only
*ties* at `e(M) = 4` (the degree sum `60` is divisible by `3`; the `n = 16` slack came from `56`
being non-divisible by `3`), so the helpers `shared_deg4_hub_deg5_seventeen` /
`shared_deg4_hub_nodeg5_seventeen` require `s ≤ 6`.

Two helpers, one per matching density:

* `halign8_eM5_seventeen` (`e(M) = 5`, `s = 10`): when the `M`-isolated cherry `t`-`p`-`q`-`r` is
  all degree-`4`, the dominating-edge centres have in-`M`-degree `3` (`dom_centres_indeg3`), giving a
  `SingleVertexConfig` double-star (`single_vertex_doublestar_count`), and the induced-`C₅` branch a
  `SingleVertexConfig` (`single_vertex_config_from_C5_three_hubs`).  The non-all-degree-`4` (a
  degree-`5` hub on the cherry, forcing `|D| ∈ {9, 10}`) two-twin route is the one residual.

* `halign8_eM4_seventeen` (`e(M) = 4`, `s = 8`): the induced-`C₅` branch is impossible
  (`s ≥ 10 > 8`), so only the dominating-edge double-star survives; producing the shared degree-`4`
  hub for the two-twin (or the `|Hub| = 9` hub-triangle) cut is the one residual.
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **`halign8` for `n = 17`, `e(M) = 5` (`s = 10`).**  Port of the `n = 16` `hall` branch: an
all-degree-`4` `M`-isolated cherry routes the dominating-edge double-star and the induced-`C₅` to
`SingleVertexConfig`.  The non-all-degree-`4` residual (a degree-`5` hub on the cherry, `|D| ∈
{9, 10}`, where `two_twin_eM5_seventeen` needs `|Hub| = 6`) is isolated as one documented `sorry`. -/
theorem halign8_eM5_seventeen (G : SimpleGraph (Fin 17))
    (_hm : G.edgeFinset.card = 30) (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 17, ({a, b, c, d, e} : Finset (Fin 17)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hiso : ∃ t : Fin 17, G.degree t = 3 ∧ ∀ w : Fin 17, G.Adj t w → G.degree w ≠ 3)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 10) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  set D : Finset (Fin 17) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hindle : ∀ x : Fin 17, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := (hmemD x).mp hx
  obtain ⟨t, ht3, htiso⟩ := hiso
  have htcard : (G.neighborFinset t).card = 3 := by rw [G.card_neighborFinset_eq_degree, ht3]
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp htcard
  have htp : G.Adj t p := (G.mem_neighborFinset _ _).mp (by rw [hset]; simp)
  have htq : G.Adj t q := (G.mem_neighborFinset _ _).mp (by rw [hset]; simp)
  have htr : G.Adj t r := (G.mem_neighborFinset _ _).mp (by rw [hset]; simp)
  by_cases hall : G.degree p = 4 ∧ G.degree q = 4 ∧ G.degree r = 4
  · obtain ⟨hp4, hq4, hr4⟩ := hall
    have hne : ∃ a b : Fin 17, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
      by_contra hcon
      push Not at hcon
      have hz : ∀ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := by
        intro v hv
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro w hw
        rw [Finset.mem_inter, G.mem_neighborFinset] at hw
        exact hcon v w hv hw.2 hw.1
      have hsum0 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := Finset.sum_eq_zero hz
      omega
    rcases dominating_edge_or_induced_C5 G D hmemD hT hC4 h2k2 hne with hdom | hC5
    · obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hdom
      obtain ⟨hin1, hin2⟩ :=
        dom_centres_indeg3 G D c₁ c₂ hc1D hc2D hc12 hindle hcov hsum10
      exact Or.inl (single_vertex_doublestar_count G D hmemD hT hC4 t p q r
        ht3 htiso hp4 hq4 hr4 hpq hpr hqr htp htq htr c₁ c₂ hc1D hc2D hc12 hin1 hin2 hcov)
    · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
        e12, e23, e34, e45, e51, n13, n14, n24, n25, n35, _⟩ := hC5
      exact Or.inl (single_vertex_config_from_C5_three_hubs G hT hC4 t p q r
        ht3 htiso hp4 hq4 hr4 hpq hpr hqr htp htq htr v₁ v₂ v₃ v₄ v₅
        ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
        ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5
        e12 e23 e34 e45 e51 n13 n14 n24 n25 n35)
  · -- **Residual (`|D| ∈ {9, 10}`).**  A neighbour of the `M`-isolated twin `t` has degree `≥ 5`, so
    -- `|D| ≥ 9`.  Extract a degree-`≤ 5` hub shared by two `M`-isolated twins (refined `|H₆| ≤ 2`
    -- count) and route the dominating-edge / induced-`C₅` structure through the deg-`≤ 5` two-twin
    -- assemblies via `two_twin_eM5_mid_seventeen`.
    have hpge4 : 4 ≤ G.degree p := by have := htiso p htp; have := h3 p; omega
    have hqge4 : 4 ≤ G.degree q := by have := htiso q htq; have := h3 q; omega
    have hrge4 : 4 ≤ G.degree r := by have := htiso r htr; have := h3 r; omega
    obtain ⟨w, hw5⟩ : ∃ w : Fin 17, 5 ≤ G.degree w := by
      by_contra hc
      push Not at hc
      exact hall ⟨by have := hc p; omega, by have := hc q; omega, by have := hc r; omega⟩
    have hDge9 : 9 ≤ D.card :=
      card_D_ge_nine_of_hub_deg5_seventeen G _hm h3 w hw5
    exact Or.inr (Or.inl (two_twin_eM5_mid_seventeen G _hm h3 hT h2k2 hC4 hDge9 hsum10))

/-- **`halign8` for `n = 17`, `e(M) = 4` (`s = 8`).**  The induced-`C₅` branch is impossible
(`s ≥ 10 > 8`), leaving only the dominating-edge double-star.  Producing the shared degree-`4` hub
for the two-twin cut (or, in the all-degree-`4` `|Hub| = 9` regime, the hub-triangle cut) is the one
residual: for `n = 17` the shared-hub pigeonhole only *ties* at `e(M) = 4` (`|Iso| − |H₅| ≥ 3`,
needs `> 3`), so it has no ready strict route.  Isolated as one documented `sorry`. -/
theorem halign8_eM4_seventeen (G : SimpleGraph (Fin 17))
    (hm : G.edgeFinset.card = 30) (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 17, ({a, b, c, d, e} : Finset (Fin 17)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (_hiso : ∃ t : Fin 17, G.degree t = 3 ∧ ∀ w : Fin 17, G.Adj t w → G.degree w ≠ 3)
    (hDne11 : (Finset.univ.filter (fun w => G.degree w = 3)).card ≠ 11)
    (hsum8 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 8) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  set D : Finset (Fin 17) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hne : ∃ a b : Fin 17, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
    by_contra hcon
    push Not at hcon
    have hz : ∀ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := by
      intro v hv
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      exact hcon v w hv hw.2 hw.1
    have hsum0 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := Finset.sum_eq_zero hz
    omega
  rcases dominating_edge_or_induced_C5 G D hmemD hT hC4 h2k2 hne with hdom | hC5
  · -- **Dominating-edge double-star (the only surviving structure at `e(M) = 4`).**
    obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hdom
    have hindle : ∀ x : Fin 17, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
      intro x hx
      calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
            Finset.card_le_card Finset.inter_subset_left
        _ = G.degree x := G.card_neighborFinset_eq_degree x
        _ = 3 := (hmemD x).mp hx
    have hge : 8 ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by omega
    by_cases hDrange : 9 ≤ D.card ∧ D.card ≤ 10
    · -- **`|D| ∈ {9, 10}`.**  Extract a shared degree-`4` hub (refined count with a `K_{2,3}`
      -- tie-break) and route the dominating-edge double-star through `dom_fat_centre_two_twin`.
      obtain ⟨hDge9, hDle10⟩ := hDrange
      obtain ⟨k, tw1, tw2, hkdeg4, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso, htw2iso⟩ :=
        shared_deg4_hub_eM4_seventeen G hm h3 h2k2 hK23 hDge9 hDle10 hsum8
      exact Or.inr (Or.inl (dom_fat_centre_two_twin_seventeen G D hmemD hT hC4 c₁ c₂ hc1D hc2D
        hc12 hcov hge hindle k tw1 tw2 hkdeg4 htw12 htw1deg htw2deg hAtw1k hAtw2k htw1iso htw2iso))
    · -- **Residual `|D| = 8` (`|Hub| = 9`, all degree-`4`, `|Iso| = 3`).**  Here the degree-`4`
      -- shared-hub pigeonhole only *ties* (`3·|Iso| = 9 = |Hub₄|`), so no two `M`-isolated twins are
      -- forced to share a hub and the dominating double-star is a hub-triangle.  Closing it requires
      -- the `|D| = 8` hub-triangle structural dispatch (extract the exact fat double-star and supply
      -- the `¬SingleVertex/¬TwoTwin/¬TwoHub` hypotheses to the `HubTriangleConfig` residual).  This
      -- is the one documented residual of the `e(M) = 4` corner.  DECOMPOSITION: an
      -- `exists_hub_triangle_config_fatstar_seventeen` helper (fat double-star, `|D| = 8`,
      -- `|Iso| = 3`) analogous to `exists_hub_triangle_config_residual_seventeen`.
      by_cases hsv : SingleVertexConfig G
      · exact Or.inl hsv
      by_cases htt : TwoTwinConfig G
      · exact Or.inr (Or.inl htt)
      by_cases hth : TwoHubConfig G
      · exact Or.inr (Or.inr (Or.inl hth))
      · exact Or.inr (Or.inr (Or.inr (fatstar_structure_eM4_D8_seventeen G hm h3 hT h2k2 hC4 hK23
          D hmemD hDne11 c₁ c₂ hc1D hc2D hc12 hcov hindle hsum8 hDrange hsv htt hth)))
  · -- **Induced-`C₅` is impossible at `e(M) = 4`:** each of the five cycle vertices has two
    -- `D`-neighbours, so `s ≥ 10 > 8`.
    exfalso
    obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
      e12, e23, e34, e45, e51, _n13, _n14, _n24, _n25, _n35, _hdom⟩ := hC5
    obtain ⟨_d12, d13, d14, _d15, _d23, d24, d25, _d34, d35, _d45⟩ :=
      distinct_five_seventeen v₁ v₂ v₃ v₄ v₅ hcard5
    have two_of : ∀ v a b : Fin 17, a ∈ D → b ∈ D → a ≠ b → G.Adj v a → G.Adj v b →
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v a b haD hbD hab hva hvb
      have hsub : ({a, b} : Finset (Fin 17)) ⊆ G.neighborFinset v ∩ D := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hva, haD⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvb, hbD⟩
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_pair hab] at hc
    have hTsub : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 17)) ⊆ D := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hbT : ∀ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 17)),
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact two_of _ v₂ v₅ hv2D hv5D d25 e12 e51.symm
      · exact two_of _ v₁ v₃ hv1D hv3D d13 e12.symm e23
      · exact two_of _ v₂ v₄ hv2D hv4D d24 e23.symm e34
      · exact two_of _ v₃ v₅ hv3D hv5D d35 e34.symm e45
      · exact two_of _ v₄ v₁ hv4D hv1D d14.symm e45.symm e51
    have hsumT : 10 ≤ ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 17)),
        (G.neighborFinset v ∩ D).card := by
      have h := Finset.card_nsmul_le_sum ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 17))
        (fun v => (G.neighborFinset v ∩ D).card) 2 hbT
      rw [hcard5] at h
      simpa using h
    have hmono : ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 17)),
        (G.neighborFinset v ∩ D).card ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
      Finset.sum_le_sum_of_subset hTsub
    omega

end N17

end ACMax
