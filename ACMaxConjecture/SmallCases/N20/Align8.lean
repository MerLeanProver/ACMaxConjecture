import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.Dense
import ACMaxConjecture.SmallCases.N20.DenseLe5
import ACMaxConjecture.SmallCases.N20.Align8Helpers
import ACMaxConjecture.SmallCases.N20.TwoHubHub6Deg5
import ACMaxConjecture.SmallCases.N20.Align8Mid
import ACMaxConjecture.SmallCases.N20.FatStarStruct
import ACMaxConjecture.SmallCases.N20.Align8D10C5
import ACMaxConjecture.SmallCases.N20.Align8D10Dom
import ACMaxConjecture.SmallCases.N20.Align8D12

/-!
# Dense `e(M) ≥ 4` alignment dichotomy for `n = 19` (`halign8` helpers)

Ports the proved-axiom-clean `n = 17` `TwinCert17Align8` to `Fin 20`, split by the value of `e(M)`.

* `halign8_eM5_twenty` (`e(M) = 5`, `s = 10`): an all-degree-`4` `M`-isolated cherry routes the
  dominating-edge double-star and the induced-`C₅` to `SingleVertexConfig`.  The non-all-degree-`4`
  residual (a degree-`5` hub on the cherry, forcing `|D| ≥ 9`) routes through the degree-`≤ 5`
  two-twin assembly (`two_twin_eM5_mid_twenty`) for `|D| ≥ 10`.  The `|D| = 9` thin double-star
  (`|Iso| = 3`, where the degree-`≤ 5` shared-hub pigeonhole only *ties*) is the one documented
  residual.

* `halign8_eM4_twenty` (`e(M) = 4`, `s = 8`): the induced-`C₅` branch is impossible (`s ≥ 10 > 8`),
  leaving only the dominating-edge double-star.  The larger `M`-isolated set (`|Iso| ≥ |D| − 5`) makes
  the degree-`≤ 5` shared-hub pigeonhole strict for all `|D| ∈ {9, …, 13}`, so those route to
  `TwoTwinConfig`.  The `|D| = 8` (`|Hub| = 10`, all degree-`4`) fat double-star hub-triangle corner
  is the one documented residual (the `n = 17` `fatstar` analog, awaiting the `n = 19` port of
  `TwinCert17HubTriangleFatStar` + `TwinCert17FatStarStruct`).
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **`halign8` for `n = 19`, `e(M) = 5` (`s = 10`).**  An all-degree-`4` `M`-isolated cherry routes
the dominating-edge double-star and the induced-`C₅` to `SingleVertexConfig`; the non-all-degree-`4`
case (a degree-`5` hub on the cherry, `|D| ≥ 10`) routes through `two_twin_eM5_mid_twenty`.  The
`|D| = 9` thin double-star is isolated as one documented `sorry`. -/
theorem halign8_eM5_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hiso : ∃ t : Fin 20, G.degree t = 3 ∧ ∀ w : Fin 20, G.Adj t w → G.degree w ≠ 3)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 10) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  set D : Finset (Fin 20) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hindle : ∀ x : Fin 20, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
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
    have hne : ∃ a b : Fin 20, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
        e12, e23, e36, e45, e51, n13, n14, n24, n25, n35, _⟩ := hC5
      exact Or.inl (single_vertex_config_from_C5_three_hubs G hT hC4 t p q r
        ht3 htiso hp4 hq4 hr4 hpq hpr hqr htp htq htr v₁ v₂ v₃ v₄ v₅
        ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
        ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5
        e12 e23 e36 e45 e51 n13 n14 n24 n25 n35)
  · -- **Residual.**  A neighbour of the `M`-isolated twin `t` has degree `≥ 5`, so `|D| ≥ 9`.
    have hpge4 : 4 ≤ G.degree p := by have := htiso p htp; have := h3 p; omega
    have hqge4 : 4 ≤ G.degree q := by have := htiso q htq; have := h3 q; omega
    have hrge4 : 4 ≤ G.degree r := by have := htiso r htr; have := h3 r; omega
    obtain ⟨w, hw5⟩ : ∃ w : Fin 20, 5 ≤ G.degree w := by
      by_contra hc
      push Not at hc
      exact hall ⟨by have := hc p; omega, by have := hc q; omega, by have := hc r; omega⟩
    have hDge9 : 9 ≤ D.card := by
      have := card_D_ge_nine_of_hub_deg5_twenty G hm h3 w hw5
      rwa [← hDdef] at this
    by_cases hD9 : D.card = 9
    · -- **`|D| = 9` thin double-star (`|Iso| = 3`).**  The degree-`≤ 5` shared-hub pigeonhole only
      -- *ties*, so re-select: the handshake forces a unique degree-`5` hub `K`; either two
      -- `M`-isolated twins meet `K` (a degree-`≤ 5` shared hub → `TwoTwinConfig`) or some
      -- `M`-isolated twin avoids `K` and is all-degree-`4` (→ `SingleVertexConfig`).
      have hnall : ¬∀ w : Fin 20, G.Adj t w → G.degree w = 4 := fun hcon =>
        hall ⟨hcon p htp, hcon q htq, hcon r htr⟩
      rcases eM5_D9_shared_or_alldeg4_twenty G hm h3 h2k2 hD9 hsum10.le t ht3 htiso hnall with
        ⟨k, tw1, tw2, hkle5, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso, htw2iso⟩ |
        ⟨t', ht'3, ht'iso, ht'all⟩
      · have hkge4 : 4 ≤ G.degree k := by have := htw1iso k hAtw1k; have := h3 k; omega
        exact (two_twin_eM5_from_shared_le5_twenty G hm h3 hT h2k2 hC4 hDge9
          hsum10 k tw1 tw2 hkge4 hkle5 htw12 htw1deg htw2deg hAtw1k hAtw2k htw1iso
          htw2iso).imp id Or.inl
      · exact Or.inl (sv_eM5_from_alldeg4_iso_twenty G hT h2k2 hC4 hsum10 t' ht'3 ht'iso ht'all)
    · by_cases hD10 : D.card = 10
      · -- **`|D| = 10` thin double-star** — CLOSED: the dominating-edge branch routes through the
        -- double-star `SingleVertex` leaf-coverage pigeonhole
        -- (`eM5_D10_domedge_sv_or_shared_twenty`), and the induced-`C₅` branch through the
        -- `|D| = 10` shared-hub count (`eM5_D10_c5_shared_twenty`); both shared-hub outcomes
        -- feed `two_twin_eM5_from_shared_le5_twenty`.
        have hne : ∃ a b : Fin 20, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
          rcases eM5_D10_domedge_sv_or_shared_twenty G hm h3 hT hD10 c₁ c₂
              ((hmemD c₁).mp hc1D) ((hmemD c₂).mp hc2D) hc12
              (fun p q hp hq hpq => hcov p q ((hmemD p).mpr hp) ((hmemD q).mpr hq) hpq)
              hsum10 with hsv |
            ⟨k, tw1', tw2', hkle5', htw12', htw1deg', htw2deg', hAtw1k', hAtw2k',
              htw1iso', htw2iso'⟩
          · exact Or.inl hsv
          · have hkge4' : 4 ≤ G.degree k := by
              have := htw1iso' k hAtw1k'
              have := h3 k
              omega
            exact (two_twin_eM5_from_shared_le5_twenty G hm h3 hT h2k2 hC4
              hDge9 hsum10 k tw1' tw2' hkge4' hkle5' htw12' htw1deg' htw2deg'
              hAtw1k' hAtw2k' htw1iso' htw2iso').imp id Or.inl
        · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
            e12, e23, e36, e45, e51, _n13, _n14, _n24, _n25, _n35, _⟩ := hC5
          obtain ⟨k, tw1', tw2', hkle5', htw12', htw1deg', htw2deg', hAtw1k', hAtw2k',
            htw1iso', htw2iso'⟩ :=
            eM5_D10_c5_shared_twenty G hm h3 hD10 v₁ v₂ v₃ v₄ v₅
              ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
              ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D)
              hcard5 e12 e23 e36 e45 e51 hsum10
          have hkge4' : 4 ≤ G.degree k := by
            have := htw1iso' k hAtw1k'
            have := h3 k
            omega
          exact (two_twin_eM5_from_shared_le5_twenty G hm h3 hT h2k2 hC4
            hDge9 hsum10 k tw1' tw2' hkge4' hkle5' htw12' htw1deg' htw2deg'
            hAtw1k' hAtw2k' htw1iso' htw2iso').imp id Or.inl
      · by_cases hD12 : D.card = 12
        · -- **`|D| = 12` `K_{2,6}` tie boundary.**  The dominating-edge branch routes through
          -- `eM5_D12_domedge_shared_or_two_hub_twenty` (a degree-`≤ 5` shared hub ∨ `TwoHubConfig`)
          -- and the induced-`C₅` branch through `eM5_D12_c5_shared_twenty`; both shared-hub outcomes
          -- feed `two_twin_eM5_from_shared_le5_twenty`.
          have hne : ∃ a b : Fin 20, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
            rcases eM5_D12_domedge_shared_or_two_hub_twenty G hm h3 hT hC4 hD12 c₁ c₂
                ((hmemD c₁).mp hc1D) ((hmemD c₂).mp hc2D) hc12
                (fun p q hp hq hpq => hcov p q ((hmemD p).mpr hp) ((hmemD q).mpr hq) hpq)
                hsum10 with
              ⟨k, tw1', tw2', hkle5', htw12', htw1deg', htw2deg', hAtw1k', hAtw2k',
                htw1iso', htw2iso'⟩ | hth
            · have hkge4' : 4 ≤ G.degree k := by
                have := htw1iso' k hAtw1k'
                have := h3 k
                omega
              exact (two_twin_eM5_from_shared_le5_twenty G hm h3 hT h2k2 hC4
                hDge9 hsum10 k tw1' tw2' hkge4' hkle5' htw12' htw1deg' htw2deg'
                hAtw1k' hAtw2k' htw1iso' htw2iso').imp id Or.inl
            · exact Or.inr (Or.inr (Or.inl hth))
          · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
              e12, e23, e36, e45, e51, _n13, _n14, _n24, _n25, _n35, _⟩ := hC5
            obtain ⟨k, tw1', tw2', hkle5', htw12', htw1deg', htw2deg', hAtw1k', hAtw2k',
              htw1iso', htw2iso'⟩ :=
              eM5_D12_c5_shared_twenty G hm h3 hD12 v₁ v₂ v₃ v₄ v₅
                ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
                ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D)
                hcard5 e12 e23 e36 e45 e51 hsum10
            have hkge4' : 4 ≤ G.degree k := by
              have := htw1iso' k hAtw1k'
              have := h3 k
              omega
            exact (two_twin_eM5_from_shared_le5_twenty G hm h3 hT h2k2 hC4
              hDge9 hsum10 k tw1' tw2' hkge4' hkle5' htw12' htw1deg' htw2deg'
              hAtw1k' hAtw2k' htw1iso' htw2iso').imp id Or.inl
        · have hDge11 : 11 ≤ D.card := by omega
          exact Or.inr (Or.inl
            (two_twin_eM5_mid_twenty G hm h3 hT h2k2 hC4 hDge11 hD12 hsum10))

/-- **`halign8` for `n = 19`, `e(M) = 4` (`s = 8`).**  The induced-`C₅` branch is impossible
(`s ≥ 10 > 8`), leaving only the dominating-edge double-star.  For `|D| ∈ {9, …, 13}` the degree-`≤ 5`
shared-hub pigeonhole is strict (`|Iso| ≥ |D| − 5`), routing to `TwoTwinConfig`.  The `|D| = 8`
(`|Hub| = 10`, all degree-`4`) fat double-star hub-triangle is isolated as one documented `sorry`. -/
theorem halign8_eM4_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 20, ({a, b, c, d, e} : Finset (Fin 20)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (_hiso : ∃ t : Fin 20, G.degree t = 3 ∧ ∀ w : Fin 20, G.Adj t w → G.degree w ≠ 3)
    (hs8 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 8) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  set D : Finset (Fin 20) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hindle : ∀ x : Fin 20, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := (hmemD x).mp hx
  have hge : 8 ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by omega
  have hne : ∃ a b : Fin 20, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
    have hD8' : 8 ≤ D.card := (residual_hub_card_le_eleven G hm h3).2
    by_cases hD8 : D.card = 8
    · -- **Residual `|D| = 8` (`|Hub| = 10`, all degree-`4`, `|Iso| = 3`).**  The dominating
      -- double-star is a fat hub-triangle; dispatch the `(3, 2)` in-`M`-degree split through
      -- `fatstar_structure_eM4_D8_twenty`, supplying the `¬SingleVertex/¬TwoTwin/¬TwoHub` residual.
      by_cases hsv : SingleVertexConfig G
      · exact Or.inl hsv
      by_cases htt : TwoTwinConfig G
      · exact Or.inr (Or.inl htt)
      by_cases hth : TwoHubConfig G
      · exact Or.inr (Or.inr (Or.inl hth))
      · exact Or.inr (Or.inr (Or.inr (fatstar_structure_eM4_D8_twenty G hm h3 hT hC4 D hmemD hD8
          c₁ c₂ hc1D hc2D hc12 hcov hindle hs8 hsv htt hth)))
    · -- **`|D| ∈ {9, …, 13}`.**  Extract a degree-`≤ 5` hub shared by two `M`-isolated twins and
      -- route the dominating-edge double-star through `dom_fat_centre_two_twin_le5_twenty`.
      have hDge9 : 9 ≤ D.card := by omega
      obtain ⟨k, tw1, tw2, hkle5, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso, htw2iso⟩ :=
        shared_hub_le5_eM4_twenty G hm h3 h2k2 hDge9 hs8.le
      have hkge4 : 4 ≤ G.degree k := by
        have := htw1iso k hAtw1k; have := h3 k; omega
      exact Or.inr (Or.inl (dom_fat_centre_two_twin_le5_twenty G D hmemD hT hC4 c₁ c₂ hc1D hc2D
        hc12 hcov hge hindle k tw1 tw2 hkge4 hkle5 htw12 htw1deg htw2deg hAtw1k hAtw2k htw1iso
        htw2iso))
  · -- **Induced-`C₅` is impossible at `e(M) = 4`:** each of the five cycle vertices has two
    -- `D`-neighbours, so `s ≥ 10 > 8`.
    exfalso
    obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
      e12, e23, e36, e45, e51, _n13, _n14, _n24, _n25, _n35, _hdom⟩ := hC5
    obtain ⟨_d12, d13, d14, _d15, _d23, d24, d25, _d36, d35, _d45⟩ :=
      distinct_five_twenty v₁ v₂ v₃ v₄ v₅ hcard5
    have two_of : ∀ v a b : Fin 20, a ∈ D → b ∈ D → a ≠ b → G.Adj v a → G.Adj v b →
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v a b haD hbD hab hva hvb
      have hsub : ({a, b} : Finset (Fin 20)) ⊆ G.neighborFinset v ∩ D := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hva, haD⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvb, hbD⟩
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_pair hab] at hc
    have hTsub : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 20)) ⊆ D := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hbT : ∀ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 20)),
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact two_of _ v₂ v₅ hv2D hv5D d25 e12 e51.symm
      · exact two_of _ v₁ v₃ hv1D hv3D d13 e12.symm e23
      · exact two_of _ v₂ v₄ hv2D hv4D d24 e23.symm e36
      · exact two_of _ v₃ v₅ hv3D hv5D d35 e36.symm e45
      · exact two_of _ v₄ v₁ hv4D hv1D d14.symm e45.symm e51
    have hsumT : 10 ≤ ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 20)),
        (G.neighborFinset v ∩ D).card := by
      have h := Finset.card_nsmul_le_sum ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 20))
        (fun v => (G.neighborFinset v ∩ D).card) 2 hbT
      rw [hcard5] at h
      simpa using h
    have hmono : ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 20)),
        (G.neighborFinset v ∩ D).card ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
      Finset.sum_le_sum_of_subset hTsub
    omega

end N20

end ACMax
