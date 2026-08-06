import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.TwoHubCornerOcta
import ACMaxConjecture.SmallCases.N19.MaxHub
import ACMaxConjecture.SmallCases.N19.FatCentre
import ACMaxConjecture.SmallCases.N19.TwoHubCornerDeg5
import ACMaxConjecture.SmallCases.N19.Dense
import ACMaxConjecture.SmallCases.N19.HubTriangle
import ACMaxConjecture.SmallCases.N19.HubTriangleCherry
import ACMaxConjecture.SmallCases.N19.CherryP3
import ACMaxConjecture.SmallCases.N19.CherryP3D12
import ACMaxConjecture.SmallCases.N19.FatStarStruct
import ACMaxConjecture.SmallCases.N19.CherryP4
import ACMaxConjecture.SmallCases.N19.CherryP4D12
import ACMaxConjecture.SmallCases.N19.Align8
import ACMaxConjecture.SmallCases.N19.TwoHubHub6
import ACMaxConjecture.SmallCases.N19.TwoHubSelect

/-!
# Existence of a twin signed-cut certificate for `n = 19` (structural assembly skeleton)

This file ports the proved `n = 18` dispatch (`exists_twin_signed_cert_eighteen`,
`ACMaxConjecture/TwinCert18.lean`) to `Fin 19`.  It is specialised to `Fin 19`,
`edgeFinset.card = 34`, `∑ deg = 68`, the good-triangle threshold `≤ 11`
(`19·(∑deg − 6) ≤ 2·3·16 = 96`; the good-triangle cut is now SLACK, `19·5 = 95 ≤ 96`), the residual
good-`C₄` threshold `≤ 14` (`19·(∑deg − 8) ≤ 2·4·15 = 120`) and the residual good-`K_{2,3}`
threshold `≤ 19` (`19·(∑deg − 12) ≤ 2·5·14 = 140`).

## `n = 19` cardinality bookkeeping (handshake)

Write `D = filter (deg = 3)` and `Hub = filter (4 ≤ deg)`, `|D| + |Hub| = 19`.  The handshake
`3|D| + ∑_{Hub} deg = 68` with `∑_{Hub} deg ≥ 4|Hub|` gives `|Hub| ≤ 11` (twelve hubs force
`4·12 + 3·7 = 69 > 68`), hence `|D| ≥ 8`.  With `e(M)` the edges inside `D`,
`s := ∑_{v∈D}|N v ∩ D| = 2·e(M)`, and `e_H` the edges inside `Hub`,

```
e(M) = 3|D| − 34 + e_H = 23 − 3|Hub| + e_H.
```

Since `e(M) ≤ 5` (`eM_le_five`) and `s` is even (`eM_even`), `s ∈ {0, 2, 4, 6, 8, 10}` and
`6|D| ≤ 68 + s ≤ 78`, so `|D| ≤ 13`.  Thus `|Hub| ∈ {6, 7, 8, 9, 10, 11}` and
`|D| ∈ {8, 9, 10, 11, 12, 13}`.

## Status

The assembly (`exists_twin_signed_cert_nineteen`) and its `s = 2·e(M) ∈ {0,2,4,6,8,10}`
case-split / dispatch are **sorry-free** and axiom-clean (`eM_even`, `eM_le_five` from
`TwinCert19Core`).  The four alignment dichotomies
(`two_hub_config_nineteen`, `exists_align_four_config_nineteen`,
`exists_align_six_config_nineteen`, `halign8_nineteen`) are the only remaining **documented `sorry`
stubs** — the deep combinatorial sub-lemmas to be ported from the `n = 18` development
(`TwinCert18*`).  The five `_to_cut` boundary certificates are now **proved** (axiom-clean), feeding
the mechanically-ported `Fin 19` cut certificates of `TwinCert19Cert`.

The frontier relative to `n = 18` is the pair of NEW boundary regimes:
* **`|Hub| = 11` (`|D| = 8`)** — eleven hubs, all degree `4` (`∑_{Hub} deg = 68 − 24 = 44 = 4·11`);
  the maximal-hub two-hub / star-triangle corner (analogous to the `n = 18` `|Hub| = 10`
  star-triangle), with NO excess slack;
* **`|D| = 13` (`|Hub| = 6`)** — the densest degree-3 set, the `e(M) = 5` boundary
  (`6·13 = 78 = 68 + 10`); the alignment residual at the new upper end of `|D|`.

Both NEW regimes are absorbed inside the four alignment stubs (flagged in each docstring).
-/

namespace ACMax

open scoped Classical

namespace N19

/-! ## Signed-cut configuration predicates (`Fin 19`)

The five configuration predicates `SingleVertexConfig`, `TwoTwinConfig`, `TwoHubConfig`,
`HubTriangleConfig`, `StarTriangleConfig` now live in `TwinCert19Cert` (matching the `n = 18`
architecture, where the Config defs sit in the Cert layer) so that the structural foundation files
can reference them.  They are re-exported here via the `TwinCert19Cert` import. -/

/-! ## `_to_cut` boundary certificates (DEEP SUB-LEMMA STUBS)

Each unpacks a config and runs the corresponding boundary signed-cut certificate (the `|P| = 3`
boundary bound `4·e(P,N) + e(P,Z) + e(N,Z) ≤ 12`, `n`-independent in the `n = 18` development).
PROVED: each feeds its `Fin 19` cut certificate in `TwinCert19Cert` (mechanical `Fin 18 → Fin 19`
port of `TwinCert18Cert` / `TwinCert18StarTriangle`). -/

/-- **Hub-triangle config yields the signed cut** (boundary certificate stub). -/
theorem hubTriangleConfig_to_cut (G : SimpleGraph (Fin 19)) (h : HubTriangleConfig G) :
    ∃ P N : Finset (Fin 19), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  obtain ⟨h₁, h₂, h₃, x, y, z, hdegx, hdegy, hdegz, hadj_12, hadj_13, hadj_23, hadj_xy, hadj_yz,
    hn1_x, hn1_y, hn1_z, hn2_x, hn2_y, hn2_z, hn3_x, hn3_y, hn3_z, hside,
    ne_h₁x, ne_h₁y, ne_h₁z, ne_h₂x, ne_h₂y, ne_h₂z, ne_h₃x, ne_h₃y, ne_h₃z,
    ne_xy, ne_yz, ne_xz⟩ := h
  exact hub_triangle_cut_certificate G h₁ h₂ h₃ x y z hdegx hdegy hdegz hadj_12 hadj_13
    hadj_23 hadj_xy hadj_yz hn1_x hn1_y hn1_z hn2_x hn2_y hn2_z hn3_x hn3_y hn3_z hside
    ne_h₁x ne_h₁y ne_h₁z ne_h₂x ne_h₂y ne_h₂z ne_h₃x ne_h₃y ne_h₃z ne_xy ne_yz ne_xz

/-- **Single-vertex config yields the signed cut** (boundary certificate stub). -/
theorem singleVertexConfig_to_cut (G : SimpleGraph (Fin 19)) (h : SingleVertexConfig G) :
    ∃ P N : Finset (Fin 19), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  obtain ⟨v, h₁, h₂, x, y, z, hdegv, hdegx, hdegy, hdegz, hadj_vh₁, hadj_vh₂, hadj_xy, hadj_yz,
    hnadj_xz, hside, ne_h₁h₂, ne_vx, ne_vy, ne_vz, ne_h₁x, ne_h₁y, ne_h₁z, ne_h₂x, ne_h₂y, ne_h₂z,
    ne_xy, ne_yz, ne_xz⟩ := h
  exact single_vertex_cut_certificate G v h₁ h₂ x y z hdegv hdegx hdegy hdegz hadj_vh₁
    hadj_vh₂ hadj_xy hadj_yz hnadj_xz hside ne_h₁h₂ ne_vx ne_vy ne_vz ne_h₁x ne_h₁y ne_h₁z ne_h₂x
    ne_h₂y ne_h₂z ne_xy ne_yz ne_xz

/-- **2-twin config yields the signed cut** (boundary certificate stub). -/
theorem twoTwinConfig_to_cut (G : SimpleGraph (Fin 19)) (h : TwoTwinConfig G) :
    ∃ P N : Finset (Fin 19), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  obtain ⟨t₁, t₂, hh, x, y, z, hdegt₁, hdegt₂, hdegh, hdegx, hdegy, hdegz, hadj_t₁h, hadj_t₂h,
    hadj_xy, hadj_yz, hnt₁_x, hnt₁_y, hnt₁_z, hnt₂_x, hnt₂_y, hnt₂_z, hnh_x, hnh_y, hnh_z,
    ne_t₁t₂, ne_t₁x, ne_t₁y, ne_t₁z, ne_t₂x, ne_t₂y, ne_t₂z, ne_hx, ne_hy, ne_hz,
    ne_xy, ne_yz, ne_xz⟩ := h
  exact two_twin_cut_certificate G t₁ t₂ hh x y z hdegt₁ hdegt₂ hdegh hdegx hdegy hdegz
    hadj_t₁h hadj_t₂h hadj_xy hadj_yz hnt₁_x hnt₁_y hnt₁_z hnt₂_x hnt₂_y hnt₂_z hnh_x hnh_y hnh_z
    ne_t₁t₂ ne_t₁x ne_t₁y ne_t₁z ne_t₂x ne_t₂y ne_t₂z ne_hx ne_hy ne_hz ne_xy ne_yz ne_xz

/-- **Two-hub config yields the signed cut** (boundary certificate stub). -/
theorem twoHubConfig_to_cut (G : SimpleGraph (Fin 19)) (h : TwoHubConfig G) :
    ∃ P N : Finset (Fin 19), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  obtain ⟨h₁, h₂, a, b, c, d, hdegh₁, hdegh₂, hdega, hdegb, hdegc, hdegd,
    hadj_ah₁, hadj_bh₁, hadj_ch₂, hadj_dh₂,
    hn_h₁h₂, hn_h₁c, hn_h₁d, hn_ah₂, hn_ac, hn_ad, hn_bh₂, hn_bc, hn_bd,
    ne_h₁h₂, ne_h₁a, ne_h₁b, ne_h₁c, ne_h₁d, ne_h₂a, ne_h₂b, ne_h₂c, ne_h₂d,
    ne_ab, ne_ac, ne_ad, ne_bc, ne_bd, ne_cd⟩ := h
  exact two_hub_opposite_twin_cert G h₁ h₂ a b c d hdegh₁ hdegh₂ hdega hdegb hdegc hdegd
    hadj_ah₁ hadj_bh₁ hadj_ch₂ hadj_dh₂ hn_h₁h₂ hn_h₁c hn_h₁d hn_ah₂ hn_ac hn_ad
    hn_bh₂ hn_bc hn_bd ne_h₁h₂ ne_h₁a ne_h₁b ne_h₁c ne_h₁d ne_h₂a ne_h₂b ne_h₂c ne_h₂d
    ne_ab ne_ac ne_ad ne_bc ne_bd ne_cd

/-- **Star-triangle config yields the signed cut** (boundary certificate stub). -/
theorem starTriangleConfig_to_cut (G : SimpleGraph (Fin 19)) (h : StarTriangleConfig G) :
    ∃ P N : Finset (Fin 19), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  obtain ⟨h, t₁, t₂, a, b, c, hdegh, hdegt1, hdegt2, hdega, hdegb, hdegc,
    hAht1, hAht2, hAab, hAac, hAbc, hnha, hnhb, hnhc, hnt1a, hnt1b, hnt1c,
    hnt2a, hnt2b, hnt2c, ne_t12, ne_ha, ne_hb, ne_hc, ne_t1a, ne_t1b, ne_t1c,
    ne_t2a, ne_t2b, ne_t2c⟩ := h
  exact star_triangle_cut_certificate G h t₁ t₂ a b c hdegh hdegt1 hdegt2 hdega hdegb hdegc
    hAht1 hAht2 hAab hAac hAbc hnha hnhb hnhc hnt1a hnt1b hnt1c hnt2a hnt2b hnt2c ne_t12
    ne_ha ne_hb ne_hc ne_t1a ne_t1b ne_t1c ne_t2a ne_t2b ne_t2c

/-! ## The four alignment dichotomies (DEEP SUB-LEMMA STUBS)

Statements ported from the proved `n = 18` analogues (`two_hub_config_eighteen`,
`exists_align_four_config_eighteen`, `exists_align_six_config_eighteen`, `halign8_eighteen`) under
`Fin 18 → Fin 19`, `edgeFinset.card = 32 → 34`.  Bodies are documented `sorry`s.  The NEW `n = 19`
boundary regimes `|Hub| = 11` (`|D| = 8`, all degree `4`) and `|D| = 13` (`|Hub| = 6`, the
`e(M) = 5` upper end) are absorbed here and flagged per lemma. -/

/-- **Degree-`≥ 6`-witness two-hub selector** for the high-degree `e(M) ≤ 1` corners
`(8,11,35)`, `(8,9,35)`, `(9,10,38)`.  Mirrors `two_hub_deg7_select_nineteen` but additionally
threads a degree-`≥ 6` hub witness (`hdeg6ex`), which pushes the deg-`≥ 5` hub mass up by `1`
(`∑_R deg ≥ 5·|R| + 1`); this closes exactly these three regimes by the residual master inequality.
The fourth high-degree corner `(9,8,38)` (single degree-`6` fat hub, `|R| = 1`) is NOT closed by
counting and is left to the structural fat-centre residual. -/
theorem deg6_witness_select_nineteen (G : SimpleGraph (Fin 19)) (Hub Iso : Finset (Fin 19))
    (hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h) (_hdeg7 : ∀ h ∈ Hub, G.degree h ≤ 7)
    (hdeg6ex : ∃ h ∈ Hub, 6 ≤ G.degree h)
    (hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3)
    (hshare : ∀ h₁ ∈ Hub, G.degree h₁ = 4 → ∀ h₂ ∈ Hub, G.degree h₂ = 4 → h₁ ≠ h₂ →
      ¬G.Adj h₁ h₂ → (G.neighborFinset h₁ ∩ G.neighborFinset h₂ ∩ Iso).card ≤ 1)
    (hdisj : Disjoint Hub Iso)
    (hregime :
      (Hub.card = 8 ∧ Iso.card = 11 ∧ ∑ w ∈ Hub, G.degree w = 35) ∨
      (Hub.card = 8 ∧ Iso.card = 9 ∧ ∑ w ∈ Hub, G.degree w = 35) ∨
      (Hub.card = 9 ∧ Iso.card = 10 ∧ ∑ w ∈ Hub, G.degree w = 38)) :
    ∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card := by
  classical
  by_contra hcon
  have key := nogood_of_not_select_nineteen G Hub Iso hcon
  have hmf := strong_deg4_count_le_two_deg5_nineteen G Hub Iso hdisj hshare key
  have hisoSum := hub_iso_sum_nineteen G Hub Iso hiso3
  have hTsum_le := deg4_sum_le_nineteen G Hub Iso hmf
  set T : Finset (Fin 19) := Hub.filter (fun h => G.degree h = 4) with hT
  set R : Finset (Fin 19) := Hub.filter (fun h => ¬ G.degree h = 4) with hR
  have hpartIso : ∑ v ∈ T, (G.neighborFinset v ∩ Iso).card
      + ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card = ∑ v ∈ Hub, (G.neighborFinset v ∩ Iso).card :=
    Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
  have hRdeg5ge : ∀ v ∈ R, 5 ≤ G.degree v := by
    intro v hv; rw [hR, Finset.mem_filter] at hv
    have := hdeg v hv.1; omega
  have hRiso_le : ∑ v ∈ R, (G.neighborFinset v ∩ Iso).card ≤ ∑ v ∈ R, G.degree v := by
    apply Finset.sum_le_sum
    intro v _
    rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_le_card Finset.inter_subset_left
  have hpartDeg : ∑ v ∈ T, G.degree v + ∑ v ∈ R, G.degree v = ∑ v ∈ Hub, G.degree v :=
    Finset.sum_filter_add_sum_filter_not Hub (fun h => G.degree h = 4) _
  have hTdeg : ∑ v ∈ T, G.degree v = 4 * T.card := by
    rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2), Finset.sum_const,
      smul_eq_mul, mul_comm]
  -- The degree-`≥ 6` witness lives in `R`, lifting the deg-`≥ 5` mass by `1`.
  obtain ⟨w, hwHub, hw6⟩ := hdeg6ex
  have hwR : w ∈ R := by rw [hR, Finset.mem_filter]; exact ⟨hwHub, by omega⟩
  have hRdeg_ge : 5 * R.card + 1 ≤ ∑ v ∈ R, G.degree v := by
    have hsplit : ∑ v ∈ R, G.degree v
        = G.degree w + ∑ v ∈ R.erase w, G.degree v := (Finset.add_sum_erase R _ hwR).symm
    have hbb : 5 * (R.erase w).card ≤ ∑ v ∈ R.erase w, G.degree v := by
      calc 5 * (R.erase w).card = ∑ _v ∈ R.erase w, 5 := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ v ∈ R.erase w, G.degree v :=
            Finset.sum_le_sum (fun v hv => hRdeg5ge v (Finset.mem_of_mem_erase hv))
    have hec : (R.erase w).card = R.card - 1 := Finset.card_erase_of_mem hwR
    have hRpos : 1 ≤ R.card := Finset.card_pos.mpr ⟨w, hwR⟩
    omega
  have hcard : T.card + R.card = Hub.card :=
    Finset.card_filter_add_card_filter_not (fun h => G.degree h = 4)
  rcases hregime with ⟨hHub, hIso, hdsum⟩ | ⟨hHub, hIso, hdsum⟩ | ⟨hHub, hIso, hdsum⟩ <;> omega

/-- **Two-hub opposite-twin selection for `n = 19`, `e(M) ≤ 1` (STUB).**
`s ≤ 2` ⟹ no degree-`3` cherry through two hubs, so the two-hub opposite-twin cut is available.
`|D| ∈ {8, 9, 10, 11, 12}` from `6·|D| ≤ 68 + s`.  **NEW frontier:** `|D| = 8` ⟺ `|Hub| = 11` (all
degree `4`, `∑_{Hub} deg = 44`) — the maximal-hub corner routed through `StarTriangleConfig`
(analogue of the `n = 18` `|Hub| = 10` star-triangle, but with eleven hubs and no excess slack). -/
theorem two_hub_config_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (h2k2 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (_hiso : ∃ t : Fin 19, G.degree t = 3 ∧ ∀ w : Fin 19, G.Adj t w → G.degree w ≠ 3)
    (hle : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card ≤ 2) :
    TwoHubConfig G ∨ StarTriangleConfig G := by
  classical
  set D : Finset (Fin 19) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  set Hub : Finset (Fin 19) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hmemHub : ∀ v : Fin 19, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  have hHubnotD : ∀ x : Fin 19, x ∈ Hub → x ∉ D := by
    intro x hx hxD; have := (hmemHub x).mp hx; have := (hmemD x).mp hxD; omega
  set Iso : Finset (Fin 19) := D.filter (fun x => (G.neighborFinset x ∩ D).card = 0) with hIsodef
  have hIsomem : ∀ x : Fin 19, x ∈ Iso ↔ x ∈ D ∧ (G.neighborFinset x ∩ D).card = 0 := by
    intro x; rw [hIsodef, Finset.mem_filter]
  have hisoD : ∀ x : Fin 19, x ∈ Iso → x ∈ D := fun x hx => ((hIsomem x).mp hx).1
  have hisoNoD : ∀ x y : Fin 19, x ∈ Iso → y ∈ D → ¬G.Adj x y := by
    intro x y hx hy hadj
    obtain ⟨_, hx0⟩ := (hIsomem x).mp hx
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hx0
    exact hx0 y (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y).mpr hadj, hy⟩)
  have hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3) := by
    intro v hv
    refine ⟨(hmemD v).mp (hisoD v hv), fun w hadj hw3 => ?_⟩
    exact hisoNoD v w hv ((hmemD w).mpr hw3) hadj
  have hDH : ∀ v : Fin 19, v ∈ D ∨ v ∈ Hub := fun v => by
    rcases Nat.lt_or_ge (G.degree v) 4 with h | h
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemHub v).mpr h)
  have hdisj : Disjoint D Hub :=
    Finset.disjoint_left.mpr (fun v hv hv' => hHubnotD v hv' hv)
  have hunion : D ∪ Hub = Finset.univ := by
    ext v; simp only [Finset.mem_union, Finset.mem_univ, iff_true]; exact hDH v
  have hcard19 : D.card + Hub.card = 19 := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at h; omega
  have hHubDc : ∀ w : Fin 19, w ∈ Hub ↔ w ∈ Dᶜ := by
    intro w; rw [Finset.mem_compl, hmemD, hmemHub]
    constructor
    · intro h he; omega
    · intro _; have := h3 w; omega
  have hsum : ∑ v : Fin 19, G.degree v = 68 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ Hub, G.degree v = 68 := by
    rw [← Finset.sum_union hdisj, hunion]; exact hsum
  have hsplitD : ∀ v ∈ D,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Hub).card = 3 := by
    intro v hv
    have hdeg : (G.neighborFinset v).card = 3 := by
      rw [G.card_neighborFinset_eq_degree, (hmemD v).mp hv]
    have hu : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Hub) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, hunion, Finset.inter_univ]
    have hdj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Hub) :=
      Finset.disjoint_left.mpr (fun a ha hb =>
        (Finset.disjoint_left.mp hdisj) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2)
    have hc := Finset.card_union_of_disjoint hdj
    rw [hu, hdeg] at hc; omega
  set s : ℕ := ∑ v ∈ D, (G.neighborFinset v ∩ D).card with hsdef
  have hSsumD : s + ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card = 3 * D.card := by
    rw [hsdef, ← Finset.sum_add_distrib, Finset.sum_congr rfl hsplitD, Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Hub).card
      = ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card := cross_count_nineteen G D Hub
  have hIntEq : (∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card) + 6 * D.card = 68 + s := by
    have hsplitHub : ∀ w ∈ Hub,
        (G.neighborFinset w ∩ D).card + (G.neighborFinset w ∩ Hub).card = G.degree w := by
      intro w hw
      have hdeg : (G.neighborFinset w).card = G.degree w := G.card_neighborFinset_eq_degree w
      have hu : (G.neighborFinset w ∩ D) ∪ (G.neighborFinset w ∩ Hub) = G.neighborFinset w := by
        rw [← Finset.inter_union_distrib_left, hunion, Finset.inter_univ]
      have hdj : Disjoint (G.neighborFinset w ∩ D) (G.neighborFinset w ∩ Hub) :=
        Finset.disjoint_left.mpr (fun a ha hb =>
          (Finset.disjoint_left.mp hdisj) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2)
      have hc := Finset.card_union_of_disjoint hdj
      rw [hu, hdeg] at hc; omega
    have hSsumHub : ∑ w ∈ Hub, (G.neighborFinset w ∩ D).card
        + ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card = ∑ w ∈ Hub, G.degree w := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hsplitHub]
    have h1 := hsumpart; rw [hsumD] at h1; omega
  have hD8 : 8 ≤ D.card := by
    have h := (residual_hub_card_le_eleven G hm h3).2; rwa [← hDdef] at h
  have heven : Even s := by rw [hsdef]; exact eM_even G D
  have hle2 : s ≤ 2 := by rw [hsdef, hDdef]; exact hle
  have hd : D.card = 8 ∨ D.card = 9 ∨ D.card = 10 ∨ D.card = 11 := by
    have hnn : 0 ≤ ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card := Nat.zero_le _
    omega
  -- **Common structural facts.**
  have hdeg : ∀ h ∈ Hub, 4 ≤ G.degree h := fun h hh => (hmemHub h).mp hh
  have hiso3 : ∀ t ∈ Iso, (G.neighborFinset t ∩ Hub).card = 3 := fun t ht =>
    each_iso_three_hubs G D Hub hmemD hmemHub h3 t (hisoD t ht) ((hIsomem t).mp ht).2
  have hisoIndep : ∀ a ∈ Iso, ∀ b ∈ Iso, ¬G.Adj a b := fun a ha b hb =>
    hisoNoD a b ha (hisoD b hb)
  have hdisjHI : Disjoint Hub Iso := by
    rw [Finset.disjoint_left]; intro x hxH hxI
    exact (Finset.disjoint_left.mp hdisj) (hisoD x hxI) hxH
  have hisodeg : ∀ t ∈ Iso, G.degree t = 3 := fun t ht => (hIsoprop t ht).1
  -- **Degree-`4` share bound** (non-adjacent degree-`4` pair shares `≤ 1` twin, else good `C₄`
  -- of degree-sum `4 + 3 + 4 + 3 = 14`).
  have hshare4 : ∀ p ∈ Hub, G.degree p = 4 → ∀ q ∈ Hub, G.degree q = 4 → p ≠ q →
      ¬G.Adj p q → (G.neighborFinset p ∩ G.neighborFinset q ∩ Iso).card ≤ 1 := by
    intro p hp hdp q hq hdq hpq hnpq
    by_contra hgt
    rw [not_le] at hgt
    obtain ⟨t₁, ht1, t₂, ht2, h12⟩ := Finset.one_lt_card.mp hgt
    have unpack : ∀ t : Fin 19, t ∈ G.neighborFinset p ∩ G.neighborFinset q ∩ Iso →
        G.Adj p t ∧ G.Adj q t ∧ t ∈ Iso := by
      intro t ht
      rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
      exact ⟨ht.1.1, ht.1.2, ht.2⟩
    obtain ⟨ha1, hb1, hI1⟩ := unpack t₁ ht1
    obtain ⟨ha2, hb2, hI2⟩ := unpack t₂ ht2
    have htw_nonadj : ¬G.Adj t₁ t₂ := hisoNoD t₁ t₂ hI1 (hisoD t₂ hI2)
    have hpne : ∀ t : Fin 19, t ∈ Iso → p ≠ t ∧ q ≠ t := by
      intro t ht
      have htD : t ∈ D := hisoD t ht
      exact ⟨fun e => hHubnotD p hp (by rw [e]; exact htD),
        fun e => hHubnotD q hq (by rw [e]; exact htD)⟩
    obtain ⟨hpt1, hqt1⟩ := hpne t₁ hI1
    obtain ⟨hpt2, hqt2⟩ := hpne t₂ hI2
    apply hC4
    refine ⟨p, t₁, q, t₂, ?_, ha1, hb1.symm, hb2, ha2.symm, hnpq, htw_nonadj, ?_⟩
    · rw [Finset.card_insert_of_notMem (by simp [hpt1, hpq, hpt2]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hqt1, h12]),
        Finset.card_insert_of_notMem (by simp [hqt2]), Finset.card_singleton]
    · have e3 := (hIsoprop t₁ hI1).1
      have e4 := (hIsoprop t₂ hI2).1
      omega
  -- **`|Iso|` from `e(M)`** (`s = 0 ⟹ Iso = D`; `s = 2 ⟹ |Iso| = |D| − 2`).
  have hIsocard : Iso.card = D.card - s := by
    set S : Finset (Fin 19) := D.filter (fun v => ¬ (G.neighborFinset v ∩ D).card = 0) with hSdef
    have hScompl : Iso.card + S.card = D.card := by
      rw [hIsodef, hSdef]
      exact Finset.card_filter_add_card_filter_not (s := D)
        (p := fun v => (G.neighborFinset v ∩ D).card = 0)
    rcases (by obtain ⟨k, hk⟩ := heven; omega : s = 0 ∨ s = 2) with hs0 | hs2
    · have hsum0 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 0 := by rw [← hsdef]; exact hs0
      have hS0 : S.card = 0 := by
        rw [hSdef, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun v hv => not_not.mpr ((Finset.sum_eq_zero_iff).mp hsum0 v hv)
      omega
    · have hSle : 2 * S.card ≤ s + 2 := by
        rw [hSdef, hsdef]; exact nonisolated_component_bound G D hmemD h2k2
      have hexists : ∃ v ∈ D, (G.neighborFinset v ∩ D).card ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have hz : s = 0 := by rw [hsdef]; exact Finset.sum_eq_zero hcon
        omega
      obtain ⟨v0, hv0D, hv0ne⟩ := hexists
      have hv0S : v0 ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨hv0D, hv0ne⟩
      obtain ⟨w0, hw0mem⟩ := Finset.card_ne_zero.mp hv0ne
      have hw0D : w0 ∈ D := (Finset.mem_inter.mp hw0mem).2
      have hadj0 : G.Adj v0 w0 := (G.mem_neighborFinset v0 w0).mp (Finset.mem_inter.mp hw0mem).1
      have hw0S : w0 ∈ S := by
        rw [hSdef, Finset.mem_filter]
        exact ⟨hw0D, Finset.card_ne_zero.mpr
          ⟨v0, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w0 v0).mpr hadj0.symm, hv0D⟩⟩⟩
      have hvw0ne : v0 ≠ w0 := G.ne_of_adj hadj0
      have hSge : 2 ≤ S.card := by
        have hsub : ({v0, w0} : Finset (Fin 19)) ⊆ S := by
          intro x hx
          rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h
          · rw [h]; exact hv0S
          · rw [h]; exact hw0S
        calc 2 = ({v0, w0} : Finset (Fin 19)).card := by rw [Finset.card_pair hvw0ne]
          _ ≤ S.card := Finset.card_le_card hsub
      omega
  have hsumHub : ∑ w ∈ Hub, G.degree w = 68 - 3 * D.card := by omega
  -- **`hleak`/`hNIof`: the `Z`-cross bound when `|Iso| = |D| − 2`.**
  have hNIof : ∀ (n : ℕ), Iso.card = n → D.card - n = 2 →
      ∑ h ∈ Hub, (G.neighborFinset h ∩ (Finset.univ \ (Hub ∪ Iso))).card ≤ 4 := by
    intro n hIson hXcard2
    set X : Finset (Fin 19) := Finset.univ \ (Hub ∪ Iso) with hXdef
    have hXeq : X = D \ Iso := by
      rw [hXdef]; ext v
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or]
      constructor
      · intro ⟨hnH, hnI⟩; exact ⟨(hDH v).resolve_right hnH, hnI⟩
      · intro ⟨hvD, hnI⟩; exact ⟨fun hvH => hHubnotD v hvH hvD, hnI⟩
    have hXsub : X ⊆ D := by rw [hXeq]; exact Finset.sdiff_subset
    have hXcard : X.card = 2 := by
      have hsub : Iso ⊆ D := Finset.filter_subset _ _
      rw [hXeq, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hIson]; omega
    have hcc : ∑ h ∈ Hub, (G.neighborFinset h ∩ X).card
        = ∑ x ∈ X, (G.neighborFinset x ∩ Hub).card := cross_count_nineteen G Hub X
    rw [hcc]
    have hbound : ∀ x ∈ X, (G.neighborFinset x ∩ Hub).card ≤ 2 := by
      intro x hx
      have hxD : x ∈ D := hXsub hx
      have hxnI : x ∉ Iso := (Finset.mem_sdiff.mp (hXeq ▸ hx)).2
      have hxDpos : 1 ≤ (G.neighborFinset x ∩ D).card := by
        rcases Nat.eq_zero_or_pos (G.neighborFinset x ∩ D).card with h0 | hpos
        · exact absurd ((hIsomem x).mpr ⟨hxD, h0⟩) hxnI
        · exact hpos
      have := hsplitD x hxD; omega
    calc ∑ x ∈ X, (G.neighborFinset x ∩ Hub).card
        ≤ ∑ _x ∈ X, 2 := Finset.sum_le_sum hbound
      _ = 2 * X.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ = 4 := by rw [hXcard]
  -- **Convert a raw good two-hub pair into a `TwoHubConfig`.**
  have pairToTH : (∃ h₁ h₂ : Fin 19, h₁ ∈ Hub ∧ h₂ ∈ Hub ∧
      G.degree h₁ = 4 ∧ G.degree h₂ = 4 ∧ h₁ ≠ h₂ ∧ ¬G.Adj h₁ h₂ ∧
      2 ≤ ((G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂).card ∧
      2 ≤ ((G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁).card) → TwoHubConfig G := by
    rintro ⟨h₁, h₂, hh1, hh2, hdeg1, hdeg2, hne12, hnadj12, hAcard, hBcard⟩
    set A : Finset (Fin 19) := (G.neighborFinset h₁ ∩ Iso) \ G.neighborFinset h₂ with hAdef
    set B : Finset (Fin 19) := (G.neighborFinset h₂ ∩ Iso) \ G.neighborFinset h₁ with hBdef
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hAcard
    obtain ⟨c, hc, d, hd2, hcd⟩ := Finset.one_lt_card.mp hBcard
    have hAprop : ∀ x : Fin 19, x ∈ A → G.Adj x h₁ ∧ x ∈ Iso ∧ ¬G.Adj x h₂ := by
      intro x hx
      rw [hAdef, Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset] at hx
      refine ⟨hx.1.1.symm, hx.1.2, ?_⟩
      intro hadj; exact hx.2 ((G.mem_neighborFinset h₂ x).mpr hadj.symm)
    have hBprop : ∀ x : Fin 19, x ∈ B → G.Adj x h₂ ∧ x ∈ Iso ∧ ¬G.Adj x h₁ := by
      intro x hx
      rw [hBdef, Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset] at hx
      refine ⟨hx.1.1.symm, hx.1.2, ?_⟩
      intro hadj; exact hx.2 ((G.mem_neighborFinset h₁ x).mpr hadj.symm)
    obtain ⟨ha_h₁, ha_iso, ha_nh₂⟩ := hAprop a ha
    obtain ⟨hb_h₁, hb_iso, hb_nh₂⟩ := hAprop b hb
    obtain ⟨hc_h₂, hc_iso, hc_nh₁⟩ := hBprop c hc
    obtain ⟨hd_h₂, hd_iso, hd_nh₁⟩ := hBprop d hd2
    have haD := hisoD a ha_iso
    have hbD := hisoD b hb_iso
    have hcD := hisoD c hc_iso
    have hdD := hisoD d hd_iso
    exact ⟨h₁, h₂, a, b, c, d, hdeg1, hdeg2,
      (hmemD a).mp haD, (hmemD b).mp hbD, (hmemD c).mp hcD, (hmemD d).mp hdD,
      ha_h₁, hb_h₁, hc_h₂, hd_h₂,
      hnadj12,
      (fun h => hc_nh₁ h.symm), (fun h => hd_nh₁ h.symm),
      ha_nh₂, hisoNoD a c ha_iso hcD, hisoNoD a d ha_iso hdD,
      hb_nh₂, hisoNoD b c hb_iso hcD, hisoNoD b d hb_iso hdD,
      hne12,
      (fun e => hHubnotD h₁ hh1 (by rw [e]; exact haD)),
      (fun e => hHubnotD h₁ hh1 (by rw [e]; exact hbD)),
      (fun e => hHubnotD h₁ hh1 (by rw [e]; exact hcD)),
      (fun e => hHubnotD h₁ hh1 (by rw [e]; exact hdD)),
      (fun e => hHubnotD h₂ hh2 (by rw [e]; exact haD)),
      (fun e => hHubnotD h₂ hh2 (by rw [e]; exact hbD)),
      (fun e => hHubnotD h₂ hh2 (by rw [e]; exact hcD)),
      (fun e => hHubnotD h₂ hh2 (by rw [e]; exact hdD)),
      hab,
      (fun e => hc_nh₁ (e ▸ ha_h₁)), (fun e => hd_nh₁ (e ▸ ha_h₁)),
      (fun e => hc_nh₁ (e ▸ hb_h₁)), (fun e => hd_nh₁ (e ▸ hb_h₁)),
      hcd⟩
  -- **`s ∈ {0, 2}`.**
  have hs02 : s = 0 ∨ s = 2 := by obtain ⟨k, hk⟩ := heven; omega
  rcases hd with hd8 | hd9 | hd10 | hd11
  · -- **`|D| = 8 ⟹ |Hub| = 11`, all degree `4`.**
    have hHub11 : Hub.card = 11 := by omega
    have hsum44 : ∑ w ∈ Hub, G.degree w = 44 := by rw [hsumHub, hd8]
    have hdeg4all : ∀ h ∈ Hub, G.degree h = 4 := by
      intro w hw
      have herase := Finset.add_sum_erase Hub (fun v => G.degree v) hw
      have hb : 4 * (Hub.erase w).card ≤ ∑ v ∈ Hub.erase w, G.degree v := by
        have hbb : ∀ x ∈ Hub.erase w, 4 ≤ G.degree x := fun i hi =>
          (hmemHub i).mp (Finset.mem_of_mem_erase hi)
        have h := Finset.card_nsmul_le_sum (Hub.erase w) (fun v => G.degree v) 4 hbb
        simpa [smul_eq_mul, mul_comm] using h
      have hec : (Hub.erase w).card = Hub.card - 1 := Finset.card_erase_of_mem hw
      have hge := (hmemHub w).mp hw
      omega
    rcases hs02 with hs0 | hs2
    · -- **`s = 0 ⟹ |Iso| = 8`: the `(11, 8, 44)` `e(M) = 0` sub-case.**  Counting ties
      -- (`134 = 134`), so the master inequality does not close it.  Closed by the **max-hub
      -- selection** (`two_hub_maxhub_pair_nineteen`): the maximum-iso-degree hub `h*` (`A ≤ 4`
      -- twins) pairs with a non-adjacent hub, since assuming no good pair forces
      -- `24 − A = ∑_{b≠h*} a(b) ≤ 22 − A` (adjacent hubs share `0` twins by the `hT` light
      -- triangle `4+4+3`, and there are `≤ 4−A` of them), a contradiction.
      have hIso8 : Iso.card = 8 := by rw [hIsocard, hd8, hs0]
      have hadj0 : ∀ a ∈ Hub, ∀ b ∈ Hub, G.Adj a b →
          (G.neighborFinset a ∩ G.neighborFinset b ∩ Iso).card = 0 := by
        intro a ha b hb hab
        by_contra hne0
        obtain ⟨p, hp⟩ := Finset.card_ne_zero.mp hne0
        rw [Finset.mem_inter, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at hp
        obtain ⟨⟨hap, hbp⟩, hpIso⟩ := hp
        have hanep : a ≠ p := fun e => (Finset.disjoint_left.mp hdisjHI) ha (e ▸ hpIso)
        have hbnep : b ≠ p := fun e => (Finset.disjoint_left.mp hdisjHI) hb (e ▸ hpIso)
        exact hT ⟨a, b, p, G.ne_of_adj hab, hbnep, hanep, hab, hbp, hap, by
          have := hdeg4all a ha; have := hdeg4all b hb; have := hisodeg p hpIso; omega⟩
      exact Or.inl (pairToTH (two_hub_maxhub_pair_nineteen G Hub Iso hHub11 hIso8 hdeg4all hiso3
        hdisjHI hadj0))
    · -- **`s = 2 ⟹ |Iso| = 6`: PART A (octahedron corner).**
      have hIso6 : Iso.card = 6 := by rw [hIsocard, hd8, hs2]
      have hNI := hNIof 6 hIso6 (by omega)
      exact two_hub_corner_select_nineteen G Hub Iso hdeg4all hiso3 hisoIndep hdisjHI hHub11 hIso6
        hisodeg h3 hsum44 hNI hshare4 hC4 hK23 hT
  · -- **`|D| = 9 ⟹ |Hub| = 10`, all degree `≤ 5`: PART B.**
    have hHub10 : Hub.card = 10 := by omega
    have hsum41 : ∑ w ∈ Hub, G.degree w = 41 := by rw [hsumHub, hd9]
    have hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5 := by
      intro h hh
      have e1 := Finset.add_sum_erase Hub (fun v => G.degree v) hh
      have hge : 4 * (Hub.erase h).card ≤ ∑ v ∈ Hub.erase h, G.degree v := by
        have hb : ∀ x ∈ Hub.erase h, 4 ≤ G.degree x := fun i hi =>
          (hmemHub i).mp (Finset.mem_of_mem_erase hi)
        have h2 := Finset.card_nsmul_le_sum (Hub.erase h) (fun v => G.degree v) 4 hb
        simpa [smul_eq_mul, mul_comm] using h2
      have hc : (Hub.erase h).card = Hub.card - 1 := Finset.card_erase_of_mem hh
      omega
    rcases hs02 with hs0 | hs2
    · have hIso9 : Iso.card = 9 := by rw [hIsocard, hd9, hs0]
      have hreg : _ := two_hub_corner_select_deg5_nineteen G Hub Iso hdeg hdeg5 hiso3 hshare4 hdisjHI
        (Or.inr (Or.inr (Or.inl ⟨hHub10, hIso9, hsum41⟩))) hC4 hK23
      rcases hreg with hpair | hstar
      · exact Or.inl (pairToTH hpair)
      · exact Or.inl hstar
    · have hIso7 : Iso.card = 7 := by rw [hIsocard, hd9, hs2]
      have hNI := hNIof 7 hIso7 (by omega)
      have hreg : _ := two_hub_corner_select_deg5_nineteen G Hub Iso hdeg hdeg5 hiso3 hshare4 hdisjHI
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hHub10, hIso7, hsum41, h3, hisodeg, hNI, hT⟩)))))
        hC4 hK23
      rcases hreg with hpair | hstar
      · exact Or.inl (pairToTH hpair)
      · exact Or.inl hstar
  · -- **`|D| = 10 ⟹ |Hub| = 9`: deg `≤ 6`; all-`≤ 5` ⟹ PART B, else a deg-`6` corner.**
    have hHub9 : Hub.card = 9 := by omega
    have hsum38 : ∑ w ∈ Hub, G.degree w = 38 := by rw [hsumHub, hd10]
    by_cases hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5
    · rcases hs02 with hs0 | hs2
      · have hIso10 : Iso.card = 10 := by rw [hIsocard, hd10, hs0]
        have hreg : _ := two_hub_corner_select_deg5_nineteen G Hub Iso hdeg hdeg5 hiso3 hshare4
          hdisjHI (Or.inr (Or.inl ⟨hHub9, hIso10, hsum38⟩)) hC4 hK23
        rcases hreg with hpair | hstar
        · exact Or.inl (pairToTH hpair)
        · exact Or.inl hstar
      · have hIso8 : Iso.card = 8 := by rw [hIsocard, hd10, hs2]
        have hNI := hNIof 8 hIso8 (by omega)
        have hreg : _ := two_hub_corner_select_deg5_nineteen G Hub Iso hdeg hdeg5 hiso3 hshare4
          hdisjHI (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hHub9, hIso8, hsum38, h3, hisodeg, hNI, hT⟩))))) hC4 hK23
        rcases hreg with hpair | hstar
        · exact Or.inl (pairToTH hpair)
        · exact Or.inl hstar
    · -- **`|Hub| = 9` with a degree-`6` hub.**  `s = 0 ⟹ (9,10,38)` closes via the
      -- degree-`6`-witness residual selector; `s = 2 ⟹ (9,8,38)` (a single degree-`6` fat hub,
      -- `|R| = 1`) is the fat-centre residual not refuted by counting.
      have hdeg7 : ∀ h ∈ Hub, G.degree h ≤ 7 := by
        intro h hh
        have e1 := Finset.add_sum_erase Hub (fun v => G.degree v) hh
        have hge : 4 * (Hub.erase h).card ≤ ∑ v ∈ Hub.erase h, G.degree v := by
          have hb : ∀ x ∈ Hub.erase h, 4 ≤ G.degree x := fun i hi =>
            (hmemHub i).mp (Finset.mem_of_mem_erase hi)
          have h2 := Finset.card_nsmul_le_sum (Hub.erase h) (fun v => G.degree v) 4 hb
          simpa [smul_eq_mul, mul_comm] using h2
        have hc : (Hub.erase h).card = Hub.card - 1 := Finset.card_erase_of_mem hh
        rw [hHub9] at hc; rw [hsum38] at e1; omega
      have hdeg6ex : ∃ h ∈ Hub, 6 ≤ G.degree h := by
        push Not at hdeg5
        obtain ⟨h, hh, hgt⟩ := hdeg5
        exact ⟨h, hh, by omega⟩
      rcases hs02 with hs0 | hs2
      · have hIso10 : Iso.card = 10 := by rw [hIsocard, hd10, hs0]
        exact Or.inl (pairToTH (deg6_witness_select_nineteen G Hub Iso hdeg hdeg7 hdeg6ex hiso3
          hshare4 hdisjHI (Or.inr (Or.inr ⟨hHub9, hIso10, hsum38⟩))))
      · -- **Residual: `(9,8,38)`, single degree-`6` fat hub (`|R| = 1`, counting ties).**
        -- Closed by the fat-centre-aware off-diagonal double count on the eight degree-`4` hubs:
        -- `∑_{offDiag} share = ∑_t d_t(d_t−1) ≤ 2·18 = 36`, but assuming no good pair forces every
        -- non-adjacent degree-`4` pair to share `≥ 1`, giving `≥ 56 − 10 = 46`, a contradiction.
        have hIso8 : Iso.card = 8 := by rw [hIsocard, hd10, hs2]
        have hhubsum : ∑ w ∈ Hub, (G.neighborFinset w ∩ Hub).card ≤ 10 := by
          have h := hIntEq; rw [hd10, hs2] at h; omega
        exact Or.inl (pairToTH (fat_centre_two_hub_pair_nineteen G Hub Iso hHub9 hIso8 hdeg hdeg7
          hdeg6ex hsum38 hiso3 hshare4 hdisjHI hhubsum))
  · -- **`|D| = 11 ⟹ |Hub| = 8`: deg `≤ 7`; all-`≤ 5` ⟹ PART B, else a deg-`6/7` corner.**
    have hHub8 : Hub.card = 8 := by omega
    have hsum35 : ∑ w ∈ Hub, G.degree w = 35 := by rw [hsumHub, hd11]
    by_cases hdeg5 : ∀ h ∈ Hub, G.degree h ≤ 5
    · rcases hs02 with hs0 | hs2
      · have hIso11 : Iso.card = 11 := by rw [hIsocard, hd11, hs0]
        have hreg : _ := two_hub_corner_select_deg5_nineteen G Hub Iso hdeg hdeg5 hiso3 hshare4
          hdisjHI (Or.inl ⟨hHub8, hIso11, hsum35⟩) hC4 hK23
        rcases hreg with hpair | hstar
        · exact Or.inl (pairToTH hpair)
        · exact Or.inl hstar
      · have hIso9 : Iso.card = 9 := by rw [hIsocard, hd11, hs2]
        have hNI := hNIof 9 hIso9 (by omega)
        have hreg : _ := two_hub_corner_select_deg5_nineteen G Hub Iso hdeg hdeg5 hiso3 hshare4
          hdisjHI (Or.inr (Or.inr (Or.inr (Or.inl ⟨hHub8, hIso9, hsum35, h3, hisodeg, hNI, hT⟩))))
          hC4 hK23
        rcases hreg with hpair | hstar
        · exact Or.inl (pairToTH hpair)
        · exact Or.inl hstar
    · -- **`|Hub| = 8` with a degree-`6/7` hub.**  Both `s = 0 ⟹ (8,11,35)` and
      -- `s = 2 ⟹ (8,9,35)` close via the degree-`6`-witness residual selector.
      have hdeg7 : ∀ h ∈ Hub, G.degree h ≤ 7 := by
        intro h hh
        have e1 := Finset.add_sum_erase Hub (fun v => G.degree v) hh
        have hge : 4 * (Hub.erase h).card ≤ ∑ v ∈ Hub.erase h, G.degree v := by
          have hb : ∀ x ∈ Hub.erase h, 4 ≤ G.degree x := fun i hi =>
            (hmemHub i).mp (Finset.mem_of_mem_erase hi)
          have h2 := Finset.card_nsmul_le_sum (Hub.erase h) (fun v => G.degree v) 4 hb
          simpa [smul_eq_mul, mul_comm] using h2
        have hc : (Hub.erase h).card = Hub.card - 1 := Finset.card_erase_of_mem hh
        rw [hHub8] at hc; rw [hsum35] at e1; omega
      have hdeg6ex : ∃ h ∈ Hub, 6 ≤ G.degree h := by
        push Not at hdeg5
        obtain ⟨h, hh, hgt⟩ := hdeg5
        exact ⟨h, hh, by omega⟩
      rcases hs02 with hs0 | hs2
      · have hIso11 : Iso.card = 11 := by rw [hIsocard, hd11, hs0]
        exact Or.inl (pairToTH (deg6_witness_select_nineteen G Hub Iso hdeg hdeg7 hdeg6ex hiso3
          hshare4 hdisjHI (Or.inl ⟨hHub8, hIso11, hsum35⟩)))
      · have hIso9 : Iso.card = 9 := by rw [hIsocard, hd11, hs2]
        exact Or.inl (pairToTH (deg6_witness_select_nineteen G Hub Iso hdeg hdeg7 hdeg6ex hiso3
          hshare4 hdisjHI (Or.inr (Or.inl ⟨hHub8, hIso9, hsum35⟩))))

/-- **Four-way alignment dichotomy for `n = 19`, `e(M) = 2` (STUB).**
`s = 4`: `M` is a single `P₃` cherry.  Ported from `exists_align_four_config_eighteen`.
**NEW frontier:** the cherry residual now also covers `|D| = 13` (`|Hub| = 6`). -/
theorem exists_align_four_config_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (h2k2 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hiso : ∃ t : Fin 19, G.degree t = 3 ∧ ∀ w : Fin 19, G.Adj t w → G.degree w ≠ 3)
    (hs4 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 4) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  have hT10 : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10 := by
    rintro ⟨x, y, z, hxy, hyz, hxz, hax, hay, haz, hsum⟩
    exact hT ⟨x, y, z, hxy, hyz, hxz, hax, hay, haz, by omega⟩
  set D : Finset (Fin 19) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hdegD : ∀ v : Fin 19, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
  obtain ⟨_hHub10, hD8le⟩ := residual_hub_card_le_eleven G hm h3
  have hne : ∃ a b : Fin 19, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
  rcases dominating_edge_or_induced_C5 G D hmemD hT10 hC4 h2k2 hne with hdom | hC5
  · -- **Dominating-edge branch.**  Rebuild the single `e(M) = 2` cherry `x–y–z` (centre `y`).
    obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hdomprop⟩ := hdom
    have hcen : 2 ≤ (G.neighborFinset c₁ ∩ D).card ∨ 2 ≤ (G.neighborFinset c₂ ∩ D).card := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      have hc2in : c₂ ∈ G.neighborFinset c₁ ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
      have hc1in : c₁ ∈ G.neighborFinset c₂ ∩ D :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
      have h1' : ∀ a ∈ G.neighborFinset c₁ ∩ D, ∀ b ∈ G.neighborFinset c₁ ∩ D, a = b :=
        Finset.card_le_one.mp (by omega)
      have h2' : ∀ a ∈ G.neighborFinset c₂ ∩ D, ∀ b ∈ G.neighborFinset c₂ ∩ D, a = b :=
        Finset.card_le_one.mp (by omega)
      have hzero : ∀ v ∈ D,
          (G.neighborFinset v ∩ D).card ≤ (if v = c₁ ∨ v = c₂ then 1 else 0) := by
        intro v hvD
        by_cases hv : v = c₁ ∨ v = c₂
        · rw [if_pos hv]
          rcases hv with rfl | rfl
          · omega
          · omega
        · rw [if_neg hv, Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro w hw
          rw [Finset.mem_inter, G.mem_neighborFinset] at hw
          obtain ⟨hvw, hwD⟩ := hw
          have hdom4 := hdomprop v w hvD hwD hvw
          push Not at hv
          rcases hdom4 with e | e | e | e
          · exact hv.1 e
          · exact hv.2 e
          · have hvmem : v ∈ G.neighborFinset c₁ ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hvw).symm, hvD⟩
            exact hv.2 (h1' v hvmem c₂ hc2in)
          · have hvmem : v ∈ G.neighborFinset c₂ ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hvw).symm, hvD⟩
            exact hv.1 (h2' v hvmem c₁ hc1in)
      have hsumle : ∑ v ∈ D, (G.neighborFinset v ∩ D).card
          ≤ ∑ v ∈ D, (if v = c₁ ∨ v = c₂ then (1 : ℕ) else 0) := Finset.sum_le_sum hzero
      have hrhs : ∑ v ∈ D, (if v = c₁ ∨ v = c₂ then (1 : ℕ) else 0) ≤ 2 := by
        rw [← Finset.card_filter]
        have hsubset : D.filter (fun v => v = c₁ ∨ v = c₂) ⊆ ({c₁, c₂} : Finset (Fin 19)) := by
          intro v hv
          rw [Finset.mem_filter] at hv
          rcases hv.2 with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        calc (D.filter (fun v => v = c₁ ∨ v = c₂)).card
            ≤ ({c₁, c₂} : Finset (Fin 19)).card := Finset.card_le_card hsubset
          _ ≤ 2 := by
              have := Finset.card_insert_le c₁ ({c₂} : Finset (Fin 19))
              simp only [Finset.card_singleton] at this
              omega
      omega
    have mkcherry : ∀ c : Fin 19, c ∈ D → 2 ≤ (G.neighborFinset c ∩ D).card →
        ∃ x y z : Fin 19, x ∈ D ∧ y ∈ D ∧ z ∈ D ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
          G.Adj x y ∧ G.Adj y z ∧ ¬G.Adj x z := by
      intro c hcD hc2
      obtain ⟨x, hx, z, hz, hxz⟩ :=
        Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset c ∩ D).card)
      rw [Finset.mem_inter, G.mem_neighborFinset] at hx hz
      obtain ⟨hcx, hxD⟩ := hx
      obtain ⟨hcz, hzD⟩ := hz
      refine ⟨x, c, z, hxD, hcD, hzD, (G.ne_of_adj hcx).symm, G.ne_of_adj hcz, hxz,
        hcx.symm, hcz, ?_⟩
      intro hxzAdj
      exact hT10 ⟨x, c, z, (G.ne_of_adj hcx).symm, G.ne_of_adj hcz, hxz, hcx.symm, hcz, hxzAdj, by
        rw [hdegD x hxD, hdegD c hcD, hdegD z hzD]; omega⟩
    obtain ⟨x, y, z, hxD, hyD, hzD, hxy_ne, hyz_ne, hxz_ne, hxyA, hyzA, hxzN⟩ :=
      hcen.elim (fun h => mkcherry c₁ hc1D h) (fun h => mkcherry c₂ hc2D h)
    have hdegx : G.degree x = 3 := hdegD x hxD
    have hdegy : G.degree y = 3 := hdegD y hyD
    have hdegz : G.degree z = 3 := hdegD z hzD
    have hsum64 : ∑ v : Fin 19, G.degree v = 68 := by
      rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
    have hsumDdeg : ∑ v ∈ D, G.degree v = 3 * D.card := by
      rw [Finset.sum_congr rfl (fun v hv => hdegD v hv), Finset.sum_const, smul_eq_mul, mul_comm]
    have hsumsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 68 := by
      rw [Finset.sum_add_sum_compl]; exact hsum64
    have hDcdeg : ∀ w ∈ Dᶜ, 4 ≤ G.degree w := by
      intro w hw; rw [Finset.mem_compl, hmemD] at hw; have := h3 w; omega
    have hcc : D.card + Dᶜ.card = 19 := by
      have h := Finset.card_add_card_compl D; simp only [Fintype.card_fin] at h; exact h
    have hsumDcdeg : ∑ w ∈ Dᶜ, G.degree w = 68 - 3 * D.card := by
      rw [hsumDdeg] at hsumsplit; omega
    have hxyzcard : ({x, y, z} : Finset (Fin 19)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy_ne, hxz_ne]),
        Finset.card_insert_of_notMem (by simp [hyz_ne]), Finset.card_singleton]
    have hsubNI : ({x, y, z} : Finset (Fin 19))
        ⊆ D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_filter]
      rcases hw with rfl | rfl | rfl
      · exact ⟨hxD, Finset.card_ne_zero.mpr
          ⟨y, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w y).mpr hxyA, hyD⟩⟩⟩
      · exact ⟨hyD, Finset.card_ne_zero.mpr
          ⟨x, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w x).mpr hxyA.symm, hxD⟩⟩⟩
      · exact ⟨hzD, Finset.card_ne_zero.mpr
          ⟨y, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w y).mpr hyzA.symm, hyD⟩⟩⟩
    have hNIcard3 : (D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0)).card ≤ 3 := by
      have hnb := nonisolated_component_bound G D hmemD h2k2
      rw [hs4] at hnb; omega
    have hNIeq : ({x, y, z} : Finset (Fin 19))
        = D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0) :=
      Finset.eq_of_subset_of_card_le hsubNI (by rw [hxyzcard]; exact hNIcard3)
    have hDsplit : ∀ w : Fin 19, w ∈ D → w ∉ ({x, y, z} : Finset (Fin 19)) →
        (G.neighborFinset w ∩ D).card = 0 := by
      intro w hwD hwxyz
      by_contra hc
      have hmem : w ∈ D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0) :=
        Finset.mem_filter.mpr ⟨hwD, hc⟩
      rw [← hNIeq] at hmem
      exact hwxyz hmem
    set Iso : Finset (Fin 19) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0)
      with hIsodef
    have hIsoprop : ∀ v ∈ Iso, G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3) := by
      intro v hv
      rw [hIsodef, Finset.mem_filter] at hv
      obtain ⟨hvD, hv0⟩ := hv
      refine ⟨hdegD v hvD, fun w hadj hw3 => ?_⟩
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
      exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
    have hisochar : ∀ w : Fin 19, w ∈ D → w ≠ x → w ≠ y → w ≠ z → w ∈ Iso := by
      intro w hwD hwx hwy hwz
      rw [hIsodef, Finset.mem_filter]
      exact ⟨hwD, hDsplit w hwD (by simp [hwx, hwy, hwz])⟩
    have hcov : ∀ p q : Fin 19, p ∈ D → q ∈ D → G.Adj p q → p = y ∨ q = y := by
      intro p q hpD hqD hpq
      have hpNI : p ∈ ({x, y, z} : Finset (Fin 19)) := by
        rw [hNIeq, Finset.mem_filter]
        exact ⟨hpD, Finset.card_ne_zero.mpr
          ⟨q, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p q).mpr hpq, hqD⟩⟩⟩
      have hqNI : q ∈ ({x, y, z} : Finset (Fin 19)) := by
        rw [hNIeq, Finset.mem_filter]
        exact ⟨hqD, Finset.card_ne_zero.mpr
          ⟨p, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset q p).mpr hpq.symm, hpD⟩⟩⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpNI hqNI
      rcases hpNI with rfl | rfl | rfl
      · rcases hqNI with rfl | rfl | rfl
        · exact (G.irrefl hpq).elim
        · exact Or.inr rfl
        · exact absurd hpq hxzN
      · exact Or.inl rfl
      · rcases hqNI with rfl | rfl | rfl
        · exact absurd hpq.symm hxzN
        · exact Or.inr rfl
        · exact (G.irrefl hpq).elim
    have hNyD : G.neighborFinset y ∩ D = ({x, z} : Finset (Fin 19)) := by
      apply Finset.Subset.antisymm
      · intro w hw
        rw [Finset.mem_inter, G.mem_neighborFinset] at hw
        obtain ⟨hyw, hwD⟩ := hw
        have hwNI : w ∈ ({x, y, z} : Finset (Fin 19)) := by
          rw [hNIeq, Finset.mem_filter]
          exact ⟨hwD, Finset.card_ne_zero.mpr
            ⟨y, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w y).mpr hyw.symm, hyD⟩⟩⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hwNI ⊢
        rcases hwNI with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact (G.irrefl hyw).elim
        · exact Or.inr rfl
      · intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hxyA.symm, hxD⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hyzA, hzD⟩
    by_cases hD8eq : D.card = 8
    · -- **`|D| = 8` (`|Hub| = 10`, all degree `4`): cherry hub-triangle residual.**
      have hdeg4all : ∀ w : Fin 19, w ∈ Dᶜ → G.degree w = 4 := by
        intro w hw
        have hspl := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hw
        have hrest : 4 * (Dᶜ.erase w).card ≤ ∑ v ∈ Dᶜ.erase w, G.degree v := by
          have hb : ∀ i ∈ Dᶜ.erase w, 4 ≤ G.degree i :=
            fun i hi => hDcdeg i (Finset.mem_of_mem_erase hi)
          have := Finset.card_nsmul_le_sum (Dᶜ.erase w) (fun v => G.degree v) 4 hb
          simpa [smul_eq_mul, mul_comm] using this
        have hec : (Dᶜ.erase w).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hw
        have hsum40 : ∑ v ∈ Dᶜ, G.degree v = 44 := by rw [hsumDcdeg, hD8eq]
        have hd4 := hDcdeg w hw
        rw [hsum40] at hspl
        omega
      by_cases hsv : SingleVertexConfig G
      · exact Or.inl hsv
      by_cases htt : TwoTwinConfig G
      · exact Or.inr (Or.inl htt)
      by_cases hth : TwoHubConfig G
      · exact Or.inr (Or.inr (Or.inl hth))
      · exact Or.inr (Or.inr (Or.inr
          (exists_hub_triangle_config_cherry_residual_nineteen G D Iso x y z hmemD hIsodef
            hIsoprop hisochar hcov hNyD hdegx hdegy hdegz hxyA hyzA hxzN hxz_ne hdeg4all
            hD8eq hC4 hT10 hsv htt hth)))
    · -- **`P₃`-cherry residual corners for `|D| ∈ {9, 10, 11}` (`|Hub| ∈ {7, 8, 9}`).**  The single
      -- `e(M) = 2` cherry `x–y–z` (centre `y`) with `|D| ≥ 9`; no `TwinCert18CherryP3` corner
      -- helper is yet available, so these are isolated as documented `sorry`s.  The cross-count
      -- bounds `|D| ≤ 12` (at `s = 4`, `6|D| ≤ 68 + 4 = 72`).
      have hDub : D.card ≤ 12 := by
        have hdsplit : ∀ v : Fin 19,
            (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
          intro v
          have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dᶜ) :=
            Finset.disjoint_left.mpr (fun a ha ha' =>
              (Finset.mem_compl.mp (Finset.mem_inter.mp ha').2) (Finset.mem_inter.mp ha).2)
          have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dᶜ) = G.neighborFinset v := by
            rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
          rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
        have hcongD : ∑ v ∈ D,
            ((G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card)
              = ∑ v ∈ D, G.degree v := Finset.sum_congr rfl (fun v _ => hdsplit v)
        rw [Finset.sum_add_distrib, hs4, hsumDdeg] at hcongD
        have hbound : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card ≤ ∑ w ∈ Dᶜ, G.degree w :=
          Finset.sum_le_sum (fun w _ => by
            calc (G.neighborFinset w ∩ D).card ≤ (G.neighborFinset w).card :=
                  Finset.card_le_card Finset.inter_subset_left
              _ = G.degree w := G.card_neighborFinset_eq_degree w)
        rw [← cross_count_nineteen G D Dᶜ, hsumDcdeg] at hbound
        omega
      -- **`P₃`-cherry residual for `|D| ∈ {9, 10, 11, 12}`.**  The hub set has degree-`3` count
      -- `≥ 8` (`hD8le`), `≠ 8` (`hD8eq`) and `≤ 12` (`hDub`), so `|D| ∈ {9, 10, 11, 12}`; dispatch
      -- to the `TwinCert19CherryP3` corner helpers (`|D| = 12` is the NEW `n = 19` boundary).
      have hDlb : 8 ≤ D.card := hD8le
      have hDval : D.card = 9 ∨ D.card = 10 ∨ D.card = 11 ∨ D.card = 12 := by omega
      rcases hDval with h9 | h10 | h11 | _h12
      · exact cherry_p3_config_D9_nineteen G hm h3 D Iso x y z hmemD hIsoprop hisochar hcov hNyD
          hdegx hdegy hdegz hxyA hyzA hxzN hxy_ne hyz_ne hxz_ne h9 hC4
      · exact cherry_p3_two_hub_D10_nineteen G hm h3 D Iso x y z hmemD hIsoprop hisochar hcov hNyD
          hdegx hdegy hdegz hxyA hyzA hxzN hxy_ne hyz_ne hxz_ne h10
      · exact cherry_p3_config_D11_nineteen G hm h3 D Iso x y z hmemD hIsoprop hisochar hcov hNyD
          hdegx hdegy hdegz hxyA hyzA hxzN hxy_ne hyz_ne hxz_ne h11
      · -- **`|D| = 12` boundary — CLOSED** (`TwinCert19CherryP3D12`): the incidence identity
        -- `27 + 5 + 2e_HH = 32` forces a hub-edge-free hub set; a cherry-avoiding deg-`≤ 5`
        -- hub with two twins gives `TwoTwin`, else the slot/avoider LP forces the
        -- `{6,6,4⁵}` tie and any two deg-`4` hubs assemble `TwoHub`.
        exact cherry_p3_config_D12_nineteen G hm h3 hT hC4 D Iso x y z hmemD hIsoprop
          hisochar hcov hNyD hdegx hdegy hdegz hxyA hyzA hxzN hxy_ne hyz_ne hxz_ne _h12
  · -- **Induced-`C₅` branch is impossible at `e(M) = 2`.**  Each cycle vertex has two `D`-neighbours,
    -- so contributes `≥ 2` to `s`; the five together force `s ≥ 10 > 4`.
    exfalso
    obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
      e12, e23, e34, e45, e51, _n13, _n14, _n24, _n25, _n35, _hdom⟩ := hC5
    obtain ⟨_d12, d13, d14, _d15, _d23, d24, d25, _d34, d35, _d45⟩ :=
      distinct_five_nineteen v₁ v₂ v₃ v₄ v₅ hcard5
    have two_of : ∀ v a b : Fin 19, a ∈ D → b ∈ D → a ≠ b → G.Adj v a → G.Adj v b →
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v a b haD hbD hab hva hvb
      have hsub : ({a, b} : Finset (Fin 19)) ⊆ G.neighborFinset v ∩ D := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hva, haD⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvb, hbD⟩
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_pair hab] at hc
    have hTsub : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 19)) ⊆ D := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hbT : ∀ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 19)),
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact two_of _ v₂ v₅ hv2D hv5D d25 e12 e51.symm
      · exact two_of _ v₁ v₃ hv1D hv3D d13 e12.symm e23
      · exact two_of _ v₂ v₄ hv2D hv4D d24 e23.symm e34
      · exact two_of _ v₃ v₅ hv3D hv5D d35 e34.symm e45
      · exact two_of _ v₄ v₁ hv4D hv1D d14.symm e45.symm e51
    have hsumT : 10 ≤ ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 19)),
        (G.neighborFinset v ∩ D).card := by
      have h := Finset.card_nsmul_le_sum ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 19))
        (fun v => (G.neighborFinset v ∩ D).card) 2 hbT
      rw [hcard5] at h
      simpa using h
    have hmono : ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 19)),
        (G.neighborFinset v ∩ D).card ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
      Finset.sum_le_sum_of_subset hTsub
    omega

/-- **Four-way alignment dichotomy for `n = 19`, `e(M) = 3` (STUB).**
`s = 6`: `M` is a `P₄` path.  Ported from `exists_align_six_config_eighteen`.
**NEW frontier:** the `P₄` residual now also covers `|D| = 13` (`|Hub| = 6`). -/
theorem exists_align_six_config_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (h2k2 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hiso : ∃ t : Fin 19, G.degree t = 3 ∧ ∀ w : Fin 19, G.Adj t w → G.degree w ≠ 3)
    (hs6 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 6) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  have hT10 : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10 := by
    rintro ⟨x, y, z, hxy, hyz, hxz, hax, hay, haz, hsum⟩
    exact hT ⟨x, y, z, hxy, hyz, hxz, hax, hay, haz, by omega⟩
  set D : Finset (Fin 19) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hdegD : ∀ v : Fin 19, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
  have hindle : ∀ x : Fin 19, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := (hmemD x).mp hx
  obtain ⟨_hHub11, hD8le⟩ := residual_hub_card_le_eleven G hm h3
  rw [← hDdef] at hD8le
  have hs6le : ∑ v ∈ D, (G.neighborFinset v ∩ D).card ≤ 6 := by omega
  -- A shared degree-`4` hub of two `M`-isolated twins (available since `s = 6 ≤ 6`).
  have hshare : ∃ h t₁ t₂ : Fin 19, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 19, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 19, G.Adj t₂ w → G.degree w ≠ 3) := by
    by_cases hg5 : ∃ g : Fin 19, 5 ≤ G.degree g
    · obtain ⟨g, hg5'⟩ := hg5
      exact shared_deg4_hub_deg5_nineteen G hm h3 hT10 hC4 h2k2 hs6le g hg5'
    · push Not at hg5
      exact shared_deg4_hub_nodeg5_nineteen G hm h3 h2k2 (fun v => by have := hg5 v; omega) hs6le
  obtain ⟨k, t₁, t₂, hkdeg4, ht12, ht1deg, ht2deg, hAt1k, hAt2k, ht1iso, ht2iso⟩ := hshare
  -- An `M`-edge exists, since `s = 6 > 0`.
  have hne : ∃ a b : Fin 19, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
  rcases dominating_edge_or_induced_C5 G D hmemD hT10 hC4 h2k2 hne with hdom | hC5
  · -- **Dominating-edge branch.**
    obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hdom
    by_cases hc1three : 3 ≤ (G.neighborFinset c₁ ∩ D).card
    · exact Or.inr (Or.inl (claw_shared_two_twin_nineteen G D hmemD hT10 hC4 c₁ t₁ t₂ k hc1D
        hc1three ht1deg ht2deg hkdeg4 ht12 hAt1k hAt2k ht1iso ht2iso))
    · by_cases hc2three : 3 ≤ (G.neighborFinset c₂ ∩ D).card
      · exact Or.inr (Or.inl (claw_shared_two_twin_nineteen G D hmemD hT10 hC4 c₂ t₁ t₂ k hc2D
          hc2three ht1deg ht2deg hkdeg4 ht12 hAt1k hAt2k ht1iso ht2iso))
      · -- **`P₄` case.**  Both endpoints have in-`M`-degree `2`.
        set Iso : Finset (Fin 19) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0)
          with hIsodef
        have hIsoprop : ∀ v ∈ Iso,
            G.degree v = 3 ∧ (∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3) := by
          intro v hv
          rw [hIsodef, Finset.mem_filter] at hv
          obtain ⟨hvD, hv0⟩ := hv
          refine ⟨hdegD v hvD, fun w hadj hw3 => ?_⟩
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
          exact hv0 w (Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
        have hsum64 : ∑ v : Fin 19, G.degree v = 68 := by
          rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
        have hsumDt : ∑ v ∈ D, G.degree v = 3 * D.card := by
          rw [Finset.sum_congr rfl (fun v hv => hdegD v hv), Finset.sum_const, smul_eq_mul,
            mul_comm]
        have hcc : D.card + Dᶜ.card = 19 := by
          have h := Finset.card_add_card_compl D; simp only [Fintype.card_fin] at h; exact h
        have hsumsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 68 := by
          rw [Finset.sum_add_sum_compl]; exact hsum64
        have hDcdeg : ∀ w ∈ Dᶜ, 4 ≤ G.degree w := by
          intro w hw; rw [Finset.mem_compl, hmemD] at hw; have := h3 w; omega
        have hsumDcdeg : ∑ w ∈ Dᶜ, G.degree w = 68 - 3 * D.card := by
          rw [hsumDt] at hsumsplit; omega
        -- In-`M`-degrees of the endpoints are both `2`.
        have hform := thin_eM_formula_nineteen G D c₁ c₂ hc1D hc2D hc12 hcov
        rw [hs6] at hform
        have hin1 : (G.neighborFinset c₁ ∩ D).card = 2 := by
          have := hindle c₁ hc1D; have := hindle c₂ hc2D; omega
        have hin2 : (G.neighborFinset c₂ ∩ D).card = 2 := by
          have := hindle c₁ hc1D; have := hindle c₂ hc2D; omega
        have hc1deg : G.degree c₁ = 3 := hdegD c₁ hc1D
        have hc2deg : G.degree c₂ = 3 := hdegD c₂ hc2D
        have hc2mem1 : c₂ ∈ G.neighborFinset c₁ ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12, hc2D⟩
        have hc1mem2 : c₁ ∈ G.neighborFinset c₂ ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hc12.symm, hc1D⟩
        have herase1 : ((G.neighborFinset c₁ ∩ D).erase c₂).card = 1 := by
          rw [Finset.card_erase_of_mem hc2mem1, hin1]
        have herase2 : ((G.neighborFinset c₂ ∩ D).erase c₁).card = 1 := by
          rw [Finset.card_erase_of_mem hc1mem2, hin2]
        obtain ⟨L₁, hL1eq⟩ := Finset.card_eq_one.mp herase1
        obtain ⟨L₂, hL2eq⟩ := Finset.card_eq_one.mp herase2
        have hNc1D : G.neighborFinset c₁ ∩ D = {c₂, L₁} := by
          rw [← Finset.insert_erase hc2mem1, hL1eq]
        have hNc2D : G.neighborFinset c₂ ∩ D = {c₁, L₂} := by
          rw [← Finset.insert_erase hc1mem2, hL2eq]
        have hL1mem : L₁ ∈ (G.neighborFinset c₁ ∩ D).erase c₂ := by rw [hL1eq]; simp
        rw [Finset.mem_erase] at hL1mem
        obtain ⟨hL1nc2, hL1ND⟩ := hL1mem
        obtain ⟨hL1N, hL1D⟩ := Finset.mem_inter.mp hL1ND
        have hac1L1 : G.Adj c₁ L₁ := (G.mem_neighborFinset _ _).mp hL1N
        have hL1deg : G.degree L₁ = 3 := hdegD L₁ hL1D
        have hL2mem : L₂ ∈ (G.neighborFinset c₂ ∩ D).erase c₁ := by rw [hL2eq]; simp
        rw [Finset.mem_erase] at hL2mem
        obtain ⟨hL2nc1, hL2ND⟩ := hL2mem
        obtain ⟨hL2N, hL2D⟩ := Finset.mem_inter.mp hL2ND
        have hac2L2 : G.Adj c₂ L₂ := (G.mem_neighborFinset _ _).mp hL2N
        have hL2deg : G.degree L₂ = 3 := hdegD L₂ hL2D
        have hnL1c2 : ¬G.Adj L₁ c₂ := fun hadj =>
          hT10 ⟨c₁, L₁, c₂, hac1L1.ne, hL1nc2, hc12.ne, hac1L1, hadj, hc12, by omega⟩
        have hnc1L2 : ¬G.Adj c₁ L₂ := fun hadj =>
          hT10 ⟨c₂, L₂, c₁, hac2L2.ne, hL2nc1, hc12.ne.symm, hac2L2, hadj.symm, hc12.symm, by omega⟩
        have hisochar : ∀ w : Fin 19, w ∈ D → w ≠ L₁ → w ≠ c₁ → w ≠ c₂ → w ≠ L₂ → w ∈ Iso := by
          intro w hwD hwL1 hwc1 hwc2 hwL2
          rw [hIsodef, Finset.mem_filter]
          refine ⟨hwD, ?_⟩
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro u hu
          rw [Finset.mem_inter, G.mem_neighborFinset] at hu
          obtain ⟨hwu, huD⟩ := hu
          rcases hcov w u hwD huD hwu with e | e | e | e
          · exact hwc1 e
          · exact hwc2 e
          · have hmem : w ∈ G.neighborFinset c₁ ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hwu).symm, hwD⟩
            rw [hNc1D] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h'
            · exact hwc2 h'
            · exact hwL1 h'
          · have hmem : w ∈ G.neighborFinset c₂ ∩ D :=
              Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (e ▸ hwu).symm, hwD⟩
            rw [hNc2D] at hmem
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h' | h'
            · exact hwc1 h'
            · exact hwL2 h'
        by_cases hD8eq : D.card = 8
        · -- **`|D| = 8` (`|Hub| = 11`) corner.**  All eleven hubs have degree `4`.
          have hdeg4all : ∀ w : Fin 19, w ∈ Dᶜ → G.degree w = 4 := by
            intro w hw
            have hspl := Finset.add_sum_erase Dᶜ (fun v => G.degree v) hw
            have hrest : 4 * (Dᶜ.erase w).card ≤ ∑ v ∈ Dᶜ.erase w, G.degree v := by
              have hb : ∀ i ∈ Dᶜ.erase w, 4 ≤ G.degree i :=
                fun i hi => hDcdeg i (Finset.mem_of_mem_erase hi)
              have := Finset.card_nsmul_le_sum (Dᶜ.erase w) (fun v => G.degree v) 4 hb
              simpa [smul_eq_mul, mul_comm] using this
            have hec : (Dᶜ.erase w).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hw
            have hsum44 : ∑ v ∈ Dᶜ, G.degree v = 44 := by rw [hsumDcdeg, hD8eq]
            have hd4 := hDcdeg w hw
            rw [hsum44] at hspl
            omega
          have hK23' : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
              G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
              ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
              G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 18 := by
            rintro ⟨a, b, c, d, e, hcard, hac, had, hae, hbc, hbd, hbe, hab, hcd, hce, hde, hsum⟩
            exact hK23 ⟨a, b, c, d, e, hcard, hac, had, hae, hbc, hbd, hbe, hab, hcd, hce, hde,
              by omega⟩
          by_cases hsv : SingleVertexConfig G
          · exact Or.inl hsv
          by_cases htt : TwoTwinConfig G
          · exact Or.inr (Or.inl htt)
          by_cases hth : TwoHubConfig G
          · exact Or.inr (Or.inr (Or.inl hth))
          · exact Or.inr (Or.inr (Or.inr (exists_hub_triangle_config_residual_nineteen G D Iso
              L₁ c₁ c₂ L₂ hT hC4 hK23' hmemD hIsodef hIsoprop hisochar hcov hNc1D hNc2D
              hc1deg hc2deg hL1deg hL2deg hac1L1 hc12 hac2L2 hnL1c2 hnc1L2
              hL1nc2 hL2nc1 hdeg4all hD8eq hsv htt hth)))
        · -- **`P₄` residual corners for `|D| ∈ {9, 10, 11, 12}` (`|Hub| ∈ {7, …, 10}`).**
          have hDub : D.card ≤ 12 := by
            have hdsplit : ∀ v : Fin 19,
                (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
              intro v
              have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dᶜ) :=
                Finset.disjoint_left.mpr (fun a ha ha' =>
                  (Finset.mem_compl.mp (Finset.mem_inter.mp ha').2) (Finset.mem_inter.mp ha).2)
              have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dᶜ)
                  = G.neighborFinset v := by
                rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
              rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
            have hcongD : ∑ v ∈ D,
                ((G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card)
                  = ∑ v ∈ D, G.degree v := Finset.sum_congr rfl (fun v _ => hdsplit v)
            rw [Finset.sum_add_distrib, hs6, hsumDt] at hcongD
            have hbound : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card ≤ ∑ w ∈ Dᶜ, G.degree w :=
              Finset.sum_le_sum (fun w _ => by
                calc (G.neighborFinset w ∩ D).card ≤ (G.neighborFinset w).card :=
                      Finset.card_le_card Finset.inter_subset_left
                  _ = G.degree w := G.card_neighborFinset_eq_degree w)
            rw [← cross_count_nineteen G D Dᶜ, hsumDcdeg] at hbound
            omega
          have hDval : D.card = 9 ∨ D.card = 10 ∨ D.card = 11 ∨ D.card = 12 := by omega
          rcases hDval with h9 | h10 | h11 | h12
          · exact cherry_p4_config_D9_nineteen G hm h3 hT10 hC4 L₁ c₁ c₂ L₂ D Iso hmemD hIsoprop
              hisochar hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D
              hin1 hin2 hs6 h9
          · exact cherry_p4_config_D10_nineteen G hm h3 hT10 hC4 L₁ c₁ c₂ L₂ D Iso hmemD hIsoprop
              hisochar hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D
              hin1 hin2 hs6 h10
          · exact cherry_p4_config_D11_nineteen G hm h3 hT10 hC4 L₁ c₁ c₂ L₂ D Iso hmemD hIsoprop
              hisochar hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1 hNc1D hNc2D
              hin1 hin2 hs6 h11
          · -- **`|D| = 12` (`|Hub| = 7`) `P₄` residual — CLOSED** (`TwinCert19CherryP4D12`):
            -- the slot supply (`|N(cᵢ) ∩ Hub| = 1` each) makes the blocked world infeasible
            -- (`slots(W) ≥ 2|W| − 2` against `Σ_Hub |N ∩ B| = 6`), so a degree-`≤ 5` hub with
            -- two `M`-isolated twins avoiding an induced `P₃` of the path always exists —
            -- `TwoTwinConfig`.
            exact cherry_p4_config_D12_nineteen G hm h3 hT10 hC4 L₁ c₁ c₂ L₂ D Iso hmemD
              hIsoprop hisochar hL1deg hc1deg hc2deg hL2deg hac1L1 hc12 hac2L2 hL1nc2 hL2nc1
              hNc1D hNc2D hin1 hin2 hs6 h12
  · -- **Induced-`C₅` branch is impossible at `e(M) = 3`.**
    exfalso
    obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
      e12, e23, e34, e45, e51, _n13, _n14, _n24, _n25, _n35, _hdom⟩ := hC5
    obtain ⟨_d12, d13, d14, _d15, _d23, d24, d25, _d34, d35, _d45⟩ :=
      distinct_five_nineteen v₁ v₂ v₃ v₄ v₅ hcard5
    have two_of : ∀ v a b : Fin 19, a ∈ D → b ∈ D → a ≠ b → G.Adj v a → G.Adj v b →
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v a b haD hbD hab hva hvb
      have hsub : ({a, b} : Finset (Fin 19)) ⊆ G.neighborFinset v ∩ D := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hva, haD⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvb, hbD⟩
      have hc := Finset.card_le_card hsub
      rwa [Finset.card_pair hab] at hc
    have hTsub : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 19)) ⊆ D := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hbT : ∀ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 19)),
        2 ≤ (G.neighborFinset v ∩ D).card := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact two_of _ v₂ v₅ hv2D hv5D d25 e12 e51.symm
      · exact two_of _ v₁ v₃ hv1D hv3D d13 e12.symm e23
      · exact two_of _ v₂ v₄ hv2D hv4D d24 e23.symm e34
      · exact two_of _ v₃ v₅ hv3D hv5D d35 e34.symm e45
      · exact two_of _ v₄ v₁ hv4D hv1D d14.symm e45.symm e51
    have hsumT : 10 ≤ ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 19)),
        (G.neighborFinset v ∩ D).card := by
      have h := Finset.card_nsmul_le_sum ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 19))
        (fun v => (G.neighborFinset v ∩ D).card) 2 hbT
      rw [hcard5] at h
      simpa using h
    have hmono : ∑ v ∈ ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 19)),
        (G.neighborFinset v ∩ D).card ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
      Finset.sum_le_sum_of_subset hTsub
    omega

/-- **Four-way alignment dichotomy for `n = 19`, `e(M) ≥ 4` (STUB).**
`s ∈ {8, 10}`: `M` is dense.  Ported from `halign8_eighteen`.  **NEW frontier:** at `e(M) = 5`
(`s = 10`) the densest case `|D| = 13` (`|Hub| = 6`) appears, the boundary `6·13 = 78 = 68 + 10`. -/
theorem halign8_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (h2k2 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hiso : ∃ t : Fin 19, G.degree t = 3 ∧ ∀ w : Fin 19, G.Adj t w → G.degree w ≠ 3)
    (hge : 8 ≤ ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card) :
    SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨ HubTriangleConfig G := by
  classical
  have hT10 : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10 := by
    rintro ⟨x, y, z, hxy, hyz, hxz, hax, hay, haz, hsum⟩
    exact hT ⟨x, y, z, hxy, hyz, hxz, hax, hay, haz, by omega⟩
  set D : Finset (Fin 19) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set s : ℕ := ∑ v ∈ D, (G.neighborFinset v ∩ D).card with hsdef
  have hle10 : s ≤ 10 := by rw [hsdef]; exact eM_le_five G D hmemD hT10 hC4 h2k2
  have heven : Even s := by rw [hsdef]; exact eM_even G D
  by_cases hD13 : D.card = 13
  · -- **`|D| = 13` (`|Hub| = 6`).**  The dedicated `|Hub| = 6` selector covers both `e(M) = 4`
    -- and `e(M) = 5`; reorder its disjunction into the standard order.
    have hHub6 : (Finset.univ.filter (fun v : Fin 19 => 4 ≤ G.degree v)).card = 6 := by
      have heq : Finset.univ.filter (fun v : Fin 19 => 4 ≤ G.degree v) = Dᶜ := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, hmemD]
        have := h3 w; omega
      rw [heq, Finset.card_compl, Fintype.card_fin, hD13]
    rcases two_hub_or_single_vertex_hub6_nineteen G hm h3 hT10 h2k2 hC4 hK23 hiso hD13 hHub6 hge with
      hth | hsv | htt | hht
    · exact Or.inr (Or.inr (Or.inl hth))
    · exact Or.inl hsv
    · exact Or.inr (Or.inl htt)
    · exact Or.inr (Or.inr (Or.inr hht))
  · -- **`|D| ∈ {8, …, 12}`.**  Split on `e(M)` (`s ∈ {8, 10}` by evenness, `hge`, `hle10`).
    by_cases hsum10 : s = 10
    · exact halign8_eM5_nineteen G hm h3 hT10 h2k2 hC4 hK23 hiso hsum10
    · have hs8 : s = 8 := by obtain ⟨k, hk⟩ := heven; omega
      exact halign8_eM4_nineteen G hm h3 hT10 h2k2 hC4 hK23 hiso hs8

/-! ## The dispatch (sorry-free, axiom-clean) -/

/-- **Twin signed-cut existence for `n = 19` (structural assembly).**  In the sparse-hub residual
(`δ ≥ 3`, no good triangle of degree-sum `≤ 11`, no induced `2K₂` on degree-`3` vertices, no good
`C₄` of degree-sum `≤ 14`, no good `K_{2,3}` of degree-sum `≤ 19`, with an `M`-isolated degree-`3`
vertex) one produces a signed cut `P, N` with `4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4·|P|`.

The dispatch case-splits on `s := 2·e(M) ∈ {0, 2, 4, 6, 8, 10}` (`eM_even`, `eM_le_five`) and routes
through the four alignment dichotomies, each followed by its `_to_cut` boundary certificate.  The
dispatch is sorry-free; the five `_to_cut` certificates are proved (`TwinCert19Cert`), so only the
four alignment dichotomies remain as documented `sorry` stubs. -/
theorem exists_twin_signed_cert_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 11)
    (h2k2 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hK23 : ¬∃ a b c d e : Fin 19, ({a, b, c, d, e} : Finset (Fin 19)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hiso : ∃ t : Fin 19, G.degree t = 3 ∧ ∀ w : Fin 19, G.Adj t w → G.degree w ≠ 3) :
    ∃ P N : Finset (Fin 19), Disjoint P N ∧ P.card = N.card ∧ 0 < P.card ∧
      4 * (∑ p ∈ P, (G.neighborFinset p ∩ N).card)
        + (∑ p ∈ P, (G.neighborFinset p \ (P ∪ N)).card)
        + (∑ q ∈ N, (G.neighborFinset q \ (P ∪ N)).card)
      ≤ 4 * P.card := by
  classical
  set D : Finset (Fin 19) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  -- Bridge the good-triangle threshold `≤ 11` down to the `≤ 10` form used by the `Core` lemmas.
  have hT10 : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10 := by
    rintro ⟨x, y, z, hxy, hyz, hxz, hax, hay, haz, hsum⟩
    exact hT ⟨x, y, z, hxy, hyz, hxz, hax, hay, haz, by omega⟩
  set s : ℕ := ∑ v ∈ D, (G.neighborFinset v ∩ D).card with hsdef
  have heven : Even s := by rw [hsdef]; exact eM_even G D
  have hle10 : s ≤ 10 := by rw [hsdef]; exact eM_le_five G D hmemD hT10 hC4 h2k2
  rcases Nat.lt_or_ge s 4 with hlt4 | hge4
  · -- `e(M) ≤ 1` (`s < 4`, sharpened to `s ≤ 2` by evenness): two-hub opposite-twin cut.
    have hle2 : s ≤ 2 := by obtain ⟨k, hk⟩ := heven; omega
    rcases two_hub_config_nineteen G hm h3 hT h2k2 hC4 hK23 hiso hle2 with hth | hstar
    · exact twoHubConfig_to_cut G hth
    · exact starTriangleConfig_to_cut G hstar
  · -- `e(M) ≥ 2` (`s ≥ 4`): four-way alignment dichotomy, split by the value of `e(M)`.
    by_cases hle4 : s ≤ 4
    · -- `e(M) = 2` (`s = 4`).
      have hs4 : s = 4 := by omega
      have halign : SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨
          HubTriangleConfig G :=
        exists_align_four_config_nineteen G hm h3 hT h2k2 hC4 hK23 hiso hs4
      rcases halign with hsv | htt | hth | hht
      · exact singleVertexConfig_to_cut G hsv
      · exact twoTwinConfig_to_cut G htt
      · exact twoHubConfig_to_cut G hth
      · exact hubTriangleConfig_to_cut G hht
    · by_cases hle6 : s ≤ 6
      · -- `e(M) = 3` (`s = 6`).
        have hs6 : s = 6 := by obtain ⟨k, hk⟩ := heven; omega
        have halign : SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨
            HubTriangleConfig G :=
          exists_align_six_config_nineteen G hm h3 hT h2k2 hC4 hK23 hiso hs6
        rcases halign with hsv | htt | hth | hht
        · exact singleVertexConfig_to_cut G hsv
        · exact twoTwinConfig_to_cut G htt
        · exact twoHubConfig_to_cut G hth
        · exact hubTriangleConfig_to_cut G hht
      · -- `e(M) ≥ 4` (`s ≥ 8`).
        have hge8 : 8 ≤ s := by obtain ⟨k, hk⟩ := heven; omega
        have halign : SingleVertexConfig G ∨ TwoTwinConfig G ∨ TwoHubConfig G ∨
            HubTriangleConfig G :=
          halign8_nineteen G hm h3 hT h2k2 hC4 hK23 hiso hge8
        rcases halign with hsv | htt | hth | hht
        · exact singleVertexConfig_to_cut G hsv
        · exact twoTwinConfig_to_cut G htt
        · exact twoHubConfig_to_cut G hth
        · exact hubTriangleConfig_to_cut G hht

end N19

end ACMax
