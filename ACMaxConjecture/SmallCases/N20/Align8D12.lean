import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.Align8Helpers
import ACMaxConjecture.SmallCases.N20.TwoHubHub6Deg5

/-!
# The `|D| = 12`, `e(M) = 5` handler for the `n = 20` Align8 chain

At `n = 20`, `e(M) = 5` (`s = 10`), the degree-`≤ 5` shared-hub pigeonhole of
`shared_hub_le5_eM5_mid_twenty` *ties* exactly at `|D| = 12` (`18 − |D| = |D| − 6`): two
degree-`6` hubs adjacent to all six `M`-isolated twins (the `K_{2,6}` world) absorb `12` of the
`18` isolated-twin incidences, leaving exactly one per degree-`4` hub.  This file closes that
boundary with two handlers:

* `eM5_D12_c5_shared_twenty` — the induced-`C₅` branch.  The `C₅` is exactly the `M`-non-isolated
  set, so `|Iso| ≥ |D| − 5 = 7` and the refined count `hub5_iso_count_twenty` keeps the
  pigeonhole strict: a degree-`≤ 5` hub shared by two `M`-isolated twins exists.

* `eM5_D12_domedge_shared_or_two_hub_twenty` — the dominating-edge branch, where the tie is
  genuine.  If no degree-`≤ 5` shared hub exists, the tight count forces the rigid structure:
  `|H₆| = 2` with both hubs of degree exactly `6` and `N(A) = N(Z) = Iso` (the `K_{2,6}`), six
  degree-`4` hubs with exactly one `M`-isolated twin each, and the balanced double-star
  `c₁–c₂` with two leaves per centre, each leaf carrying two degree-`4` hubs.  Same-centre
  leaves have disjoint hub sets (the `ℓ–h–ℓ'–c` induced `C₄` has degree sum `13 ≤ 14`).  If some
  cross pair (a hub of `ℓ₁`, a hub of `ℓ₂`) is non-adjacent, it assembles `TwoHubConfig` with the
  two iso-twins and the two `c₁`-leaves; otherwise the four cross edges saturate all four hub
  neighbourhoods (`deg = 4` = leaf + two cross hubs + iso twin), so the hub sets of `ℓ₃, ℓ₄`
  live in the remaining `6 − 4 = 2` degree-`4` hubs and must intersect — a shared hub between
  same-centre leaves, contradicting the `C₄` certificate.
-/

namespace ACMax

open scoped Classical

namespace N20

set_option maxHeartbeats 1000000 in
/-- **The `|D| = 12` induced-`C₅` shared-hub extraction (`e(M) = 5`, `n = 20`).**  The `C₅`
accounts for all ten `M`-incidences, so `|Iso| ≥ |D| − 5 = 7`; the refined handshake count
`hub5_iso_count_twenty` (`|Hub₅| + 2 ≤ ∑_{Iso}|N ∩ Hub₅|`, valid for all `|D| ≥ 11` under this
isolation bound) keeps the degree-`≤ 5` pigeonhole strict at `|D| = 12`, unlike the double-star
branch where it ties. -/
theorem eM5_D12_c5_shared_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hD12 : (Finset.univ.filter (fun w : Fin 20 => G.degree w = 3)).card = 12)
    (v₁ v₂ v₃ v₄ v₅ : Fin 20)
    (hv1D : G.degree v₁ = 3) (hv2D : G.degree v₂ = 3) (hv3D : G.degree v₃ = 3)
    (hv4D : G.degree v₄ = 3) (hv5D : G.degree v₅ = 3)
    (hcard5 : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 20)).card = 5)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e34 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w : Fin 20 => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w : Fin 20 => G.degree w = 3)).card
        = 10) :
    ∃ k tw₁ tw₂ : Fin 20, G.degree k ≤ 5 ∧ tw₁ ≠ tw₂ ∧
      G.degree tw₁ = 3 ∧ G.degree tw₂ = 3 ∧ G.Adj tw₁ k ∧ G.Adj tw₂ k ∧
      (∀ w : Fin 20, G.Adj tw₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 20, G.Adj tw₂ w → G.degree w ≠ 3) := by
  classical
  set D : Finset (Fin 20) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 20) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 20, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  set Hub5 : Finset (Fin 20) :=
    Finset.univ.filter (fun v => 4 ≤ G.degree v ∧ G.degree v ≤ 5) with hHub5def
  have hmemHub5 : ∀ v : Fin 20, v ∈ Hub5 ↔ 4 ≤ G.degree v ∧ G.degree v ≤ 5 := by
    intro v; rw [hHub5def]; simp
  set H6 : Finset (Fin 20) := Finset.univ.filter (fun v => 6 ≤ G.degree v) with hH6def
  have hmemH6 : ∀ v : Fin 20, v ∈ H6 ↔ 6 ≤ G.degree v := by intro v; rw [hH6def]; simp
  set Iso : Finset (Fin 20) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3 := by
    intro v hv
    rw [hIsodef, Finset.mem_filter] at hv
    obtain ⟨hvD, hv0⟩ := hv
    refine ⟨(hmemD v).mp hvD, fun w hadj hw3 => ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
    exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
  have hIsoge : D.card - 5 ≤ Iso.card := by
    have hnon5 := nonIso_le_five_of_C5_twenty G D v₁ v₂ v₃ v₄ v₅
      ((hmemD v₁).mpr hv1D) ((hmemD v₂).mpr hv2D) ((hmemD v₃).mpr hv3D) ((hmemD v₄).mpr hv4D)
      ((hmemD v₅).mpr hv5D) hcard5 e12 e23 e34 e45 e51 hsum10
    have hpart := Finset.card_filter_add_card_filter_not (s := D)
      (fun v => (G.neighborFinset v ∩ D).card = 0)
    rw [← hIsodef] at hpart
    omega
  have hcount2 : Hub5.card + 2 ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card :=
    hub5_iso_count_twenty G D Hub Hub5 H6 Iso hmemD hmemHub hmemHub5 hmemH6 hIsodef hm h3
      (by omega) hIsoge
  have hHub5deg : ∀ h ∈ Hub5, G.degree h ≤ 5 := fun h hh => ((hmemHub5 h).mp hh).2
  obtain ⟨k, t₁, t₂, _, hd5, hne, hd1, hd2, ha1, ha2, hi1, hi2⟩ :=
    shared_hub_le5_from_count_twenty G Iso Hub5 hIsoiso hHub5deg (by omega)
  exact ⟨k, t₁, t₂, hd5, hne, hd1, hd2, ha1, ha2, hi1, hi2⟩

set_option maxHeartbeats 1000000 in
/-- **The `|D| = 12` dominating-edge dichotomy (`e(M) = 5`, `n = 20`): a degree-`≤ 5` shared hub
or `TwoHubConfig`.**  This is the genuine `K_{2,6}` tie: if no degree-`≤ 5` hub carries two
`M`-isolated twins, the `18` isolated-twin incidences against the handshake
(`∑_Hub deg = 36` over `8` hubs) force `|H₆| = 2` with `N(A) = N(Z) = Iso` and six degree-`4`
hubs with exactly one iso twin each.  The balanced double-star's same-centre leaves have
disjoint hub sets (`C₄` of degree sum `13`); a non-adjacent cross pair of `ℓ₁`/`ℓ₂` hubs
assembles `TwoHubConfig` from the two iso twins and the two `c₁`-leaves, and the fully-adjacent
alternative saturates all four hub neighbourhoods, pinning the hub sets of `ℓ₃, ℓ₄` inside the
remaining two degree-`4` hubs — a shared same-centre hub, contradicting `hC4`. -/
theorem eM5_D12_domedge_shared_or_two_hub_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hD12 : (Finset.univ.filter (fun w : Fin 20 => G.degree w = 3)).card = 12)
    (c₁ c₂ : Fin 20) (hc1D : G.degree c₁ = 3) (hc2D : G.degree c₂ = 3)
    (hc12 : G.Adj c₁ c₂)
    (hcov : ∀ p q : Fin 20, G.degree p = 3 → G.degree q = 3 → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w : Fin 20 => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w : Fin 20 => G.degree w = 3)).card
        = 10) :
    (∃ k tw₁ tw₂ : Fin 20, G.degree k ≤ 5 ∧ tw₁ ≠ tw₂ ∧
      G.degree tw₁ = 3 ∧ G.degree tw₂ = 3 ∧ G.Adj tw₁ k ∧ G.Adj tw₂ k ∧
      (∀ w : Fin 20, G.Adj tw₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 20, G.Adj tw₂ w → G.degree w ≠ 3)) ∨ TwoHubConfig G := by
  classical
  by_cases hshared : ∃ k tw₁ tw₂ : Fin 20, G.degree k ≤ 5 ∧ tw₁ ≠ tw₂ ∧
      G.degree tw₁ = 3 ∧ G.degree tw₂ = 3 ∧ G.Adj tw₁ k ∧ G.Adj tw₂ k ∧
      (∀ w : Fin 20, G.Adj tw₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 20, G.Adj tw₂ w → G.degree w ≠ 3)
  · exact Or.inl hshared
  right
  set D : Finset (Fin 20) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hindle : ∀ x : Fin 20, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := (hmemD x).mp hx
  have hc1Dm : c₁ ∈ D := (hmemD c₁).mpr hc1D
  have hc2Dm : c₂ ∈ D := (hmemD c₂).mpr hc2D
  have hcov' : ∀ p q : Fin 20, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂ :=
    fun p q hp hq => hcov p q ((hmemD p).mp hp) ((hmemD q).mp hq)
  obtain ⟨hin1, hin2⟩ := dom_centres_indeg3 G D c₁ c₂ hc1Dm hc2Dm hc12 hindle hcov' hsum10
  obtain ⟨l₁, l₂, l₃, l₄, hd1, hd2, hd3, hd4, hcard6, ha1, ha2, ha3, ha4,
      hND1, hND2, hND3, hND4, -, -, -, -, hl12, hl34⟩ :=
    dom_doublestar_leaves G D hmemD hT c₁ c₂ hc1Dm hc2Dm hc12 hin1 hin2 hcov'
  have hl1D : l₁ ∈ D := (hmemD l₁).mpr hd1
  have hl2D : l₂ ∈ D := (hmemD l₂).mpr hd2
  have hl3D : l₃ ∈ D := (hmemD l₃).mpr hd3
  have hl4D : l₄ ∈ D := (hmemD l₄).mpr hd4
  -- distinctness of the six double-star vertices used below
  have hl1c2 : l₁ ≠ c₂ := by
    intro e
    have h3m : l₃ ∈ G.neighborFinset l₁ ∩ D := by
      rw [e]
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha3, hl3D⟩
    have h4m : l₄ ∈ G.neighborFinset l₁ ∩ D := by
      rw [e]
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha4, hl4D⟩
    rw [hND1, Finset.mem_singleton] at h3m h4m
    exact hl34 (h3m.trans h4m.symm)
  have hl2c2 : l₂ ≠ c₂ := by
    intro e
    have h3m : l₃ ∈ G.neighborFinset l₂ ∩ D := by
      rw [e]
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha3, hl3D⟩
    have h4m : l₄ ∈ G.neighborFinset l₂ ∩ D := by
      rw [e]
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha4, hl4D⟩
    rw [hND2, Finset.mem_singleton] at h3m h4m
    exact hl34 (h3m.trans h4m.symm)
  have hl3c1 : l₃ ≠ c₁ := by
    intro e
    have h1m : l₁ ∈ G.neighborFinset l₃ ∩ D := by
      rw [e]
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha1, hl1D⟩
    have h2m : l₂ ∈ G.neighborFinset l₃ ∩ D := by
      rw [e]
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha2, hl2D⟩
    rw [hND3, Finset.mem_singleton] at h1m h2m
    exact hl12 (h1m.trans h2m.symm)
  have hl4c1 : l₄ ≠ c₁ := by
    intro e
    have h1m : l₁ ∈ G.neighborFinset l₄ ∩ D := by
      rw [e]
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha1, hl1D⟩
    have h2m : l₂ ∈ G.neighborFinset l₄ ∩ D := by
      rw [e]
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha2, hl2D⟩
    rw [hND4, Finset.mem_singleton] at h1m h2m
    exact hl12 (h1m.trans h2m.symm)
  have hcross : ∀ u v : Fin 20, G.neighborFinset u ∩ D = {c₁} → G.Adj c₂ v → u ≠ v := by
    intro u v hu hcv e
    subst e
    have hmem : c₂ ∈ G.neighborFinset u ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hcv.symm, hc2Dm⟩
    rw [hu, Finset.mem_singleton] at hmem
    exact hc12.ne hmem.symm
  have hl13 : l₁ ≠ l₃ := hcross l₁ l₃ hND1 ha3
  have hl14 : l₁ ≠ l₄ := hcross l₁ l₄ hND1 ha4
  have hl23 : l₂ ≠ l₃ := hcross l₂ l₃ hND2 ha3
  have hl24 : l₂ ≠ l₄ := hcross l₂ l₄ hND2 ha4
  -- the centres' full neighbourhoods
  have hNc1 : G.neighborFinset c₁ = {c₂, l₁, l₂} := by
    have hsub : ({c₂, l₁, l₂} : Finset (Fin 20)) ⊆ G.neighborFinset c₁ := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [G.mem_neighborFinset]
      rcases hw with rfl | rfl | rfl
      · exact hc12
      · exact ha1
      · exact ha2
    have hcard : ({c₂, l₁, l₂} : Finset (Fin 20)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun e => hl1c2 e.symm, fun e => hl2c2 e.symm⟩),
        Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hl12),
        Finset.card_singleton]
    have hNcard : (G.neighborFinset c₁).card = 3 := by
      rw [G.card_neighborFinset_eq_degree]; exact hc1D
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hNc2 : G.neighborFinset c₂ = {c₁, l₃, l₄} := by
    have hsub : ({c₁, l₃, l₄} : Finset (Fin 20)) ⊆ G.neighborFinset c₂ := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [G.mem_neighborFinset]
      rcases hw with rfl | rfl | rfl
      · exact hc12.symm
      · exact ha3
      · exact ha4
    have hcard : ({c₁, l₃, l₄} : Finset (Fin 20)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun e => hl3c1 e.symm, fun e => hl4c1 e.symm⟩),
        Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hl34),
        Finset.card_singleton]
    have hNcard : (G.neighborFinset c₂).card = 3 := by
      rw [G.card_neighborFinset_eq_degree]; exact hc2D
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hfullc1 : ∀ w : Fin 20, G.Adj c₁ w → w = c₂ ∨ w = l₁ ∨ w = l₂ := by
    intro w hw
    have hmem : w ∈ G.neighborFinset c₁ := (G.mem_neighborFinset _ _).mpr hw
    rw [hNc1] at hmem
    simpa using hmem
  have hfullc2 : ∀ w : Fin 20, G.Adj c₂ w → w = c₁ ∨ w = l₃ ∨ w = l₄ := by
    intro w hw
    have hmem : w ∈ G.neighborFinset c₂ := (G.mem_neighborFinset _ _).mpr hw
    rw [hNc2] at hmem
    simpa using hmem
  have hnl12 : ¬G.Adj l₁ l₂ := by
    intro hadj
    have hmem : l₂ ∈ G.neighborFinset l₁ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hl2D⟩
    rw [hND1, Finset.mem_singleton] at hmem
    exact ha2.ne' hmem
  have hnl34 : ¬G.Adj l₃ l₄ := by
    intro hadj
    have hmem : l₄ ∈ G.neighborFinset l₃ ∩ D :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, hl4D⟩
    rw [hND3, Finset.mem_singleton] at hmem
    exact ha4.ne' hmem
  -- same-centre leaves cannot share a degree-`4` hub (`C₄` of degree sum `13`)
  have hshare_c1 : ∀ h : Fin 20, G.degree h = 4 → G.Adj l₁ h → ¬G.Adj l₂ h := by
    intro h hdeg hadj1 hadj2
    have hl1h : l₁ ≠ h := by intro e; rw [← e] at hdeg; omega
    have hl2h : l₂ ≠ h := by intro e; rw [← e] at hdeg; omega
    have hhc1 : h ≠ c₁ := by intro e; rw [e] at hdeg; omega
    have hnhc1 : ¬G.Adj h c₁ := by
      intro hcon
      rcases hfullc1 h hcon.symm with rfl | rfl | rfl <;> omega
    have hcard4 : ({l₁, h, l₂, c₁} : Finset (Fin 20)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hl1h, hl12, ha1.ne'⟩),
        Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun e => hl2h e.symm, hhc1⟩),
        Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton]
            exact ha2.ne'),
        Finset.card_singleton]
    exact hC4 ⟨l₁, h, l₂, c₁, hcard4, hadj1, hadj2.symm, ha2.symm, ha1, hnl12, hnhc1, by omega⟩
  have hshare_c2 : ∀ h : Fin 20, G.degree h = 4 → G.Adj l₃ h → ¬G.Adj l₄ h := by
    intro h hdeg hadj3 hadj4
    have hl3h : l₃ ≠ h := by intro e; rw [← e] at hdeg; omega
    have hl4h : l₄ ≠ h := by intro e; rw [← e] at hdeg; omega
    have hhc2 : h ≠ c₂ := by intro e; rw [e] at hdeg; omega
    have hnhc2 : ¬G.Adj h c₂ := by
      intro hcon
      rcases hfullc2 h hcon.symm with rfl | rfl | rfl <;> omega
    have hcard4 : ({l₃, h, l₄, c₂} : Finset (Fin 20)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hl3h, hl34, ha3.ne'⟩),
        Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun e => hl4h e.symm, hhc2⟩),
        Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton]
            exact ha4.ne'),
        Finset.card_singleton]
    exact hC4 ⟨l₃, h, l₄, c₂, hcard4, hadj3, hadj4.symm, ha4.symm, ha3, hnl34, hnhc2, by omega⟩
  -- the block `B`, the `M`-isolated residue `Iso`, and the tight incidence count
  set Hub : Finset (Fin 20) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 20, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  set Hub5 : Finset (Fin 20) :=
    Finset.univ.filter (fun v => 4 ≤ G.degree v ∧ G.degree v ≤ 5) with hHub5def
  have hmemHub5 : ∀ v : Fin 20, v ∈ Hub5 ↔ 4 ≤ G.degree v ∧ G.degree v ≤ 5 := by
    intro v; rw [hHub5def]; simp
  set H6 : Finset (Fin 20) := Finset.univ.filter (fun v => 6 ≤ G.degree v) with hH6def
  have hmemH6 : ∀ v : Fin 20, v ∈ H6 ↔ 6 ≤ G.degree v := by intro v; rw [hH6def]; simp
  set B : Finset (Fin 20) := {c₁, c₂, l₁, l₂, l₃, l₄} with hBdef
  have hBsub : B ⊆ D := by
    intro x hx
    rw [hBdef] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [hmemD]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hc1D
    · exact hc2D
    · exact hd1
    · exact hd2
    · exact hd3
    · exact hd4
  have hBcard : B.card = 6 := by rw [hBdef]; exact hcard6
  set Iso : Finset (Fin 20) := D \ B with hIsodef
  have hIsocard : Iso.card = 6 := by
    rw [hIsodef, Finset.card_sdiff_of_subset hBsub, hBcard, hD12]
  have hc1B : c₁ ∈ B := by rw [hBdef]; simp
  have hl1B : l₁ ∈ B := by rw [hBdef]; simp
  have hl2B : l₂ ∈ B := by rw [hBdef]; simp
  have hl3B : l₃ ∈ B := by rw [hBdef]; simp
  have hl4B : l₄ ∈ B := by rw [hBdef]; simp
  have hIsonotB : ∀ v ∈ Iso, v ∉ B := by
    intro v hv
    rw [hIsodef, Finset.mem_sdiff] at hv
    exact hv.2
  have hIsoD : ∀ v ∈ Iso, v ∈ D := by
    intro v hv
    rw [hIsodef, Finset.mem_sdiff] at hv
    exact hv.1
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ u : Fin 20, G.Adj v u → G.degree u ≠ 3 := by
    intro v hv
    rw [hIsodef, Finset.mem_sdiff] at hv
    obtain ⟨hvD, hvB⟩ := hv
    rw [hBdef] at hvB
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvB
    obtain ⟨hvc1, hvc2, hvl1, hvl2, hvl3, hvl4⟩ := hvB
    have hv3 : G.degree v = 3 := (hmemD v).mp hvD
    refine ⟨hv3, fun u hadj hu3 => ?_⟩
    rcases hcov v u hv3 hu3 hadj with e | e | e | e
    · exact hvc1 e
    · exact hvc2 e
    · subst e
      rcases hfullc1 v hadj.symm with e | e | e
      · exact hvc2 e
      · exact hvl1 e
      · exact hvl2 e
    · subst e
      rcases hfullc2 v hadj.symm with e | e | e
      · exact hvc1 e
      · exact hvl3 e
      · exact hvl4 e
  have hNsub : ∀ v ∈ Iso, G.neighborFinset v ⊆ Hub := by
    intro v hv u hu
    rw [G.mem_neighborFinset] at hu
    rw [hmemHub]
    have h1 := (hIsoiso v hv).2 u hu
    have h2 := h3 u
    omega
  have hIso3 : ∀ v ∈ Iso, (G.neighborFinset v ∩ Hub).card = 3 := by
    intro v hv
    rw [Finset.inter_eq_left.mpr (hNsub v hv), G.card_neighborFinset_eq_degree,
      (hIsoiso v hv).1]
  have hsumIso : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card = 18 := by
    rw [Finset.sum_congr rfl hIso3, Finset.sum_const, smul_eq_mul, hIsocard]
  have hsum72 : ∑ v : Fin 20, G.degree v = 72 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplitDeg : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 72 := by
    rw [Finset.sum_add_sum_compl]
    exact hsum72
  have hHubeqDc : Hub = Dᶜ := by
    ext u
    rw [hmemHub, Finset.mem_compl, hmemD]
    have := h3 u
    omega
  have hHubsum : ∑ v ∈ Hub, G.degree v = 36 := by
    rw [hHubeqDc]
    rw [hsumD, hD12] at hsplitDeg
    omega
  have hHubcard : Hub.card = 8 := by
    rw [hHubeqDc, Finset.card_compl, Fintype.card_fin, hD12]
  have hdisjHub : Disjoint Hub5 H6 :=
    Finset.disjoint_left.mpr (fun a ha ha' => by
      rw [hmemHub5] at ha; rw [hmemH6] at ha'; omega)
  have huHub : Hub5 ∪ H6 = Hub := by
    ext w; rw [Finset.mem_union, hmemHub5, hmemH6, hmemHub]; omega
  have hHubpart : Hub5.card + H6.card = 8 := by
    rw [← Finset.card_union_of_disjoint hdisjHub, huHub, hHubcard]
  have hHub5degsum : 4 * Hub5.card ≤ ∑ v ∈ Hub5, G.degree v := by
    have := Finset.card_nsmul_le_sum Hub5 (fun v => G.degree v) 4
      (fun v hv => ((hmemHub5 v).mp hv).1)
    simpa [smul_eq_mul, mul_comm] using this
  have hH6degsum : 6 * H6.card ≤ ∑ v ∈ H6, G.degree v := by
    have := Finset.card_nsmul_le_sum H6 (fun v => G.degree v) 6
      (fun v hv => (hmemH6 v).mp hv)
    simpa [smul_eq_mul, mul_comm] using this
  have hDcdegsplit : ∑ v ∈ Hub5, G.degree v + ∑ v ∈ H6, G.degree v = 36 := by
    rw [← Finset.sum_union hdisjHub, huHub, hHubsum]
  have hvsplit : ∀ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card + (G.neighborFinset v ∩ H6).card
      = (G.neighborFinset v ∩ Hub).card := by
    intro v _
    have hdisj : Disjoint (G.neighborFinset v ∩ Hub5) (G.neighborFinset v ∩ H6) :=
      Finset.disjoint_left.mpr (fun a ha ha' => by
        rw [Finset.mem_inter] at ha ha'
        rw [hmemHub5] at ha; rw [hmemH6] at ha'; omega)
    rw [← Finset.card_union_of_disjoint hdisj, ← Finset.inter_union_distrib_left, huHub]
  have hsumsplit : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card
      + ∑ v ∈ Iso, (G.neighborFinset v ∩ H6).card = 18 := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hvsplit, hsumIso]
  have hcross5 : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card
      = ∑ h ∈ Hub5, (G.neighborFinset h ∩ Iso).card := cross_count_twenty G Iso Hub5
  have hcross6 : ∑ v ∈ Iso, (G.neighborFinset v ∩ H6).card
      = ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card := cross_count_twenty G Iso H6
  -- no degree-`≤ 5` hub carries two `M`-isolated twins
  have hHub5le1 : ∀ h ∈ Hub5, (G.neighborFinset h ∩ Iso).card ≤ 1 := by
    intro h hh
    by_contra hcon
    obtain ⟨t₁, ht₁, t₂, ht₂, ht12⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset h ∩ Iso).card)
    obtain ⟨ht₁N, ht₁Iso⟩ := Finset.mem_inter.mp ht₁
    obtain ⟨ht₂N, ht₂Iso⟩ := Finset.mem_inter.mp ht₂
    exact hshared ⟨h, t₁, t₂, ((hmemHub5 h).mp hh).2, ht12,
      (hIsoiso t₁ ht₁Iso).1, (hIsoiso t₂ ht₂Iso).1,
      ((G.mem_neighborFinset _ _).mp ht₁N).symm, ((G.mem_neighborFinset _ _).mp ht₂N).symm,
      (hIsoiso t₁ ht₁Iso).2, (hIsoiso t₂ ht₂Iso).2⟩
  have hsum5le : ∑ h ∈ Hub5, (G.neighborFinset h ∩ Iso).card ≤ Hub5.card := by
    calc ∑ h ∈ Hub5, (G.neighborFinset h ∩ Iso).card ≤ ∑ _h ∈ Hub5, 1 :=
          Finset.sum_le_sum hHub5le1
      _ = Hub5.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  have hH6Isole : ∀ h ∈ H6, (G.neighborFinset h ∩ Iso).card ≤ 6 := by
    intro h _
    calc (G.neighborFinset h ∩ Iso).card ≤ Iso.card :=
          Finset.card_le_card Finset.inter_subset_right
      _ = 6 := hIsocard
  have hsum6le : ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card ≤ 6 * H6.card := by
    calc ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card ≤ ∑ _h ∈ H6, 6 :=
          Finset.sum_le_sum hH6Isole
      _ = 6 * H6.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- the tie is exact: `|H₆| = 2`, both of degree `6` meeting all of `Iso`; six degree-`4` hubs
  have hH6card : H6.card = 2 := by omega
  have hHub5card : Hub5.card = 6 := by omega
  have hH6sumdeg : ∑ v ∈ H6, G.degree v = 12 := by omega
  have hHub5sumdeg : ∑ v ∈ Hub5, G.degree v = 24 := by omega
  have hsum6Iso : ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card = 12 := by omega
  have hsum5Iso : ∑ h ∈ Hub5, (G.neighborFinset h ∩ Iso).card = 6 := by omega
  have hH6deg6 : ∀ h ∈ H6, G.degree h = 6 := by
    intro h hh
    have hsplit := Finset.add_sum_erase H6 (fun v => G.degree v) hh
    have hbound : 6 * (H6.erase h).card ≤ ∑ v ∈ H6.erase h, G.degree v := by
      have := Finset.card_nsmul_le_sum (H6.erase h) (fun v => G.degree v) 6
        (fun v hv => (hmemH6 v).mp (Finset.mem_of_mem_erase hv))
      simpa [smul_eq_mul, mul_comm] using this
    have hcarde : (H6.erase h).card = 1 := by
      rw [Finset.card_erase_of_mem hh, hH6card]
    have hge := (hmemH6 h).mp hh
    omega
  have hH6Iso6 : ∀ h ∈ H6, (G.neighborFinset h ∩ Iso).card = 6 := by
    intro h hh
    have hsplit := Finset.add_sum_erase H6 (fun v => (G.neighborFinset v ∩ Iso).card) hh
    have hbound : ∑ v ∈ H6.erase h, (G.neighborFinset v ∩ Iso).card
        ≤ 6 * (H6.erase h).card := by
      calc ∑ v ∈ H6.erase h, (G.neighborFinset v ∩ Iso).card
          ≤ ∑ _v ∈ H6.erase h, 6 :=
            Finset.sum_le_sum (fun v hv => hH6Isole v (Finset.mem_of_mem_erase hv))
        _ = 6 * (H6.erase h).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hcarde : (H6.erase h).card = 1 := by
      rw [Finset.card_erase_of_mem hh, hH6card]
    have hle := hH6Isole h hh
    omega
  have hHub5deg4 : ∀ h ∈ Hub5, G.degree h = 4 := by
    intro h hh
    have hsplit := Finset.add_sum_erase Hub5 (fun v => G.degree v) hh
    have hbound : 4 * (Hub5.erase h).card ≤ ∑ v ∈ Hub5.erase h, G.degree v := by
      have := Finset.card_nsmul_le_sum (Hub5.erase h) (fun v => G.degree v) 4
        (fun v hv => ((hmemHub5 v).mp (Finset.mem_of_mem_erase hv)).1)
      simpa [smul_eq_mul, mul_comm] using this
    have hcarde : (Hub5.erase h).card = 5 := by
      rw [Finset.card_erase_of_mem hh, hHub5card]
    have hge := ((hmemHub5 h).mp hh).1
    omega
  have hHub5Iso1 : ∀ h ∈ Hub5, (G.neighborFinset h ∩ Iso).card = 1 := by
    intro h hh
    have hsplit := Finset.add_sum_erase Hub5 (fun v => (G.neighborFinset v ∩ Iso).card) hh
    have hbound : ∑ v ∈ Hub5.erase h, (G.neighborFinset v ∩ Iso).card
        ≤ (Hub5.erase h).card := by
      calc ∑ v ∈ Hub5.erase h, (G.neighborFinset v ∩ Iso).card
          ≤ ∑ _v ∈ Hub5.erase h, 1 :=
            Finset.sum_le_sum (fun v hv => hHub5le1 v (Finset.mem_of_mem_erase hv))
        _ = (Hub5.erase h).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    have hcarde : (Hub5.erase h).card = 5 := by
      rw [Finset.card_erase_of_mem hh, hHub5card]
    have hle := hHub5le1 h hh
    omega
  -- the two degree-`6` hubs `A, Z` with `N(A) = N(Z) = Iso` (the `K_{2,6}`)
  obtain ⟨A, Z, hAZ, hH6eq⟩ := Finset.card_eq_two.mp hH6card
  have hAH6 : A ∈ H6 := by rw [hH6eq]; simp
  have hZH6 : Z ∈ H6 := by rw [hH6eq]; simp
  have hdegA : G.degree A = 6 := hH6deg6 A hAH6
  have hdegZ : G.degree Z = 6 := hH6deg6 Z hZH6
  have hNeq : ∀ h : Fin 20, h ∈ H6 → G.neighborFinset h = Iso := by
    intro h hh
    have hcardN : (G.neighborFinset h).card = 6 := by
      rw [G.card_neighborFinset_eq_degree, hH6deg6 h hh]
    have hIso6 : (G.neighborFinset h ∩ Iso).card = 6 := hH6Iso6 h hh
    have heq1 : G.neighborFinset h ∩ Iso = G.neighborFinset h :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have heq2 : G.neighborFinset h ∩ Iso = Iso :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    rw [← heq1, heq2]
  have hAdjA : ∀ t ∈ Iso, G.Adj t A := by
    intro t ht
    have hmem : t ∈ G.neighborFinset A := by rw [hNeq A hAH6]; exact ht
    exact ((G.mem_neighborFinset _ _).mp hmem).symm
  have hAdjZ : ∀ t ∈ Iso, G.Adj t Z := by
    intro t ht
    have hmem : t ∈ G.neighborFinset Z := by rw [hNeq Z hZH6]; exact ht
    exact ((G.mem_neighborFinset _ _).mp hmem).symm
  have hnotIso : ∀ h : Fin 20, h ∈ H6 → ∀ w : Fin 20, G.Adj h w → w ∈ Iso := by
    intro h hh w hw
    have hmem : w ∈ G.neighborFinset h := (G.mem_neighborFinset _ _).mpr hw
    rwa [hNeq h hh] at hmem
  -- every `M`-isolated twin sees exactly `A`, `Z` and its unique degree-`4` hub
  have hIsoNbr : ∀ t ∈ Iso, ∀ h : Fin 20, G.Adj h t → G.degree h = 4 →
      ∀ w : Fin 20, G.Adj t w → w = A ∨ w = Z ∨ w = h := by
    intro t ht h hth hdeg w htw
    have hsub : ({A, Z, h} : Finset (Fin 20)) ⊆ G.neighborFinset t := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [G.mem_neighborFinset]
      rcases hx with rfl | rfl | rfl
      · exact hAdjA t ht
      · exact hAdjZ t ht
      · exact hth.symm
    have hcard3 : ({A, Z, h} : Finset (Fin 20)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hAZ, fun e => by rw [e] at hdegA; omega⟩),
        Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton]
            exact fun e => by rw [e] at hdegZ; omega),
        Finset.card_singleton]
    have hNcard : (G.neighborFinset t).card = 3 := by
      rw [G.card_neighborFinset_eq_degree, (hIsoiso t ht).1]
    have hNeqt : G.neighborFinset t = {A, Z, h} :=
      (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    have hwmem : w ∈ G.neighborFinset t := (G.mem_neighborFinset _ _).mpr htw
    rw [hNeqt] at hwmem
    simpa using hwmem
  have hIsoTwin : ∀ h ∈ Hub5, ∃ t : Fin 20, t ∈ Iso ∧ G.Adj h t := by
    intro h hh
    obtain ⟨t, hteq⟩ := Finset.card_eq_one.mp (hHub5Iso1 h hh)
    have hmem : t ∈ G.neighborFinset h ∩ Iso := by rw [hteq]; simp
    exact ⟨t, (Finset.mem_inter.mp hmem).2,
      (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hmem).1⟩
  -- each leaf carries exactly two hubs, both of degree `4`
  have hleafhubs : ∀ l c : Fin 20, G.degree l = 3 → G.degree c = 3 → G.Adj c l →
      G.neighborFinset l ∩ D = {c} →
      ∃ x₁ x₂ : Fin 20, x₁ ≠ x₂ ∧ G.Adj l x₁ ∧ G.Adj l x₂ ∧
        G.degree x₁ = 4 ∧ G.degree x₂ = 4 := by
    intro l c hl3 hc3 hcl hNDl
    have hcN : c ∈ G.neighborFinset l := (G.mem_neighborFinset _ _).mpr hcl.symm
    have hNcard : (G.neighborFinset l).card = 3 := by
      rw [G.card_neighborFinset_eq_degree, hl3]
    have herase : ((G.neighborFinset l).erase c).card = 2 := by
      rw [Finset.card_erase_of_mem hcN, hNcard]
    obtain ⟨x₁, x₂, hx12, hxset⟩ := Finset.card_eq_two.mp herase
    have hxmem : ∀ w : Fin 20, w = x₁ ∨ w = x₂ → w ≠ c ∧ G.Adj l w := by
      intro w hw
      have hwe : w ∈ (G.neighborFinset l).erase c := by
        rw [hxset]; rcases hw with rfl | rfl <;> simp
      rw [Finset.mem_erase] at hwe
      exact ⟨hwe.1, (G.mem_neighborFinset _ _).mp hwe.2⟩
    obtain ⟨hx1c, hlx1⟩ := hxmem x₁ (Or.inl rfl)
    obtain ⟨hx2c, hlx2⟩ := hxmem x₂ (Or.inr rfl)
    have hdeg : ∀ w : Fin 20, w ≠ c → G.Adj l w → G.degree w = 4 := by
      intro w hwc hlw
      have hwD : w ∉ D := by
        intro hwD
        have hmem : w ∈ G.neighborFinset l ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hlw, hwD⟩
        rw [hNDl, Finset.mem_singleton] at hmem
        exact hwc hmem
      have hge4 : 4 ≤ G.degree w := by
        have h1 := h3 w
        have h2 : G.degree w ≠ 3 := fun e => hwD ((hmemD w).mpr e)
        omega
      have hle5 : G.degree w ≤ 5 := by
        by_contra hcon
        have hwH6 : w ∈ H6 := (hmemH6 w).mpr (by omega)
        have hlIso : l ∈ Iso := hnotIso w hwH6 l hlw.symm
        exact (hIsoiso l hlIso).2 c hcl.symm hc3
      exact hHub5deg4 w ((hmemHub5 w).mpr ⟨hge4, hle5⟩)
    exact ⟨x₁, x₂, hx12, hlx1, hlx2, hdeg x₁ hx1c hlx1, hdeg x₂ hx2c hlx2⟩
  obtain ⟨p₁, p₂, hp12, hl1p1, hl1p2, hdegp1, hdegp2⟩ :=
    hleafhubs l₁ c₁ hd1 hc1D ha1 hND1
  obtain ⟨q₁, q₂, hq12, hl2q1, hl2q2, hdegq1, hdegq2⟩ :=
    hleafhubs l₂ c₁ hd2 hc1D ha2 hND2
  by_cases hnadj : ¬G.Adj p₁ q₁ ∨ ¬G.Adj p₁ q₂ ∨ ¬G.Adj p₂ q₁ ∨ ¬G.Adj p₂ q₂
  · -- a non-adjacent cross pair assembles `TwoHubConfig`
    have hassemble : ∀ h₁ h₂ : Fin 20, G.Adj l₁ h₁ → G.Adj l₂ h₂ →
        G.degree h₁ = 4 → G.degree h₂ = 4 → ¬G.Adj h₁ h₂ → TwoHubConfig G := by
      intro h₁ h₂ hadj1 hadj2 hdeg1 hdeg2 hnadj12
      have hne12 : h₁ ≠ h₂ := by
        intro e
        exact hshare_c1 h₁ hdeg1 hadj1 (by rw [e]; exact hadj2)
      obtain ⟨a, haIso, hh1a⟩ := hIsoTwin h₁ ((hmemHub5 h₁).mpr ⟨by omega, by omega⟩)
      obtain ⟨c, hcIso, hh2c⟩ := hIsoTwin h₂ ((hmemHub5 h₂).mpr ⟨by omega, by omega⟩)
      have hdega : G.degree a = 3 := (hIsoiso a haIso).1
      have hdegc : G.degree c = 3 := (hIsoiso c hcIso).1
      have haN := hIsoNbr a haIso h₁ hh1a hdeg1
      have hcN := hIsoNbr c hcIso h₂ hh2c hdeg2
      have hnh1c : ¬G.Adj h₁ c := by
        intro hcon
        rcases hcN h₁ hcon.symm with rfl | rfl | rfl
        · omega
        · omega
        · exact hne12 rfl
      have hnah2 : ¬G.Adj a h₂ := by
        intro hcon
        rcases haN h₂ hcon with rfl | rfl | rfl
        · omega
        · omega
        · exact hne12 rfl
      have hnac : ¬G.Adj a c := by
        intro hcon
        rcases haN c hcon with rfl | rfl | rfl
        · omega
        · omega
        · omega
      have hnad : ¬G.Adj a l₂ := by
        intro hcon
        rcases haN l₂ hcon with rfl | rfl | rfl
        · omega
        · omega
        · omega
      have hnh1d : ¬G.Adj h₁ l₂ := fun hcon => hshare_c1 h₁ hdeg1 hadj1 hcon.symm
      have hnbh2 : ¬G.Adj l₁ h₂ := fun hcon => hshare_c1 h₂ hdeg2 hcon hadj2
      have hnbc : ¬G.Adj l₁ c := by
        intro hcon
        have hmem : c ∈ G.neighborFinset l₁ ∩ D :=
          Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hcon, hIsoD c hcIso⟩
        rw [hND1, Finset.mem_singleton] at hmem
        exact hIsonotB c hcIso (by rw [hmem]; exact hc1B)
      have hne_h1a : h₁ ≠ a := by intro e; rw [e] at hdeg1; omega
      have hne_h1b : h₁ ≠ l₁ := by intro e; rw [e] at hdeg1; omega
      have hne_h1c : h₁ ≠ c := by intro e; rw [e] at hdeg1; omega
      have hne_h1d : h₁ ≠ l₂ := by intro e; rw [e] at hdeg1; omega
      have hne_h2a : h₂ ≠ a := by intro e; rw [e] at hdeg2; omega
      have hne_h2b : h₂ ≠ l₁ := by intro e; rw [e] at hdeg2; omega
      have hne_h2c : h₂ ≠ c := by intro e; rw [e] at hdeg2; omega
      have hne_h2d : h₂ ≠ l₂ := by intro e; rw [e] at hdeg2; omega
      have hne_ab : a ≠ l₁ := fun e => hIsonotB a haIso (e ▸ hl1B)
      have hne_ac : a ≠ c := by
        intro e
        rw [e] at hnah2
        exact hnah2 hh2c.symm
      have hne_ad : a ≠ l₂ := fun e => hIsonotB a haIso (e ▸ hl2B)
      have hne_bc : l₁ ≠ c := fun e => hIsonotB c hcIso (e ▸ hl1B)
      have hne_cd : c ≠ l₂ := fun e => hIsonotB c hcIso (e ▸ hl2B)
      exact ⟨h₁, h₂, a, l₁, c, l₂, hdeg1, hdeg2, hdega, hd1, hdegc, hd2,
        hh1a.symm, hadj1, hh2c.symm, hadj2,
        hnadj12, hnh1c, hnh1d, hnah2, hnac, hnad, hnbh2, hnbc, hnl12,
        hne12, hne_h1a, hne_h1b, hne_h1c, hne_h1d,
        hne_h2a, hne_h2b, hne_h2c, hne_h2d,
        hne_ab, hne_ac, hne_ad, hne_bc, hl12, hne_cd⟩
    rcases hnadj with h | h | h | h
    · exact hassemble p₁ q₁ hl1p1 hl2q1 hdegp1 hdegq1 h
    · exact hassemble p₁ q₂ hl1p1 hl2q2 hdegp1 hdegq2 h
    · exact hassemble p₂ q₁ hl1p2 hl2q1 hdegp2 hdegq1 h
    · exact hassemble p₂ q₂ hl1p2 hl2q2 hdegp2 hdegq2 h
  · -- all four cross pairs adjacent: the four hub neighbourhoods are saturated
    push Not at hnadj
    obtain ⟨e11, e12', e21, e22⟩ := hnadj
    obtain ⟨ap₁, hap1Iso, hp1ap1⟩ := hIsoTwin p₁ ((hmemHub5 p₁).mpr ⟨by omega, by omega⟩)
    obtain ⟨ap₂, hap2Iso, hp2ap2⟩ := hIsoTwin p₂ ((hmemHub5 p₂).mpr ⟨by omega, by omega⟩)
    obtain ⟨aq₁, haq1Iso, hq1aq1⟩ := hIsoTwin q₁ ((hmemHub5 q₁).mpr ⟨by omega, by omega⟩)
    obtain ⟨aq₂, haq2Iso, hq2aq2⟩ := hIsoTwin q₂ ((hmemHub5 q₂).mpr ⟨by omega, by omega⟩)
    have hdegap1 : G.degree ap₁ = 3 := (hIsoiso ap₁ hap1Iso).1
    have hdegap2 : G.degree ap₂ = 3 := (hIsoiso ap₂ hap2Iso).1
    have hdegaq1 : G.degree aq₁ = 3 := (hIsoiso aq₁ haq1Iso).1
    have hdegaq2 : G.degree aq₂ = 3 := (hIsoiso aq₂ haq2Iso).1
    have hNfour : ∀ h x y z t : Fin 20, G.degree h = 4 → G.Adj h x → G.Adj h y →
        G.Adj h z → G.Adj h t → x ≠ y → x ≠ z → x ≠ t → y ≠ z → y ≠ t → z ≠ t →
        ∀ w : Fin 20, G.Adj h w → w = x ∨ w = y ∨ w = z ∨ w = t := by
      intro h x y z t hdeg hx hy hz ht hxy hxz hxt hyz hyt hzt w hw
      have hsub : ({x, y, z, t} : Finset (Fin 20)) ⊆ G.neighborFinset h := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rw [G.mem_neighborFinset]
        rcases hu with rfl | rfl | rfl | rfl
        · exact hx
        · exact hy
        · exact hz
        · exact ht
      have hcard4 : ({x, y, z, t} : Finset (Fin 20)).card = 4 := by
        rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hxy, hxz, hxt⟩),
          Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hyz, hyt⟩),
          Finset.card_insert_of_notMem (by
              simp only [Finset.mem_singleton]; exact hzt),
          Finset.card_singleton]
      have hNcard : (G.neighborFinset h).card = 4 := by
        rw [G.card_neighborFinset_eq_degree, hdeg]
      have hNeqh : G.neighborFinset h = {x, y, z, t} :=
        (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
      have hwm : w ∈ G.neighborFinset h := (G.mem_neighborFinset _ _).mpr hw
      rw [hNeqh] at hwm
      simpa using hwm
    have hfullp1 : ∀ w : Fin 20, G.Adj p₁ w → w = l₁ ∨ w = q₁ ∨ w = q₂ ∨ w = ap₁ :=
      hNfour p₁ l₁ q₁ q₂ ap₁ hdegp1 hl1p1.symm e11 e12' hp1ap1
        (by intro e; rw [← e] at hdegq1; omega)
        (by intro e; rw [← e] at hdegq2; omega)
        (fun e => hIsonotB ap₁ hap1Iso (e ▸ hl1B))
        hq12
        (by intro e; rw [e] at hdegq1; omega)
        (by intro e; rw [e] at hdegq2; omega)
    have hfullp2 : ∀ w : Fin 20, G.Adj p₂ w → w = l₁ ∨ w = q₁ ∨ w = q₂ ∨ w = ap₂ :=
      hNfour p₂ l₁ q₁ q₂ ap₂ hdegp2 hl1p2.symm e21 e22 hp2ap2
        (by intro e; rw [← e] at hdegq1; omega)
        (by intro e; rw [← e] at hdegq2; omega)
        (fun e => hIsonotB ap₂ hap2Iso (e ▸ hl1B))
        hq12
        (by intro e; rw [e] at hdegq1; omega)
        (by intro e; rw [e] at hdegq2; omega)
    have hfullq1 : ∀ w : Fin 20, G.Adj q₁ w → w = l₂ ∨ w = p₁ ∨ w = p₂ ∨ w = aq₁ :=
      hNfour q₁ l₂ p₁ p₂ aq₁ hdegq1 hl2q1.symm e11.symm e21.symm hq1aq1
        (by intro e; rw [← e] at hdegp1; omega)
        (by intro e; rw [← e] at hdegp2; omega)
        (fun e => hIsonotB aq₁ haq1Iso (e ▸ hl2B))
        hp12
        (by intro e; rw [e] at hdegp1; omega)
        (by intro e; rw [e] at hdegp2; omega)
    have hfullq2 : ∀ w : Fin 20, G.Adj q₂ w → w = l₂ ∨ w = p₁ ∨ w = p₂ ∨ w = aq₂ :=
      hNfour q₂ l₂ p₁ p₂ aq₂ hdegq2 hl2q2.symm e12'.symm e22.symm hq2aq2
        (by intro e; rw [← e] at hdegp1; omega)
        (by intro e; rw [← e] at hdegp2; omega)
        (fun e => hIsonotB aq₂ haq2Iso (e ▸ hl2B))
        hp12
        (by intro e; rw [e] at hdegp1; omega)
        (by intro e; rw [e] at hdegp2; omega)
    -- hub neighbours of `ℓ₃, ℓ₄` avoid all of `p₁, p₂, q₁, q₂`
    have hnotpq : ∀ ℓ : Fin 20, G.degree ℓ = 3 → ℓ ∈ B → ℓ ≠ l₁ → ℓ ≠ l₂ →
        ∀ u : Fin 20, G.Adj ℓ u → u ≠ p₁ ∧ u ≠ p₂ ∧ u ≠ q₁ ∧ u ≠ q₂ := by
      intro ℓ hdegℓ hℓB hℓl1 hℓl2 u hℓu
      refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
      · subst e
        rcases hfullp1 ℓ hℓu.symm with rfl | rfl | rfl | rfl
        · exact hℓl1 rfl
        · omega
        · omega
        · exact hIsonotB _ hap1Iso hℓB
      · subst e
        rcases hfullp2 ℓ hℓu.symm with rfl | rfl | rfl | rfl
        · exact hℓl1 rfl
        · omega
        · omega
        · exact hIsonotB _ hap2Iso hℓB
      · subst e
        rcases hfullq1 ℓ hℓu.symm with rfl | rfl | rfl | rfl
        · exact hℓl2 rfl
        · omega
        · omega
        · exact hIsonotB _ haq1Iso hℓB
      · subst e
        rcases hfullq2 ℓ hℓu.symm with rfl | rfl | rfl | rfl
        · exact hℓl2 rfl
        · omega
        · omega
        · exact hIsonotB _ haq2Iso hℓB
    obtain ⟨r₁, r₂, hr12, hl3r1, hl3r2, hdegr1, hdegr2⟩ :=
      hleafhubs l₃ c₂ hd3 hc2D ha3 hND3
    obtain ⟨s₁, _s₂, -, hl4s1, -, hdegs1, -⟩ :=
      hleafhubs l₄ c₂ hd4 hc2D ha4 hND4
    obtain ⟨hr1p1, hr1p2, hr1q1, hr1q2⟩ := hnotpq l₃ hd3 hl3B hl13.symm hl23.symm r₁ hl3r1
    obtain ⟨hr2p1, hr2p2, hr2q1, hr2q2⟩ := hnotpq l₃ hd3 hl3B hl13.symm hl23.symm r₂ hl3r2
    obtain ⟨hs1p1, hs1p2, hs1q1, hs1q2⟩ := hnotpq l₄ hd4 hl4B hl14.symm hl24.symm s₁ hl4s1
    have hp1H5 : p₁ ∈ Hub5 := (hmemHub5 p₁).mpr ⟨by omega, by omega⟩
    have hp2H5 : p₂ ∈ Hub5 := (hmemHub5 p₂).mpr ⟨by omega, by omega⟩
    have hq1H5 : q₁ ∈ Hub5 := (hmemHub5 q₁).mpr ⟨by omega, by omega⟩
    have hq2H5 : q₂ ∈ Hub5 := (hmemHub5 q₂).mpr ⟨by omega, by omega⟩
    have hr1H5 : r₁ ∈ Hub5 := (hmemHub5 r₁).mpr ⟨by omega, by omega⟩
    have hr2H5 : r₂ ∈ Hub5 := (hmemHub5 r₂).mpr ⟨by omega, by omega⟩
    have hs1H5 : s₁ ∈ Hub5 := (hmemHub5 s₁).mpr ⟨by omega, by omega⟩
    have hPQsub : ({p₁, p₂, q₁, q₂} : Finset (Fin 20)) ⊆ Hub5 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hp1H5
      · exact hp2H5
      · exact hq1H5
      · exact hq2H5
    have hpq_ne : ∀ i j : Fin 20, G.Adj l₁ i → G.Adj l₂ j → G.degree i = 4 →
        G.degree j = 4 → i ≠ j := by
      intro i j hi hj hdi hdj e
      exact hshare_c1 i hdi hi (by rw [e]; exact hj)
    have hp1q1 : p₁ ≠ q₁ := hpq_ne p₁ q₁ hl1p1 hl2q1 hdegp1 hdegq1
    have hp1q2 : p₁ ≠ q₂ := hpq_ne p₁ q₂ hl1p1 hl2q2 hdegp1 hdegq2
    have hp2q1 : p₂ ≠ q₁ := hpq_ne p₂ q₁ hl1p2 hl2q1 hdegp2 hdegq1
    have hp2q2 : p₂ ≠ q₂ := hpq_ne p₂ q₂ hl1p2 hl2q2 hdegp2 hdegq2
    have hPQcard : ({p₁, p₂, q₁, q₂} : Finset (Fin 20)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hp12, hp1q1, hp1q2⟩),
        Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hp2q1, hp2q2⟩),
        Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton]; exact hq12),
        Finset.card_singleton]
    have hFcard : (Hub5 \ ({p₁, p₂, q₁, q₂} : Finset (Fin 20))).card = 2 := by
      rw [Finset.card_sdiff_of_subset hPQsub, hPQcard, hHub5card]
    have hr1F : r₁ ∈ Hub5 \ ({p₁, p₂, q₁, q₂} : Finset (Fin 20)) := by
      rw [Finset.mem_sdiff]
      refine ⟨hr1H5, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hr1p1, hr1p2, hr1q1, hr1q2⟩
    have hr2F : r₂ ∈ Hub5 \ ({p₁, p₂, q₁, q₂} : Finset (Fin 20)) := by
      rw [Finset.mem_sdiff]
      refine ⟨hr2H5, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hr2p1, hr2p2, hr2q1, hr2q2⟩
    have hs1F : s₁ ∈ Hub5 \ ({p₁, p₂, q₁, q₂} : Finset (Fin 20)) := by
      rw [Finset.mem_sdiff]
      refine ⟨hs1H5, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hs1p1, hs1p2, hs1q1, hs1q2⟩
    have hs1r : s₁ = r₁ ∨ s₁ = r₂ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hs1r1, hs1r2⟩ := hcon
      have hsub3 : ({r₁, r₂, s₁} : Finset (Fin 20))
          ⊆ Hub5 \ ({p₁, p₂, q₁, q₂} : Finset (Fin 20)) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hr1F
        · exact hr2F
        · exact hs1F
      have hcard3 : ({r₁, r₂, s₁} : Finset (Fin 20)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hr12, fun e => hs1r1 e.symm⟩),
          Finset.card_insert_of_notMem (by
              simp only [Finset.mem_singleton]
              exact fun e => hs1r2 e.symm),
          Finset.card_singleton]
      have hle := Finset.card_le_card hsub3
      omega
    rcases hs1r with e | e
    · exact absurd (e ▸ hl4s1) (hshare_c2 r₁ hdegr1 hl3r1)
    · exact absurd (e ▸ hl4s1) (hshare_c2 r₂ hdegr2 hl3r2)

end N20

end ACMax
