import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N17.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N17.Dense
import ACMaxConjecture.SmallCases.N17.DenseLe5
import ACMaxConjecture.SmallCases.N17.Align8Helpers
import ACMaxConjecture.SmallCases.N17.TwoHubHub6Deg5

/-!
# Mid-density shared-hub extraction for `n = 17`, `e(M) = 5`, `|D| ∈ {9, 10}` (`halign8` residual)

This file closes the `|D| ∈ {9, 10}` (`|Hub| ∈ {7, 8}`) residual of `halign8_eM5_seventeen`: a
degree-`5` hub sits on the `M`-isolated cherry, so the all-degree-`4` `SingleVertexConfig` route is
unavailable.  We instead produce a degree-`≤ 5` hub shared by two `M`-isolated twins and route the
dominating-edge / induced-`C₅` structure through the proved deg-`≤ 5` two-twin assemblies.

The shared-hub pigeonhole at `e(M) = 5` only *ties* under the crude `∑_{H₆} deg` bound (the
`n = 17` slack `60` is divisible by `3`).  The fix is a **refined** count: each degree-`≥ 6` hub
contributes at most `|Iso|` `M`-isolated-twin incidences (not `deg`), and there are at most `2` such
hubs.  Case-splitting on `|H₆| ∈ {0, 1, 2}` then closes the strict pigeonhole for every
`|D| ∈ {9, …, 13}`, in particular `|D| ∈ {9, 10}`.
-/

namespace ACMax

open scoped Classical

namespace N17

/-- **`|D| ≥ 9` from a degree-`≥ 5` hub (`n = 17`).**  With `∑ deg = 60` and every non-`D` vertex of
degree `≥ 4`, the existence of one degree-`≥ 5` vertex pushes the hub-degree sum above `4 |Hub| + 1`,
forcing `|D| ≥ 9` by the handshake. -/
theorem card_D_ge_nine_of_hub_deg5_seventeen (G : SimpleGraph (Fin 17))
    (hm : G.edgeFinset.card = 30) (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (w : Fin 17) (hw5 : 5 ≤ G.degree w) :
    9 ≤ (Finset.univ.filter (fun v : Fin 17 => G.degree v = 3)).card := by
  classical
  set D : Finset (Fin 17) := Finset.univ.filter (fun v : Fin 17 => G.degree v = 3) with hDdef
  have hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 17) := Finset.univ.filter (fun v : Fin 17 => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 17, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  have hHubeqDc : Hub = Dᶜ := by
    ext v; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 v; omega
  have hsum60 : ∑ v : Fin 17, G.degree v = 60 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 60 := by
    rw [Finset.sum_add_sum_compl]; exact hsum60
  have hHubsum : ∑ v ∈ Hub, G.degree v = 60 - 3 * D.card := by
    rw [hHubeqDc]; rw [hsumD] at hsplit; omega
  have hHubcard : Hub.card = 17 - D.card := by
    rw [hHubeqDc, Finset.card_compl]; simp [Fintype.card_fin]
  have hDle17 : D.card ≤ 17 := by
    have := Finset.card_le_univ D; simpa [Fintype.card_fin] using this
  have hwHub : w ∈ Hub := (hmemHub w).mpr (by omega)
  have hsplitw : G.degree w + ∑ v ∈ Hub.erase w, G.degree v = ∑ v ∈ Hub, G.degree v :=
    Finset.add_sum_erase Hub (fun v => G.degree v) hwHub
  have herase4 : 4 * (Hub.erase w).card ≤ ∑ v ∈ Hub.erase w, G.degree v := by
    have := Finset.card_nsmul_le_sum (Hub.erase w) (fun v => G.degree v) 4
      (fun v hv => by rw [Finset.mem_erase, hmemHub] at hv; exact hv.2)
    simpa [smul_eq_mul, mul_comm] using this
  have herasecard : (Hub.erase w).card = Hub.card - 1 := Finset.card_erase_of_mem hwHub
  have hHubpos : 1 ≤ Hub.card := Finset.card_pos.mpr ⟨w, hwHub⟩
  omega

/-- **Refined deg-`≤ 5` shared-hub count for `e(M) = 5`, `|D| ≥ 9` (`n = 17`).**  In the
`M`-isolated-twin-dense regime (`s ≤ 10`, `|D| ≥ 9`) there is a degree-`≤ 5` hub adjacent to two
distinct `M`-isolated degree-`3` twins.  Unlike the `|D| = 11` count, a degree-`≥ 6` hub's
isolated-twin incidences are bounded by `|Iso|` rather than its degree, and `|H₆| ≤ 2`; a
case-split on `|H₆|` then makes the strict pigeonhole `|Hub₅| < ∑_{Iso}|N ∩ Hub₅|` hold. -/
theorem shared_hub_le5_eM5_mid_seventeen (G : SimpleGraph (Fin 17))
    (hm : G.edgeFinset.card = 30) (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (h2k2 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hDge9 : 9 ≤ (Finset.univ.filter (fun w : Fin 17 => G.degree w = 3)).card)
    (hsumle : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card ≤ 10) :
    ∃ h t₁ t₂ : Fin 17, G.degree h ≤ 5 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 17, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 17, G.Adj t₂ w → G.degree w ≠ 3) := by
  classical
  set D : Finset (Fin 17) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 17) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 17, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  set Hub5 : Finset (Fin 17) :=
    Finset.univ.filter (fun v => 4 ≤ G.degree v ∧ G.degree v ≤ 5) with hHub5def
  have hmemHub5 : ∀ v : Fin 17, v ∈ Hub5 ↔ 4 ≤ G.degree v ∧ G.degree v ≤ 5 := by
    intro v; rw [hHub5def]; simp
  set H6 : Finset (Fin 17) := Finset.univ.filter (fun v => 6 ≤ G.degree v) with hH6def
  have hmemH6 : ∀ v : Fin 17, v ∈ H6 ↔ 6 ≤ G.degree v := by intro v; rw [hH6def]; simp
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  have hsum56 : ∑ v : Fin 17, G.degree v = 60 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 60 := by
    rw [Finset.sum_add_sum_compl]; exact hsum56
  have hHubsum : ∑ v ∈ Hub, G.degree v = 60 - 3 * D.card := by
    rw [hHubeqDc]; rw [hsumD] at hsplit; omega
  have hHubcard : Hub.card = 17 - D.card := by
    rw [hHubeqDc, Finset.card_compl]; simp [Fintype.card_fin]
  have hDle17 : D.card ≤ 17 := by
    have := Finset.card_le_univ D; simpa [Fintype.card_fin] using this
  have hH6sub : H6 ⊆ Hub := by
    intro v hv; rw [hmemH6] at hv; rw [hmemHub]; omega
  have hHub5sub : ∀ v ∈ Hub5, 4 ≤ G.degree v := fun v hv => ((hmemHub5 v).mp hv).1
  have hH6ge : ∀ v ∈ H6, 6 ≤ G.degree v := fun v hv => (hmemH6 v).mp hv
  set Iso : Finset (Fin 17) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3 := by
    intro v hv
    rw [hIsodef, Finset.mem_filter] at hv
    obtain ⟨hvD, hv0⟩ := hv
    refine ⟨(hmemD v).mp hvD, fun w hadj hw3 => ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
    exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
  have hIso6 : D.card - 6 ≤ Iso.card := by
    have hnb := nonisolated_component_bound G D hmemD h2k2
    have hpart := Finset.card_filter_add_card_filter_not (s := D)
      (fun v => (G.neighborFinset v ∩ D).card = 0)
    rw [← hIsodef] at hpart
    omega
  have hdisjHub : Disjoint Hub5 H6 :=
    Finset.disjoint_left.mpr (fun a ha ha' => by
      rw [hmemHub5] at ha; rw [hmemH6] at ha'; omega)
  have huHub : Hub5 ∪ H6 = Hub := by
    ext w; rw [Finset.mem_union, hmemHub5, hmemH6, hmemHub]; omega
  have hHubpart : Hub5.card + H6.card = Hub.card := by
    rw [← huHub, Finset.card_union_of_disjoint hdisjHub]
  have hHub5degsum : 4 * Hub5.card ≤ ∑ v ∈ Hub5, G.degree v := by
    have := Finset.card_nsmul_le_sum Hub5 (fun v => G.degree v) 4 hHub5sub
    simpa [smul_eq_mul, mul_comm] using this
  have hH6degsum : 6 * H6.card ≤ ∑ v ∈ H6, G.degree v := by
    have := Finset.card_nsmul_le_sum H6 (fun v => G.degree v) 6 hH6ge
    simpa [smul_eq_mul, mul_comm] using this
  have hDcdegsplit : ∑ v ∈ Hub5, G.degree v + ∑ v ∈ H6, G.degree v = ∑ v ∈ Hub, G.degree v := by
    rw [← Finset.sum_union hdisjHub, huHub]
  -- Iso → Hub incidence is `3|Iso|` and bounded by `∑_{Hub} deg`, forcing `|D| ≤ 13`.
  have hsumHub3 : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card = 3 * Iso.card := by
    rw [Finset.sum_congr rfl (fun v hv => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hIsodef, Finset.mem_filter] at hv
    exact each_iso_three_hubs G D Hub hmemD hmemHub h3 v hv.1 hv.2
  have hcrossHub : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card
      = ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card := cross_count G Iso Hub
  have hHubdegbound : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card ≤ ∑ h ∈ Hub, G.degree h := by
    apply Finset.sum_le_sum
    intro h _
    calc (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree h := G.card_neighborFinset_eq_degree h
  have hDle13 : D.card ≤ 13 := by omega
  -- `|H₆| ≤ 2` from the degree-sum lower bounds.
  have hH6le2 : H6.card ≤ 2 := by omega
  have hHub5deg : ∀ h ∈ Hub5, G.degree h ≤ 5 := fun h hh => ((hmemHub5 h).mp hh).2
  -- Refined strict pigeonhole on `Hub5`.
  have hcount : Hub5.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card := by
    have hsumHub3' : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card = 3 * Iso.card := hsumHub3
    have hvsplit : ∀ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card + (G.neighborFinset v ∩ H6).card
        = (G.neighborFinset v ∩ Hub).card := by
      intro v _
      have hdisj : Disjoint (G.neighborFinset v ∩ Hub5) (G.neighborFinset v ∩ H6) :=
        Finset.disjoint_left.mpr (fun a ha ha' => by
          rw [Finset.mem_inter] at ha ha'
          rw [hmemHub5] at ha; rw [hmemH6] at ha'; omega)
      rw [← Finset.card_union_of_disjoint hdisj, ← Finset.inter_union_distrib_left, huHub]
    have hsumsplit : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card
        + ∑ v ∈ Iso, (G.neighborFinset v ∩ H6).card = 3 * Iso.card := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hvsplit, hsumHub3']
    have hcrossH6 : ∑ v ∈ Iso, (G.neighborFinset v ∩ H6).card
        = ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card := cross_count G Iso H6
    -- Refined bound: each `H₆` hub meets at most `|Iso|` isolated twins.
    have hH6refined : ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card ≤ H6.card * Iso.card := by
      calc ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card ≤ ∑ _h ∈ H6, Iso.card :=
            Finset.sum_le_sum (fun h _ => Finset.card_le_card Finset.inter_subset_right)
        _ = H6.card * Iso.card := by rw [Finset.sum_const, smul_eq_mul]
    interval_cases hh6 : H6.card
    · omega
    · omega
    · omega
  obtain ⟨h, t₁, t₂, _, hd5, hne, hd1, hd2, ha1, ha2, hi1, hi2⟩ :=
    shared_hub_le5_from_count_seventeen G Iso Hub5 hIsoiso hHub5deg hcount
  exact ⟨h, t₁, t₂, hd5, hne, hd1, hd2, ha1, ha2, hi1, hi2⟩

/-- **`e(M) = 5` (`s = 10`) two-twin cut for the mid corner `|D| ∈ {9, 10}` (`n = 17`).**  A
degree-`5` hub on the `M`-isolated cherry rules out the all-degree-`4` `SingleVertexConfig` route, so
we extract a degree-`≤ 5` hub shared by two `M`-isolated twins (`shared_hub_le5_eM5_mid_seventeen`)
and route the dominating-edge double-star through `dom_fat_centre_two_twin_le5_seventeen` and the
induced-`C₅` through `c5_shared_two_twin_le5_seventeen`. -/
theorem two_twin_eM5_mid_seventeen (G : SimpleGraph (Fin 17))
    (hm : G.edgeFinset.card = 30) (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 17, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hDge9 : 9 ≤ (Finset.univ.filter (fun w : Fin 17 => G.degree w = 3)).card)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 10) :
    TwoTwinConfig G := by
  classical
  set D : Finset (Fin 17) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hindle : ∀ x : Fin 17, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := (hmemD x).mp hx
  have hge : 8 ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by omega
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
    obtain ⟨k, tw1, tw2, hkle5, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso, htw2iso⟩ :=
      shared_hub_le5_eM5_mid_seventeen G hm h3 h2k2 (by rw [← hDdef]; exact hDge9)
        (by rw [← hDdef]; exact hsum10.le)
    have hkge4 : 4 ≤ G.degree k := by
      have := htw1iso k hAtw1k; have := h3 k; omega
    exact dom_fat_centre_two_twin_le5_seventeen G D hmemD hT hC4 c₁ c₂ hc1D hc2D hc12 hcov hge
      hindle k tw1 tw2 hkge4 hkle5 htw12 htw1deg htw2deg hAtw1k hAtw2k htw1iso htw2iso
  · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5, e12, e23, e34, e45, e51,
      n13, n14, n24, n25, n35, _hdom⟩ := hC5
    obtain ⟨k, tw1, tw2, hkle5, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso, htw2iso⟩ :=
      shared_hub_le5_eM5_mid_seventeen G hm h3 h2k2 (by rw [← hDdef]; exact hDge9)
        (by rw [← hDdef]; exact hsum10.le)
    have hkge4 : 4 ≤ G.degree k := by
      have := htw1iso k hAtw1k; have := h3 k; omega
    exact c5_shared_two_twin_le5_seventeen G hT hC4 k tw1 tw2 hkge4 hkle5 htw12 htw1deg htw2deg
      hAtw1k hAtw2k htw1iso htw2iso
      (fun a b c hda hdb hdc hka hkb hkc hab hbc hab_ne hbc_ne hac_ne =>
        exists_nonk_two_twin_hub_seventeen G hm h3 (by rw [← hDdef]; exact hDge9)
          v₁ v₂ v₃ v₄ v₅ ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
          ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5 e12 e23 e34 e45 e51
          (by rw [← hDdef]; exact hsum10) k a b c
          hkge4 hkle5 hda hdb hdc hka hkb hkc hab hbc hab_ne hbc_ne hac_ne)
      v₁ v₂ v₃ v₄ v₅ ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D)
      ((hmemD v₃).mp hv3D) ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5
      e12 e23 e34 e45 e51 n13 n14 n24 n25 n35

/-- **Shared deg-`4` hub for `e(M) = 4`, `|D| ∈ {9, 10}` (`n = 17`).**  At `s = 8` there is a
degree-`4` hub adjacent to two distinct `M`-isolated degree-`3` twins.  Each `M`-isolated twin meets
exactly three hubs, of which at most `|D| − 8 ≤ 2` have degree `≥ 5`; a degree-`≥ 5` hub's
isolated-twin incidences are bounded by `|Iso|`.  Case-splitting on the number of degree-`≥ 5` hubs
closes the strict pigeonhole except for `|D| = 10` with two degree-`5` hubs each dominating the five
`M`-isolated twins, which is excluded by the no-good-`K_{2,3}` hypothesis (degree sum
`5 + 5 + 3 + 3 + 3 = 19`). -/
theorem shared_deg4_hub_eM4_seventeen (G : SimpleGraph (Fin 17))
    (hm : G.edgeFinset.card = 30) (h3 : ∀ v : Fin 17, 3 ≤ G.degree v)
    (h2k2 : ¬∃ a b c d : Fin 17, ({a, b, c, d} : Finset (Fin 17)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hK23 : ¬∃ a b c d e : Fin 17, ({a, b, c, d, e} : Finset (Fin 17)).card = 5 ∧
      G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
      ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
      G.degree a + G.degree b + G.degree c + G.degree d + G.degree e ≤ 19)
    (hDge9 : 9 ≤ (Finset.univ.filter (fun w : Fin 17 => G.degree w = 3)).card)
    (hDle10 : (Finset.univ.filter (fun w : Fin 17 => G.degree w = 3)).card ≤ 10)
    (hs8 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 8) :
    ∃ h t₁ t₂ : Fin 17, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 17, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 17, G.Adj t₂ w → G.degree w ≠ 3) := by
  classical
  set D : Finset (Fin 17) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 17, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 17) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 17, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  set Hub4 : Finset (Fin 17) := Finset.univ.filter (fun v => G.degree v = 4) with hHub4def
  have hmemHub4 : ∀ v : Fin 17, v ∈ Hub4 ↔ G.degree v = 4 := by intro v; rw [hHub4def]; simp
  set H5 : Finset (Fin 17) := Finset.univ.filter (fun v => 5 ≤ G.degree v) with hH5def
  have hmemH5 : ∀ v : Fin 17, v ∈ H5 ↔ 5 ≤ G.degree v := by intro v; rw [hH5def]; simp
  have hHub4deg : ∀ h ∈ Hub4, G.degree h = 4 := fun h hh => (hmemHub4 h).mp hh
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  have hsum60 : ∑ v : Fin 17, G.degree v = 60 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 60 := by
    rw [Finset.sum_add_sum_compl]; exact hsum60
  have hHubsum : ∑ v ∈ Hub, G.degree v = 60 - 3 * D.card := by
    rw [hHubeqDc]; rw [hsumD] at hsplit; omega
  have hHubcard : Hub.card = 17 - D.card := by
    rw [hHubeqDc, Finset.card_compl]; simp [Fintype.card_fin]
  -- `Hub4` and `H5` partition `Hub`.
  have hdisjHub : Disjoint Hub4 H5 :=
    Finset.disjoint_left.mpr (fun a ha ha' => by
      rw [hmemHub4] at ha; rw [hmemH5] at ha'; omega)
  have huHub : Hub4 ∪ H5 = Hub := by
    ext w; rw [Finset.mem_union, hmemHub4, hmemH5, hmemHub]; omega
  have hHubpart : Hub4.card + H5.card = Hub.card := by
    rw [← huHub, Finset.card_union_of_disjoint hdisjHub]
  have hHub4degsum : ∑ v ∈ Hub4, G.degree v = 4 * Hub4.card := by
    rw [Finset.sum_congr rfl hHub4deg, Finset.sum_const, smul_eq_mul, mul_comm]
  have hH5degsum : 5 * H5.card ≤ ∑ v ∈ H5, G.degree v := by
    have := Finset.card_nsmul_le_sum H5 (fun v => G.degree v) 5
      (fun v hv => (hmemH5 v).mp hv)
    simpa [smul_eq_mul, mul_comm] using this
  have hDcdegsplit : ∑ v ∈ Hub4, G.degree v + ∑ v ∈ H5, G.degree v = ∑ v ∈ Hub, G.degree v := by
    rw [← Finset.sum_union hdisjHub, huHub]
  have hH5le2 : H5.card ≤ 2 := by omega
  -- `Iso`.
  set Iso : Finset (Fin 17) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 17, G.Adj v w → G.degree w ≠ 3 := by
    intro v hv
    rw [hIsodef, Finset.mem_filter] at hv
    obtain ⟨hvD, hv0⟩ := hv
    refine ⟨(hmemD v).mp hvD, fun w hadj hw3 => ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
    exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
  have hIsoge : D.card - 5 ≤ Iso.card := by
    have hnb := nonisolated_component_bound G D hmemD h2k2
    have hpart := Finset.card_filter_add_card_filter_not (s := D)
      (fun v => (G.neighborFinset v ∩ D).card = 0)
    rw [← hIsodef] at hpart
    omega
  have hIsoD : Iso ⊆ D := by rw [hIsodef]; exact Finset.filter_subset _ _
  -- Iso → Hub incidence is `3|Iso|`.
  have hsumHub3 : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card = 3 * Iso.card := by
    rw [Finset.sum_congr rfl (fun v hv => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hIsodef, Finset.mem_filter] at hv
    exact each_iso_three_hubs G D Hub hmemD hmemHub h3 v hv.1 hv.2
  have hvsplit : ∀ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card + (G.neighborFinset v ∩ H5).card
      = (G.neighborFinset v ∩ Hub).card := by
    intro v _
    have hdisj : Disjoint (G.neighborFinset v ∩ Hub4) (G.neighborFinset v ∩ H5) :=
      Finset.disjoint_left.mpr (fun a ha ha' => by
        rw [Finset.mem_inter] at ha ha'
        rw [hmemHub4] at ha; rw [hmemH5] at ha'; omega)
    rw [← Finset.card_union_of_disjoint hdisj, ← Finset.inter_union_distrib_left, huHub]
  have hsumsplit : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card
      + ∑ v ∈ Iso, (G.neighborFinset v ∩ H5).card = 3 * Iso.card := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hvsplit, hsumHub3]
  have hcrossH5 : ∑ v ∈ Iso, (G.neighborFinset v ∩ H5).card
      = ∑ h ∈ H5, (G.neighborFinset h ∩ Iso).card := cross_count G Iso H5
  -- Strict pigeonhole on `Hub4` (with the `K_{2,3}` tie-break for `|H5| = 2`).
  have hcount : Hub4.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
    by_contra hcon
    push Not at hcon
    have hH5refined : ∑ h ∈ H5, (G.neighborFinset h ∩ Iso).card ≤ H5.card * Iso.card := by
      calc ∑ h ∈ H5, (G.neighborFinset h ∩ Iso).card ≤ ∑ _h ∈ H5, Iso.card :=
            Finset.sum_le_sum (fun h _ => Finset.card_le_card Finset.inter_subset_right)
        _ = H5.card * Iso.card := by rw [Finset.sum_const, smul_eq_mul]
    interval_cases hh5 : H5.card
    · omega
    · omega
    · -- `|H5| = 2`, forced `|Iso| = 5` and both hubs dominate `Iso`: build a good `K_{2,3}`.
      have hIso5 : Iso.card = 5 := by omega
      have hH5sum : ∑ h ∈ H5, (G.neighborFinset h ∩ Iso).card = 10 := by omega
      obtain ⟨h₁, h₂, hh12, hH5eq⟩ := Finset.card_eq_two.mp hh5
      have hmem1 : h₁ ∈ H5 := by rw [hH5eq]; simp
      have hmem2 : h₂ ∈ H5 := by rw [hH5eq]; simp
      have hsumpair : (G.neighborFinset h₁ ∩ Iso).card + (G.neighborFinset h₂ ∩ Iso).card = 10 := by
        rw [hH5eq, Finset.sum_insert (by simp [hh12]), Finset.sum_singleton] at hH5sum; exact hH5sum
      have hle1 : (G.neighborFinset h₁ ∩ Iso).card ≤ Iso.card :=
        Finset.card_le_card Finset.inter_subset_right
      have hle2 : (G.neighborFinset h₂ ∩ Iso).card ≤ Iso.card :=
        Finset.card_le_card Finset.inter_subset_right
      have heq1 : (G.neighborFinset h₁ ∩ Iso).card = 5 := by omega
      have heq2 : (G.neighborFinset h₂ ∩ Iso).card = 5 := by omega
      have hdom1 : Iso ⊆ G.neighborFinset h₁ := by
        have : G.neighborFinset h₁ ∩ Iso = Iso :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [heq1, hIso5])
        rw [← this]; exact Finset.inter_subset_left
      have hdom2 : Iso ⊆ G.neighborFinset h₂ := by
        have : G.neighborFinset h₂ ∩ Iso = Iso :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [heq2, hIso5])
        rw [← this]; exact Finset.inter_subset_left
      -- `|D| = 10` and `∑_{H5} deg = |D| = 10`, so both degree-`5` hubs are exactly degree `5`.
      have hpairdeg : G.degree h₁ + G.degree h₂ = ∑ v ∈ H5, G.degree v := by
        rw [hH5eq, Finset.sum_insert (by simp [hh12]), Finset.sum_singleton]
      have hge1 : 5 ≤ G.degree h₁ := (hmemH5 h₁).mp hmem1
      have hge2 : 5 ≤ G.degree h₂ := (hmemH5 h₂).mp hmem2
      have hdeg1 : G.degree h₁ = 5 := by omega
      have hdeg2 : G.degree h₂ = 5 := by omega
      have hNh1 : G.neighborFinset h₁ = Iso :=
        (Finset.eq_of_subset_of_card_le hdom1
          (by rw [G.card_neighborFinset_eq_degree, hdeg1, hIso5])).symm
      -- `h₂ ∉ N(h₁)`, hence `¬G.Adj h₁ h₂`.
      have hnadj : ¬G.Adj h₁ h₂ := by
        intro hadj
        have : h₂ ∈ G.neighborFinset h₁ := (G.mem_neighborFinset _ _).mpr hadj
        rw [hNh1] at this
        obtain ⟨hd2, _⟩ := hIsoiso h₂ this
        omega
      -- Pick three distinct `M`-isolated twins.
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (show 1 < Iso.card by omega)
      have hpos : 0 < ((Iso.erase x).erase y).card := by
        have hyex : y ∈ Iso.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
        have h1 := Finset.card_erase_of_mem hyex
        have h2 := Finset.card_erase_of_mem hx
        omega
      obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_erase, Finset.mem_erase] at hz
      obtain ⟨hzy, hzx, hzIso⟩ := hz
      have hxz : x ≠ z := Ne.symm hzx
      have hyz : y ≠ z := Ne.symm hzy
      -- Adjacencies and non-adjacencies for the `K_{2,3}`.
      have hax1 : G.Adj h₁ x := (G.mem_neighborFinset _ _).mp (hdom1 hx)
      have hay1 : G.Adj h₁ y := (G.mem_neighborFinset _ _).mp (hdom1 hy)
      have haz1 : G.Adj h₁ z := (G.mem_neighborFinset _ _).mp (hdom1 hzIso)
      have hax2 : G.Adj h₂ x := (G.mem_neighborFinset _ _).mp (hdom2 hx)
      have hay2 : G.Adj h₂ y := (G.mem_neighborFinset _ _).mp (hdom2 hy)
      have haz2 : G.Adj h₂ z := (G.mem_neighborFinset _ _).mp (hdom2 hzIso)
      obtain ⟨_, hxiso⟩ := hIsoiso x hx
      obtain ⟨_, hyiso⟩ := hIsoiso y hy
      have hnxy : ¬G.Adj x y := fun hadj => hyiso x hadj.symm (by
        obtain ⟨hd, _⟩ := hIsoiso x hx; exact hd)
      have hnxz : ¬G.Adj x z := fun hadj => hxiso z hadj (by
        obtain ⟨hd, _⟩ := hIsoiso z hzIso; exact hd)
      have hnyz : ¬G.Adj y z := fun hadj => hyiso z hadj (by
        obtain ⟨hd, _⟩ := hIsoiso z hzIso; exact hd)
      -- `h₁, h₂ ∈ Dᶜ`, the twins are in `D`, so the five vertices are distinct.
      have hd1mem : G.degree x = 3 := (hIsoiso x hx).1
      have hd2mem : G.degree y = 3 := (hIsoiso y hy).1
      have hd3mem : G.degree z = 3 := (hIsoiso z hzIso).1
      have hh1x : h₁ ≠ x := by rintro rfl; omega
      have hh1y : h₁ ≠ y := by rintro rfl; omega
      have hh1z : h₁ ≠ z := by rintro rfl; omega
      have hh2x : h₂ ≠ x := by rintro rfl; omega
      have hh2y : h₂ ≠ y := by rintro rfl; omega
      have hh2z : h₂ ≠ z := by rintro rfl; omega
      have hcard5 : ({h₁, h₂, x, y, z} : Finset (Fin 17)).card = 5 := by
        rw [Finset.card_insert_of_notMem (by simp [hh12, hh1x, hh1y, hh1z]),
          Finset.card_insert_of_notMem (by simp [hh2x, hh2y, hh2z]),
          Finset.card_insert_of_notMem (by simp [hxy, hxz]),
          Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
      exact hK23 ⟨h₁, h₂, x, y, z, hcard5, hax1, hay1, haz1, hax2, hay2, haz2, hnadj,
        hnxy, hnxz, hnyz, by omega⟩
  exact shared_deg4_hub_from_count_seventeen G Iso Hub4 hIsoiso hHub4deg hcount

end N17

end ACMax
