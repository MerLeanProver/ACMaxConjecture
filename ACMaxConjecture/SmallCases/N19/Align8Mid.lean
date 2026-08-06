import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.N19.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N19.Dense
import ACMaxConjecture.SmallCases.N19.DenseLe5
import ACMaxConjecture.SmallCases.N19.Align8Helpers
import ACMaxConjecture.SmallCases.N19.TwoHubHub6Deg5

/-!
# Mid-density shared-hub extraction for `n = 19`, dense `e(M)` (`halign8` residual)

Ports the proved-axiom-clean `n = 17` `TwinCert17Align8Mid` to `Fin 19`.  Two density regimes:

* `e(M) = 5` (`s = 10`), `|D| ∈ {10, …, 13}`: a degree-`5` hub sits on the `M`-isolated cherry, so
  the all-degree-`4` `SingleVertexConfig` route is unavailable.  We produce a degree-`≤ 5` hub shared
  by two `M`-isolated twins and route the dominating-edge / induced-`C₅` structure through the proved
  deg-`≤ 5` two-twin assemblies.  (Unlike `n = 17`, the `n = 19` `|Hub| = |D|` shift pushes the strict
  pigeonhole margin past `|D| = 9`, so the `e(M) = 5` mid extraction needs `|D| ≥ 10`.)

* `e(M) = 4` (`s = 8`), `|D| ≥ 9`: the induced-`C₅` branch is impossible, so only the dominating-edge
  double-star survives.  Here the larger `M`-isolated set (`|Iso| ≥ |D| − 5`) makes the deg-`≤ 5`
  shared-hub pigeonhole strict already at `|D| = 9`, so no `K_{2,3}` tie-break is needed: we route
  the dominating double-star through `dom_fat_centre_two_twin_le5_nineteen`.
-/

namespace ACMax

open scoped Classical

namespace N19

/-- **`|D| ≥ 9` from a degree-`≥ 5` hub (`n = 19`).**  With `∑ deg = 64` and every non-`D` vertex of
degree `≥ 4`, the existence of one degree-`≥ 5` vertex pushes the hub-degree sum above `4 |Hub| + 1`,
forcing `|D| ≥ 9` by the handshake. -/
theorem card_D_ge_nine_of_hub_deg5_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (w : Fin 19) (hw5 : 5 ≤ G.degree w) :
    9 ≤ (Finset.univ.filter (fun v : Fin 19 => G.degree v = 3)).card := by
  classical
  set D : Finset (Fin 19) := Finset.univ.filter (fun v : Fin 19 => G.degree v = 3) with hDdef
  have hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 19) := Finset.univ.filter (fun v : Fin 19 => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 19, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  have hHubeqDc : Hub = Dᶜ := by
    ext v; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 v; omega
  have hsum64 : ∑ v : Fin 19, G.degree v = 68 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 68 := by
    rw [Finset.sum_add_sum_compl]; exact hsum64
  have hHubsum : ∑ v ∈ Hub, G.degree v = 68 - 3 * D.card := by
    rw [hHubeqDc]; rw [hsumD] at hsplit; omega
  have hHubcard : Hub.card = 19 - D.card := by
    rw [hHubeqDc, Finset.card_compl]; simp [Fintype.card_fin]
  have hDle18 : D.card ≤ 19 := by
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

/-- **Refined deg-`≤ 5` shared-hub count for `e(M) = 5`, `|D| ≥ 11` (`n = 19`).**  In the
`M`-isolated-twin-dense regime (`s ≤ 10`, `|D| ≥ 11`) there is a degree-`≤ 5` hub adjacent to two
distinct `M`-isolated degree-`3` twins.  Each degree-`≥ 6` hub's isolated-twin incidences are bounded
by both `|Iso|` and its degree, and `|H₆| ≤ 3`; a case-split on `|H₆|` closes the strict pigeonhole
for every `|D| ∈ {11, …, 14}`.  (Unlike `n = 18`, the excess-`11` boundary has no slack, so the
strict pigeonhole only holds from `|D| ≥ 11`; the `|D| = 10` tie is rerouted via a `D10` handler.) -/
theorem shared_hub_le5_eM5_mid_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (h2k2 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hDge11 : 11 ≤ (Finset.univ.filter (fun w : Fin 19 => G.degree w = 3)).card)
    (hsumle : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card ≤ 10) :
    ∃ h t₁ t₂ : Fin 19, G.degree h ≤ 5 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 19, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 19, G.Adj t₂ w → G.degree w ≠ 3) := by
  classical
  set D : Finset (Fin 19) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 19) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 19, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  set Hub5 : Finset (Fin 19) :=
    Finset.univ.filter (fun v => 4 ≤ G.degree v ∧ G.degree v ≤ 5) with hHub5def
  have hmemHub5 : ∀ v : Fin 19, v ∈ Hub5 ↔ 4 ≤ G.degree v ∧ G.degree v ≤ 5 := by
    intro v; rw [hHub5def]; simp
  set H6 : Finset (Fin 19) := Finset.univ.filter (fun v => 6 ≤ G.degree v) with hH6def
  have hmemH6 : ∀ v : Fin 19, v ∈ H6 ↔ 6 ≤ G.degree v := by intro v; rw [hH6def]; simp
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  have hsum64 : ∑ v : Fin 19, G.degree v = 68 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 68 := by
    rw [Finset.sum_add_sum_compl]; exact hsum64
  have hHubsum : ∑ v ∈ Hub, G.degree v = 68 - 3 * D.card := by
    rw [hHubeqDc]; rw [hsumD] at hsplit; omega
  have hHubcard : Hub.card = 19 - D.card := by
    rw [hHubeqDc, Finset.card_compl]; simp [Fintype.card_fin]
  have hDle18 : D.card ≤ 19 := by
    have := Finset.card_le_univ D; simpa [Fintype.card_fin] using this
  have hH6sub : H6 ⊆ Hub := by
    intro v hv; rw [hmemH6] at hv; rw [hmemHub]; omega
  have hHub5sub : ∀ v ∈ Hub5, 4 ≤ G.degree v := fun v hv => ((hmemHub5 v).mp hv).1
  have hH6ge : ∀ v ∈ H6, 6 ≤ G.degree v := fun v hv => (hmemH6 v).mp hv
  set Iso : Finset (Fin 19) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3 := by
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
  have hsumHub3 : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card = 3 * Iso.card := by
    rw [Finset.sum_congr rfl (fun v hv => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hIsodef, Finset.mem_filter] at hv
    exact each_iso_three_hubs G D Hub hmemD hmemHub h3 v hv.1 hv.2
  have hcrossHub : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card
      = ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card := cross_count_nineteen G Iso Hub
  have hHubdegbound : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card ≤ ∑ h ∈ Hub, G.degree h := by
    apply Finset.sum_le_sum
    intro h _
    calc (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree h := G.card_neighborFinset_eq_degree h
  have hDle14 : D.card ≤ 14 := by omega
  have hH6le3 : H6.card ≤ 3 := by omega
  have hHub5deg : ∀ h ∈ Hub5, G.degree h ≤ 5 := fun h hh => ((hmemHub5 h).mp hh).2
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
        = ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card := cross_count_nineteen G Iso H6
    have hH6refined : ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card ≤ H6.card * Iso.card := by
      calc ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card ≤ ∑ _h ∈ H6, Iso.card :=
            Finset.sum_le_sum (fun h _ => Finset.card_le_card Finset.inter_subset_right)
        _ = H6.card * Iso.card := by rw [Finset.sum_const, smul_eq_mul]
    have hH6degboundIso : ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card ≤ ∑ h ∈ H6, G.degree h := by
      apply Finset.sum_le_sum
      intro h _
      calc (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
            Finset.card_le_card Finset.inter_subset_left
        _ = G.degree h := G.card_neighborFinset_eq_degree h
    interval_cases hh6 : H6.card
    · omega
    · omega
    · omega
    · omega
  obtain ⟨h, t₁, t₂, _, hd5, hne, hd1, hd2, ha1, ha2, hi1, hi2⟩ :=
    shared_hub_le5_from_count_nineteen G Iso Hub5 hIsoiso hHub5deg hcount
  exact ⟨h, t₁, t₂, hd5, hne, hd1, hd2, ha1, ha2, hi1, hi2⟩

/-- **`e(M) = 5` (`s = 10`) two-twin cut for the mid corner `|D| ∈ {11, …, 14}` (`n = 19`).**  A
degree-`5` hub on the `M`-isolated cherry rules out the all-degree-`4` `SingleVertexConfig` route, so
we extract a degree-`≤ 5` hub shared by two `M`-isolated twins (`shared_hub_le5_eM5_mid_nineteen`) and
route the dominating-edge double-star through `dom_fat_centre_two_twin_le5_nineteen` and the
induced-`C₅` through `c5_shared_two_twin_le5_nineteen`. -/
theorem two_twin_eM5_mid_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hDge11 : 11 ≤ (Finset.univ.filter (fun w : Fin 19 => G.degree w = 3)).card)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 10) :
    TwoTwinConfig G := by
  classical
  set D : Finset (Fin 19) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hindle : ∀ x : Fin 19, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := (hmemD x).mp hx
  have hge : 8 ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by omega
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
  rcases dominating_edge_or_induced_C5 G D hmemD hT hC4 h2k2 hne with hdom | hC5
  · obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hdom
    obtain ⟨k, tw1, tw2, hkle5, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso, htw2iso⟩ :=
      shared_hub_le5_eM5_mid_nineteen G hm h3 h2k2 (by rw [← hDdef]; exact hDge11)
        (by rw [← hDdef]; exact hsum10.le)
    have hkge4 : 4 ≤ G.degree k := by
      have := htw1iso k hAtw1k; have := h3 k; omega
    exact dom_fat_centre_two_twin_le5_nineteen G D hmemD hT hC4 c₁ c₂ hc1D hc2D hc12 hcov hge
      hindle k tw1 tw2 hkge4 hkle5 htw12 htw1deg htw2deg hAtw1k hAtw2k htw1iso htw2iso
  · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5, e12, e23, e34, e45, e51,
      n13, n14, n24, n25, n35, _hdom⟩ := hC5
    obtain ⟨k, tw1, tw2, hkle5, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso, htw2iso⟩ :=
      shared_hub_le5_eM5_mid_nineteen G hm h3 h2k2 (by rw [← hDdef]; exact hDge11)
        (by rw [← hDdef]; exact hsum10.le)
    have hkge4 : 4 ≤ G.degree k := by
      have := htw1iso k hAtw1k; have := h3 k; omega
    exact c5_shared_two_twin_le5_nineteen G hT hC4 k tw1 tw2 hkge4 hkle5 htw12 htw1deg htw2deg
      hAtw1k hAtw2k htw1iso htw2iso
      (fun a b c hda hdb hdc hka hkb hkc hab hbc hab_ne hbc_ne hac_ne =>
        exists_nonk_two_twin_hub_nineteen G hm h3 (by rw [← hDdef]; omega)
          v₁ v₂ v₃ v₄ v₅ ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
          ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5 e12 e23 e34 e45 e51
          (by rw [← hDdef]; exact hsum10) k a b c
          hkge4 hkle5 hda hdb hdc hka hkb hkc hab hbc hab_ne hbc_ne hac_ne)
      v₁ v₂ v₃ v₄ v₅ ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D)
      ((hmemD v₃).mp hv3D) ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5
      e12 e23 e34 e45 e51 n13 n14 n24 n25 n35

/-- **Deg-`≤ 5` shared hub for `e(M) = 4`, `|D| ≥ 9` (`n = 19`).**  At `s = 8` the `M`-isolated set
satisfies `|Iso| ≥ |D| − 5`, so the deg-`≤ 5` shared-hub pigeonhole is strict already at `|D| = 9`
(no `K_{2,3}` tie-break needed): there is a degree-`≤ 5` hub adjacent to two distinct `M`-isolated
degree-`3` twins.  Each degree-`≥ 6` hub's isolated-twin incidences are bounded by `|Iso|` and
`|H₆| ≤ 2`; a case-split on `|H₆|` closes the count for every `|D| ∈ {9, …, 13}`. -/
theorem shared_hub_le5_eM4_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (h2k2 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hDge9 : 9 ≤ (Finset.univ.filter (fun w : Fin 19 => G.degree w = 3)).card)
    (hsumle : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card ≤ 8) :
    ∃ h t₁ t₂ : Fin 19, G.degree h ≤ 5 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 19, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 19, G.Adj t₂ w → G.degree w ≠ 3) := by
  classical
  set D : Finset (Fin 19) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 19) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 19, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  set Hub5 : Finset (Fin 19) :=
    Finset.univ.filter (fun v => 4 ≤ G.degree v ∧ G.degree v ≤ 5) with hHub5def
  have hmemHub5 : ∀ v : Fin 19, v ∈ Hub5 ↔ 4 ≤ G.degree v ∧ G.degree v ≤ 5 := by
    intro v; rw [hHub5def]; simp
  set H6 : Finset (Fin 19) := Finset.univ.filter (fun v => 6 ≤ G.degree v) with hH6def
  have hmemH6 : ∀ v : Fin 19, v ∈ H6 ↔ 6 ≤ G.degree v := by intro v; rw [hH6def]; simp
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  have hsum64 : ∑ v : Fin 19, G.degree v = 68 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 68 := by
    rw [Finset.sum_add_sum_compl]; exact hsum64
  have hHubsum : ∑ v ∈ Hub, G.degree v = 68 - 3 * D.card := by
    rw [hHubeqDc]; rw [hsumD] at hsplit; omega
  have hHubcard : Hub.card = 19 - D.card := by
    rw [hHubeqDc, Finset.card_compl]; simp [Fintype.card_fin]
  have hDle18 : D.card ≤ 19 := by
    have := Finset.card_le_univ D; simpa [Fintype.card_fin] using this
  have hH6sub : H6 ⊆ Hub := by
    intro v hv; rw [hmemH6] at hv; rw [hmemHub]; omega
  have hHub5sub : ∀ v ∈ Hub5, 4 ≤ G.degree v := fun v hv => ((hmemHub5 v).mp hv).1
  have hH6ge : ∀ v ∈ H6, 6 ≤ G.degree v := fun v hv => (hmemH6 v).mp hv
  set Iso : Finset (Fin 19) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3 := by
    intro v hv
    rw [hIsodef, Finset.mem_filter] at hv
    obtain ⟨hvD, hv0⟩ := hv
    refine ⟨(hmemD v).mp hvD, fun w hadj hw3 => ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
    exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
  have hIso5 : D.card - 5 ≤ Iso.card := by
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
  have hsumHub3 : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card = 3 * Iso.card := by
    rw [Finset.sum_congr rfl (fun v hv => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hIsodef, Finset.mem_filter] at hv
    exact each_iso_three_hubs G D Hub hmemD hmemHub h3 v hv.1 hv.2
  have hcrossHub : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card
      = ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card := cross_count_nineteen G Iso Hub
  have hHubdegbound : ∑ h ∈ Hub, (G.neighborFinset h ∩ Iso).card ≤ ∑ h ∈ Hub, G.degree h := by
    apply Finset.sum_le_sum
    intro h _
    calc (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree h := G.card_neighborFinset_eq_degree h
  have hDle13 : D.card ≤ 13 := by omega
  have hH6le2 : H6.card ≤ 2 := by omega
  have hHub5deg : ∀ h ∈ Hub5, G.degree h ≤ 5 := fun h hh => ((hmemHub5 h).mp hh).2
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
        = ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card := cross_count_nineteen G Iso H6
    have hH6refined : ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card ≤ H6.card * Iso.card := by
      calc ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card ≤ ∑ _h ∈ H6, Iso.card :=
            Finset.sum_le_sum (fun h _ => Finset.card_le_card Finset.inter_subset_right)
        _ = H6.card * Iso.card := by rw [Finset.sum_const, smul_eq_mul]
    have hH6degboundIso : ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card ≤ ∑ h ∈ H6, G.degree h := by
      apply Finset.sum_le_sum
      intro h _
      calc (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
            Finset.card_le_card Finset.inter_subset_left
        _ = G.degree h := G.card_neighborFinset_eq_degree h
    interval_cases hh6 : H6.card
    · omega
    · omega
    · omega
  obtain ⟨h, t₁, t₂, _, hd5, hne, hd1, hd2, ha1, ha2, hi1, hi2⟩ :=
    shared_hub_le5_from_count_nineteen G Iso Hub5 hIsoiso hHub5deg hcount
  exact ⟨h, t₁, t₂, hd5, hne, hd1, hd2, ha1, ha2, hi1, hi2⟩

/-- **Routing a given degree-`≤ 5` shared hub to `TwoTwinConfig` (`e(M) = 5`, `n = 19`).**  Given a
degree-`≤ 5` hub `k` adjacent to two distinct `M`-isolated degree-`3` twins, the dominating-edge
double-star routes through `dom_fat_centre_two_twin_le5_nineteen` and the induced-`C₅` through
`c5_shared_two_twin_le5_nineteen`.  This is the post-pigeonhole part of `two_twin_eM5_mid_nineteen`,
factored out for reuse by the `|D| = 9` re-selection. -/
theorem two_twin_eM5_from_shared_le5_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (_hDge9 : 9 ≤ (Finset.univ.filter (fun w : Fin 19 => G.degree w = 3)).card)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 10)
    (k tw1 tw2 : Fin 19) (hkge4 : 4 ≤ G.degree k) (hkle5 : G.degree k ≤ 5) (htw12 : tw1 ≠ tw2)
    (htw1deg : G.degree tw1 = 3) (htw2deg : G.degree tw2 = 3)
    (hAtw1k : G.Adj tw1 k) (hAtw2k : G.Adj tw2 k)
    (htw1iso : ∀ w : Fin 19, G.Adj tw1 w → G.degree w ≠ 3)
    (htw2iso : ∀ w : Fin 19, G.Adj tw2 w → G.degree w ≠ 3) :
    TwoTwinConfig G := by
  classical
  set D : Finset (Fin 19) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hindle : ∀ x : Fin 19, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := (hmemD x).mp hx
  have hge : 8 ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by omega
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
  rcases dominating_edge_or_induced_C5 G D hmemD hT hC4 h2k2 hne with hdom | hC5
  · obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hdom
    exact dom_fat_centre_two_twin_le5_nineteen G D hmemD hT hC4 c₁ c₂ hc1D hc2D hc12 hcov hge
      hindle k tw1 tw2 hkge4 hkle5 htw12 htw1deg htw2deg hAtw1k hAtw2k htw1iso htw2iso
  · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5, e12, e23, e34, e45, e51,
      n13, n14, n24, n25, n35, _hdom⟩ := hC5
    exact c5_shared_two_twin_le5_nineteen G hT hC4 k tw1 tw2 hkge4 hkle5 htw12 htw1deg htw2deg
      hAtw1k hAtw2k htw1iso htw2iso
      (fun a b c hda hdb hdc hka hkb hkc hab hbc hab_ne hbc_ne hac_ne => by
        -- CLOSED (was the PORT-SORRY `|D| = 9` boundary): dispatch on `|D|`.  At `|D| ≥ 11`
        -- the ported pigeonhole applies; at `|D| ∈ {9, 10}` the shared hub `k` has its five
        -- neighbours pinned (`a, b, c, tw1, tw2`), so `deg k = 5`, the hub degree-sum excludes
        -- degree-`≥ 6` hubs, and the low-`|D|` second-hub extraction
        -- `exists_nonk_two_twin_hub_lowD_nineteen` closes the consecutive-cherry sub-case.
        by_cases hD11 : 11 ≤ D.card
        · exact exists_nonk_two_twin_hub_nineteen G hm h3
            (by rw [← hDdef]; exact hD11)
            v₁ v₂ v₃ v₄ v₅ ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
            ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5 e12 e23 e34 e45 e51
            (by rw [← hDdef]; exact hsum10) k a b c
            hkge4 hkle5 hda hdb hdc hka hkb hkc hab hbc hab_ne hbc_ne hac_ne
        · exact exists_nonk_two_twin_hub_lowD_nineteen G hm h3
            (by rw [← hDdef]; exact _hDge9)
            (by rw [← hDdef]; omega)
            v₁ v₂ v₃ v₄ v₅ ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
            ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5 e12 e23 e34 e45 e51
            (by rw [← hDdef]; exact hsum10) k a b c tw1 tw2
            hkle5 hda hdb hdc hka hkb hkc hab hbc hab_ne hbc_ne hac_ne
            htw12 htw1deg htw2deg hAtw1k hAtw2k htw1iso htw2iso)
      v₁ v₂ v₃ v₄ v₅ ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D)
      ((hmemD v₃).mp hv3D) ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5
      e12 e23 e34 e45 e51 n13 n14 n24 n25 n35

/-- **Routing an all-degree-`4` `M`-isolated cherry to `SingleVertexConfig` (`e(M) = 5`, `n = 19`).**
Given an `M`-isolated degree-`3` twin `t'` whose three neighbours are all degree-`4`, the
dominating-edge double-star routes through `single_vertex_doublestar_count` and the induced-`C₅`
through `single_vertex_config_from_C5_three_hubs`.  This is the `hall` branch of
`halign8_eM5_nineteen`, factored out for reuse by the `|D| = 9` re-selection. -/
theorem sv_eM5_from_alldeg4_iso_nineteen (G : SimpleGraph (Fin 19))
    (hT : ¬∃ x y z : Fin 19, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 10)
    (t' : Fin 19) (ht3 : G.degree t' = 3)
    (htiso : ∀ w : Fin 19, G.Adj t' w → G.degree w ≠ 3)
    (htall : ∀ w : Fin 19, G.Adj t' w → G.degree w = 4) :
    SingleVertexConfig G := by
  classical
  set D : Finset (Fin 19) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hindle : ∀ x : Fin 19, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := (hmemD x).mp hx
  have htcard : (G.neighborFinset t').card = 3 := by rw [G.card_neighborFinset_eq_degree, ht3]
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp htcard
  have htp : G.Adj t' p := (G.mem_neighborFinset _ _).mp (by rw [hset]; simp)
  have htq : G.Adj t' q := (G.mem_neighborFinset _ _).mp (by rw [hset]; simp)
  have htr : G.Adj t' r := (G.mem_neighborFinset _ _).mp (by rw [hset]; simp)
  have hp4 : G.degree p = 4 := htall p htp
  have hq4 : G.degree q = 4 := htall q htq
  have hr4 : G.degree r = 4 := htall r htr
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
  rcases dominating_edge_or_induced_C5 G D hmemD hT hC4 h2k2 hne with hdom | hC5
  · obtain ⟨c₁, c₂, hc1D, hc2D, hc12, hcov⟩ := hdom
    obtain ⟨hin1, hin2⟩ :=
      dom_centres_indeg3 G D c₁ c₂ hc1D hc2D hc12 hindle hcov hsum10
    exact single_vertex_doublestar_count G D hmemD hT hC4 t' p q r
      ht3 htiso hp4 hq4 hr4 hpq hpr hqr htp htq htr c₁ c₂ hc1D hc2D hc12 hin1 hin2 hcov
  · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
      e12, e23, e34, e45, e51, n13, n14, n24, n25, n35, _⟩ := hC5
    exact single_vertex_config_from_C5_three_hubs G hT hC4 t' p q r
      ht3 htiso hp4 hq4 hr4 hpq hpr hqr htp htq htr v₁ v₂ v₃ v₄ v₅
      ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
      ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5
      e12 e23 e34 e45 e51 n13 n14 n24 n25 n35

/-- **`|D| = 9` re-selection dichotomy for `e(M) = 5` (`n = 19`).**  At `|D| = 9` the hub-degree sum
`37` over `9` hubs forces *exactly one* degree-`5` hub `K` (the rest degree-`4`).  If two distinct
`M`-isolated twins are adjacent to `K`, that is a degree-`≤ 5` shared hub (left); otherwise at most
one `M`-isolated twin meets `K`, so (as `|Iso| ≥ 3`) some `M`-isolated twin avoids `K` and hence has
all-degree-`4` neighbours (right).  This closes the thin double-star where the shared-hub pigeonhole
only ties. -/
theorem eM5_D9_shared_or_alldeg4_nineteen (G : SimpleGraph (Fin 19))
    (hm : G.edgeFinset.card = 34) (h3 : ∀ v : Fin 19, 3 ≤ G.degree v)
    (h2k2 : ¬∃ a b c d : Fin 19, ({a, b, c, d} : Finset (Fin 19)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hD9 : (Finset.univ.filter (fun w : Fin 19 => G.degree w = 3)).card = 9)
    (hsumle : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card ≤ 10)
    (t : Fin 19) (_ht3 : G.degree t = 3) (htiso : ∀ w : Fin 19, G.Adj t w → G.degree w ≠ 3)
    (hnall : ¬∀ w : Fin 19, G.Adj t w → G.degree w = 4) :
    (∃ k tw1 tw2 : Fin 19, G.degree k ≤ 5 ∧ tw1 ≠ tw2 ∧ G.degree tw1 = 3 ∧ G.degree tw2 = 3 ∧
        G.Adj tw1 k ∧ G.Adj tw2 k ∧ (∀ w : Fin 19, G.Adj tw1 w → G.degree w ≠ 3) ∧
        (∀ w : Fin 19, G.Adj tw2 w → G.degree w ≠ 3))
      ∨ (∃ t' : Fin 19, G.degree t' = 3 ∧ (∀ w : Fin 19, G.Adj t' w → G.degree w ≠ 3) ∧
        (∀ w : Fin 19, G.Adj t' w → G.degree w = 4)) := by
  classical
  set D : Finset (Fin 19) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 19, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 19) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 19, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  set Hub4 : Finset (Fin 19) := Finset.univ.filter (fun v => G.degree v = 4) with hHub4def
  have hmemHub4 : ∀ v : Fin 19, v ∈ Hub4 ↔ G.degree v = 4 := by intro v; rw [hHub4def]; simp
  set H5 : Finset (Fin 19) := Finset.univ.filter (fun v => 5 ≤ G.degree v) with hH5def
  have hmemH5 : ∀ v : Fin 19, v ∈ H5 ↔ 5 ≤ G.degree v := by intro v; rw [hH5def]; simp
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  have hsum64 : ∑ v : Fin 19, G.degree v = 68 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 68 := by
    rw [Finset.sum_add_sum_compl]; exact hsum64
  have hHubsum : ∑ v ∈ Hub, G.degree v = 41 := by
    rw [hHubeqDc]; rw [hsumD, hD9] at hsplit; omega
  have hHubcard : Hub.card = 10 := by
    rw [hHubeqDc, Finset.card_compl]; simp [Fintype.card_fin, hD9]
  have hdisjHub : Disjoint Hub4 H5 :=
    Finset.disjoint_left.mpr (fun a ha ha' => by
      rw [hmemHub4] at ha; rw [hmemH5] at ha'; omega)
  have huHub : Hub4 ∪ H5 = Hub := by
    ext w; rw [Finset.mem_union, hmemHub4, hmemH5, hmemHub]; omega
  have hHubpart : Hub4.card + H5.card = Hub.card := by
    rw [← huHub, Finset.card_union_of_disjoint hdisjHub]
  have hHub4degsum : ∑ v ∈ Hub4, G.degree v = 4 * Hub4.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemHub4 v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hH5degsum : 5 * H5.card ≤ ∑ v ∈ H5, G.degree v := by
    have := Finset.card_nsmul_le_sum H5 (fun v => G.degree v) 5
      (fun v hv => (hmemH5 v).mp hv)
    simpa [smul_eq_mul, mul_comm] using this
  have hDcdegsplit : ∑ v ∈ Hub4, G.degree v + ∑ v ∈ H5, G.degree v = ∑ v ∈ Hub, G.degree v := by
    rw [← Finset.sum_union hdisjHub, huHub]
  have hH5le1 : H5.card ≤ 1 := by omega
  -- `t` has a neighbour of degree `≥ 5`, hence `H5` is non-empty, hence `|H5| = 1`.
  obtain ⟨w0, hw0adj, hw0ne4⟩ : ∃ w : Fin 19, G.Adj t w ∧ G.degree w ≠ 4 := by
    by_contra hc
    push Not at hc
    exact hnall (fun w hw => hc w hw)
  have hw0ge5 : 5 ≤ G.degree w0 := by
    have := htiso w0 hw0adj; have := h3 w0; omega
  have hw0H5 : w0 ∈ H5 := (hmemH5 w0).mpr hw0ge5
  have hH5pos : 1 ≤ H5.card := Finset.card_pos.mpr ⟨w0, hw0H5⟩
  have hH5one : H5.card = 1 := by omega
  obtain ⟨K, hKeq⟩ := Finset.card_eq_one.mp hH5one
  have hKH5 : K ∈ H5 := by rw [hKeq]; simp
  have hKge5 : 5 ≤ G.degree K := (hmemH5 K).mp hKH5
  have hKle5 : G.degree K ≤ 5 := by
    have hHub4card : Hub4.card = 9 := by omega
    have hKsum : ∑ v ∈ H5, G.degree v = G.degree K := by rw [hKeq, Finset.sum_singleton]
    omega
  -- `Iso`.
  set Iso : Finset (Fin 19) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 19, G.Adj v w → G.degree w ≠ 3 := by
    intro v hv
    rw [hIsodef, Finset.mem_filter] at hv
    obtain ⟨hvD, hv0⟩ := hv
    refine ⟨(hmemD v).mp hvD, fun w hadj hw3 => ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
    exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
  have hIso3 : 3 ≤ Iso.card := by
    have hnb := nonisolated_component_bound G D hmemD h2k2
    have hpart := Finset.card_filter_add_card_filter_not (s := D)
      (fun v => (G.neighborFinset v ∩ D).card = 0)
    rw [← hIsodef] at hpart
    omega
  by_cases hsh : ∃ a b : Fin 19, a ∈ Iso ∧ b ∈ Iso ∧ a ≠ b ∧ G.Adj a K ∧ G.Adj b K
  · obtain ⟨a, b, haIso, hbIso, hab, haK, hbK⟩ := hsh
    obtain ⟨hadeg, haiso⟩ := hIsoiso a haIso
    obtain ⟨hbdeg, hbiso⟩ := hIsoiso b hbIso
    exact Or.inl ⟨K, a, b, hKle5, hab, hadeg, hbdeg, haK, hbK, haiso, hbiso⟩
  · -- No two `M`-isolated twins meet `K`, so some `M`-isolated twin avoids `K`.
    have hex : ∃ t' ∈ Iso, ¬G.Adj t' K := by
      by_contra hc
      push Not at hc
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < Iso.card by omega)
      exact hsh ⟨a, b, ha, hb, hab, hc a ha, hc b hb⟩
    obtain ⟨t', ht'Iso, ht'K⟩ := hex
    obtain ⟨ht'deg, ht'iso⟩ := hIsoiso t' ht'Iso
    refine Or.inr ⟨t', ht'deg, ht'iso, fun w hadj => ?_⟩
    have hwne3 : G.degree w ≠ 3 := ht'iso w hadj
    have hwge4 : 4 ≤ G.degree w := by have := h3 w; omega
    by_contra hwne4
    have hwge5 : 5 ≤ G.degree w := by omega
    have hwH5 : w ∈ H5 := (hmemH5 w).mpr hwge5
    have hwK : w = K := by rw [hKeq] at hwH5; simpa using hwH5
    exact ht'K (hwK ▸ hadj)

end N19

end ACMax
