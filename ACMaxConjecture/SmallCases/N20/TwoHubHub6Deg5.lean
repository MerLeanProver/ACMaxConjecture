import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.N20.Core
import ACMaxConjecture.SmallCases.StarCertificates
import ACMaxConjecture.SmallCases.N20.Dense
import ACMaxConjecture.SmallCases.N20.DenseLe5
import ACMaxConjecture.SmallCases.N20.Align8Helpers

/-!
# `n = 20`, `|D| = 13`, `|Hub| = 7`, `e(M) = 5` (`s = 10`) shared-hub helper

The genuinely degenerate `e(M) = 5` corner of the `|D| = 13` alignment selector
(`two_hub_or_single_vertex_hub6_twenty`), ported from `TwinCert19TwoHubHub6Deg5.lean`.  At
`e(M) = 5` the residual is a double-star (dominating edge) or an induced `C₅`.  The
deg-`4`-shared-hub pigeonhole used at `e(M) ≤ 4` degenerates; for `n = 20` (degree sum `72`,
divisible by `3`) it no longer even *ties* strictly in the `C₅` branch, so we route through a
deg-`≤ 5` shared hub:

* **double-star branch (fully proved):** the `M`-isolated twins each meet `3` hubs; with
  `|Hub| = 7` and at most two degree-`≥ 6` hubs the deg-`≤ 5` count is strict, so a deg-`≤ 5` hub
  is shared by two `M`-isolated twins, and the deg-`≤ 5` leaf-cherry (`claw`) assembly closes the
  cut.

* **induced-`C₅` branch (fully proved):** the deg-`4` pigeonhole ties (`X ≥ 3`, `|Hub₄| = 3`), so
  the shared hub may be degree `5`; a deg-`5` hub may hit three consecutive cycle vertices (triangle
  degree sum `5 + 3 + 3 = 11 > 10`, escaping `hT`).  That residual is closed by
  `exists_nonk_two_twin_hub_twenty`: those three hit vertices have the deg-`5` hub `k` as their
  unique hub neighbour, so a second deg-`≤ 5` hub `h ≠ k` (with two `M`-isolated twins, extracted by
  the refined `hub5_iso_count_twenty` pigeonhole on `Hub₅ \ {k}`) avoids that cherry instead.

The helper lemmas (`shared_hub_le5_from_count_twenty`, `dense_two_twin_assemble_le5_twenty`,
`claw_shared_two_twin_le5_twenty`, `dom_fat_centre_two_twin_le5_twenty`,
`shared_hub_le5_eM5_twenty`) are all axiom-clean ports.
-/

namespace ACMax

open scoped Classical

namespace N20

/-- **Shared deg-`≤ 5` hub by pigeonhole (`n = 20`).**  Port of `shared_deg4_hub_from_count_twenty`
dropping the degree-`4` restriction to degree-`≤ 5`: if the deg-`≤ 5` hub set `Hub` carries strictly
more twin-incidences from the `M`-isolated set `Iso` than it has vertices, some hub is adjacent to
two distinct `M`-isolated degree-`3` twins. -/
theorem shared_hub_le5_from_count_twenty (G : SimpleGraph (Fin 20)) (Iso Hub : Finset (Fin 20))
    (hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3)
    (hHubdeg : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hcount : Hub.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card) :
    ∃ h t₁ t₂ : Fin 20, h ∈ Hub ∧ G.degree h ≤ 5 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 20, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 20, G.Adj t₂ w → G.degree w ≠ 3) := by
  classical
  have hincid : ∃ h ∈ Hub, 2 ≤ (Iso.filter (fun v => G.Adj v h)).card := by
    by_contra hcon
    push Not at hcon
    have hsum1 : ∑ h ∈ Hub, (Iso.filter (fun v => G.Adj v h)).card ≤ Hub.card := by
      calc ∑ h ∈ Hub, (Iso.filter (fun v => G.Adj v h)).card
          ≤ ∑ _h ∈ Hub, 1 := Finset.sum_le_sum (fun h hh => by have := hcon h hh; omega)
        _ = Hub.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    have hswap : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card
        = ∑ h ∈ Hub, (Iso.filter (fun v => G.Adj v h)).card := by
      have hL : ∀ v : Fin 20, (G.neighborFinset v ∩ Hub).card
          = (Hub.filter (fun h => G.Adj v h)).card := by
        intro v
        congr 1
        ext h
        simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_filter]
        tauto
      simp_rw [hL, Finset.card_filter]
      rw [Finset.sum_comm]
    omega
  obtain ⟨h, hhHub, hh2⟩ := hincid
  obtain ⟨t₁, ht1, t₂, ht2, ht12⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (Iso.filter (fun v => G.Adj v h)).card)
  rw [Finset.mem_filter] at ht1 ht2
  obtain ⟨ht1Iso, hAt1h⟩ := ht1
  obtain ⟨ht2Iso, hAt2h⟩ := ht2
  obtain ⟨ht1deg, ht1iso⟩ := hIsoiso t₁ ht1Iso
  obtain ⟨ht2deg, ht2iso⟩ := hIsoiso t₂ ht2Iso
  exact ⟨h, t₁, t₂, hhHub, hHubdeg h hhHub, ht12, ht1deg, ht2deg, hAt1h, hAt2h, ht1iso, ht2iso⟩


/-- **Fat-dominating claw assembly with a deg-`≤ 5` hub (`n = 20`).**  Port of
`claw_shared_two_twin_twenty` permitting `4 ≤ deg h ≤ 5`: the C₄ obstruction `h–i–c–j` has degree
sum `deg h + 9 ≤ 14`, so it is still forbidden by `hC4` at `deg h = 5`, and the hub meets at most
one of `c`'s three degree-`3` neighbours. -/
theorem claw_shared_two_twin_le5_twenty (G : SimpleGraph (Fin 20)) (D : Finset (Fin 20))
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (c t₁ t₂ h : Fin 20) (hcD : c ∈ D)
    (hcge : 3 ≤ (G.neighborFinset c ∩ D).card)
    (ht1deg : G.degree t₁ = 3) (ht2deg : G.degree t₂ = 3)
    (hhge4 : 4 ≤ G.degree h) (hhle5 : G.degree h ≤ 5)
    (ht12 : t₁ ≠ t₂) (hAt1h : G.Adj t₁ h) (hAt2h : G.Adj t₂ h)
    (ht1iso : ∀ w : Fin 20, G.Adj t₁ w → G.degree w ≠ 3)
    (ht2iso : ∀ w : Fin 20, G.Adj t₂ w → G.degree w ≠ 3) :
    TwoTwinConfig G := by
  classical
  have hdegD : ∀ v : Fin 20, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
  have hc3 : G.degree c = 3 := hdegD c hcD
  have hle : (G.neighborFinset c ∩ D).card ≤ 3 := by
    calc (G.neighborFinset c ∩ D).card ≤ (G.neighborFinset c).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree c := G.card_neighborFinset_eq_degree c
      _ = 3 := hc3
  have heq3 : (G.neighborFinset c ∩ D).card = 3 := le_antisymm hle hcge
  obtain ⟨n₁, n₂, n₃, hne12, hne13, hne23, hset⟩ := Finset.card_eq_three.mp heq3
  have hcardeq : (G.neighborFinset c).card = (G.neighborFinset c ∩ D).card := by
    rw [G.card_neighborFinset_eq_degree, hc3, heq3]
  have hNsubeq : G.neighborFinset c ∩ D = G.neighborFinset c :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq hcardeq)
  have hmem_i : ∀ w : Fin 20, w ∈ ({n₁, n₂, n₃} : Finset (Fin 20)) → G.Adj c w ∧ w ∈ D := by
    intro w hw
    have hw' : w ∈ G.neighborFinset c ∩ D := hset ▸ hw
    exact ⟨(G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hw').1,
      (Finset.mem_inter.mp hw').2⟩
  obtain ⟨a1, hn1D⟩ := hmem_i n₁ (by simp)
  obtain ⟨a2, hn2D⟩ := hmem_i n₂ (by simp)
  obtain ⟨a3, hn3D⟩ := hmem_i n₃ (by simp)
  have hd1 : G.degree n₁ = 3 := hdegD n₁ hn1D
  have hd2 : G.degree n₂ = 3 := hdegD n₂ hn2D
  have hd3 : G.degree n₃ = 3 := hdegD n₃ hn3D
  have hcnbhd : ∀ w : Fin 20, G.Adj c w → w = n₁ ∨ w = n₂ ∨ w = n₃ := by
    intro w hw
    have hw' : w ∈ G.neighborFinset c ∩ D := by
      rw [hNsubeq]; exact (G.mem_neighborFinset _ _).mpr hw
    rw [hset] at hw'; simpa using hw'
  have hhc : ¬G.Adj h c := by
    intro hadj
    rcases hcnbhd h hadj.symm with e | e | e <;> rw [e] at hhge4 <;> omega
  have hmeet : ∀ i j : Fin 20, G.degree i = 3 → G.degree j = 3 →
      G.Adj c i → G.Adj c j → i ≠ j → ¬(G.Adj h i ∧ G.Adj h j) := by
    rintro i j hi3 hj3 ci cj hij ⟨hhi, hhj⟩
    have nij : ¬G.Adj i j := fun aij =>
      hT ⟨c, i, j, ci.ne, hij, cj.ne, ci, aij, cj, by omega⟩
    exact hC4 ⟨h, i, c, j,
      card_four_twenty h i c j (by rintro rfl; omega) (by rintro rfl; omega)
        (by rintro rfl; omega) ci.ne.symm hij cj.ne,
      hhi, ci.symm, cj, hhj.symm, hhc, nij, by omega⟩
  have not12 := hmeet n₁ n₂ hd1 hd2 a1 a2 hne12
  have not13 := hmeet n₁ n₃ hd1 hd3 a1 a3 hne13
  have not23 := hmeet n₂ n₃ hd2 hd3 a2 a3 hne23
  by_cases hb1 : G.Adj h n₁
  · exact dense_two_twin_assemble_le5_twenty G t₁ t₂ h n₂ c n₃ ht1deg ht2deg hhge4 hhle5
      hd2 hc3 hd3 hAt1h hAt2h a2.symm a3 ht1iso ht2iso
      (fun hv => not12 ⟨hb1, hv⟩) hhc (fun hv => not13 ⟨hb1, hv⟩) ht12
      a2.symm.ne a3.ne hne23
  · by_cases hb2 : G.Adj h n₂
    · exact dense_two_twin_assemble_le5_twenty G t₁ t₂ h n₁ c n₃ ht1deg ht2deg hhge4 hhle5
        hd1 hc3 hd3 hAt1h hAt2h a1.symm a3 ht1iso ht2iso
        hb1 hhc (fun hv => not23 ⟨hb2, hv⟩) ht12 a1.symm.ne a3.ne hne13
    · exact dense_two_twin_assemble_le5_twenty G t₁ t₂ h n₁ c n₂ ht1deg ht2deg hhge4 hhle5
        hd1 hc3 hd2 hAt1h hAt2h a1.symm a2 ht1iso ht2iso
        hb1 hhc hb2 ht12 a1.symm.ne a2.ne hne12

/-- **Dominating-edge fat-centre dispatch with a deg-`≤ 5` hub (`n = 20`).**  Port of
`dom_fat_centre_two_twin_twenty` with the hub permitted degree `4` or `5`. -/
theorem dom_fat_centre_two_twin_le5_twenty (G : SimpleGraph (Fin 20)) (D : Finset (Fin 20))
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (c₁ c₂ : Fin 20) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hcov : ∀ p q : Fin 20, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hge : 8 ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card)
    (hindle : ∀ x : Fin 20, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3)
    (k t₁ t₂ : Fin 20) (hkge4 : 4 ≤ G.degree k) (hkle5 : G.degree k ≤ 5) (ht12 : t₁ ≠ t₂)
    (ht1deg : G.degree t₁ = 3) (ht2deg : G.degree t₂ = 3)
    (hAt1k : G.Adj t₁ k) (hAt2k : G.Adj t₂ k)
    (ht1iso : ∀ w : Fin 20, G.Adj t₁ w → G.degree w ≠ 3)
    (ht2iso : ∀ w : Fin 20, G.Adj t₂ w → G.degree w ≠ 3) :
    TwoTwinConfig G := by
  have hform := thin_eM_formula_twenty G D c₁ c₂ hc1D hc2D hc12 hcov
  have hle1 := hindle c₁ hc1D
  have hle2 := hindle c₂ hc2D
  by_cases hc1 : 3 ≤ (G.neighborFinset c₁ ∩ D).card
  · exact claw_shared_two_twin_le5_twenty G D hmemD hT hC4 c₁ t₁ t₂ k hc1D hc1 ht1deg ht2deg
      hkge4 hkle5 ht12 hAt1k hAt2k ht1iso ht2iso
  · have hc2 : 3 ≤ (G.neighborFinset c₂ ∩ D).card := by omega
    exact claw_shared_two_twin_le5_twenty G D hmemD hT hC4 c₂ t₁ t₂ k hc2D hc2 ht1deg ht2deg
      hkge4 hkle5 ht12 hAt1k hAt2k ht1iso ht2iso

/-- **Shared deg-`≤ 5` hub in the `e(M) = 5`, `|D| = 13`, `|Hub| = 7` regime (`n = 20`).**  The
`M`-isolated twins each meet `3` hubs; with `|Hub| = 7` and degree sum `33` (excess `5`) at most two
hubs have degree `≥ 6`, so excluding them leaves enough twin-incidences on the deg-`≤ 5` hubs
(`|Iso| ≥ 7`) to force, by a strict pigeonhole, a deg-`≤ 5` hub shared by two `M`-isolated twins. -/
theorem shared_hub_le5_eM5_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (h2k2 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hD12 : (Finset.univ.filter (fun w : Fin 20 => G.degree w = 3)).card = 13)
    (hsumle : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card ≤ 10) :
    ∃ h t₁ t₂ : Fin 20, G.degree h ≤ 5 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 20, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 20, G.Adj t₂ w → G.degree w ≠ 3) := by
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
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  -- `∑_{Hub} deg = 26` from the handshake.
  have hsum56 : ∑ v : Fin 20, G.degree v = 72 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 72 := by
    rw [Finset.sum_add_sum_compl]; exact hsum56
  have hHubsum : ∑ v ∈ Hub, G.degree v = 72 - 3 * D.card := by
    rw [hHubeqDc]; rw [hsumD] at hsplit; omega
  have hHubcard : Hub.card = 20 - D.card := by
    rw [hHubeqDc, Finset.card_compl]; simp [Fintype.card_fin]
  have hH6sub : H6 ⊆ Hub := by
    intro v hv; rw [hmemH6] at hv; rw [hmemHub]; omega
  -- `Hub5` and `H6` partition `Hub`; `∑_{Hub5} deg ≥ 4|Hub5|` and `∑_{H6} deg ≥ 6|H6|`.
  have hHub5sub : ∀ v ∈ Hub5, 4 ≤ G.degree v := fun v hv => ((hmemHub5 v).mp hv).1
  have hH6ge : ∀ v ∈ H6, 6 ≤ G.degree v := fun v hv => (hmemH6 v).mp hv
  -- `Iso`.
  set Iso : Finset (Fin 20) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3 := by
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
  -- `Hub5` and `H6` partition `Hub`.
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
  -- Refined count: `|Hub5| < ∑_{Iso}|N ∩ Hub5|`.
  have hcount : Hub5.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card := by
    have hsumHub3 : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card = 3 * Iso.card := by
      rw [Finset.sum_congr rfl (fun v hv => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
      rw [hIsodef, Finset.mem_filter] at hv
      exact each_iso_three_hubs G D Hub hmemD hmemHub h3 v hv.1 hv.2
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
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hvsplit, hsumHub3]
    have hcrossH6 : ∑ v ∈ Iso, (G.neighborFinset v ∩ H6).card
        = ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card := cross_count_twenty G Iso H6
    have hH6degbound : ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card ≤ ∑ h ∈ H6, G.degree h := by
      apply Finset.sum_le_sum
      intro h _
      calc (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
            Finset.card_le_card Finset.inter_subset_left
        _ = G.degree h := G.card_neighborFinset_eq_degree h
    omega
  have hHub5deg : ∀ h ∈ Hub5, G.degree h ≤ 5 := fun h hh => ((hmemHub5 h).mp hh).2
  obtain ⟨h, t₁, t₂, _, hd5, hne, hd1, hd2, ha1, ha2, hi1, hi2⟩ :=
    shared_hub_le5_from_count_twenty G Iso Hub5 hIsoiso hHub5deg hcount
  exact ⟨h, t₁, t₂, hd5, hne, hd1, hd2, ha1, ha2, hi1, hi2⟩

/-- **An induced `C₅` accounts for all of `M` at `e(M) = 5` (`n = 20`).**  If `v₁–⋯–v₅` is an
induced `C₅` of degree-`3` vertices and `∑_{v ∈ D}|N v ∩ D| = 10` (`e(M) = 5`), then the
`M`-non-isolated set is *exactly* the five cycle vertices: each `vᵢ` already contributes its two
cycle neighbours, exhausting the budget `10`, so every other `D`-vertex is `M`-isolated.  Hence at
most five `D`-vertices are non-isolated. -/
theorem nonIso_le_five_of_C5_twenty (G : SimpleGraph (Fin 20)) (D : Finset (Fin 20))
    (v₁ v₂ v₃ v₄ v₅ : Fin 20)
    (hv1D : v₁ ∈ D) (hv2D : v₂ ∈ D) (hv3D : v₃ ∈ D) (hv4D : v₄ ∈ D) (hv5D : v₅ ∈ D)
    (hcard5 : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 20)).card = 5)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e36 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁)
    (hsum10 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 10) :
    (D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0)).card ≤ 5 := by
  classical
  obtain ⟨_, d13, d14, _, _, d24, d25, _, d35, _⟩ :=
    distinct_five_twenty v₁ v₂ v₃ v₄ v₅ hcard5
  set C : Finset (Fin 20) := {v₁, v₂, v₃, v₄, v₅} with hCdef
  have two_nbrs : ∀ a x y : Fin 20, G.Adj a x → G.Adj a y → x ∈ D → y ∈ D → x ≠ y →
      2 ≤ (G.neighborFinset a ∩ D).card := by
    intro a x y hax hay hxD hyD hxy
    have hsub : ({x, y} : Finset (Fin 20)) ⊆ G.neighborFinset a ∩ D := by
      intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hax, hxD⟩
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hay, hyD⟩
    have hcard2 : ({x, y} : Finset (Fin 20)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    calc 2 = ({x, y} : Finset (Fin 20)).card := hcard2.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hCsub : C ⊆ D := by
    intro w hw; rw [hCdef] at hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hCge : ∀ v ∈ C, 2 ≤ (G.neighborFinset v ∩ D).card := by
    intro v hv; rw [hCdef] at hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h | h | h | h <;> rw [h]
    · exact two_nbrs v₁ v₂ v₅ e12 e51.symm hv2D hv5D d25
    · exact two_nbrs v₂ v₁ v₃ e12.symm e23 hv1D hv3D d13
    · exact two_nbrs v₃ v₂ v₄ e23.symm e36 hv2D hv4D d24
    · exact two_nbrs v₄ v₃ v₅ e36.symm e45 hv3D hv5D d35
    · exact two_nbrs v₅ v₄ v₁ e45.symm e51 hv4D hv1D d14.symm
  have hCcard : C.card = 5 := by rw [hCdef]; exact hcard5
  have hCsum : 10 ≤ ∑ v ∈ C, (G.neighborFinset v ∩ D).card := by
    calc 10 = 2 * C.card := by rw [hCcard]
      _ = ∑ _v ∈ C, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hCge
  have hzeroOut : ∀ v ∈ D, v ∉ C → (G.neighborFinset v ∩ D).card = 0 := by
    intro v hvD hvC
    by_contra hne
    have hlt : ∑ w ∈ C, (G.neighborFinset w ∩ D).card
        < ∑ w ∈ D, (G.neighborFinset w ∩ D).card :=
      Finset.sum_lt_sum_of_subset hCsub hvD hvC (Nat.pos_of_ne_zero hne)
        (fun _ _ _ => Nat.zero_le _)
    omega
  have hsubset : D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0) ⊆ C := by
    intro v hv; rw [Finset.mem_filter] at hv
    by_contra hvC
    exact hv.2 (hzeroOut v hv.1 hvC)
  calc (D.filter (fun v => ¬(G.neighborFinset v ∩ D).card = 0)).card ≤ C.card :=
        Finset.card_le_card hsubset
    _ = 5 := hCcard

/-- **Refined `e(M) = 5` handshake count (`|D| ≥ 11`, `n = 20`).**  The handshake
(`∑_{Hub} deg = 72 − 3|D|`) caps the degree-`≥ 6` hubs, so the degree-`≤ 5` hubs `Hub₅` carry,
summed over the `M`-isolated set `Iso`, strictly more than `|Hub₅| + 1` incidences:
`|Hub₅| + 2 ≤ ∑_{Iso}|N ∩ Hub₅|`.  This sharpens the `< ` of `shared_hub_le5_eM5_twenty` to leave
room for deleting one hub. -/
theorem hub5_iso_count_twenty (G : SimpleGraph (Fin 20))
    (D Hub Hub5 H6 Iso : Finset (Fin 20))
    (hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3)
    (hmemHub : ∀ v : Fin 20, v ∈ Hub ↔ 4 ≤ G.degree v)
    (hmemHub5 : ∀ v : Fin 20, v ∈ Hub5 ↔ 4 ≤ G.degree v ∧ G.degree v ≤ 5)
    (hmemH6 : ∀ v : Fin 20, v ∈ H6 ↔ 6 ≤ G.degree v)
    (hIsoeq : Iso = D.filter (fun v => (G.neighborFinset v ∩ D).card = 0))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hDge9 : 11 ≤ D.card) (hIsoge : D.card - 5 ≤ Iso.card) :
    Hub5.card + 2 ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card := by
  classical
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  have hsum56 : ∑ v : Fin 20, G.degree v = 72 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 72 := by
    rw [Finset.sum_add_sum_compl]; exact hsum56
  have hHubsum : ∑ v ∈ Hub, G.degree v = 72 - 3 * D.card := by
    rw [hHubeqDc]; rw [hsumD] at hsplit; omega
  have hHubcard : Hub.card = 20 - D.card := by
    rw [hHubeqDc, Finset.card_compl]; simp [Fintype.card_fin]
  have hH6sub : H6 ⊆ Hub := by
    intro v hv; rw [hmemH6] at hv; rw [hmemHub]; omega
  have hHub5sub : ∀ v ∈ Hub5, 4 ≤ G.degree v := fun v hv => ((hmemHub5 v).mp hv).1
  have hH6ge : ∀ v ∈ H6, 6 ≤ G.degree v := fun v hv => (hmemH6 v).mp hv
  have hmemIso : ∀ v : Fin 20, v ∈ Iso ↔ v ∈ D ∧ (G.neighborFinset v ∩ D).card = 0 := by
    intro v; rw [hIsoeq, Finset.mem_filter]
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
    rw [hmemIso] at hv
    exact each_iso_three_hubs G D Hub hmemD hmemHub h3 v hv.1 hv.2
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
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hvsplit, hsumHub3]
  have hcrossH6 : ∑ v ∈ Iso, (G.neighborFinset v ∩ H6).card
      = ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card := cross_count_twenty G Iso H6
  have hH6degbound : ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card ≤ ∑ h ∈ H6, G.degree h := by
    apply Finset.sum_le_sum
    intro h _
    calc (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree h := G.card_neighborFinset_eq_degree h
  omega

/-- **A second deg-`≤ 5` shared hub avoiding a given hub `k` (`e(M) = 5`, `|D| ≥ 11`, `n = 20`).**
Suppose `k` is a degree-`≤ 5` hub whose neighbourhood contains a degree-`3` path `a–b–c` (so
`a, b, c` are *non*-`M`-isolated, with `k` their unique hub neighbour).  Then there is a
*different* deg-`≤ 5` hub `h ≠ k` carrying two distinct `M`-isolated degree-`3` twins.  The refined count
`hub5_iso_count_twenty` (`|Hub₅| + 2 ≤ ∑_{Iso}|N ∩ Hub₅|`) and the bound that `k` absorbs at most
two `Iso`-incidences (its other three neighbours `a, b, c` are non-isolated) keep the pigeonhole of
`shared_hub_le5_from_count_twenty` strict on `Hub₅ \ {k}`. -/
theorem exists_nonk_two_twin_hub_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hDge9 : 11 ≤ (Finset.univ.filter (fun w : Fin 20 => G.degree w = 3)).card)
    (v₁ v₂ v₃ v₄ v₅ : Fin 20)
    (hv1D : G.degree v₁ = 3) (hv2D : G.degree v₂ = 3) (hv3D : G.degree v₃ = 3)
    (hv4D : G.degree v₄ = 3) (hv5D : G.degree v₅ = 3)
    (hcard5 : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 20)).card = 5)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e36 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w : Fin 20 => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w : Fin 20 => G.degree w = 3)).card = 10)
    (k a b c : Fin 20) (hk4 : 4 ≤ G.degree k) (hk5 : G.degree k ≤ 5)
    (hda : G.degree a = 3) (hdb : G.degree b = 3) (hdc : G.degree c = 3)
    (hka : G.Adj k a) (hkb : G.Adj k b) (hkc : G.Adj k c)
    (hab : G.Adj a b) (hbc : G.Adj b c)
    (hab_ne : a ≠ b) (hbc_ne : b ≠ c) (hac_ne : a ≠ c) :
    ∃ h tt₁ tt₂ : Fin 20, h ≠ k ∧ 4 ≤ G.degree h ∧ G.degree h ≤ 5 ∧ tt₁ ≠ tt₂ ∧
      G.degree tt₁ = 3 ∧ G.degree tt₂ = 3 ∧ G.Adj tt₁ h ∧ G.Adj tt₂ h ∧
      (∀ w : Fin 20, G.Adj tt₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 20, G.Adj tt₂ w → G.degree w ≠ 3) := by
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
  -- `Iso.card ≥ |D| − 5`: the induced `C₅` is exactly the `M`-non-isolated set.
  have hIsoge : D.card - 5 ≤ Iso.card := by
    have hnon5 := nonIso_le_five_of_C5_twenty G D v₁ v₂ v₃ v₄ v₅
      ((hmemD v₁).mpr hv1D) ((hmemD v₂).mpr hv2D) ((hmemD v₃).mpr hv3D) ((hmemD v₄).mpr hv4D)
      ((hmemD v₅).mpr hv5D) hcard5 e12 e23 e36 e45 e51 hsum10
    have hpart := Finset.card_filter_add_card_filter_not (s := D)
      (fun v => (G.neighborFinset v ∩ D).card = 0)
    rw [← hIsodef] at hpart
    omega
  have hcount2 : Hub5.card + 2 ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card :=
    hub5_iso_count_twenty G D Hub Hub5 H6 Iso hmemD hmemHub hmemHub5 hmemH6 hIsodef hm h3
      hDge9 hIsoge
  -- `k ∈ Hub₅` and `k` absorbs at most two `Iso`-incidences.
  have hkHub5 : k ∈ Hub5 := (hmemHub5 k).mpr ⟨hk4, hk5⟩
  have haNotIso : a ∉ Iso := by
    rw [hIsodef, Finset.mem_filter]; rintro ⟨_, h0⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h0
    exact h0 b (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hab, (hmemD b).mpr hdb⟩)
  have hbNotIso : b ∉ Iso := by
    rw [hIsodef, Finset.mem_filter]; rintro ⟨_, h0⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h0
    exact h0 a (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hab.symm, (hmemD a).mpr hda⟩)
  have hcNotIso : c ∉ Iso := by
    rw [hIsodef, Finset.mem_filter]; rintro ⟨_, h0⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at h0
    exact h0 b (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hbc.symm, (hmemD b).mpr hdb⟩)
  set S : Finset (Fin 20) := Iso.filter (fun v => G.Adj v k) with hSdef
  have hSsub : insert a (insert b (insert c S)) ⊆ G.neighborFinset k := by
    intro w hw
    simp only [Finset.mem_insert] at hw
    rcases hw with rfl | rfl | rfl | hwS
    · exact (G.mem_neighborFinset _ _).mpr hka
    · exact (G.mem_neighborFinset _ _).mpr hkb
    · exact (G.mem_neighborFinset _ _).mpr hkc
    · rw [hSdef, Finset.mem_filter] at hwS
      exact (G.mem_neighborFinset _ _).mpr hwS.2.symm
  have hcS : c ∉ S := fun hm => hcNotIso (by rw [hSdef, Finset.mem_filter] at hm; exact hm.1)
  have hbS : b ∉ insert c S := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hbc_ne, fun hm => hbNotIso (by rw [hSdef, Finset.mem_filter] at hm; exact hm.1)⟩
  have haS : a ∉ insert b (insert c S) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hab_ne, hac_ne, fun hm => haNotIso (by rw [hSdef, Finset.mem_filter] at hm; exact hm.1)⟩
  have hcardins : (insert a (insert b (insert c S))).card = S.card + 3 := by
    rw [Finset.card_insert_of_notMem haS, Finset.card_insert_of_notMem hbS,
        Finset.card_insert_of_notMem hcS]
  have hSle2 : S.card ≤ 2 := by
    have hle := Finset.card_le_card hSsub
    rw [hcardins, G.card_neighborFinset_eq_degree] at hle
    omega
  -- Deleting `k` from `Hub₅` loses at most `|S| ≤ 2` incidences.
  have hper : ∀ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card
      ≤ (G.neighborFinset v ∩ Hub5.erase k).card + (if G.Adj v k then 1 else 0) := by
    intro v _
    rw [Finset.inter_erase]
    by_cases hvk : G.Adj v k
    · simp only [hvk, if_true]
      have hmem : k ∈ G.neighborFinset v ∩ Hub5 :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvk, hkHub5⟩
      rw [Finset.card_erase_of_mem hmem]; omega
    · simp only [hvk, if_false, add_zero]
      have hk_notin : k ∉ G.neighborFinset v ∩ Hub5 := fun hmem =>
        hvk ((G.mem_neighborFinset _ _).mp (Finset.mem_of_mem_inter_left hmem))
      rw [Finset.erase_eq_of_notMem hk_notin]
  have hsum_erase : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card
      ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub5.erase k).card + 2 := by
    have h1 : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub5).card
        ≤ ∑ v ∈ Iso, ((G.neighborFinset v ∩ Hub5.erase k).card
          + (if G.Adj v k then 1 else 0)) := Finset.sum_le_sum hper
    rw [Finset.sum_add_distrib] at h1
    have h2 : ∑ v ∈ Iso, (if G.Adj v k then 1 else 0) = S.card := by
      rw [hSdef]; exact (Finset.card_filter _ _).symm
    omega
  have hkpos : 1 ≤ Hub5.card := Finset.card_pos.mpr ⟨k, hkHub5⟩
  have heraseCard : (Hub5.erase k).card = Hub5.card - 1 := Finset.card_erase_of_mem hkHub5
  have hcountE : (Hub5.erase k).card
      < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub5.erase k).card := by omega
  -- Pigeonhole on `Hub₅ \ {k}` via `shared_hub_le5_from_count_twenty`.
  obtain ⟨h, tt₁, tt₂, hhErase, hh5, ht12, ht1deg, ht2deg, hAt1h, hAt2h, ht1iso, ht2iso⟩ :=
    shared_hub_le5_from_count_twenty G Iso (Hub5.erase k) hIsoiso
      (fun h hh => ((hmemHub5 h).mp (Finset.mem_of_mem_erase hh)).2) hcountE
  have hhk : h ≠ k := Finset.ne_of_mem_erase hhErase
  have hh4 : 4 ≤ G.degree h := ((hmemHub5 h).mp (Finset.mem_of_mem_erase hhErase)).1
  exact ⟨h, tt₁, tt₂, hhk, hh4, hh5, ht12, ht1deg, ht2deg, hAt1h, hAt2h, ht1iso, ht2iso⟩

/-- **The `|D| = 10` second-hub extraction** — the low-`|D|` complement of
`exists_nonk_two_twin_hub_twenty`, using the shared hub's **own two twins**.
With `k`'s five neighbours pinned (`a, b, c` on the cycle plus the two
`M`-isolated twins `tw₁, tw₂`), `deg k = 5` exactly, and the hub degree-sum
`72 − 3|D|` over `20 − |D|` hubs excludes every degree-`≥ 6` hub whenever
`|D| ≤ 10` (`5 + 6 + 4(|Hub|−2) = 83 − 4|D| > 72 − 3|D|`).  All hubs are then
`Hub₅`, every `M`-isolated twin carries three `Hub₅`-incidences, and deleting
`k` (which absorbs exactly two) leaves `3(|D|−5) − 2 > 19 − |D|` incidences on
`Hub₅ \ {k}` (strict **only** for `|D| = 10` at `n = 20`: unlike `n = 19`,
the pigeonhole *ties* at `|D| = 9`, where the second hub can fail to exist —
that boundary is covered by `alldeg4_iso_cherry_D9_twenty` below), so the
pigeonhole extractor `shared_hub_le5_from_count_twenty` returns the second hub. -/
theorem exists_nonk_two_twin_hub_lowD_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hD10 : (Finset.univ.filter (fun w : Fin 20 => G.degree w = 3)).card = 10)
    (v₁ v₂ v₃ v₄ v₅ : Fin 20)
    (hv1D : G.degree v₁ = 3) (hv2D : G.degree v₂ = 3) (hv3D : G.degree v₃ = 3)
    (hv4D : G.degree v₄ = 3) (hv5D : G.degree v₅ = 3)
    (hcard5 : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 20)).card = 5)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e36 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w : Fin 20 => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w : Fin 20 => G.degree w = 3)).card = 10)
    (k a b c tw₁ tw₂ : Fin 20) (hk5 : G.degree k ≤ 5)
    (hda : G.degree a = 3) (hdb : G.degree b = 3) (hdc : G.degree c = 3)
    (hka : G.Adj k a) (hkb : G.Adj k b) (hkc : G.Adj k c)
    (hab : G.Adj a b) (hbc : G.Adj b c)
    (hab_ne : a ≠ b) (hbc_ne : b ≠ c) (hac_ne : a ≠ c)
    (htw12 : tw₁ ≠ tw₂) (htw1deg : G.degree tw₁ = 3) (htw2deg : G.degree tw₂ = 3)
    (hAtw1k : G.Adj tw₁ k) (hAtw2k : G.Adj tw₂ k)
    (htw1iso : ∀ w : Fin 20, G.Adj tw₁ w → G.degree w ≠ 3)
    (htw2iso : ∀ w : Fin 20, G.Adj tw₂ w → G.degree w ≠ 3) :
    ∃ h tt₁ tt₂ : Fin 20, h ≠ k ∧ 4 ≤ G.degree h ∧ G.degree h ≤ 5 ∧ tt₁ ≠ tt₂ ∧
      G.degree tt₁ = 3 ∧ G.degree tt₂ = 3 ∧ G.Adj tt₁ h ∧ G.Adj tt₂ h ∧
      (∀ w : Fin 20, G.Adj tt₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 20, G.Adj tt₂ w → G.degree w ≠ 3) := by
  classical
  set D : Finset (Fin 20) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 20) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 20, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  -- the five pinned neighbours of `k` are pairwise distinct
  have hatw1 : a ≠ tw₁ := by rintro rfl; exact htw1iso b hab hdb
  have hbtw1 : b ≠ tw₁ := by rintro rfl; exact htw1iso a hab.symm hda
  have hctw1 : c ≠ tw₁ := by rintro rfl; exact htw1iso b hbc.symm hdb
  have hatw2 : a ≠ tw₂ := by rintro rfl; exact htw2iso b hab hdb
  have hbtw2 : b ≠ tw₂ := by rintro rfl; exact htw2iso a hab.symm hda
  have hctw2 : c ≠ tw₂ := by rintro rfl; exact htw2iso b hbc.symm hdb
  have hsub5 : ({a, b, c, tw₁, tw₂} : Finset (Fin 20)) ⊆ G.neighborFinset k := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr hka
    · exact (G.mem_neighborFinset _ _).mpr hkb
    · exact (G.mem_neighborFinset _ _).mpr hkc
    · exact (G.mem_neighborFinset _ _).mpr hAtw1k.symm
    · exact (G.mem_neighborFinset _ _).mpr hAtw2k.symm
  have hcard5' : ({a, b, c, tw₁, tw₂} : Finset (Fin 20)).card = 5 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hab_ne, hac_ne, hatw1, hatw2⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hbc_ne, hbtw1, hbtw2⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hctw1, hctw2⟩),
      Finset.card_insert_of_notMem (by
        rw [Finset.mem_singleton]
        exact htw12),
      Finset.card_singleton]
  have hk5eq : G.degree k = 5 := by
    have hle := Finset.card_le_card hsub5
    rw [hcard5', G.card_neighborFinset_eq_degree] at hle
    omega
  -- the neighbourhood of `k` is exactly the pinned five
  have hNk : G.neighborFinset k = ({a, b, c, tw₁, tw₂} : Finset (Fin 20)) := by
    refine (Finset.eq_of_subset_of_card_le hsub5 ?_).symm
    rw [hcard5', G.card_neighborFinset_eq_degree, hk5eq]
  -- the handshake and the hub degree sum
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  have hsum72 : ∑ v : Fin 20, G.degree v = 72 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 72 := by
    rw [Finset.sum_add_sum_compl]; exact hsum72
  have hHubsum : ∑ v ∈ Hub, G.degree v = 72 - 3 * D.card := by
    rw [hHubeqDc]; rw [hsumD] at hsplit; omega
  have hHubcard : Hub.card = 20 - D.card := by
    rw [hHubeqDc, Finset.card_compl]; simp [Fintype.card_fin]
  have hkHub : k ∈ Hub := (hmemHub k).mpr (by omega)
  -- `|D| ≤ 10` kills every degree-`≥ 6` hub
  have hH5 : ∀ h ∈ Hub, G.degree h ≤ 5 := by
    intro h6 hh6
    by_contra hcon
    push Not at hcon
    have hne : k ≠ h6 := by
      rintro rfl
      omega
    have hh6e : h6 ∈ Hub.erase k := Finset.mem_erase.mpr ⟨fun he => hne he.symm, hh6⟩
    have hsum1 : ∑ v ∈ Hub, G.degree v
        = G.degree k + ∑ v ∈ Hub.erase k, G.degree v :=
      (Finset.add_sum_erase _ _ hkHub).symm
    have hsum2 : ∑ v ∈ Hub.erase k, G.degree v
        = G.degree h6 + ∑ v ∈ (Hub.erase k).erase h6, G.degree v :=
      (Finset.add_sum_erase _ _ hh6e).symm
    have hsum3 : 4 * ((Hub.erase k).erase h6).card
        ≤ ∑ v ∈ (Hub.erase k).erase h6, G.degree v := by
      calc 4 * ((Hub.erase k).erase h6).card
          = ∑ _v ∈ (Hub.erase k).erase h6, 4 := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ v ∈ (Hub.erase k).erase h6, G.degree v := by
            refine Finset.sum_le_sum fun v hv => ?_
            exact (hmemHub v).mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv))
    have hcards : ((Hub.erase k).erase h6).card = Hub.card - 2 := by
      rw [Finset.card_erase_of_mem hh6e, Finset.card_erase_of_mem hkHub]
      omega
    -- `72 − 3|D| ≥ 5 + 6 + 4(|Hub| − 2) = 83 − 4|D|` forces `|D| ≥ 11`
    have hDcard20 : D.card ≤ 20 := by
      rw [hDdef]
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    omega
  -- the `M`-isolated set and its size
  set Iso : Finset (Fin 20) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0)
    with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3 := by
    intro v hv
    rw [hIsodef, Finset.mem_filter] at hv
    obtain ⟨hvD, hv0⟩ := hv
    refine ⟨(hmemD v).mp hvD, fun w hadj hw3 => ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
    exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj,
      (hmemD w).mpr hw3⟩)
  have hIsoge : D.card - 5 ≤ Iso.card := by
    have hnon5 := nonIso_le_five_of_C5_twenty G D v₁ v₂ v₃ v₄ v₅
      ((hmemD v₁).mpr hv1D) ((hmemD v₂).mpr hv2D) ((hmemD v₃).mpr hv3D)
      ((hmemD v₄).mpr hv4D) ((hmemD v₅).mpr hv5D) hcard5 e12 e23 e36 e45 e51 hsum10
    have hpart := Finset.card_filter_add_card_filter_not (s := D)
      (fun v => (G.neighborFinset v ∩ D).card = 0)
    rw [← hIsodef] at hpart
    omega
  -- every `M`-isolated twin carries three `Hub`-incidences
  have hIso3 : ∀ v ∈ Iso, (G.neighborFinset v ∩ Hub).card = 3 := by
    intro v hv
    obtain ⟨hv3, hviso⟩ := hIsoiso v hv
    have hsub : G.neighborFinset v ⊆ Hub := by
      intro w hw
      rw [G.mem_neighborFinset] at hw
      rw [hmemHub]
      have h1 := hviso w hw
      have h2 := h3 w
      omega
    rw [Finset.inter_eq_left.mpr hsub, G.card_neighborFinset_eq_degree, hv3]
  have hsumIso : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card = 3 * Iso.card := by
    rw [Finset.sum_congr rfl hIso3, Finset.sum_const, smul_eq_mul, mul_comm]
  -- `k` absorbs exactly its two twins from `Iso`
  set S : Finset (Fin 20) := Iso.filter (fun v => G.Adj v k) with hSdef
  have hSle2 : S.card ≤ 2 := by
    have hsub : S ⊆ ({tw₁, tw₂} : Finset (Fin 20)) := by
      intro w hw
      rw [hSdef, Finset.mem_filter] at hw
      obtain ⟨hwIso, hwk⟩ := hw
      have hwNk : w ∈ G.neighborFinset k := (G.mem_neighborFinset _ _).mpr hwk.symm
      rw [hNk] at hwNk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwNk
      rcases hwNk with rfl | rfl | rfl | rfl | rfl
      · exact absurd hab ((hIsoiso w hwIso).2 b · hdb)
      · exact absurd hab.symm ((hIsoiso w hwIso).2 a · hda)
      · exact absurd hbc.symm ((hIsoiso w hwIso).2 b · hdb)
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    calc S.card ≤ ({tw₁, tw₂} : Finset (Fin 20)).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by rw [Finset.card_singleton])
  -- deleting `k` loses at most two incidences
  have hper : ∀ v ∈ Iso, (G.neighborFinset v ∩ Hub).card
      ≤ (G.neighborFinset v ∩ Hub.erase k).card + (if G.Adj v k then 1 else 0) := by
    intro v _
    rw [Finset.inter_erase]
    by_cases hvk : G.Adj v k
    · simp only [hvk, if_true]
      have hmem : k ∈ G.neighborFinset v ∩ Hub :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvk, hkHub⟩
      rw [Finset.card_erase_of_mem hmem]; omega
    · simp only [hvk, if_false, add_zero]
      have hk_notin : k ∉ G.neighborFinset v ∩ Hub := fun hmem =>
        hvk ((G.mem_neighborFinset _ _).mp (Finset.mem_of_mem_inter_left hmem))
      rw [Finset.erase_eq_of_notMem hk_notin]
  have hsum_erase : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card
      ≤ ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub.erase k).card + 2 := by
    have h1 : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card
        ≤ ∑ v ∈ Iso, ((G.neighborFinset v ∩ Hub.erase k).card
          + (if G.Adj v k then 1 else 0)) := Finset.sum_le_sum hper
    rw [Finset.sum_add_distrib] at h1
    have h2 : ∑ v ∈ Iso, (if G.Adj v k then 1 else 0) = S.card := by
      rw [hSdef]; exact (Finset.card_filter _ _).symm
    omega
  -- the strict count on `Hub \ {k}` and the extraction
  have heraseCard : (Hub.erase k).card = Hub.card - 1 := Finset.card_erase_of_mem hkHub
  have hcountE : (Hub.erase k).card
      < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub.erase k).card := by
    -- `18 − |D| < 3(|D| − 5) − 2` for `|D| ≥ 9`
    omega
  obtain ⟨h, tt₁, tt₂, hhErase, hh5, ht12, ht1deg, ht2deg, hAt1h, hAt2h, ht1iso, ht2iso⟩ :=
    shared_hub_le5_from_count_twenty G Iso (Hub.erase k) hIsoiso
      (fun h hh => hH5 h (Finset.mem_of_mem_erase hh)) hcountE
  have hhk : h ≠ k := Finset.ne_of_mem_erase hhErase
  have hh4 : 4 ≤ G.degree h := (hmemHub h).mp (Finset.mem_of_mem_erase hhErase)
  exact ⟨h, tt₁, tt₂, hhk, hh4, hh5, ht12, ht1deg, ht2deg, hAt1h, hAt2h, ht1iso, ht2iso⟩

/-- **The `|D| = 9` all-degree-`4` `M`-isolated cherry (`n = 20`).**  At `n = 20` the second-hub
pigeonhole of `exists_nonk_two_twin_hub_lowD_twenty` *ties* at `|D| = 9` (`3(|D|−5) − 2 = 10`
incidences on the `10` hubs other than `k`), and the second hub can genuinely fail to exist.
Instead the handshake kills the residual: `k`'s five neighbours are pinned (`deg k = 5`), the hub
degree-sum `72 − 27 = 45` over `11` hubs makes `k` the *unique* degree-`5` hub
(`5 + 5 + 4 · 9 = 46 > 45`), and an `M`-isolated twin avoiding `k` exists (`|Iso| ≥ 4` while `k`
carries only `tw₁, tw₂`); all three of its neighbours have degree exactly `4`, feeding the
`SingleVertexConfig` route. -/
theorem alldeg4_iso_cherry_D9_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hD9 : (Finset.univ.filter (fun w : Fin 20 => G.degree w = 3)).card = 9)
    (v₁ v₂ v₃ v₄ v₅ : Fin 20)
    (hv1D : G.degree v₁ = 3) (hv2D : G.degree v₂ = 3) (hv3D : G.degree v₃ = 3)
    (hv4D : G.degree v₄ = 3) (hv5D : G.degree v₅ = 3)
    (hcard5 : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 20)).card = 5)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e36 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w : Fin 20 => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w : Fin 20 => G.degree w = 3)).card = 10)
    (k a b c tw₁ tw₂ : Fin 20) (hk5 : G.degree k ≤ 5)
    (hda : G.degree a = 3) (hdb : G.degree b = 3) (hdc : G.degree c = 3)
    (hka : G.Adj k a) (hkb : G.Adj k b) (hkc : G.Adj k c)
    (hab : G.Adj a b) (hbc : G.Adj b c)
    (hab_ne : a ≠ b) (hbc_ne : b ≠ c) (hac_ne : a ≠ c)
    (htw12 : tw₁ ≠ tw₂) (htw1deg : G.degree tw₁ = 3) (htw2deg : G.degree tw₂ = 3)
    (hAtw1k : G.Adj tw₁ k) (hAtw2k : G.Adj tw₂ k)
    (htw1iso : ∀ w : Fin 20, G.Adj tw₁ w → G.degree w ≠ 3)
    (htw2iso : ∀ w : Fin 20, G.Adj tw₂ w → G.degree w ≠ 3) :
    ∃ u : Fin 20, G.degree u = 3 ∧ (∀ w : Fin 20, G.Adj u w → G.degree w ≠ 3) ∧
      (∀ w : Fin 20, G.Adj u w → G.degree w = 4) := by
  classical
  set D : Finset (Fin 20) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 20, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 20) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 20, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  -- the five pinned neighbours of `k` are pairwise distinct, so `deg k = 5` and
  -- `N(k) = {a, b, c, tw₁, tw₂}`
  have hatw1 : a ≠ tw₁ := by rintro rfl; exact htw1iso b hab hdb
  have hbtw1 : b ≠ tw₁ := by rintro rfl; exact htw1iso a hab.symm hda
  have hctw1 : c ≠ tw₁ := by rintro rfl; exact htw1iso b hbc.symm hdb
  have hatw2 : a ≠ tw₂ := by rintro rfl; exact htw2iso b hab hdb
  have hbtw2 : b ≠ tw₂ := by rintro rfl; exact htw2iso a hab.symm hda
  have hctw2 : c ≠ tw₂ := by rintro rfl; exact htw2iso b hbc.symm hdb
  have hsub5 : ({a, b, c, tw₁, tw₂} : Finset (Fin 20)) ⊆ G.neighborFinset k := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr hka
    · exact (G.mem_neighborFinset _ _).mpr hkb
    · exact (G.mem_neighborFinset _ _).mpr hkc
    · exact (G.mem_neighborFinset _ _).mpr hAtw1k.symm
    · exact (G.mem_neighborFinset _ _).mpr hAtw2k.symm
  have hcard5' : ({a, b, c, tw₁, tw₂} : Finset (Fin 20)).card = 5 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hab_ne, hac_ne, hatw1, hatw2⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hbc_ne, hbtw1, hbtw2⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hctw1, hctw2⟩),
      Finset.card_insert_of_notMem (by
        rw [Finset.mem_singleton]
        exact htw12),
      Finset.card_singleton]
  have hk5eq : G.degree k = 5 := by
    have hle := Finset.card_le_card hsub5
    rw [hcard5', G.card_neighborFinset_eq_degree] at hle
    omega
  have hNk : G.neighborFinset k = ({a, b, c, tw₁, tw₂} : Finset (Fin 20)) := by
    refine (Finset.eq_of_subset_of_card_le hsub5 ?_).symm
    rw [hcard5', G.card_neighborFinset_eq_degree, hk5eq]
  -- the handshake: `∑_{Hub} deg = 45` over `11` hubs, so `k` is the unique degree-`5` hub
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  have hsum72 : ∑ v : Fin 20, G.degree v = 72 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 72 := by
    rw [Finset.sum_add_sum_compl]; exact hsum72
  have hHubsum : ∑ v ∈ Hub, G.degree v = 72 - 3 * D.card := by
    rw [hHubeqDc]; rw [hsumD] at hsplit; omega
  have hHubcard : Hub.card = 20 - D.card := by
    rw [hHubeqDc, Finset.card_compl]; simp [Fintype.card_fin]
  have hkHub : k ∈ Hub := (hmemHub k).mpr (by omega)
  have hother4 : ∀ h ∈ Hub, h ≠ k → G.degree h = 4 := by
    intro h6 hh6 hne
    by_contra hcon
    have hh5 : 5 ≤ G.degree h6 := by
      have := (hmemHub h6).mp hh6; omega
    have hh6e : h6 ∈ Hub.erase k := Finset.mem_erase.mpr ⟨hne, hh6⟩
    have hsum1 : ∑ v ∈ Hub, G.degree v
        = G.degree k + ∑ v ∈ Hub.erase k, G.degree v :=
      (Finset.add_sum_erase _ _ hkHub).symm
    have hsum2 : ∑ v ∈ Hub.erase k, G.degree v
        = G.degree h6 + ∑ v ∈ (Hub.erase k).erase h6, G.degree v :=
      (Finset.add_sum_erase _ _ hh6e).symm
    have hsum3 : 4 * ((Hub.erase k).erase h6).card
        ≤ ∑ v ∈ (Hub.erase k).erase h6, G.degree v := by
      calc 4 * ((Hub.erase k).erase h6).card
          = ∑ _v ∈ (Hub.erase k).erase h6, 4 := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ v ∈ (Hub.erase k).erase h6, G.degree v := by
            refine Finset.sum_le_sum fun v hv => ?_
            exact (hmemHub v).mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv))
    have hcards : ((Hub.erase k).erase h6).card = Hub.card - 2 := by
      rw [Finset.card_erase_of_mem hh6e, Finset.card_erase_of_mem hkHub]
      omega
    -- `45 = 72 − 27 ≥ 5 + 5 + 4 · 9 = 46` is absurd
    omega
  -- the `M`-isolated set has at least four members and `k` carries only `tw₁, tw₂`
  set Iso : Finset (Fin 20) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0)
    with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 20, G.Adj v w → G.degree w ≠ 3 := by
    intro v hv
    rw [hIsodef, Finset.mem_filter] at hv
    obtain ⟨hvD, hv0⟩ := hv
    refine ⟨(hmemD v).mp hvD, fun w hadj hw3 => ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
    exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj,
      (hmemD w).mpr hw3⟩)
  have hIsoge : D.card - 5 ≤ Iso.card := by
    have hnon5 := nonIso_le_five_of_C5_twenty G D v₁ v₂ v₃ v₄ v₅
      ((hmemD v₁).mpr hv1D) ((hmemD v₂).mpr hv2D) ((hmemD v₃).mpr hv3D)
      ((hmemD v₄).mpr hv4D) ((hmemD v₅).mpr hv5D) hcard5 e12 e23 e36 e45 e51 hsum10
    have hpart := Finset.card_filter_add_card_filter_not (s := D)
      (fun v => (G.neighborFinset v ∩ D).card = 0)
    rw [← hIsodef] at hpart
    omega
  set S : Finset (Fin 20) := Iso.filter (fun v => G.Adj v k) with hSdef
  have hSle2 : S.card ≤ 2 := by
    have hsub : S ⊆ ({tw₁, tw₂} : Finset (Fin 20)) := by
      intro w hw
      rw [hSdef, Finset.mem_filter] at hw
      obtain ⟨hwIso, hwk⟩ := hw
      have hwNk : w ∈ G.neighborFinset k := (G.mem_neighborFinset _ _).mpr hwk.symm
      rw [hNk] at hwNk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwNk
      rcases hwNk with rfl | rfl | rfl | rfl | rfl
      · exact absurd hab ((hIsoiso w hwIso).2 b · hdb)
      · exact absurd hab.symm ((hIsoiso w hwIso).2 a · hda)
      · exact absurd hbc.symm ((hIsoiso w hwIso).2 b · hdb)
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    calc S.card ≤ ({tw₁, tw₂} : Finset (Fin 20)).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by rw [Finset.card_singleton])
  -- extract an `M`-isolated twin avoiding `k`; its cherry is all-degree-`4`
  obtain ⟨u, huIso, huS⟩ : ∃ u : Fin 20, u ∈ Iso ∧ u ∉ S := by
    by_contra hcon
    push Not at hcon
    have hsub : Iso ⊆ S := fun w hw => hcon w hw
    have := Finset.card_le_card hsub
    omega
  obtain ⟨hu3, huiso⟩ := hIsoiso u huIso
  have hunk : ¬G.Adj u k := fun hadj =>
    huS (by rw [hSdef, Finset.mem_filter]; exact ⟨huIso, hadj⟩)
  refine ⟨u, hu3, huiso, fun w hw => ?_⟩
  have hw4 : 4 ≤ G.degree w := by
    have h1 := huiso w hw
    have h2 := h3 w
    omega
  have hwk : w ≠ k := fun he => hunk (he ▸ hw)
  exact hother4 w ((hmemHub w).mpr hw4) hwk

/-- **`e(M) = 5` (`s = 10`) two-twin cut for the `|D| = 13`, `|Hub| = 7` corner (`n = 20`).**
Unlike `n = 16`, the degree sum `72` is divisible by `3`, so the *degree-`4`* shared-hub
pigeonhole only *ties* in the induced-`C₅` branch and is no longer strict.  We therefore
route the **dominating-edge** branch through the deg-`≤ 5` shared hub (`shared_hub_le5_eM5`,
strict because `|Hub| = 7`) and the deg-`≤ 5` leaf-cherry (`claw`) assembly, and the
**induced-`C₅`**
branch through `c5_shared_two_twin_le5_twenty` (`TwinCert20DenseLe5`).  The former residual — a
deg-`5` shared hub adjacent to three *consecutive* cycle vertices (triangle degree sum
`5 + 3 + 3 = 11 > 10`, escaping `hT`, with no induced `C₄`) — is now closed via the second-hub
extraction `exists_nonk_two_twin_hub_twenty` threaded as `hnonk`. -/
theorem two_twin_eM5_twenty (G : SimpleGraph (Fin 20))
    (hm : G.edgeFinset.card = 36) (h3 : ∀ v : Fin 20, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 20, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 20, ({a, b, c, d} : Finset (Fin 20)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (hHub7 : (Finset.univ.filter (fun v : Fin 20 => 4 ≤ G.degree v)).card = 7)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 10) :
    TwoTwinConfig G := by
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
  -- `|D| = 13` from `|Hub| = |Dᶜ| = 7`.
  have hDc : Dᶜ = Finset.univ.filter (fun v : Fin 20 => 4 ≤ G.degree v) := by
    ext w
    rw [Finset.mem_compl, hmemD, Finset.mem_filter]
    constructor
    · intro hne3; exact ⟨Finset.mem_univ _, by have := h3 w; omega⟩
    · rintro ⟨_, h4⟩ h3eq; omega
  have hcc : D.card + Dᶜ.card = 20 := by
    have h := Finset.card_add_card_compl D; simp only [Fintype.card_fin] at h; exact h
  have hD13 : D.card = 13 := by rw [hDc] at hcc; omega
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
    obtain ⟨k, tw1, tw2, hkle5, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso, htw2iso⟩ :=
      shared_hub_le5_eM5_twenty G hm h3 h2k2 (by rw [← hDdef]; exact hD13)
        (by rw [← hDdef]; exact hsum10.le)
    have hkge4 : 4 ≤ G.degree k := by
      have := htw1iso k hAtw1k; have := h3 k; omega
    exact dom_fat_centre_two_twin_le5_twenty G D hmemD hT hC4 c₁ c₂ hc1D hc2D hc12 hcov hge
      hindle k tw1 tw2 hkge4 hkle5 htw12 htw1deg htw2deg hAtw1k hAtw2k htw1iso htw2iso
  · -- **Induced-`C₅` branch with a deg-`≤ 5` shared hub.**  Extract a shared deg-`≤ 5` hub and
    -- route through `c5_shared_two_twin_le5_twenty`; the deg-`5` 3-consecutive-hit residual is
    -- closed by `exists_nonk_two_twin_hub_twenty` supplying a second hub `h ≠ k`.
    obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5, e12, e23, e36, e45, e51,
      n13, n14, n24, n25, n35, _hdom⟩ := hC5
    obtain ⟨k, tw1, tw2, hkle5, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso, htw2iso⟩ :=
      shared_hub_le5_eM5_twenty G hm h3 h2k2 (by rw [← hDdef]; exact hD13)
        (by rw [← hDdef]; exact hsum10.le)
    have hkge4 : 4 ≤ G.degree k := by
      have := htw1iso k hAtw1k; have := h3 k; omega
    exact c5_shared_two_twin_le5_twenty G hT hC4 k tw1 tw2 hkge4 hkle5 htw12 htw1deg htw2deg
      hAtw1k hAtw2k htw1iso htw2iso
      (fun a b c hda hdb hdc hka hkb hkc hab hbc hab_ne hbc_ne hac_ne =>
        exists_nonk_two_twin_hub_twenty G hm h3 (by rw [← hDdef]; omega)
          v₁ v₂ v₃ v₄ v₅ ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D) ((hmemD v₃).mp hv3D)
          ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5 e12 e23 e36 e45 e51
          (by rw [← hDdef]; exact hsum10) k a b c
          hkge4 hkle5 hda hdb hdc hka hkb hkc hab hbc hab_ne hbc_ne hac_ne)
      v₁ v₂ v₃ v₄ v₅ ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D)
      ((hmemD v₃).mp hv3D) ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5
      e12 e23 e36 e45 e51 n13 n14 n24 n25 n35

end N20

end ACMax
