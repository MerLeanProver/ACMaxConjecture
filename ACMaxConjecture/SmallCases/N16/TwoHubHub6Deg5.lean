import ACMaxConjecture.Base
import ACMaxConjecture.SmallCases.N16.Core
import ACMaxConjecture.SmallCases.Certificates
import ACMaxConjecture.SmallCases.N16.Dense
import ACMaxConjecture.SmallCases.N16.Align8Helpers

/-!
# `n = 16`, `|D| = 10`, `|Hub| = 6`, `e(M) = 5` (`s = 10`) shared-hub helper

The genuinely degenerate `e(M) = 5` corner of the `|Hub| = 6` alignment selector
(`two_hub_or_single_vertex_hub6_sixteen`).  At `e(M) = 5` the residual is the double-star
(`|Iso| = 4`, two centres of in-`M`-degree `3` plus four leaves) or an induced `C₅`
(`|Iso| = 5`).  The deg-`4`-shared-hub pigeonhole used at `e(M) ≤ 4` degenerates, BUT:

* **double-star branch:** the `4` `M`-isolated twins each meet `3` hubs, giving `12 > 6 = |Hub|`
  twin–hub incidences; excluding the at-most-one degree-`6` hub leaves `≥ 2·|Iso| = 8 > 6`
  incidences on the deg-`≤ 5` hubs, so a deg-`≤ 5` hub is shared by two `M`-isolated twins.  The
  two-twin cut certificate permits `deg h ≤ 5` (boundary `deg h + 7 ≤ 12`), so the leaf-cherry
  assembly (`claw`) goes through with a deg-`≤ 5` hub.

* **induced-`C₅` branch:** the `5` cycle vertices carry all `10` of `∑_{v∈D}|N v ∩ D|`, so the
  other `5` degree-`3` vertices are `M`-isolated (`|Iso| ≥ 5`); the refined cross count then forces
  a deg-`4` hub shared by two `M`-isolated twins, and the existing `C₅` two-twin assembly applies.

This closes the `e(M) = 5` sub-case of `two_hub_or_single_vertex_hub6_sixteen`
(`TwinCert16TwoHubHub6.lean`) and supplies the shared-hub lemma `halign8_sixteen` needs.
-/

namespace ACMax

open scoped Classical

namespace N16

/-- **Shared deg-`≤ 5` hub by pigeonhole (`n = 16`).**  Port of `shared_deg4_hub_from_count_sixteen`
dropping the degree-`4` restriction to degree-`≤ 5`: if the deg-`≤ 5` hub set `Hub` carries strictly
more twin-incidences from the `M`-isolated set `Iso` than it has vertices, some hub is adjacent to
two distinct `M`-isolated degree-`3` twins. -/
theorem shared_hub_le5_from_count_sixteen (G : SimpleGraph (Fin 16)) (Iso Hub : Finset (Fin 16))
    (hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 16, G.Adj v w → G.degree w ≠ 3)
    (hHubdeg : ∀ h ∈ Hub, G.degree h ≤ 5)
    (hcount : Hub.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub).card) :
    ∃ h t₁ t₂ : Fin 16, G.degree h ≤ 5 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 16, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 16, G.Adj t₂ w → G.degree w ≠ 3) := by
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
      have hL : ∀ v : Fin 16, (G.neighborFinset v ∩ Hub).card
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
  exact ⟨h, t₁, t₂, hHubdeg h hhHub, ht12, ht1deg, ht2deg, hAt1h, hAt2h, ht1iso, ht2iso⟩

/-- **Two-twin bundle assembly with a deg-`≤ 5` hub (`n = 16`).**  Port of `dense_two_twin_assemble`
permitting the hub `h` to have degree `4` or `5` (the two-twin cut certificate allows `deg h ≤ 5`).
The hub being a genuine hub (`4 ≤ deg h`) supplies the `h ≠ x/y/z` distinctnesses. -/
theorem dense_two_twin_assemble_le5 (G : SimpleGraph (Fin 16)) (t₁ t₂ h x y z : Fin 16)
    (ht1deg : G.degree t₁ = 3) (ht2deg : G.degree t₂ = 3)
    (hhge4 : 4 ≤ G.degree h) (hhle5 : G.degree h ≤ 5)
    (hdegx : G.degree x = 3) (hdegy : G.degree y = 3) (hdegz : G.degree z = 3)
    (hAt1h : G.Adj t₁ h) (hAt2h : G.Adj t₂ h) (hxyA : G.Adj x y) (hyzA : G.Adj y z)
    (ht1iso : ∀ w : Fin 16, G.Adj t₁ w → G.degree w ≠ 3)
    (ht2iso : ∀ w : Fin 16, G.Adj t₂ w → G.degree w ≠ 3)
    (hhx : ¬G.Adj h x) (hhy : ¬G.Adj h y) (hhz : ¬G.Adj h z)
    (ht12 : t₁ ≠ t₂) (hxy_ne : x ≠ y) (hyz_ne : y ≠ z) (hxz_ne : x ≠ z) :
    TwoTwinConfig G := by
  exact ⟨t₁, t₂, h, x, y, z, ht1deg, ht2deg, hhle5, hdegx, hdegy, hdegz,
    hAt1h, hAt2h, hxyA, hyzA,
    (fun hadj => ht1iso x hadj hdegx), (fun hadj => ht1iso y hadj hdegy),
    (fun hadj => ht1iso z hadj hdegz),
    (fun hadj => ht2iso x hadj hdegx), (fun hadj => ht2iso y hadj hdegy),
    (fun hadj => ht2iso z hadj hdegz),
    hhx, hhy, hhz, ht12,
    (by rintro rfl; exact ht1iso y hxyA hdegy),
    (by rintro rfl; exact ht1iso z hyzA hdegz),
    (by rintro rfl; exact ht1iso y hyzA.symm hdegy),
    (by rintro rfl; exact ht2iso y hxyA hdegy),
    (by rintro rfl; exact ht2iso z hyzA hdegz),
    (by rintro rfl; exact ht2iso y hyzA.symm hdegy),
    (by rintro rfl; omega), (by rintro rfl; omega), (by rintro rfl; omega),
    hxy_ne, hyz_ne, hxz_ne⟩

/-- **Fat-dominating claw assembly with a deg-`≤ 5` hub (`n = 16`).**  Port of
`claw_shared_two_twin_sixteen` permitting `4 ≤ deg h ≤ 5`: the C₄ obstruction `h–i–c–j` has degree
sum `deg h + 9 ≤ 14`, so it is still forbidden by `hC4` at `deg h = 5`, and the hub meets at most
one of `c`'s three degree-`3` neighbours. -/
theorem claw_shared_two_twin_le5_sixteen (G : SimpleGraph (Fin 16)) (D : Finset (Fin 16))
    (hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 16, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (c t₁ t₂ h : Fin 16) (hcD : c ∈ D)
    (hcge : 3 ≤ (G.neighborFinset c ∩ D).card)
    (ht1deg : G.degree t₁ = 3) (ht2deg : G.degree t₂ = 3)
    (hhge4 : 4 ≤ G.degree h) (hhle5 : G.degree h ≤ 5)
    (ht12 : t₁ ≠ t₂) (hAt1h : G.Adj t₁ h) (hAt2h : G.Adj t₂ h)
    (ht1iso : ∀ w : Fin 16, G.Adj t₁ w → G.degree w ≠ 3)
    (ht2iso : ∀ w : Fin 16, G.Adj t₂ w → G.degree w ≠ 3) :
    TwoTwinConfig G := by
  classical
  have hdegD : ∀ v : Fin 16, v ∈ D → G.degree v = 3 := fun v hv => (hmemD v).mp hv
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
  have hmem_i : ∀ w : Fin 16, w ∈ ({n₁, n₂, n₃} : Finset (Fin 16)) → G.Adj c w ∧ w ∈ D := by
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
  have hcnbhd : ∀ w : Fin 16, G.Adj c w → w = n₁ ∨ w = n₂ ∨ w = n₃ := by
    intro w hw
    have hw' : w ∈ G.neighborFinset c ∩ D := by
      rw [hNsubeq]; exact (G.mem_neighborFinset _ _).mpr hw
    rw [hset] at hw'; simpa using hw'
  have hhc : ¬G.Adj h c := by
    intro hadj
    rcases hcnbhd h hadj.symm with e | e | e <;> rw [e] at hhge4 <;> omega
  have hmeet : ∀ i j : Fin 16, G.degree i = 3 → G.degree j = 3 →
      G.Adj c i → G.Adj c j → i ≠ j → ¬(G.Adj h i ∧ G.Adj h j) := by
    rintro i j hi3 hj3 ci cj hij ⟨hhi, hhj⟩
    have nij : ¬G.Adj i j := fun aij =>
      hT ⟨c, i, j, ci.ne, hij, cj.ne, ci, aij, cj, by omega⟩
    exact hC4 ⟨h, i, c, j,
      card_four_sixteen h i c j (by rintro rfl; omega) (by rintro rfl; omega)
        (by rintro rfl; omega) ci.ne.symm hij cj.ne,
      hhi, ci.symm, cj, hhj.symm, hhc, nij, by omega⟩
  have not12 := hmeet n₁ n₂ hd1 hd2 a1 a2 hne12
  have not13 := hmeet n₁ n₃ hd1 hd3 a1 a3 hne13
  have not23 := hmeet n₂ n₃ hd2 hd3 a2 a3 hne23
  by_cases hb1 : G.Adj h n₁
  · exact dense_two_twin_assemble_le5 G t₁ t₂ h n₂ c n₃ ht1deg ht2deg hhge4 hhle5
      hd2 hc3 hd3 hAt1h hAt2h a2.symm a3 ht1iso ht2iso
      (fun hv => not12 ⟨hb1, hv⟩) hhc (fun hv => not13 ⟨hb1, hv⟩) ht12
      a2.symm.ne a3.ne hne23
  · by_cases hb2 : G.Adj h n₂
    · exact dense_two_twin_assemble_le5 G t₁ t₂ h n₁ c n₃ ht1deg ht2deg hhge4 hhle5
        hd1 hc3 hd3 hAt1h hAt2h a1.symm a3 ht1iso ht2iso
        hb1 hhc (fun hv => not23 ⟨hb2, hv⟩) ht12 a1.symm.ne a3.ne hne13
    · exact dense_two_twin_assemble_le5 G t₁ t₂ h n₁ c n₂ ht1deg ht2deg hhge4 hhle5
        hd1 hc3 hd2 hAt1h hAt2h a1.symm a2 ht1iso ht2iso
        hb1 hhc hb2 ht12 a1.symm.ne a2.ne hne12

/-- **Dominating-edge fat-centre dispatch with a deg-`≤ 5` hub (`n = 16`).**  Port of
`dom_fat_centre_two_twin_sixteen` with the hub permitted degree `4` or `5`. -/
theorem dom_fat_centre_two_twin_le5_sixteen (G : SimpleGraph (Fin 16)) (D : Finset (Fin 16))
    (hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3)
    (hT : ¬∃ x y z : Fin 16, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (hC4 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (c₁ c₂ : Fin 16) (hc1D : c₁ ∈ D) (hc2D : c₂ ∈ D) (hc12 : G.Adj c₁ c₂)
    (hcov : ∀ p q : Fin 16, p ∈ D → q ∈ D → G.Adj p q →
      p = c₁ ∨ p = c₂ ∨ q = c₁ ∨ q = c₂)
    (hge : 8 ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card)
    (hindle : ∀ x : Fin 16, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3)
    (k t₁ t₂ : Fin 16) (hkge4 : 4 ≤ G.degree k) (hkle5 : G.degree k ≤ 5) (ht12 : t₁ ≠ t₂)
    (ht1deg : G.degree t₁ = 3) (ht2deg : G.degree t₂ = 3)
    (hAt1k : G.Adj t₁ k) (hAt2k : G.Adj t₂ k)
    (ht1iso : ∀ w : Fin 16, G.Adj t₁ w → G.degree w ≠ 3)
    (ht2iso : ∀ w : Fin 16, G.Adj t₂ w → G.degree w ≠ 3) :
    TwoTwinConfig G := by
  have hform := thin_eM_formula_sixteen G D c₁ c₂ hc1D hc2D hc12 hcov
  have hle1 := hindle c₁ hc1D
  have hle2 := hindle c₂ hc2D
  by_cases hc1 : 3 ≤ (G.neighborFinset c₁ ∩ D).card
  · exact claw_shared_two_twin_le5_sixteen G D hmemD hT hC4 c₁ t₁ t₂ k hc1D hc1 ht1deg ht2deg
      hkge4 hkle5 ht12 hAt1k hAt2k ht1iso ht2iso
  · have hc2 : 3 ≤ (G.neighborFinset c₂ ∩ D).card := by omega
    exact claw_shared_two_twin_le5_sixteen G D hmemD hT hC4 c₂ t₁ t₂ k hc2D hc2 ht1deg ht2deg
      hkge4 hkle5 ht12 hAt1k hAt2k ht1iso ht2iso

/-- **Shared deg-`≤ 5` hub in the `e(M) = 5`, `|D| = 10`, `|Hub| = 6` regime (`n = 16`).**  The
`≥ 4` `M`-isolated twins each meet `3` hubs; at most one hub has degree `≥ 6` (the residual
degree-excess over the six hubs is `26 − 24 = 2`), so excluding it leaves `≥ 2·|Iso| ≥ 8 > 6`
twin-incidences on the deg-`≤ 5` hubs, forcing a deg-`≤ 5` hub shared by two `M`-isolated twins. -/
theorem shared_hub_le5_eM5_sixteen (G : SimpleGraph (Fin 16))
    (hm : G.edgeFinset.card = 28) (h3 : ∀ v : Fin 16, 3 ≤ G.degree v)
    (h2k2 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hDge9 : 9 ≤ (Finset.univ.filter (fun w : Fin 16 => G.degree w = 3)).card)
    (hDle11 : (Finset.univ.filter (fun w : Fin 16 => G.degree w = 3)).card ≤ 11)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 10) :
    ∃ h t₁ t₂ : Fin 16, G.degree h ≤ 5 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 16, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 16, G.Adj t₂ w → G.degree w ≠ 3) := by
  classical
  set D : Finset (Fin 16) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 16) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 16, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  set Hub5 : Finset (Fin 16) :=
    Finset.univ.filter (fun v => 4 ≤ G.degree v ∧ G.degree v ≤ 5) with hHub5def
  have hmemHub5 : ∀ v : Fin 16, v ∈ Hub5 ↔ 4 ≤ G.degree v ∧ G.degree v ≤ 5 := by
    intro v; rw [hHub5def]; simp
  set H6 : Finset (Fin 16) := Finset.univ.filter (fun v => 6 ≤ G.degree v) with hH6def
  have hmemH6 : ∀ v : Fin 16, v ∈ H6 ↔ 6 ≤ G.degree v := by intro v; rw [hH6def]; simp
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  -- `∑_{Hub} deg = 26` from the handshake.
  have hsum56 : ∑ v : Fin 16, G.degree v = 56 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 56 := by
    rw [Finset.sum_add_sum_compl]; exact hsum56
  have hHubsum : ∑ v ∈ Hub, G.degree v = 56 - 3 * D.card := by
    rw [hHubeqDc]; rw [hsumD] at hsplit; omega
  have hHubcard : Hub.card = 16 - D.card := by
    rw [hHubeqDc, Finset.card_compl]; simp [Fintype.card_fin]
  have hH6sub : H6 ⊆ Hub := by
    intro v hv; rw [hmemH6] at hv; rw [hmemHub]; omega
  -- `Hub5` and `H6` partition `Hub`; `∑_{Hub5} deg ≥ 4|Hub5|` and `∑_{H6} deg ≥ 6|H6|`.
  have hHub5sub : ∀ v ∈ Hub5, 4 ≤ G.degree v := fun v hv => ((hmemHub5 v).mp hv).1
  have hH6ge : ∀ v ∈ H6, 6 ≤ G.degree v := fun v hv => (hmemH6 v).mp hv
  -- `Iso`.
  set Iso : Finset (Fin 16) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 16, G.Adj v w → G.degree w ≠ 3 := by
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
        = ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card := cross_count G Iso H6
    have hH6degbound : ∑ h ∈ H6, (G.neighborFinset h ∩ Iso).card ≤ ∑ h ∈ H6, G.degree h := by
      apply Finset.sum_le_sum
      intro h _
      calc (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
            Finset.card_le_card Finset.inter_subset_left
        _ = G.degree h := G.card_neighborFinset_eq_degree h
    omega
  have hHub5deg : ∀ h ∈ Hub5, G.degree h ≤ 5 := fun h hh => ((hmemHub5 h).mp hh).2
  exact shared_hub_le5_from_count_sixteen G Iso Hub5 hIsoiso hHub5deg hcount

/-- **`|Iso| ≥ |D| − 5` in the induced-`C₅`, `e(M) = 5` regime (`n = 16`).**  The five cycle
vertices each have in-`M`-degree `≥ 2`, so they already carry all `10 = ∑_{v∈D}|N v ∩ D|`; hence
every degree-`3` vertex outside the cycle is `M`-isolated, giving `|Iso| ≥ |D| − 5`. -/
theorem iso_ge_C5_sixteen (G : SimpleGraph (Fin 16)) (D : Finset (Fin 16))
    (hsum10 : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 10)
    (v₁ v₂ v₃ v₄ v₅ : Fin 16)
    (hv1D : v₁ ∈ D) (hv2D : v₂ ∈ D) (hv3D : v₃ ∈ D) (hv4D : v₄ ∈ D) (hv5D : v₅ ∈ D)
    (hcard5 : ({v₁, v₂, v₃, v₄, v₅} : Finset (Fin 16)).card = 5)
    (e12 : G.Adj v₁ v₂) (e23 : G.Adj v₂ v₃) (e34 : G.Adj v₃ v₄)
    (e45 : G.Adj v₄ v₅) (e51 : G.Adj v₅ v₁) :
    D.card - 5 ≤ (D.filter (fun v => (G.neighborFinset v ∩ D).card = 0)).card := by
  classical
  obtain ⟨_d12, d13, d14, _d15, _d23, d24, d25, _d34, d35, _d45⟩ :=
    distinct_five_sixteen v₁ v₂ v₃ v₄ v₅ hcard5
  set C : Finset (Fin 16) := {v₁, v₂, v₃, v₄, v₅} with hCdef
  have hCsub : C ⊆ D := by
    intro w hw; rw [hCdef] at hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
  have two_nbrs : ∀ a b c : Fin 16, G.Adj a b → G.Adj a c → b ∈ D → c ∈ D → b ≠ c →
      2 ≤ (G.neighborFinset a ∩ D).card := by
    intro a b c hab hac hbD hcD hbc
    have hsub : ({b, c} : Finset (Fin 16)) ⊆ G.neighborFinset a ∩ D := by
      intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hab, hbD⟩
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hac, hcD⟩
    have hbc2 : ({b, c} : Finset (Fin 16)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    calc 2 = ({b, c} : Finset (Fin 16)).card := hbc2.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hCge : ∀ v ∈ C, 2 ≤ (G.neighborFinset v ∩ D).card := by
    intro v hv; rw [hCdef] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h | h | h | h <;> rw [h]
    · exact two_nbrs v₁ v₂ v₅ e12 e51.symm hv2D hv5D d25
    · exact two_nbrs v₂ v₁ v₃ e12.symm e23 hv1D hv3D d13
    · exact two_nbrs v₃ v₂ v₄ e23.symm e34 hv2D hv4D d24
    · exact two_nbrs v₄ v₃ v₅ e34.symm e45 hv3D hv5D d35
    · exact two_nbrs v₅ v₄ v₁ e45.symm e51 hv4D hv1D d14.symm
  have hCcard : C.card = 5 := by rw [hCdef]; exact hcard5
  have hCsum : 10 ≤ ∑ v ∈ C, (G.neighborFinset v ∩ D).card := by
    calc 10 = 2 * C.card := by rw [hCcard]
      _ = ∑ _v ∈ C, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ C, (G.neighborFinset v ∩ D).card := Finset.sum_le_sum hCge
  have hsdiff : ∑ v ∈ D \ C, (G.neighborFinset v ∩ D).card
      + ∑ v ∈ C, (G.neighborFinset v ∩ D).card = 10 := by
    rw [Finset.sum_sdiff hCsub]; exact hsum10
  have hCle : ∑ v ∈ C, (G.neighborFinset v ∩ D).card ≤ 10 := by omega
  have hCeq : ∑ v ∈ C, (G.neighborFinset v ∩ D).card = 10 := le_antisymm hCle hCsum
  have hDC0 : ∑ v ∈ D \ C, (G.neighborFinset v ∩ D).card = 0 := by omega
  have hDCsub : D \ C ⊆ D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) := by
    intro v hv
    rw [Finset.mem_filter]
    refine ⟨(Finset.mem_sdiff.mp hv).1, ?_⟩
    exact (Finset.sum_eq_zero_iff.mp hDC0) v hv
  have hDCcard : (D \ C).card = D.card - 5 := by
    have h1 : (D \ C).card + C.card = D.card := Finset.card_sdiff_add_card_eq_card hCsub
    rw [hCcard] at h1; omega
  calc D.card - 5 = (D \ C).card := hDCcard.symm
    _ ≤ _ := Finset.card_le_card hDCsub

/-- **Shared degree-`4` hub from `|Iso| ≥ 5` (`n = 16`, `|D| = 10`, `|Hub| = 6`).**  The residual
degree-excess over the six hubs is `26 − 24 = 2`, so `|H₅| ≤ 2`; the refined cross count
`∑_{Iso}|N ∩ Hub₄| = 3|Iso| − ∑_{H₅}|N ∩ Iso| ≥ 15 − (2 + 4|H₅|)` against `|Hub₄| = 6 − |H₅|` is
strict (`26 < 3(|Iso| + |Hub₄|)`), forcing a degree-`4` hub shared by two `M`-isolated twins. -/
theorem shared_deg4_hub_iso5_sixteen (G : SimpleGraph (Fin 16))
    (hm : G.edgeFinset.card = 28) (h3 : ∀ v : Fin 16, 3 ≤ G.degree v)
    (hDge9 : 9 ≤ (Finset.univ.filter (fun w : Fin 16 => G.degree w = 3)).card)
    (hDle11 : (Finset.univ.filter (fun w : Fin 16 => G.degree w = 3)).card ≤ 11)
    (hIsoC : (Finset.univ.filter (fun w : Fin 16 => G.degree w = 3)).card - 5 ≤
      ((Finset.univ.filter (fun w : Fin 16 => G.degree w = 3)).filter
      (fun v => (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 0)).card) :
    ∃ h t₁ t₂ : Fin 16, G.degree h = 4 ∧ t₁ ≠ t₂ ∧
      G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.Adj t₁ h ∧ G.Adj t₂ h ∧
      (∀ w : Fin 16, G.Adj t₁ w → G.degree w ≠ 3) ∧
      (∀ w : Fin 16, G.Adj t₂ w → G.degree w ≠ 3) := by
  classical
  set D : Finset (Fin 16) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  set Hub : Finset (Fin 16) := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hHubdef
  have hmemHub : ∀ v : Fin 16, v ∈ Hub ↔ 4 ≤ G.degree v := by intro v; rw [hHubdef]; simp
  set Hub4 : Finset (Fin 16) := Finset.univ.filter (fun v => G.degree v = 4) with hHub4def
  have hmemHub4 : ∀ v : Fin 16, v ∈ Hub4 ↔ G.degree v = 4 := by intro v; rw [hHub4def]; simp
  have hHub4deg : ∀ h ∈ Hub4, G.degree h = 4 := fun h hh => (hmemHub4 h).mp hh
  set H5 : Finset (Fin 16) := Finset.univ.filter (fun v => 5 ≤ G.degree v) with hH5def
  have hmemH5 : ∀ v : Fin 16, v ∈ H5 ↔ 5 ≤ G.degree v := by intro v; rw [hH5def]; simp
  have hHubeqDc : Hub = Dᶜ := by
    ext w; rw [hmemHub, Finset.mem_compl, hmemD]; have := h3 w; omega
  have hsum56 : ∑ v : Fin 16, G.degree v = 56 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 56 := by
    rw [Finset.sum_add_sum_compl]; exact hsum56
  have hHubsum : ∑ v ∈ Hub, G.degree v = 56 - 3 * D.card := by
    rw [hHubeqDc]; rw [hsumD] at hsplit; omega
  have hHubcard : Hub.card = 16 - D.card := by
    rw [hHubeqDc, Finset.card_compl]; simp [Fintype.card_fin]
  -- `Hub₄` and `H₅` partition `Hub = Dᶜ`.
  have hdisjHub : Disjoint Hub4 H5 :=
    Finset.disjoint_left.mpr (fun a ha ha' => by
      have := (hmemHub4 a).mp ha; have := (hmemH5 a).mp ha'; omega)
  have huHub : Hub4 ∪ H5 = Hub := by
    ext w; rw [Finset.mem_union, hmemHub4, hmemH5, hmemHub]; omega
  have hHubpart : Hub4.card + H5.card = Hub.card := by
    rw [← huHub, Finset.card_union_of_disjoint hdisjHub]
  have hHub4degsum : ∑ v ∈ Hub4, G.degree v = 4 * Hub4.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemHub4 v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hDcdegsplit : ∑ v ∈ Hub4, G.degree v + ∑ v ∈ H5, G.degree v = ∑ v ∈ Hub, G.degree v := by
    rw [← Finset.sum_union hdisjHub, huHub]
  -- `|H₅| ≤ |D| − 8`.
  have hH5le : H5.card ≤ D.card - 8 := by
    have hge : ∀ v ∈ Hub, 4 + (if v ∈ H5 then 1 else 0) ≤ G.degree v := by
      intro v hv
      by_cases hvH5 : v ∈ H5
      · rw [if_pos hvH5]; have := (hmemH5 v).mp hvH5; omega
      · rw [if_neg hvH5]; exact (hmemHub v).mp hv
    have hle := Finset.sum_le_sum hge
    have hH5sub : H5 ⊆ Hub := by intro v hv; rw [hmemH5] at hv; rw [hmemHub]; omega
    have hval : ∑ v ∈ Hub, (4 + (if v ∈ H5 then 1 else 0)) = 4 * Hub.card + H5.card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
      have : ∑ v ∈ Hub, (if v ∈ H5 then 1 else 0) = H5.card := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hH5sub, Finset.sum_const,
          smul_eq_mul, mul_one]
      rw [this]
    rw [hval, hHubsum, hHubcard] at hle
    omega
  -- `Iso`.
  set Iso : Finset (Fin 16) := D.filter (fun v => (G.neighborFinset v ∩ D).card = 0) with hIsodef
  have hIsoiso : ∀ v ∈ Iso, G.degree v = 3 ∧ ∀ w : Fin 16, G.Adj v w → G.degree w ≠ 3 := by
    intro v hv
    rw [hIsodef, Finset.mem_filter] at hv
    obtain ⟨hvD, hv0⟩ := hv
    refine ⟨(hmemD v).mp hvD, fun w hadj hw3 => ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hv0
    exact hv0 w (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj, (hmemD w).mpr hw3⟩)
  -- Refined cross count.
  have hcount : Hub4.card < ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card := by
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
          have := (hmemHub4 a).mp ha.2; have := (hmemH5 a).mp ha'.2; omega)
      rw [← Finset.card_union_of_disjoint hdisj, ← Finset.inter_union_distrib_left, huHub]
    have hsumsplit : ∑ v ∈ Iso, (G.neighborFinset v ∩ Hub4).card
        + ∑ v ∈ Iso, (G.neighborFinset v ∩ H5).card = 3 * Iso.card := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hvsplit, hsumHub3]
    have hcrossH5 : ∑ v ∈ Iso, (G.neighborFinset v ∩ H5).card
        = ∑ h ∈ H5, (G.neighborFinset h ∩ Iso).card := cross_count G Iso H5
    have hH5degbound : ∑ h ∈ H5, (G.neighborFinset h ∩ Iso).card ≤ ∑ h ∈ H5, G.degree h := by
      apply Finset.sum_le_sum
      intro h _
      calc (G.neighborFinset h ∩ Iso).card ≤ (G.neighborFinset h).card :=
            Finset.card_le_card Finset.inter_subset_left
        _ = G.degree h := G.card_neighborFinset_eq_degree h
    omega
  exact shared_deg4_hub_from_count_sixteen G Iso Hub4 hIsoiso hHub4deg hcount

/-- **`e(M) = 5` (`s = 10`) two-twin cut for the `|D| = 10`, `|Hub| = 6` corner (`n = 16`).**  The
double-star branch routes a deg-`≤ 5` shared hub through the leaf-cherry (`claw`) assembly; the
induced-`C₅` branch derives `|Iso| ≥ 5`, extracts a deg-`4` shared hub and applies the `C₅`
two-twin assembly.  This closes the `e(M) = 5` sub-case of the `|Hub| = 6` alignment selector. -/
theorem two_twin_eM5_sixteen (G : SimpleGraph (Fin 16))
    (hm : G.edgeFinset.card = 28) (h3 : ∀ v : Fin 16, 3 ≤ G.degree v)
    (hT : ¬∃ x y z : Fin 16, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧ G.degree x + G.degree y + G.degree z ≤ 10)
    (h2k2 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
      G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d)
    (hC4 : ¬∃ a b c d : Fin 16, ({a, b, c, d} : Finset (Fin 16)).card = 4 ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14)
    (g : Fin 16) (hg5 : 5 ≤ G.degree g)
    (hsum10 : ∑ v ∈ Finset.univ.filter (fun w => G.degree w = 3),
      (G.neighborFinset v ∩ Finset.univ.filter (fun w => G.degree w = 3)).card = 10) :
    TwoTwinConfig G := by
  classical
  set D : Finset (Fin 16) := Finset.univ.filter (fun w => G.degree w = 3) with hDdef
  have hmemD : ∀ v : Fin 16, v ∈ D ↔ G.degree v = 3 := by intro v; rw [hDdef]; simp
  have hindle : ∀ x : Fin 16, x ∈ D → (G.neighborFinset x ∩ D).card ≤ 3 := by
    intro x hx
    calc (G.neighborFinset x ∩ D).card ≤ (G.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = 3 := (hmemD x).mp hx
  have hge : 8 ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by omega
  -- `9 ≤ |D| ≤ 11` from the degree-`5` hub and the cross count.
  have hsum56 : ∑ v : Fin 16, G.degree v = 56 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsplit : ∑ v ∈ D, G.degree v + ∑ v ∈ Dᶜ, G.degree v = 56 := by
    rw [Finset.sum_add_sum_compl]; exact hsum56
  have hcc : D.card + Dᶜ.card = 16 := by
    have h := Finset.card_add_card_compl D; simp only [Fintype.card_fin] at h; exact h
  have hDcdeg : ∀ v ∈ Dᶜ, 4 ≤ G.degree v := by
    intro v hv; rw [Finset.mem_compl, hmemD] at hv; have := h3 v; omega
  have hgDc : g ∈ Dᶜ := by rw [Finset.mem_compl, hmemD]; omega
  have hDge9 : 9 ≤ D.card := by
    have hsg := (Finset.add_sum_erase Dᶜ (fun v => G.degree v) hgDc).symm
    have hrest : 4 * (Dᶜ.erase g).card ≤ ∑ v ∈ Dᶜ.erase g, G.degree v := by
      have hb : ∀ x ∈ Dᶜ.erase g, 4 ≤ G.degree x :=
        fun x hx => hDcdeg x (Finset.mem_of_mem_erase hx)
      have := Finset.card_nsmul_le_sum (Dᶜ.erase g) (fun v => G.degree v) 4 hb
      simpa [smul_eq_mul, mul_comm] using this
    have hcg : (Dᶜ.erase g).card = Dᶜ.card - 1 := Finset.card_erase_of_mem hgDc
    have hpos : 1 ≤ Dᶜ.card := Finset.card_pos.mpr ⟨g, hgDc⟩
    rw [hsumD] at hsplit; omega
  have hdegsplit : ∀ v : Fin 16,
      (G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card = G.degree v := by
    intro v
    have hdisj : Disjoint (G.neighborFinset v ∩ D) (G.neighborFinset v ∩ Dᶜ) :=
      Finset.disjoint_left.mpr (fun a ha ha' => by
        rw [Finset.mem_inter] at ha ha'; exact (Finset.mem_compl.mp ha'.2) ha.2)
    have hun : (G.neighborFinset v ∩ D) ∪ (G.neighborFinset v ∩ Dᶜ) = G.neighborFinset v := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    rw [← Finset.card_union_of_disjoint hdisj, hun, G.card_neighborFinset_eq_degree]
  have hsum10D : ∑ v ∈ D, (G.neighborFinset v ∩ D).card = 10 := hsum10
  have hDle11 : D.card ≤ 11 := by
    have hcross : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
        = ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card := cross_count G D Dᶜ
    have hsumDND : ∑ v ∈ D, (G.neighborFinset v ∩ Dᶜ).card
        = 3 * D.card - ∑ v ∈ D, (G.neighborFinset v ∩ D).card := by
      have hcong : ∑ v ∈ D, ((G.neighborFinset v ∩ D).card + (G.neighborFinset v ∩ Dᶜ).card)
          = ∑ v ∈ D, G.degree v :=
        Finset.sum_congr rfl (fun v _ => hdegsplit v)
      rw [Finset.sum_add_distrib, hsumD] at hcong; omega
    have hle : ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ D).card ≤ ∑ w ∈ Dᶜ, G.degree w := by
      apply Finset.sum_le_sum
      intro w _
      calc (G.neighborFinset w ∩ D).card ≤ (G.neighborFinset w).card :=
            Finset.card_le_card Finset.inter_subset_left
        _ = G.degree w := G.card_neighborFinset_eq_degree w
    rw [hsumD] at hsplit; omega
  have hDge9' : 9 ≤ (Finset.univ.filter (fun w : Fin 16 => G.degree w = 3)).card := by
    rw [← hDdef]; exact hDge9
  have hDle11' : (Finset.univ.filter (fun w : Fin 16 => G.degree w = 3)).card ≤ 11 := by
    rw [← hDdef]; exact hDle11
  have hne : ∃ a b : Fin 16, a ∈ D ∧ b ∈ D ∧ G.Adj a b := by
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
      shared_hub_le5_eM5_sixteen G hm h3 h2k2 hDge9' hDle11' hsum10
    have hkge4 : 4 ≤ G.degree k := by
      have := htw1iso k hAtw1k; have := h3 k; omega
    exact dom_fat_centre_two_twin_le5_sixteen G D hmemD hT hC4 c₁ c₂ hc1D hc2D hc12 hcov hge
      hindle k tw1 tw2 hkge4 hkle5 htw12 htw1deg htw2deg hAtw1k hAtw2k htw1iso htw2iso
  · obtain ⟨v₁, v₂, v₃, v₄, v₅, hv1D, hv2D, hv3D, hv4D, hv5D, hcard5,
      e12, e23, e34, e45, e51, n13, n14, n24, n25, n35, _⟩ := hC5
    have hIsoC := iso_ge_C5_sixteen G D hsum10D v₁ v₂ v₃ v₄ v₅
      hv1D hv2D hv3D hv4D hv5D hcard5 e12 e23 e34 e45 e51
    have hIsoC' : (Finset.univ.filter (fun w : Fin 16 => G.degree w = 3)).card - 5 ≤
        ((Finset.univ.filter (fun w : Fin 16 => G.degree w = 3)).filter
          (fun v => (G.neighborFinset v ∩
            Finset.univ.filter (fun w => G.degree w = 3)).card = 0)).card := by
      rw [← hDdef]; exact hIsoC
    obtain ⟨k, tw1, tw2, hkdeg4, htw12, htw1deg, htw2deg, hAtw1k, hAtw2k, htw1iso, htw2iso⟩ :=
      shared_deg4_hub_iso5_sixteen G hm h3 hDge9' hDle11' hIsoC'
    exact c5_shared_two_twin_sixteen G hT hC4 k tw1 tw2 hkdeg4 htw12 htw1deg htw2deg hAtw1k hAtw2k
      htw1iso htw2iso v₁ v₂ v₃ v₄ v₅ ((hmemD v₁).mp hv1D) ((hmemD v₂).mp hv2D)
      ((hmemD v₃).mp hv3D) ((hmemD v₄).mp hv4D) ((hmemD v₅).mp hv5D) hcard5
      e12 e23 e34 e45 e51 n13 n14 n24 n25 n35

end N16

end ACMax
